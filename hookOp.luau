local parser = require("@std/syntax/parser")
local fs = require("@std/fs")
local prettyPrint = true

local constantCollection
local format = string.format

local function readfile(path : string) : string?
    assert(fs.exists(path), "invalid argument #1 to 'readfile', file does not exist.")

    local handle = fs.open(path, "r");
    local content = fs.read(handle)
    fs.close(handle)
    return content
end

local maxNum, tab, visited, callId = 2^64, "    ", {}, nil;

local beautifyHandlers = {
    table = function(data, tabs)
        if visited[data] then return "{ 'recursive table' }" end

        tabs = tabs or 1

        local out = "{\n"
        local p = string.rep(tab, tabs);

        visited[data] = true

        for i, v in next, data do
            --if i == "location" or i == "position" or i == "trailingtrivia" or i == "leadingtrivia" then continue end

            out ..= `{p}[{beautify(i, tabs + 1)}] = {beautify(v, tabs + 1)},\n`
        end

        visited[data] = false

        if #out == 2 then return "{}" end

        return out:sub(1, -3) .. "\n" .. string.rep(tab, tabs - 1) .. "}"
    end,
    string = function(data, style, depth)
        if (style == 'block') then
            local equals = string.rep("=", depth or 1)
            return format("[%s[%s]%s]", equals, data, equals)
        else
            local quote = style == "double" and '"' or style == "interp" and "`" or "'"
            return quote .. data .. quote
        end
    end,
    number = function(data)
        local str = tostring(data)
        if str == "nan" then return "0/0" elseif str == "inf" then return "math.huge" elseif str == "-inf" then return "-math.huge" end

        return str
    end
}

function beautify(data : any, ...) : string
    local type = typeof(data);

    local f = beautifyHandlers[type] or tostring
    return f(data, ...);
end

local function callFormat(...)
    return callId .. format(...)
end

local unparser = {
    binaryOperatorNames = {
        ["and"] = "CHECKAND",
        ["or"] = "CHECKOR",
        [">"] = "COMPG",
        ["<"] = "COMPL",
        [">="] = "COMPGE",
        ["<="] = "COMPLE",
        ["=="] = "CHECKEQ",
        ["~="] = "CHECKNEQ",
        [".."] = "CONCAT"
    },
    unaryOperatorNames = {
        ["#"] = "CHECKLEN",
        ["-"] = "CHECKUNM",
        ["not"] = "CHECKNOT"
    }
}

local forId, ifId, whileId = 0, 0, 0;
local lines = {}

local function readParams(statement)
    local code = "("

    local params = statement.parameters

    for i, param in params do
        code = code .. (i > 1 and ", " or "") .. unparser:readexpr(param)
    end
    if statement.vararg then
        code = code .. (#params == 0 and "" or ",") .. "..."
    end
    
    return code .. ")", statement.vararg
end

local function getValue(op, v1, v2)
    if op == "+" then return v1 + v2
    elseif op == "-" then return v1 - v2
    elseif op == "*" then return v1 * v2
    elseif op == "/" then return v1 / v2
    elseif op == "^" then return v1 ^ v2
    elseif op == "%" then return v1 % v2
    elseif op == ".." then return v1 .. v2
    elseif op == "//" then return v1 // v2
    elseif op == "and" then return v1 and v2
    elseif op == "or" then return v1 or v2
    elseif op == "==" then return v1 == v2
    elseif op == "~=" then return v1 ~= v2
    elseif op == ">" then return v1 > v2
    elseif op == "<" then return v1 < v2
    elseif op == ">=" then return v1 >= v2
    elseif op == "<=" then return v1 <= v2
    end
end

function unparser:construct(statement : table) : table
    if statement.istoken then
        return {
            class = "constant"
        }
    end

    if statement.kind == "stat" then --> statement
        return {
            class = "statement",
            kind = statement.tag
        }
    elseif statement.kind == "expr" then
        return {
            class = "expression",
            kind = statement.tag
        }
    end

    return {
        class = "other"
    }
end

local function is(statement, tag, deepSearch) --> tries to find the deepest mention of 'tag' that does not make it contradict it's original value (for example in a + )
    if not statement then return false end
    if statement.tag == tag then return statement end
    if statement.expression then --> works for groups!
        return is(statement.expression, tag)
    end
    if statement.lhsoperand then
        return is(statement.lhsoperand, tag)
    end
    if statement.tag == "unary" then
        return is(statement.operand, tag)
    end
    if deepSearch then
        if statement.rhsoperand then
            return is(statement.rhsoperand, tag)
        end
    end
end

local Spied = {}

local function Spy(statement)
    local tag = statement.tag
    if tag == "global" or tag == "call" or tag == "index" or tag == "indexname" then
        Spied[statement] = true
    end
end

local function isSpiedVar(statement, dontIncludeLocals)
    -- This isn't 100% accurate, it's just if this is false, then you can treat the statement as normal, otherwise hook certain things. (For optimization)
    local Binary = is(statement, "binary")
    if(Binary) then
        --> keep looking through the operands till u find a spied var
        if(isSpiedVar(Binary.lhsoperand) or isSpiedVar(Binary.rhsoperand)) then
            return true;
        end
    end

    return
        is(statement, "global") or
        is(statement, "call") or
        is(statement, "index") or
        is(statement, "indexname") or
        (not dontIncludeLocals and statement.tag == "local") or
        Spied[statement];
end

local function getLength(thing)
    local count = 0;
    if thing.tag == "table" then
        for i in thing.entries do
            count += 1
        end
    elseif thing.tag == "string" then
        count = #thing.text
    end
    return count
end

function unparser:readstatementF(statement, dontAddDo, ...)
    --> if dontAddDo is on, it also means that we're in an if check / while loop / something, which means we need to properly close before 'return' or 'break'
    local tag = statement.tag

    Spy(statement)

    if tag == "local" then
        local code = "local ";
        local DoSpy;
        for i, var in statement.variables do
            local variable = var.node.name.text
            code = code .. (i > 1 and "," or "") .. variable
        end
        if #statement.values == 0 then return code end

        code = code .. " = "
        for i, val in statement.values do
            code = code .. (i > 1 and "," or "") .. self:readexpr(val.node)
            DoSpy = DoSpy or Spied[val.node]
        end
        Spied[statement] = Spied[statement] or DoSpy
        return code
    elseif tag == "assign" then
        local code = "";

        for i, var in statement.variables do
            code = code .. (i > 1 and ", " or "") .. self:readexpr(var.node, false, true)
        end

        code = code .. " = "

        for i, val in statement.values do
            local node = val.node
            local var = statement.variables[i]
            if constantCollection and (var and is(var.node, "index") or is(node, "string")) then -- a[x] = 1 or a = "hi"
                code = code .. callFormat("GET(%s)", self:readexpr(node))
            else
                code = code .. self:readexpr(node)
            end
            if(i~=#statement.values) then code = code .. "," end
        end
        return code
    elseif tag == "compoundassign" then
        return format("%s%s%s", self:readexpr(statement.variable, nil, true), statement.operand.text, self:readexpr(statement.value))
    elseif tag == "expression" then
        return self:readexpr(statement.expression)
    elseif tag == "function" then
        local params, vararg = readParams(statement.body)
        local code = "function " .. self:readexpr(statement.name, nil, true, true) .. params
        code = code .. self:readexpr(statement.body.body, true, nil, vararg) .. "end"
        
        return code
    elseif tag == "block" then
        local location = statement.location.begin
        local content = lines[location.line + 1]
        local shouldAddDo = content:sub(location.column + 1, location.column + 2) == "do"
        local code = shouldAddDo and "do " or ""
        
        for _, stat in statement.statements do
            local str = self:readexpr(stat, typeof(dontAddDo) == "string" and dontAddDo or nil)
            code = code .. str .. (str ~= "..." and str:sub(#str) ~= ";" and ";" or "")
        end
        return code .. (shouldAddDo and "end;" or "")
    elseif tag == "localfunction" then
        local name = self:readexpr(statement.name)
        local params, vararg = readParams(statement.body)
        local code = "local function " .. name .. params
        code = code .. self:readexpr(statement.body.body, true, nil, vararg) .. "end"
        
        return code
    elseif tag == "conditional" then
        ifId += 1

        local elseblock = statement.elseblock
        local condition = self:readexpr(statement.condition)
        local Thing, Path;

        local Elseifs = statement.elseifs

        if(not isSpiedVar(statement.condition)) then
            Thing = condition
        else
            Thing = callFormat("CHECKIF(%s,%d,%d)", condition, ifId, elseblock and 1 or 0)
            Path = callFormat("checkifend(%d)", ifId)
        end

        local code = format("if %s then %s", Thing, self:readstatement(statement.thenblock, Path))

        for _, elif in next, Elseifs do
            local OtherThing = callFormat("CHECKIF(%s,%d)", self:readexpr(elif.condition), ifId)
            --local OtherThing = callFormat("CHECKELSEIF(%s,%d)", self:readexpr(elif.condition), ifId)

            code = code .. format("elseif %s then %s", OtherThing, self:readstatement(elif.thenblock, Path))
        end

        if elseblock then
            code = code .. format("else %s", self:readexpr(elseblock, Path))
        end

        return code .. "end" .. (Path and ";" .. Path or "");
    elseif tag == "while" then
        whileId += 1

        local Cond = self:readexpr(statement.condition)
        local While = callFormat("checkwhile(%s,%d)", Cond, whileId)
        local WhileEnd = callFormat("checkwhileend(%d)", whileId)

        if (isSpiedVar(statement.condition) or is(statement.condition, "boolean") or is(statement.condition, "bool")) then
            return format("while %s do %send;%s", While, self:readstatement(statement.body, WhileEnd), WhileEnd)
        else
            return format("while %s do %send", Cond, self:readstatement(statement.body))
        end
    elseif tag == "return" then
        --local Start = (dontAddDo and dontAddDo .. ";" or "") .. "return"
        local Start = "return "
        --[[if dontAddDo then
            Start = Start .. callFormat("BREAK(%s",dontAddDo:match("%((%d+)"))
        end]]

        if #statement.expressions == 0 then
            if dontAddDo then
               -- return Start .. ")"
            end
            return Start
        end

        local args = ""
        for i, node in statement.expressions do
            --args = args .. (dontAddDo and ", " or (i > 1 and ", " or "")) .. self:readexpr(node.node)
            args = args .. (i > 1 and ", " or "") .. self:readexpr(node.node)
        end

        Start = Start .. args-- .. (dontAddDo and ")" or "")
        
        return Start
    elseif tag == "for" then
        forId += 1

        local stepCode = statement.step
        stepCode = stepCode and "," .. self:readexpr(stepCode) or "";

        local from, to = self:readexpr(statement.from), self:readexpr(statement.to)
        local var = statement.variable.name.text
        local code =
            callFormat("FORINFO(%d,%s,%s%s)", forId, from, to, stepCode) --> feed info into unveilr
        
        --code = code .. `for {var}={callFormat("FORSTEP1(%d)", forId)},{callFormat("FORSTEP2(%d)", forId)}{stepCode} do {var}+={callFormat("FORSTEP3(%d)", forId)}; {self:readstatement(statement.body, true)}end`
        code = code .. `for {var}={callFormat("FORSTEP1(%d)", forId)},{callFormat("FORSTEP2(%d)", forId)}{stepCode} do {self:readstatement(statement.body, true)}end`

        return code
    elseif tag == "forin" then
        local code = "for "
        for i, node in statement.variables do
            code = code .. (i > 1 and ", " or "") .. node.node.name.text
        end
        local forin = ""
        for i, val in statement.values do
            forin = forin .. (i > 1 and ", " or "") .. self:readexpr(val.node)
        end

        code = code .. format(" in %s do %send", forin, self:readstatement(statement.body, true))
        return code
    elseif tag == "repeat" then
        return format("repeat %s until %s", self:readexpr(statement.body, true), self:readexpr(statement.condition))
    elseif tag == "typealias" then -- export
        return format("export type %s = %s", statement.name.text, self:readexpr(statement.type, nil, nil, true))
    end

    print(beautify(statement))
    error("unsupported statement '" .. (statement.tag or "???") .. "'")
end

function unparser:readstatement(...)
    local stat = self:readstatementF(...)
    
    if(prettyPrint) then
        stat = "\n" .. stat
    end
    return stat
end

function unparser:readexpr(statement, ...)
    local expr = self:construct(statement)

    if expr.class == "statement" then
        return self:readstatement(statement, ...)
    elseif statement.istoken and not statement.tag then
        if statement.value ~= nil then return beautify(statement.value, statement.quotestyle) end

        return beautify(statement.text, statement.quotestyle)
    end

    local node = statement.node
    if node then statement = node end

    local tag = statement.tag or statement.kind;

    local _, _, rawNextQuestion = ...
    if not rawNextQuestion then rawNextQuestion = not constantCollection end

    if tag == "number" then
        return statement.value or statement.text
    elseif tag == "string" then
        return beautify(statement.text, statement.quotestyle, statement.blockdepth)
    elseif tag == "nil" then
        return "nil"
    elseif tag == "vararg" then
        return "..."
    elseif tag == "break" then
        local thing = ...
        return "break"
    elseif tag == "continue" then
        return "continue"
    elseif tag == "bool" or tag == "boolean" then
        return tostring(statement.value)
    elseif tag == "call" then --> call
        local start = ""
        local func = self:readexpr(statement.func, nil, statement.self)

        if statement.func.tag == "group" then
            local code = func .. "("

            for i, arg in statement.arguments do
                local data = self:readexpr(arg.node)

                code = code .. (i>1 and "," or "") .. data
            end
            return code .. ")"
        elseif statement.self then
            start = callFormat("NAMECALL(%s", func)
        else
            start = callFormat("CALL(%s", func)
        end

        local code = start--callFormat("CALL(%s", self:readexpr(statement.func))

        for i, arg in statement.arguments do
            local comma = ","
            local data = self:readexpr(arg.node)

            code = code .. comma .. data
        end

        return code .. ")"
    elseif tag == "local" or tag == "global" then --> variable name
        return (statement.name or statement.token).text
    elseif tag == "table" then
        local code = "{";
        local len = #statement.entries

        for i, entry in statement.entries do
            local key = entry.key
            if rawNextQuestion then
                if(isSpiedVar(entry.value) or (key and isSpiedVar(key))) then
                    rawNextQuestion = false
                end
            end

            if key then
                if entry.value.tag == "reference" then
                    code = code .. format("%s: %s%s", key.text, self:readexpr(entry.value), (i ~= len and ";" or ""))
                    continue
                end
                code = code .. format("[%s]=", self:readexpr(entry.key))
            end
            code = code .. self:readexpr(entry.value) .. (i ~= len and ";" or "")
        end

        code = code .. "}"

        if not rawNextQuestion then
            code = callFormat("CONSTRUCT(%s)", code)
        end

        return code
    elseif tag == "binary" then -- comparison, math & eq
        local rhs = statement.rhsoperand
        local lhs = statement.lhsoperand
        local operator = statement.operator.text

        if not rhs.istoken or not lhs.istoken then --> Cant simplify, just return it raw (Or, apply the custom funcs)
            local name = self.binaryOperatorNames[operator]

            local Lhs = unparser:readexpr(lhs)--Simplify(lhs, DoIgnore);
            local Rhs = unparser:readexpr(rhs)--Simplify(rhs, DoIgnore);

            local Wrapped = (is(rhs, "call") or is(rhs, "unary")) and "function(...)return " .. Rhs .. " end" or Rhs

            if name then
                if name == "CHECKAND" or name == "CHECKOR" then
                    local _, _, _, isInVararg = ...
                    return callFormat("%s(%s,%s,%s%s)", name, Lhs, Wrapped, tostring(Wrapped ~= Rhs), (isInVararg and ",..." or ""))
                elseif name == "CONCAT" then
                    if constantCollection and (is(rhs, "call") or is(lhs, "call") or is(rhs, "string") or is(lhs, "string")) then
                        return callFormat(name .. "(%s,%s)", Lhs, Rhs)
                    end
                    return format("%s %s %s", Lhs, operator, Rhs)
                else
                    return callFormat("%s(%s, %s)", name, Lhs, Rhs)
                end
            end

            --if false then return callFormat("%s(%s,%s)", name, Lhs, Rhs) end

            return format("%s %s %s", Lhs, operator, Rhs)
        end

        local s, value = pcall(getValue, operator, lhs.text or lhs.value, rhs.text or rhs.value)

        if not s or typeof(value) == "number" and value >= maxNum then --> Results that are too large, for example 2^100 can break parsing.
            return format("%s %s %s", self:readexpr(lhs), operator, self:readexpr(rhs))
        end

        return beautify(value)
    elseif tag == "unary" then -- -, not, #
        local operator = statement.operator.text

        if operator == "not" and statement.operand.tag == "boolean" then -- not true
            return tostring(not statement.operand.value)
        elseif operator == "#" and (statement.operand.tag == "table" or statement.operand.tag == "string") then
            return tostring(getLength(statement.operand))
        end
        
        return callFormat("%s(%s)", self.unaryOperatorNames[operator], self:readexpr(statement.operand))
    elseif tag == "group" then -- (...)
        return format("(%s)", self:readexpr(statement.expression))
    elseif tag == "indexname" then -- x.y
        local accessor = statement.accessor.text
        local parent = self:readexpr(statement.expression, nil, true)
        local index = statement.index.text

        local _, dontHook, superDuperDontHook = ...

        if superDuperDontHook or (not dontHook and (not constantCollection) and not isSpiedVar(statement)) then
            return format("%s%s%s", parent, accessor, index)
        end

        if dontHook then
            return accessor == ":" and format("%s,%q", parent, index) or format("%s%s%s", parent, accessor, index)
        end

        return callFormat("CHECKINDEX(%s,%q)",
            parent,
            index
    )
    elseif tag == "index" then
        local _, dontHook = ...
        local base, index = self:readexpr(statement.expression, nil, true), self:readexpr(statement.index)

        if dontHook or not constantCollection then
            return format("%s[%s]", base, index)
        end

        return callFormat("CHECKINDEX(%s, %s)",
            base,
            index
        )
    elseif tag == "function" then --> function expr
        local params, vararg = readParams(statement.body)
        local code = format("function%s%send", params, self:readexpr(statement.body.body, nil, nil, vararg))
        
        return code
    elseif tag == "conditional" then
        local code = format("if %s then %s ", self:readexpr(statement.condition), self:readexpr(statement.thenexpr))

        for _, elif in statement.elseifs do
            code = code .. format("elseif %s then %s ", self:readexpr(elif.condition), self:readexpr(elif.thenexpr))
        end

        code = code .. format("else %s", self:readexpr(statement.elseexpr))
        return code
    elseif tag == "interpolatedstring" then
        local code = "\""
        local list = {}

        for _, str in statement.strings do
            table.insert(list, {
                kind = "string",
                at = str.position.column,
                expr = str.text
            })
        end

        for _, expr in statement.expressions do
            table.insert(list, {
                kind = "expr",
                at = (expr.position or expr.location.begin).column,
                expr = expr
            })
        end

        table.sort(list, function(a, b) return a.at < b.at end) --> works pretty well

        local exprs = {}

        for _, v in list do
            if v.kind == "expr" then
                code = code .. "%s"--format("{%s}", self:readexpr(v.expr))
                table.insert(exprs, self:readexpr(v.expr))
            else
                code = code .. v.expr
            end
        end
        return callFormat("TEMPLATE_STRING(%s,%s)", code .. "\"", (#exprs == 0 and "nil" or table.concat(exprs, ",")))
    elseif tag == "cast" then
        print("cast")
        return ""
    elseif tag == "reference" then -- Name: string
        return statement.name.text
    end

    print(beautify(statement))
    error("unsupported expression '" .. (statement.tag or "???") .. "'")
end

local args = { ... }

local input = args[2]
local out = args[3]
prettyPrint = not args[4] or args[4] == ""
callId = args[4] or ""
constantCollection = args[5] == "1"

if callId == "0" then callId = "" end

print("Constant collection:",constantCollection)

local output = {}

local source = readfile(input)
lines = source:split("\n")

local s = os.clock()
for _, v in parser.parsefile(source).root.statements do
    output[#output+1] = unparser:readexpr(v)
end

print("finished everything in",os.clock()-s,"seconds, file size:",#source / 1024,"kb.")

fs.writestringtofile(out, table.concat(output, " "))
