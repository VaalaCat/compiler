# （1）给出主要数据结构：分析栈、符号表；
# （2）将词法扫描器作为一个子程序，每次调用返回一个TOKEN；
# （3）程序界面：表达式输入、语法分析的表示结果（文件或者图形方式）；
# LR语法分析器的功能是分析token流，得到语法树
# 这里设计使用分析器接受token流输入，输出每棵树的根结点和所有的树
import json
import lex
import copy

actionSymbol = ["=", "<", ">", "-", "+", ";", "*", "/", "==", "(", ")", "$",
                "while", "if", "else", "id", "digits", "float", "int"]
grammar = [
    {"P_": ["P"]},
    {"P": ["D", "S"]},
    {"D": [""]},
    {"D": ["L", "id", ";", "D"]},
    {"L": ["int"]},
    {"L": ["float"]},
    {"S": ["id", "=", "E", ";"]},
    {"S": ["if", "(", "C", ")", "M", "S"]},
    {"S": ["if", "(", "C", ")", "M", "S", "N", "else", "M", "S"]},
    {"S": ["while", "M", "(", "C", ")", "M", "S"]},
    {"S": ["S", "M", "S"]},
    {"C": ["E", ">", "E"]},
    {"C": ["E", "<", "E"]},
    {"C": ["E", "==", "E"]},
    {"E": ["E", "+", "T"]},
    {"E": ["E", "-", "T"]},
    {"E": ["T"]},
    {"T": ["F"]},
    {"T": ["T", "*", "F"]},
    {"T": ["T", "/", "F"]},
    {"F": ["(", "E", ")"]},
    {"F": ["id"]},
    {"F": ["digits"]},
    {"M": [""]},
    {"N": [""]}
]
symbols = []
tokens = []
midCode = []
originStatus = []
statusSet = [[]]
analyzerTable = {}
tmpCnt = 0
firstSet = {
    "C": ["digits", "id", "("],
    "D": ["int", "float", ""],
    "E": ["digits", "id", "("],
    "F": ["digits", "id", "("],
    "L": ["int", "float"],
    "M": [""],
    "N": [""],
    "O": [""],
    "P": ["if", "while", "int", "float", "id", ""],
    "S": ["if", "while", "id", ""],
    "T": ["digits", "id", "("],
    "P_": ["if", "while", "int", "float", "id", ""]
}
followSet = {
    "C": [")"],
    "D": ["if", "while", "id", "$"],
    "E": ["==", ">", "<", "+", "-", ";", ")"],
    "F": ["==", ">", "<", "+", "-", "*", "/", ";", ")"],
    "L": ["id"],
    "M": ["if", "else", "while", "id", "(", "$"],
    "N": ["else"],
    "O": ["if", "while", "int", "float", "id", "$"],
    "P": ["$"],
    "S": ["if", "else", "while", "id", "$"],
    "T": ["==", ">", "<", "+", "-", "*", "/", ";", ")"],
    "P_": ["$"]
}
LOGLEVEL = 0
# 初始化状态，也就是加个点


def initStatus():
    global originStatus
    global statusSet
    sourceStatus = copy.deepcopy(grammar)
    for i in range(0, len(sourceStatus)):
        tmp = getGrammarValue(sourceStatus[i])
        if tmp[0] == "":
            tmp[0] = "."
        else:
            tmp.insert(0, ".")
        sourceStatus[i][getGrammarKey(sourceStatus[i])] = tmp
    originStatus = sourceStatus
    statusSet[0].append(originStatus[0])

# 从初始状态递归生成后续状态


def genStatusSet(statusCur):
    global statusSet
    if statusCur == len(statusSet):
        return
    # 首先是要拓展该状态
    extedStatus = extendStatus(statusSet[statusCur])
    statusSet[statusCur] += extedStatus
    # 然后是要找出产生式右部的点的右边的符号，将对应的项集点全部右移后变成新状态
    nextSymbol = findNext(statusSet[statusCur])
    nextSymbolMap = {}
    for i in nextSymbol:
        if i["next"] not in nextSymbolMap:
            nextSymbolMap[i["next"]] = []
        nextSymbolMap[i["next"]].append(i["idx"])
    # 如果没有下一个符号
    if nextSymbolMap == {} and getGrammarValue(statusSet[statusCur][0])[-1] == ".":
        # 读到P代表已经接受了
        if getGrammarKey(statusSet[statusCur][0]) == "P_":
            fillAnalysTable(statusCur, "$", ".")
        else:
            tmpK = getGrammarKey(statusSet[statusCur][0])
            tmpV = getGrammarValue(statusSet[statusCur][0])[:-1]
            fillAnalysTable(statusCur, "$", f"r{getPosition({tmpK: tmpV})}")
    tmpReduceG = getReduce(statusSet[statusCur])
    if tmpReduceG != {} and statusCur != 0:
        tmpK = getGrammarKey(tmpReduceG)
        tmpV = getGrammarValue(tmpReduceG)[:-1]
        if len(tmpV) == 0:
            tmpV = [""]
        fillAnalysTable(statusCur, "$", f"r{getPosition({tmpK: tmpV})}")
    # k是下一个符号，v是状态中对应产生式的序号表
    for k, v in nextSymbolMap.items():
        tmpStatus = []
        rG = {}
        # 将接受一个符号都能转移到下一步的项目合在一起右移，并且在不存在重复状态时加入项目集，i代表一个序号
        for i in v:
            tmpV = rightSuffle(getGrammarValue(statusSet[statusCur][i]))
            tmpK = getGrammarKey(statusSet[statusCur][i])
            # 如果产生了可归约情况，那么记录归约的产生式
            if tmpV[-1] == ".":
                if len(tmpV) == 1:
                    rG = {tmpK: [""]}
                else:
                    rG = {tmpK: tmpV[0:-1]}
            if not exsitStatus(tmpStatus, {tmpK: tmpV}):
                tmpStatus.append({tmpK: tmpV})
            else:
                continue
        # tmpStatus代表当前状态接受符号k，转移到的下一个状态
        tmpStatus += extendStatus(tmpStatus)
        # 我们需要在分析表中记录这个跳转
        # 对于可归约情况我们需要进行特判
        nxtCur = exsitStatusSet(tmpStatus)
        if -1 == nxtCur:
            # 如果是新状态，那么新状态序号就是statusSet没有append之前的长度
            fillAnalysTable(statusCur, k, len(statusSet))
            # 如果产生的新状态可归约，那么需要填写新状态的可归约情况
            if rG != {}:
                fillAnalysTable(len(statusSet), getGrammarValue(rG)[-1],
                                f"r{getPosition(rG)}")
            statusSet.append(tmpStatus)
        # 如果不是新状态，那么就是查找函数返回的位置
        else:
            fillAnalysTable(statusCur, k, nxtCur)
    genStatusSet(statusCur+1)


def findNext(status):
    ans = []
    cnt = 0
    for i in status:
        v = getGrammarValue(i)
        dotCur = v.index(".")
        if dotCur == len(v)-1:
            cnt += 1
            continue
        ans.append({"next": v[dotCur+1], "idx": cnt})
        cnt += 1
    return ans

# 判断一个状态中是否有可归约的项


def getReduce(status):
    for i in status:
        tmpV = getGrammarValue(i)
        if tmpV[-1] == ".":
            return i
    return {}

# 判断一个状态之前有没有出现过，如果出现过就返回位置


def exsitStatusSet(status):
    for i in range(len(statusSet)):
        for j in range(len(status)):
            if status[j] not in statusSet[i]:
                break
            if j == len(status)-1:
                return i
    return -1


# 从当前状态拓展点后面的状态，也就是把点后面的非终结符号（在这里是大写字母）加入项集中，还要比较是不是已经有相同的状态在里面


def extendStatus(status):
    ansStatus = []
    for i in status:
        # 找到点后面的符号
        dotCur = getGrammarValue(i).index(".")
        if dotCur != len(getGrammarValue(i))-1:
            k = getGrammarValue(i)[dotCur+1][0]
            extStatus = getAllGrammarFor(k)
            # 判断每一条拓展后的东西是否存在
            for i in extStatus:
                if not exsitStatus(status, i):
                    ansStatus.append(i)
        else:
            continue
    if len(ansStatus) == 0:
        return []
    return ansStatus+extendStatus(ansStatus)

# 将当前生成式点向右移动


def rightSuffle(v):
    ans = copy.deepcopy(v)
    dotCur = ans.index(".")
    if dotCur == len(v)-1:
        return ans
    ans[dotCur] = ans[dotCur+1]
    ans[dotCur+1] = "."
    return ans

# 获得所有由当前非终结符号开始的产生式状态


def getAllGrammarFor(lt):
    ans = []
    for i in originStatus:
        if getGrammarKey(i) == lt:
            ans.append(i)
    return ans

# 判断该条目是否在某状态中存在


def exsitStatus(status, g):
    k = getGrammarKey(g)
    v = getGrammarValue(g)
    for i in status:
        if getGrammarKey(i) == k and getGrammarValue(i) == v:
            return True
    return False


def getPosition(g):
    k = getGrammarKey(g)
    v = getGrammarValue(g)
    for i in range(len(grammar)):
        tmpK = getGrammarKey(grammar[i])
        tmpV = getGrammarValue(grammar[i])
        if k == tmpK and v == tmpV:
            return i
    return False


def getGrammarValue(g):
    k = list(g.keys())[0]
    v = g[k]
    return v


def getGrammarKey(g):
    return list(g.keys())[0]


def outputStatus(g):
    print(getGrammarKey(g), "->", end="")
    for i in getGrammarValue(g):
        print(i, end="")
    print("")


def outputSymbolStack(stack):
    for i in stack:
        if isinstance(i, list):
            if i[0] == 'OP' or i[0] == 'Keyword' or i[0] == 'mid':
                print(i[1], end=", ")
            else:
                print(i[0], end=", ")
        else:
            print(i, end=", ")


def outputStackStatus(symbolStacks, statusStacks, tmpG=""):
    if LOGLEVEL < 2:
        return
    lex.spaceser()
    print("symbolStacks: [", end="")
    outputSymbolStack(symbolStacks)
    print("]")
    print("statusStacks:", statusStacks)
    if tmpG != "":
        print("useReduce:", tmpG)


def outputStatusSet(status):
    lex.spaceser()
    for i in status:
        outputStatus(i)

# 创建LR分析表


def fillAnalysTable(statusCur, inputSymbol, nextStatus):
    # LR分析表接受当前状态和文法符号的输入，按不同的情况有三种结果：
    # 1. 文法符号为非终结符，需要转移到对应状态
    # 2. 文法符号为终结符，但无法归约，需要转移到对应状态
    # 3. 文法符号为终结符，可以归约，进行归约
    # 首先将数据结构初始化
    global analyzerTable
    if statusCur not in analyzerTable:
        analyzerTable[statusCur] = {}
    # 然后填写状态表
    # 如果可以归约，将归约的产生式左部的follow集填写上归约标志
    if isinstance(nextStatus, str):
        if nextStatus == ".":
            analyzerTable[statusCur]["$"] = ["ACCEPT"]
            return
        tmpG = grammar[int(nextStatus.replace("r", ""))]
        tmpK = getGrammarKey(tmpG)
        for i in followSet[tmpK]:
            # if i == "else":
            #     continue
            if i not in analyzerTable[statusCur]:
                analyzerTable[statusCur][i] = []
                analyzerTable[statusCur][i].append(nextStatus)
            else:
                if analyzerTable[statusCur][i][-1] == nextStatus:
                    continue
                else:
                    analyzerTable[statusCur][i].append(nextStatus)
        return
    if inputSymbol not in analyzerTable[statusCur]:
        analyzerTable[statusCur][inputSymbol] = []
    analyzerTable[statusCur][inputSymbol].append(nextStatus)

# 用这个函数来查LR分析表


def getNextStatus(token, statusCur, mode=""):
    kwd = []
    if isinstance(token, list):
        try:
            if token[0] == "Keyword":
                kwd = analyzerTable[statusCur][token[1]]
            elif token[0] == "OP":
                kwd = analyzerTable[statusCur][token[1]]
            elif token[0] == "id":
                kwd = analyzerTable[statusCur][token[0]]
            elif token[0] == "digits":
                kwd = analyzerTable[statusCur][token[0]]
            elif token[0] == "mid":
                kwd = analyzerTable[statusCur][token[1]]
            else:
                exit(1)
        except:
            if mode == "try":
                if LOGLEVEL >= 1:
                    print("INFO:", "Vaala's LR machine fix an Error at:")
                    print(
                        f"line {token[2]['line']} cur {token[2]['cur']}: {token[1]}")
                return []
            exit(1)
    else:
        if token in analyzerTable[statusCur]:
            kwd = analyzerTable[statusCur][token]
        else:
            return kwd
    if len(kwd) > 1:
        if isinstance(token, list):
            lex.lexWarning(token[2]["cur"], token[2]["line"], token[1])
    elif len(kwd) == 0:
        lex.spaceser()
        print("Fatal Error:",
              f"Your code is not allowed to compile!\n The error is line {kwd[2]['line']} cur {kwd[2]['cur']}:\n{kwd[1]}")
        exit(1)
    return kwd[0]

# 使用分析栈进行分析


def parseToken(tokens):
    # 在得到项集族和分析表后，我们需要使用分析栈对Token串进行处理
    tokenBuffer = copy.deepcopy(tokens)
    # 我们先在输入流中加一个结束符
    tokenBuffer.append("$")
    # 创建符号栈和状态栈
    statusStacks = []
    symbolStacks = []
    # 初始化栈
    statusStacks.append(0)
    symbolStacks.append("$")
    # 在终结之前一直读取
    while len(tokenBuffer) > 0:
        tmpSymbol = tokenBuffer.pop(0)
        # LR表第一个括号是状态，第二个括号是输入
        nextStatus = getNextStatus(tmpSymbol, statusStacks[-1], mode="try")
        if isinstance(nextStatus, int):
            symbolStacks.append(tmpSymbol)
            statusStacks.append(nextStatus)

        outputStackStatus(symbolStacks, statusStacks)

        # 如果无法归约则读入符号，使用LR分析表转到对应状态
        # 归约在前面，如果可以归约就一直归约
        while True:
            if nextStatus == "ACCEPT":
                print("OHHHHHH!")
                break
            nextStatus = getNextStatus(
                tokenBuffer[0], statusStacks[-1], "try")
            if not isinstance(nextStatus, str):
                break
            if nextStatus == "ACCEPT":
                print("ACCEPT")
                break
            # 获取归约所用的文法
            tmpG = grammar[int(nextStatus[1:])]
            # 使用文法归约
            tmpK = getGrammarKey(tmpG)
            tmpV = getGrammarValue(tmpG)
            # 保存一下弹出来的符号
            reducedSymbols = []
            for i in range(len(tmpV)):
                # 依次弹栈
                if tmpV[0] != "":
                    tmpS = symbolStacks.pop()
                    statusStacks.pop()
                    reducedSymbols.insert(0, tmpS)
                    outputStackStatus(symbolStacks, statusStacks, tmpG)
            # 确定归约的规则后，使用对应的语义规则对其进行处理
            value = genCode(tmpG, reducedSymbols)
            # 弹完了记得把新的装进来，这里装进去多一个元素是为了携带信息
            symbolStacks.append(["mid", tmpK, value])
            nextStatus = getNextStatus(tmpK, statusStacks[-1])
            statusStacks.append(nextStatus)
            outputStackStatus(symbolStacks, statusStacks, tmpG)


def readFile(tokenFilepath="token.out", symbolFilepath="symbol.out"):
    tokenFile = open(tokenFilepath, "r").read().split("\n")
    symbolFile = open(symbolFilepath, "r").read().replace(
        "'", "\"").split("\n")
    global tokens
    global symbols
    for line in tokenFile:
        if line == "":
            continue
        tmp = json.loads(line)
        tokens.append(tmp)

    for line in symbolFile:
        if line == "":
            continue
        tmp = json.loads(line)
        symbols.append(tmp)
    return [tokens, symbols]


# 目 标 机：及其兼容处理器
# 中间代码：三地址码
# 主要数据结构：三地址码表、符号表
#
# 语义分析内容要求：
# 1. 变量说明语句
# 2. 赋值语句
# 3. 控制语句任选一种
#
# 其它要求：
# 1. 将词法分析（扫描器）作为子程序，供语法、语义程序调用；
# 2. 使用语法制导的语义翻译方法；
# 3. 编程语言自定；
# 4. 提供源程序输入界面；
# 5. 目标代码生成暂不做；
# 6. 编译后，可查看TOKEN串、符号表、三地址码表；
# 7. 主要数据结构：产生式表、符号表、三地址码表。

# 在生成代码的时候需要查找符号表中的内容
def findSymbol(addr):
    for i in symbols:
        if addr == i["addr"]:
            return i
    return None


# 用于产生临时变量


def genTmpVar():
    global tmpCnt
    tmpCnt += 1
    return f"t{tmpCnt}"
    # 中间代码的生成需要语法分析的同时进行语义分析，
    # 在归约的时候生成代码，这个时候把代码给塞到栈里


def outputCode():
    pass

# 传入文法和空闲地址以及被归约的各个符号属性，返回归约符号的属性


def genCode(g, reducedSymbols):
    # 先从简单的开始
    tmpK = getGrammarKey(g)
    tmpV = getGrammarValue(g)

    # M -> e
    if tmpK == "M" and tmpV[0] == "":
        return {"to": len(midCode)}
    # N -> e
    # N.nextList.append(nextAddr);
    # gen(goto __"):
    if tmpK == "N" and tmpV[0] == "":
        tmpNextList = []
        tmpNextList.append(len(midCode))
        midCode.append("goto __")
        return {"nextList": tmpNextList}

    # F -> id
    # F -> digits
    # 单纯的标识符号，如果使用这两个产生式归约的话传递一个值就行了
    # 要注意的是这个 id 标识符和数字都需要去符号表中查找，把找到的 value 赋值给 F.name
    if tmpK == "F":
        if reducedSymbols[0][0] == "id" or reducedSymbols[0][0] == "digits":
            # token中第二个值为符号表的入口地址
            return {"addr": findSymbol(reducedSymbols[0][1])["value"]}
    # 接下来的要复杂一点，我们之前处理了简单的F
    # T -> F
    if tmpK == "T" and tmpV[0] == "F":
        # token中第三个值为附带值
        return {"addr": reducedSymbols[0][2]["addr"]}
    # E -> T
    if tmpK == "E" and tmpV[0] == "T":
        return {"addr": reducedSymbols[0][2]["addr"]}
    # S -> id = E;
    # 生成赋值语句，在符号表中查找名字生成中间代码
    # gen(id.value = E.addr)
    # addr属性表示对应变量的变量名/临时变量名/代数值
    if tmpK == "S" and tmpV == ["id", "=", "E", ";"]:
        tmpCode = f"{findSymbol(reducedSymbols[0][1])['value']} = {reducedSymbols[2][2]['addr']}"
        midCode.append(tmpCode)
        # 这一句存疑
        # return {"addr": f"{reducedSymbols[0][2]}"}
    # E -> E+T
    # E -> E-T
    # E.addr = genTmpVar()
    # gen(E.addr = E.addr OP T.addr)
    # 计算表达式，生成中间变量
    if tmpK == "E" and (tmpV == ["E", "+", "T"] or tmpV == ["E", "-", "T"]):
        tmpVarCode = genTmpVar()
        tmpCode = f"{tmpVarCode} = {reducedSymbols[0][2]['addr']} {reducedSymbols[1][1]} {reducedSymbols[2][2]['addr']}"
        midCode.append(tmpCode)
        return {"addr": tmpVarCode}
    # F -> (E)
    if tmpK == "F" and tmpV == ["(", "E", ")"]:
        return {"addr": reducedSymbols[1][2]["addr"]}
    # T -> T*F
    # T -> T/F
    if tmpK == "T" and (tmpV == ["T", "*", "F"] or tmpV == ["T", "/", "F"]):
        tmpVarCode = genTmpVar()
        tmpCode = f"{tmpVarCode} = {reducedSymbols[0][2]['addr']} {reducedSymbols[1][1]} {reducedSymbols[2][2]['addr']}"
        midCode.append(tmpCode)
        return {"addr": tmpVarCode}

    # 对于布尔运算我们需要用到跳转
    # C -> E > E
    # C -> E < E
    # C -> E == E
    # 对于布尔表达式有
    # C.truelist.append(nextAddr)
    # C.falselist.append(nextAddr+1)
    # gen(if E.addr relop E.addr goto __)
    # gen(goto __)
    if tmpK == "C" and (tmpV == ["E", ">", "E"] or tmpV == ["E", "<", "E"] or tmpV == ["E", "==", "E"]):
        trueList = []
        falseList = []
        trueList.append(len(midCode))
        falseList.append(len(midCode)+1)
        tmpCode = f"if {reducedSymbols[0][2]['addr']} {reducedSymbols[1][1]} {reducedSymbols[2][2]['addr']} goto __"
        midCode.append(tmpCode)
        midCode.append("goto __")
        return {"trueList": trueList, "falseList": falseList}

    # S -> if(C)MS
    # 使用回填，C是布尔表达式
    # backpatch(B.truelist, M.to);
    # S.nextList=merge(B.falselist, S.nextlist)
    if tmpK == "S" and tmpV == ["if", "(", "C", ")", "M", "S"]:
        tmpC = reducedSymbols[2][2]
        # 先回填
        for i in tmpC["trueList"]:
            midCode[i] = midCode[i].replace(
                "__", str(reducedSymbols[4][2]["to"]))
        tmpNextList = []
        tmpNextList += tmpC["falseList"]
        if None != reducedSymbols[5][2]:
            if "nextList" in reducedSymbols[5][2]:
                tmpNextList += reducedSymbols[5][2]["nextList"]

    # S -> if(C)SelseS
    if tmpK == "S" and tmpV == ["if", "(", "C", ")", "M", "S", "N", "else", "M", "S"]:
        tmpC = reducedSymbols[2][2]
        for i in tmpC["trueList"]:
            midCode[i] = midCode[i].replace(
                "__", str(reducedSymbols[4][2]["to"])
            )
        for i in tmpC["falseList"]:
            midCode[i] = midCode[i].replace(
                "__", str(reducedSymbols[4][2]["to"])
            )
        tmpNextList = []
        tmpNextList += reducedSymbols[6][2]["to"]
        if None != reducedSymbols[5][2]:
            if "nextList" in reducedSymbols[5][2]:
                tmpNextList += reducedSymbols[5][2]["nextList"]
        if None != reducedSymbols[9][2]:
            if "nextList" in reducedSymbols[9][2]:
                tmpNextList += reducedSymbols[9][2]["nextList"]

    # S -> SS
    # backpatch( S1.nextlist, M.to );
    # S.nextlist = S2.nextlist
    if tmpK == "S" and tmpK == ["S", "M", "S"]:
        for i in reducedSymbols[0][2]["nextList"]:
            # 回填
            midCode[i] = midCode[i].replace(
                "__", str(reducedSymbols[1][2]["to"]))
        return {"nextList": reducedSymbols[2][2]["nextList"]}

    pass


# 对于每一个文法我们需要构造一个中间代码生成规则
# P_ -> P

# P -> D

# D -> e
# D -> Lid;D
# 填符号表，在 id 的值类型填写 valuetype为 L.valuetype

# L -> int
# L.valuetype = int
# L -> float
# L.valuetype = float


if __name__ == "__main__":
    lex.helloFunc()
    lex.spaceser()
    sourceCode = lex.read(mode="file", filepath="test.cpp")
    tokens, symbols = lex.lexer(sourceCode)
    LOGLEVEL = 2
    # a, b = readFile()
    initStatus()
    genStatusSet(0)
    parseToken(tokens)
    lex.finalReport()
    print(midCode)
