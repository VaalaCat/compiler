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
    {"S": ["if", "(", "C", ")", "S"]},
    {"S": ["if", "(", "C", ")", "S", "else", "S"]},
    {"S": ["while", "(", "C", ")", "S"]},
    {"S": ["S", "S"]},
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
    {"F": ["digits"]}
]
originStatus = []
statusSet = [[]]
analyzerTable = {}
firstSet = {}
followSet = {}

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


def outputStatusSet(status):
    lex.spaceser()
    for i in status:
        outputStatus(i)

# 递归求First集


def getFirst(symbol):
    global firstSet
    if symbol in actionSymbol:
        firstSet[symbol] = [symbol]
        return symbol
    tmpGs = getAllGrammarFor(symbol)
    for i in tmpGs:
        tmpK = getGrammarKey(i)
        tmpV = getGrammarValue(i)[1:]
        if tmpK not in firstSet:
            firstSet[tmpK] = []
        if len(tmpV) == 0:
            firstSet[tmpK].append("$")
            return "$"
        for j in tmpV:
            firstSet[tmpK].append(getFirst(j))

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
    if isinstance(nextStatus, str):
        if nextStatus == ".":
            analyzerTable[statusCur]["$"] = ["ACCEPT"]
            return
        for i in actionSymbol:
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
            else:
                exit(1)
        except:
            if mode == "try":
                return []
            exit(1)
    else:
        if token in analyzerTable[statusCur]:
            kwd = analyzerTable[statusCur][token]
        else:
            return kwd
    if len(kwd) > 1:
        lex.lexWarning(kwd[2]["cur"], kwd[2]["line"], kwd[1])
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
    tokenBuffer.append(("stop", "$"))
    # 创建符号栈和状态栈
    statusStacks = []
    symbolStacks = []
    # 初始化栈
    statusStacks.append(0)
    symbolStacks.append("$")
    # 在终结之前一直读取
    tmpSymbol = tokenBuffer.pop(0)
    symbolStacks.append(tmpSymbol)
    nextStatus = getNextStatus(tmpSymbol, statusStacks[-1])
    statusStacks.append(nextStatus)
    while len(tokenBuffer) > 0:
        tmpSymbol = tokenBuffer.pop(0)
        # 如果读到终结符就停止
        if tmpSymbol[0] == "stop":
            break
        # LR表第一个括号是状态，第二个括号是输入
        # 如果无法归约则读入符号，使用LR分析表转到对应状态
        # 归约在前面，如果可以归约就一直归约
        while True:
            nextStatus = getNextStatus(
                "$", statusStacks[-1], "try")
            if not isinstance(nextStatus, str):
                break
            # 获取归约所用的文法
            tmpG = grammar[int(nextStatus[1:])]
            # 使用文法归约
            tmpK = getGrammarKey(tmpG)
            tmpV = getGrammarValue(tmpG)
            for i in range(len(tmpV)):
                # 依次弹栈
                if tmpV[0] != "":
                    symbolStacks.pop()
                    statusStacks.pop()
            symbolStacks.append(tmpK)
            nextStatus = getNextStatus(tmpK, statusStacks[-1])
            statusStacks.append(nextStatus)
            lex.spaceser()
            print("symbolStacks:", symbolStacks)
            print("statusStacks:", statusStacks)
            print("useReduce:", tmpG)
        symbolStacks.append(tmpSymbol)
        nextStatus = getNextStatus(tmpSymbol, statusStacks[-1])
        statusStacks.append(nextStatus)

        lex.spaceser()
        print("symbolStacks:", symbolStacks)
        print("statusStacks:", statusStacks)
        print("useReduce:", tmpG)


def readFile(tokenFilepath="token.out", symbolFilepath="symbol.out"):
    tokenFile = open(tokenFilepath, "r").read().split("\n")
    symbolFile = open(symbolFilepath, "r").read().replace(
        "'", "\"").split("\n")
    tokens = []
    symbols = []
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


if __name__ == "__main__":
    a, b = readFile()
    # genStatusSet()
    initStatus()
    # outputStatus(statusSet[0][1])
    # outputStatusSet(statusSet[0])
    # print(getAllGrammarFor("D"))
    # outputStatusSet(statusSet[0]+extendStatus(statusSet[0]))
    genStatusSet(0)
    # parseToken(a)
    getFirst("P_")
