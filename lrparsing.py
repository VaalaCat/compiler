# （1）给出主要数据结构：分析栈、符号表；
# （2）将词法扫描器作为一个子程序，每次调用返回一个TOKEN；
# （3）程序界面：表达式输入、语法分析的表示结果（文件或者图形方式）；
# LR语法分析器的功能是分析token流，得到语法树
# 这里设计使用分析器接受token流输入，输出每棵树的根结点和所有的树
import json
import lex

grammar = {
    "P": [["D", "S"]],
    "D": [["L", "id", ";", "D"], [""]],
    "L": [["int"], ["float"]],
    "S": [["id", "=", "E", ";"]],
    "S": [["if", "(", "C", ")", "S1"]],
    "S": [["if", "(", "C", ")", "S1", "else", "S2"]],
    "S": [["while", "(", "C", ")", "S1"]],
    "S": [["S", ";", "S"]],
    "C": [["E1", ">", "E2"]],
    "C": [["E1", "<", "E2"]],
    "C": [["E1", "==", "E2"]],
    "E": [["E1", "+", "T"]],
    "E": [["E1", "-", "T"]],
    "E": [["T"]],
    "T": [["F"]],
    "T": [["T1", "*", "F"]],
    "T": [["T1", "/", "F"]],
    "F": [["(", "E", ")"]],
    "F": [["id"]],
    "F": [["digits"]]
}


def readFile(tokenFilepath="token.out", symbolFilepath="symbol.out"):
    tokenFile = open(tokenFilepath, "r").read().split("\n")
    symbolFile = open(symbolFilepath, "r").read().replace(
        "'", "\"").split("\n")
    tokens = []
    symbols = []
    for line in tokenFile:
        if line == "":
            continue
        tmp = line[1:-1]
        mid = tmp.index(",")
        tokens.append((tmp[:mid][1:-1], tmp[mid+2:][1:-1]))

    for line in symbolFile:
        if line == "":
            continue
        tmp = json.loads(line)
        symbols.append(tmp)
    return tokens, symbols


if __name__ == "__main__":
    a, b = readFile()
