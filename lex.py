# （1）	根据附录给定的文法，从输入的类C语言源程序中，识别出各个具有独立意义的单词，即关键字、标识符、常数、运算符、分隔符五大类；文法见最后附录。
# （2）	提供源程序输入界面；
# （3）	词法分析后可查看符号表和TOKEN串表；
# （4）	保存符号表和TOKEN串表（如：文本文件）；
# （5）	遇到错误时可显示提示信息，然后跳过错误部分继续进行分析。

errCnt = 0
warCnt = 0

# （1）	根据附录给定的文法，从输入的类C语言源程序中，识别出各个具有独立意义的单词，即关键字、标识符、常数、运算符、分隔符五大类；文法见最后附录。


def read(**kwargs):
    content = ""
    if "mode" in kwargs and kwargs["mode"] == 'file':
        if "filepath" in kwargs and kwargs["filepath"] is None:
            print("Error:", "Empty File Path.")
            return False
        try:
            f = open(kwargs["filepath"])
        except:
            print("Error:", "Open file failed, please confirm your filepath is right.")
            return False

        content = f.read()
    else:
        print("Please input your code HERE ,press 'EOF' and ENTER to end your input!")
        print(">>> ", end="")
        tmp = ""
        while tmp != "EOF":
            tmp = input()
            print(">>> ", end="")
            if tmp != "EOF":
                content += tmp+"\n"
        print("")
    return content


# id->Letter|Letter id
# digits->digit digits|digit
# OP->+ | - | * | / | > | < | = | ( | ) | ; | ‘ | == | >= | <= | !=
# Keyword->if|else|while|int|float
# Letter->a|b|c|d|e|f|g|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|_
# digit->0|1|2|3|4|5|6|7|8|9

# （3）	词法分析后可查看符号表和TOKEN串表；
# （4）	保存符号表和TOKEN串表（如：文本文件）；
# （5）	遇到错误时可显示提示信息，然后跳过错误部分继续进行分析。
def lexer(sourceCode):
    # 添加结束符
    sourceCode += "$"
    finalTokens = []
    symbols = []
    previousLetters = ""
    # cnt,line用于错误提示定位
    cnt = 1
    line = 1
    for i in sourceCode:
        cnt += 1
        if i == "\n":
            line += 1
            cnt = 1
        # 关键词是最优先的
        if isKeyword(previousLetters):
            finalTokens.append(("Keyword", previousLetters))
            previousLetters = ""
        # 首先是OP,先处理单个无后继符号
        if previousLetters == "":
            # 读到这几个符号那一定是独立符号，直接存
            if i == "+" or i == "-" or i == "*" or i == "/" or i == ";" or i == "(" or i == ")" or i == "'":
                finalTokens.append(("OP", i))
                continue
            # 这几个符号可能有后继，需要先存着给后面
            elif i == "<" or i == "=" or i == ">" or i == "!":
                previousLetters += i
                continue
        # 然后处理可能有后续的符号
        elif previousLetters == "<" or previousLetters == "=" or previousLetters == "<" or previousLetters == "!":
            # 如果是等号那组合起来就是OP
            if i == "=":
                previousLetters += i
                finalTokens.append(("OP", previousLetters))
                previousLetters = ""
                continue
            # 后面是空格或者字符/数字，就存了
            elif isSpacer(i) or isLetter(i) or isNumber(i):
                finalTokens.append(("OP", previousLetters))
                if not isSpacer(i):
                    previousLetters = i
                else:
                    previousLetters = ""
                continue
            # 如果后面不是等号或者合法的跟随字，那就报错并询问要不要跳过它继续处理
            else:
                # 如果选择跳过，那就清空记录，并且下一个词
                if lexErrMsg(cnt, line, previousLetters):
                    previousLetters = ""
                    continue
                # 如果选择不跳过，那就错误退出
                else:
                    exit(1)
        # 最后处理前面传来的OP
        elif maybeOP(previousLetters):
            finalTokens.append(("OP", previousLetters))
            if not isSpacer(i):
                previousLetters = i
            else:
                previousLetters = ""
            continue
        # 到这里OP就处理完了，接下来处理id
        # id是单个letter或letter组合
        # 如果刚开始读就直接开始处理
        if previousLetters == "":
            # 读到字母就继续
            if isLetter(i):
                previousLetters += i
                continue
        # 只需要检测前一个符号是不是字母
        elif isLetter(previousLetters[-1]):
            if isLetter(i):
                previousLetters += i
                continue
            # 读到空格或符号代表终结
            elif isSpacer(i) or maybeOP(i):
                # 如果没填过这个符号
                idx = lookup(symbols, previousLetters)
                if idx == -1:
                    addr = len(symbols)
                    symbols.append(
                        {"addr": str(addr), "value": previousLetters, "type": "id", "line": line, "cur": cnt})
                    idx = addr
                finalTokens.append(("id", str(idx)))
                if maybeOP(i):
                    previousLetters = i
                else:
                    previousLetters = ""
                continue
            # 读到其它东西先报个Warning然后存token
            else:
                lexWarning(cnt, line, previousLetters+i)
                idx = lookup(symbols, previousLetters)
                if idx == -1:
                    addr = len(symbols)
                    symbols.append(
                        {"addr": str(addr), "value": previousLetters, "type": "id", "line": line, "cur": cnt})
                    idx = addr
                finalTokens.append(("id", str(idx)))
                previousLetters = i
                continue
        # id处理完过后我们来处理digits
        # 首先处理缓冲区没东西的情况
        if previousLetters == "":
            if isNumber(i):
                previousLetters += i
                continue
        # 只需要判断前一个符号是不是数字
        elif isNumber(previousLetters[-1]):
            # 如果当前符号是数字那就继续
            if isNumber(i):
                previousLetters += i
                continue
            # 如果是空格或者符号那就存
            elif isSpacer(i) or maybeOP(i):
                addr = len(symbols)
                symbols.append(
                    {"addr": str(addr), "value": previousLetters, "type": "digits", "line": line, "cur": cnt})
                finalTokens.append(("digits", str(addr)))
                if maybeOP(i):
                    previousLetters = i
                else:
                    previousLetters = ""
                continue
            # 如果读到其它东西报Warning然后存
            else:
                lexWarning(cnt, line, previousLetters+i)
                addr = len(symbols)
                symbols.append(
                    {"addr": str(addr), "value": previousLetters, "type": "digits", "line": line, "cur": cnt})
                finalTokens.append(("digits", str(addr)))
                previousLetters = i
                continue
    return finalTokens, symbols


def lookup(symbols, value):
    for i in range(len(symbols)):
        if symbols[i]["value"] == value:
            return i
    return -1


def outputTokens(tokens, filepath=""):
    if filepath == "":
        for i in tokens:
            print(i)
    else:
        try:
            print("Writing tokens to file: " + filepath)
            f = open(filepath, "w")
            for i in tokens:
                print(i, file=f)
        except:
            print("Error:", "Filepath error!")


def outputSymbols(symbols, filepath=""):
    if filepath == "":
        for i in symbols:
            print(i)
    else:
        try:
            print("Writing symbols to file: " + filepath)
            f = open(filepath, "w")
            for i in symbols:
                print(i, file=f)
        except:
            print("Error:", "Filepath error!")


def isLetter(lt):
    if ord(lt) >= ord("a") and ord(lt) <= ord("z") or ord(lt) >= ord("A") and ord(lt) <= ord("Z") or ord(lt) == ord("_"):
        return True
    return False


# 判断是否为数字

def isNumber(lt):
    if ord(lt) >= ord("0") and ord(lt) <= ord("9"):
        return True
    return False

# 判断是否为运算符开头


def maybeOP(lt):
    if lt == "+" or lt == "-" or lt == "*" or lt == "/" or lt == ";" or lt == "(" or lt == ")" or lt == "'" or lt == "<" or lt == "=" or lt == ">" or lt == "!":
        return True
    return False

# 判断是否为关键字


def isKeyword(word):
    kwd = ["if", "else", "while", "int", "float"]
    if word in kwd:
        return True
    return False


def isSpacer(lt):
    if lt == " " or lt == "\n":
        return True
    return False


def lexErrMsg(cur=0, line=0, content=""):
    global errCnt
    errCnt += 1
    spaceser()
    print(
        f"Error {errCnt}:", f"there's a error at line {line} cur {cur} which is:")

    print(content)
    print("Please check your code, ignore it and continue? (Y/N): ", end="")
    while True:
        opt = input("")
        if opt == "Y":
            print("Ignore this error, continue process...")
            spaceser()
            return True
        elif opt == "N":
            print("Error, Exit process...")
            spaceser()
            return False
        else:
            print("Please input Y/N:", end="")


def lexWarning(cur=0, line=0, content=""):
    global warCnt
    warCnt += 1
    spaceser()
    print(f"Warning {warCnt}:",
          f"There's a warning at line {line} cur {cur} which is:")
    print(content)
    print("Vaala's Lexer try to continue, the ans may be not right, check your code.")
    spaceser()

# （2）	提供源程序输入界面；


def helloFunc():
    spaceser()
    print(r"""
      ___           ___           ___           ___       ___           ___     
     /\__\         /\  \         /\  \         /\__\     /\  \         /\  \    
    /:/  /        /::\  \       /::\  \       /:/  /    /::\  \       /::\  \   
   /:/  /        /:/\:\  \     /:/\:\  \     /:/  /    /:/\:\  \     /:/\ \  \  
  /:/__/  ___   /::\~\:\  \   /::\~\:\  \   /:/  /    /::\~\:\  \   _\:\~\ \  \ 
  |:|  | /\__\ /:/\:\ \:\__\ /:/\:\ \:\__\ /:/__/    /:/\:\ \:\__\ /\ \:\ \ \__\
  |:|  |/:/  / \/__\:\/:/  / \/__\:\/:/  / \:\  \    \/__\:\/:/  / \:\ \:\ \/__/
  |:|__/:/  /       \::/  /       \::/  /   \:\  \        \::/  /   \:\ \:\__\  
   \::::/__/        /:/  /        /:/  /     \:\  \       /:/  /     \:\/:/  /  
    ~~~~           /:/  /        /:/  /       \:\__\     /:/  /       \::/  /   
                   \/__/         \/__/         \/__/     \/__/         \/__/    
      ___       ___           ___           ___           ___                   
     /\__\     /\  \         |\__\         /\  \         /\  \                  
    /:/  /    /::\  \        |:|  |       /::\  \       /::\  \                 
   /:/  /    /:/\:\  \       |:|  |      /:/\:\  \     /:/\:\  \                
  /:/  /    /::\~\:\  \      |:|__|__   /::\~\:\  \   /::\~\:\  \               
 /:/__/    /:/\:\ \:\__\ ____/::::\__\ /:/\:\ \:\__\ /:/\:\ \:\__\              
 \:\  \    \:\~\:\ \/__/ \::::/~~/~    \:\~\:\ \/__/ \/_|::\/:/  /              
  \:\  \    \:\ \:\__\    ~~|:|~~|      \:\ \:\__\      |:|::/  /               
   \:\  \    \:\ \/__/      |:|  |       \:\ \/__/      |:|\/__/                
    \:\__\    \:\__\        |:|  |        \:\__\        |:|  |                  
     \/__/     \/__/         \|__|         \/__/         \|__|                  

""")
    spaceser()


def spaceser():
    print("=========================================================")


def finalReport():
    if errCnt == 0 and warCnt == 0:
        print("0 Warning, 0 Error, Great! Good to go.")
    else:
        warMsg = "Warning"if warCnt == 1 else "Warnings"
        errMsg = "Error"if errCnt == 1 else "Errors"
        print(f"{warCnt} {warMsg}, {errCnt} {errMsg}, OH NO.")


def test(**kwargs):
    print(kwargs)


if __name__ == "__main__":
    sourceCode = ""
    helloFunc()
    print("Choose input mode...")
    print("1. filepath")
    print("2. standard input")
    print(">>> ", end="")
    mode = input()
    if mode == "1":
        print("your code path is:")
        print(">>> ", end="")
        filepath = input()
        sourceCode = read(mode="file", filepath=filepath)
        spaceser()

    else:
        sourceCode = read(mode="standard")
    if sourceCode == False:
        exit(1)
    tokens, symbols = lexer(sourceCode)
    outputTokens(tokens, "token.out")
    outputSymbols(symbols, "symbol.out")
    finalReport()
