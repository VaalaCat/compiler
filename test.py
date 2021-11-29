import lrparsing
import lex
import json

if __name__ == '__main__':
    lrparsing.initStatus()
    lrparsing.genStatusSet(0)
    f = open("analyzerTable.out", "w")
    l = []
    # print(json.dumps(lrparsing.analyzerTable), file=f)
    for k, v in lrparsing.analyzerTable.items():
        print(k, ":", v, file=f)
    for k, v in lrparsing.analyzerTable.items():
        l.append(k)
    l.sort()
    print(l)
    print(len(l))
    for i in range(0, len(l)-1):
        if abs(l[i]-l[i+1]) != 1:
            print("lackof:", l[i+1]-1)
    f = open("statusSet.out", "w")
    for i in lrparsing.statusSet:
        print(i, file=f)
