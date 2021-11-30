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
        for kk, vv in v.items():
            if len(vv) > 1:
                print("冲突!")
                print(kk, vv)
    for k, v in lrparsing.analyzerTable.items():
        l.append(k)
    l.sort()
    print(l)
    print(len(l))
    for i in range(0, len(l)-1):
        if abs(l[i]-l[i+1]) != 1:
            print("lackof:", l[i+1]-1)
    f = open("statusSet.out", "w")
    cnt = 0
    for i in lrparsing.statusSet:
        print(cnt, i, file=f)
        cnt += 1
