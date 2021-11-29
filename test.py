import lrparsing
import lex

if __name__ == '__main__':
    lrparsing.initStatus()
    lrparsing.genStatusSet(0)
    for k, v in lrparsing.analyzerTable.items():
        for kk, vv in v.items():
            if len(vv) > 1:
                print(kk, vv)
