"""R23 の設計の上限を測る。

深さ（影を何段使うか）を総当たりで振って、シートの正解を作れる行を数える。
作れた行 = 「深さ規則さえ正しければ届く行」、作れない行 = 設計そのものが足りない行。

  python3 tools/dbms/ceiling.py
"""
import sys, os, itertools, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_sheet import load
import rule as R
d=[x for x in load() if x[3]==3]
out=[]; nsol=0
for r,mb,md,_ in d:
    B=[x for x,c in enumerate(mb) if c[1]==1 and c[2]==0 and c[0]>=2]
    if len(B)>12: continue
    sols=[]
    for bits in itertools.product((0,1), repeat=len(B)):
        dd=dict(zip(B,bits))
        if R.dedup(R._stair(mb,3, lambda x,c: dd.get(x,0)))==md: sols.append(dd)
    if not sols: continue
    nsol+=1
    fixed={}
    for x in B:
        vals={s[x] for s in sols}
        if len(vals)==1: fixed[x]=vals.pop()
    out.append((list(map(list,mb)), {str(k):v for k,v in fixed.items()}, len(sols)))
print('解のあった行', nsol, ' 平均解数 %.2f'%(sum(o[2] for o in out)/max(1,len(out))))
print('確定した列', sum(len(o[1]) for o in out))
if len(sys.argv) > 1:
    json.dump(out, open(sys.argv[1], 'w'))
