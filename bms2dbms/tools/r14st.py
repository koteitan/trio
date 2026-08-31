import sys, os
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7, sheet3
from rows3 import b2d3
MODE = sys.argv[1]
_t = rows3.tie_sd
if MODE == 'guard':
    rows3.V18['tiesd'] = True
    rows3.tie_sd = lambda Mo, off: False if off == len(Mo) - 1 else _t(Mo, off)
elif MODE == 'on':
    rows3.V18['tiesd'] = True
elif MODE == 'noaw':
    rows3.V17['awflip'] = False
elif MODE == 'noh1':
    rows3.V14['h1'] = False
elif MODE == 'awmono':
    _p = rows3.par0
    def aw2(Mo, off):
        a01 = _p(Mo, off)
        if a01 >= 0 and off - a01 > 3:
            return False
        p0 = Mo[off][0]
        for t in range(off - 1, -1, -1):
            if Mo[t][0] < p0:
                return False
            if Mo[t][0] == p0:
                return Mo[t][0] == Mo[t][1] and Mo[t][0] >= 1
        return False
    rows3.aw_flip = aw2
P = r7.stts_pool(5, 10)
IM = []
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IM.append(tuple(tuple(c) for c in b2d3(list(M))))
o = sorted(range(len(P)), key=lambda i: P[i])
dn = sum(1 for i in range(len(o) - 1) if IM[o[i]] > IM[o[i + 1]])
eq = sum(1 for i in range(len(o) - 1) if IM[o[i]] == IM[o[i + 1]])
ns = sum(1 for B in IM if not core.isstd(B, 'DBMS'))
ok = sum(1 for row, b, d in sheet3.load(1) if tuple(b2d3(b)) == d)
print('%-6s  **減 %d**（重複 %d）  非標準の像 %d  シート %d/1358'
      % (MODE, dn, eq, ns, ok))
