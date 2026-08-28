# -*- coding: utf-8 -*-
"""H19: 順序保存（R7 の指標）を旗つきの写しで測る。"""
import sys, os, time, importlib
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import core, r7
mod = importlib.import_module(sys.argv[1])
v = int(sys.argv[2]) if len(sys.argv) > 2 else 5
L = int(sys.argv[3]) if len(sys.argv) > 3 else 10
P = r7.stts_pool(v, L)
IM = []
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IM.append(tuple(tuple(c) for c in mod.b2d3(list(M))))
o1 = sorted(range(len(P)), key=lambda i: P[i])
up, eq, dn, bad = r7.adj([IM[i] for i in o1])
o2 = sorted(range(len(P)), key=lambda i: IM[i])
u2, e2, d2, _ = r7.adj([P[i] for i in o2])
print('%s (%s) v<=%d len<=%d 母数 %d: **(→) 破れ %d（等 %d / 減 %d）  (←) 破れ %d**'
      % (sys.argv[1], os.environ.get('PXFLAGS', ''), v, L, len(P),
         eq + dn, eq, dn, e2 + d2))
for k, i in bad[:3]:
    print('   %s M1=%s' % (k, ''.join(str(c).replace(' ', '') for c in P[o1[i]])))
    print('      M2=%s' % ''.join(str(c).replace(' ', '') for c in P[o1[i + 1]]))
