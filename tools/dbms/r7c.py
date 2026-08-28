# -*- coding: utf-8 -*-
"""`SeqEmbT3` の破れの数だけを出す（旗の掃き出し用）。環境変数で版を切り替える。"""
import sys, os
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3

v = int(sys.argv[1]); L = int(sys.argv[2])
P = r7.stts_pool(v, L)
IM = []
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IM.append(tuple(tuple(c) for c in b2d3(list(M))))
o = sorted(range(len(P)), key=lambda i: P[i])
dn = sum(1 for i in range(len(o) - 1) if IM[o[i]] > IM[o[i + 1]])
eq = sum(1 for i in range(len(o) - 1) if IM[o[i]] == IM[o[i + 1]])
flags = ' '.join('%s=%s' % (k, os.environ[k]) for k in sorted(os.environ)
                 if k.startswith('RS_'))
print('%-40s 母数 %d  逆転 %d  重複 %d  **破れ %d**'
      % (flags or '(既定 = v18)', len(P), dn, eq, dn + eq))
