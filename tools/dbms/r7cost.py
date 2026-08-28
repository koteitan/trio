# -*- coding: utf-8 -*-
"""3 旗（tiesd / awflip / h1）を切る代償を測る。像を pickle して外で比べる。"""
import sys, os, pickle
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3
from core import isstd

v, L, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
P = r7.stts_pool(v, L)
IM = []; ns = 0
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    B = tuple(tuple(c) for c in b2d3(list(M)))
    IM.append(B)
    if not isstd(B, 'DBMS'):
        ns += 1
print('%s  母数 %d  **非標準の像 %d**'
      % (' '.join(k for k in sorted(os.environ) if k.startswith('RS_')) or '既定',
         len(P), ns))
pickle.dump(IM, open(out, 'wb'), protocol=4)
