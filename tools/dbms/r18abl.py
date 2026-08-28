# -*- coding: utf-8 -*-
"""順序保存 (→) を `ST_TS v<=5 len<=11` で、条項を切りながら測る。

母集団を 1 度だけ作り、旗の辞書を書き換えて何通りも回す。
使い方: python3 tools/dbms/r18abl.py [v] [len]
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3

v = int(sys.argv[1]) if len(sys.argv) > 1 else 5
L = int(sys.argv[2]) if len(sys.argv) > 2 else 11

t0 = time.time()
P = r7.stts_pool(v, L)
print('母集団 ST_TS v<=%d len<=%d  %d 個  (%.0fs)' % (v, L, len(P), time.time() - t0),
      flush=True)

# (旗の場所, 鍵, 値) の並び。既定 = v20。
CFG = [
    ('     h1 off',     [(rows3.V14, 'h1', False)]),
    ('v18  tlterm+awdown off',
                        [(rows3.V20, 'tlterm', False), (rows3.V17, 'awdown', False)]),
]


def run(name, sets):
    old = [(d, k, d[k]) for d, k, _ in sets]
    for d, k, val in sets:
        d[k] = val
    t = time.time()
    up = eq = dn = 0
    ex = []
    prev = None
    for i, M in enumerate(P):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        cur = tuple(tuple(c) for c in b2d3([list(c) for c in M]))
        if prev is not None:
            a, b = prev[0], cur
            if a < b:
                up += 1
            else:
                if a == b:
                    eq += 1
                else:
                    dn += 1
                if len(ex) < 4:
                    ex.append((('eq' if a == b else 'dn'), prev[1], M))
        prev = (cur, M)
    print('%-26s 破れ **%d**（等 %d / 減 %d）  (%.0fs)'
          % (name, eq + dn, eq, dn, time.time() - t), flush=True)
    for k, A, B in ex:
        f = lambda X: ''.join('(%d,%d,%d)' % c for c in X)
        print('     %s M1=%s' % (k, f(A)), flush=True)
        print('        M2=%s' % f(B), flush=True)
    for d, k, val in old:
        d[k] = val


for name, sets in CFG:
    run(name, sets)
