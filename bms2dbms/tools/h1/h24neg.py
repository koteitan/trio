# -*- coding: utf-8 -*-
"""H24: `fE` が **C2 を壊す site** を集める（発火は展開 `A<n>` の側で起きる）。"""
import sys, os, pickle, time
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3z, core
from rows3 import gen3, key, cmpmat
from core import expand, show

NN, MC = 24, 40


def mk(mode, target=None, offs=None):
    # mode: 'all' 全部発火 / 'none' 一切発火しない / 'one' target の off だけ
    def f(X):
        Xt = tuple(map(tuple, X))
        if mode == 'all':
            s = None
        elif mode == 'none':
            s = set()
        else:
            s = offs if Xt == target else set()
        return rows3z.b2d3z(list(Xt), sites=s)[0]
    return f


def c2ok(f, M):
    N = tuple(f(list(M)))
    E = [tuple(expand(N, m)) for m in range(1, MC + 1)]
    for np in range(1, NN + 1):
        g = tuple(f(list(expand(tuple(M), np))))
        if not any(cmpmat(g, e) <= 0 for e in E):
            return False
    return True


A = [M for M in sorted(gen3('BMS', 6, zcap=1), key=key) if len(M) > 1]
NEG, POSA = set(), []
t0 = time.time()
nb = 0
base = mk('none')               # どこでも発火しない ＝ v20
allon = mk('all')               # 全部発火
for i, M in enumerate(A):
    if i % 500 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    S = tuple(map(tuple, M))
    if c2ok(allon, S) or not c2ok(base, S):
        continue
    nb += 1
    # 発火している (行列, off) を全部集める
    cand = []
    for X in [S] + [tuple(tuple(c) for c in expand(S, n)) for n in range(1, NN + 1)]:
        for off in sorted(set(x[0] for x in rows3z.b2d3z(list(X))[1])):
            cand.append((X, off))
    for X, off in cand:
        if not c2ok(mk('one', X, {off}), S):
            NEG.add((X, off))
    POSA.append(S)
print('C2 が `fE` で壊れる A %d 個 -> 単独で壊す site %d  (%.0fs)'
      % (nb, len(NEG), time.time() - t0))
pickle.dump(sorted(NEG), open('/tmp/h1work/h24neg.pkl', 'wb'))
