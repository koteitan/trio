# -*- coding: utf-8 -*-
"""H7: **ずらしを全部見る**一致の数え上げ（今までは ずれ -1 しか見ていなかった）。

    agree(f) = { (A, n, m) : conv3(A<n>) == (conv3 A)<m> }

条項を入れて **1 組でも壊れたら落ちる**、という足切りに使う。
`tt` は ずれ -1 だけ見ると +8 / 壊れた 0 だが、ずれ 0 を見ると壊れる。
"""
import sys, time
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, core
from core import expand

def agree(f, lim=6, nmax=4, mmax=6, zcap=1):
    A = sorted(rows3.gen3('BMS', lim, zcap=zcap), key=rows3.key)
    S = set()
    for i, M in enumerate(A):
        if len(M) < 2: continue
        if i % 2000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        Mt = tuple(map(tuple, M))
        fM = tuple(map(tuple, f(list(M))))
        Ts = {}
        for m in range(1, mmax + 1):
            T = tuple(expand(fM, m)); Ts.setdefault(len(T), []).append((m, T))
        for n in range(1, nmax + 1):
            E = [tuple(x) for x in expand(Mt, n)]
            U = tuple(f(E))
            for m, T in Ts.get(len(U), ()):
                if U == T: S.add((Mt, n, m))
    return S
