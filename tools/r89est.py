# -*- coding: utf-8 -*-
"""R89 の見積もり: 「数えるだけ」＋ 1 件あたりの実測時間（教訓: 走らせる前に見積もる）。"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio

def cols(DS, BS, CS):
    return [(d, b, c) for d in DS for b in BS for c in CS]

# 主母集団のグリッド案
DS, BS, CS = (1, 2, 3), (0, 1, 2), (0, 1)
VS, ZS, TS = (0, 1, 2), (0, 1), (0, 1, 2)
CAPB, CAPC = (0, 1, 2, 3), (0, 1, 2)
COL = cols(DS, BS, CS)
print('column alphabet |COL| =', len(COL))
tot = 0
for L in range(1, 5):
    nM = len(COL) ** L
    inst = nM * len(VS) * len(ZS) * len(TS) * len(CAPB) * len(CAPC)
    print(f'  |M|={L}: contexts={nM:9d}  instances={inst:12d}')
    if L <= 3:
        tot += inst
print('total instances for |M|<=3 =', tot)

# 1 件あたりの実測（構造測定のみ: badroot / srow / d0 / d1）
def lift1(S, t):
    return [(c[0], c[1] + (t if trio.is_ancestor(S, 1, 0, i) else 0), c[2])
            for i, c in enumerate(S)]

def badroot(S):
    x = len(S) - 1
    if x == 0:
        return ('ident', None, None, 0, 0)
    if all(v == 0 for v in S[x]):
        return ('zero', None, None, 0, 0)
    t = max(y for y in range(3) if S[x][y] > 0)
    r = trio.parent(S, t, x)
    if r is None:
        return ('noparent', None, t, 0, 0)
    d0 = S[x][0] - S[r][0] if t > 0 else 0
    d1 = S[x][1] - S[r][1] if t > 1 else 0
    return ('copy', r, t, d0, d1)

N = 20000
Ms = [list(m) for m in itertools.islice(itertools.product(COL, repeat=3), 400)]
t0 = time.time()
k = 0
for M in Ms:
    for v in VS:
        for z in ZS:
            for b in CAPB:
                for c in CAPC:
                    cap = M[:-1] + [(M[-1][0], b, c)]
                    for t in TS:
                        S = lift1([(0, v, z)] + cap, t)
                        badroot(S)
                        k += 1
                        if k >= N:
                            break
                    if k >= N: break
                if k >= N: break
            if k >= N: break
        if k >= N: break
    if k >= N: break
dt = time.time() - t0
print(f'structural: {k} instances in {dt:.2f}s -> {dt/k*1e6:.1f} us/instance')
print(f'  => |M|<=3 ({tot} inst) ~ {tot*dt/k:.0f} s')
