# -*- coding: utf-8 -*-
"""**R89 その 2 —— 展開の「形」を判定する。**

R89 その 1 で分かったこと: `CoreCap` の見る `S = Lift1 ((0,v,z) :: cap M b c) t` は
展開の分岐が 2 つしかない（`branch/copy` と `branch/noparent`）。ここではさらに、
`copy` の中を **`j0 = 0`（塔）** と **`j0 >= 1`（cons 保存）** に割り、
**その各々が本当にその形になっているか**を、形の等式で検算する。

検算する等式（神託ゼロ。純粋に `oper` の計算結果を照合するだけ）:

  (P1) `j0 >= 1`  ⟹  `S⟦n⟧` の先頭列 = `S` の先頭列（＝根が cons のまま残る）
       かつ `S⟦n⟧ = S[0] :: (S.tail)⟦n⟧`（根を外して再帰できる）
  (P2) `j0 = 0`   ⟹  `S⟦n⟧ = concat_{k<n} Lift1 (shiftr01 (k*d0) 0 Q) (k*d1)`,
       `Q = S[0:j1]`  （＝ 根つき塔。`Lift1` は `Wset.lean:927` の錐リフト）
  (P3) `noparent` ⟹  `S⟦n⟧ = S.dropLast = Lift1 ((0,v,z) :: M.take (|M|-1)) t`
       （＝ `CtxOK` が `k = |M|-1` で直接くれるもの）

さらに:
  (Q1) `j0 = 0` は行 0 の親 `p1` が 0 であることと同値か（＝ `b,c` に依らない M だけの条件か）
  (Q2) 二分（j0=0 か否か）は `b, c` に依存するか
  (Q3) `j0 = 0` のときの `(i1, z)` 分布（`tower2_root_z_zero`: srow=2 & z=1 は起きない、の検算）
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter

from r89 import lift1, shape, cap, inW


def rowparent0(S, j):
    """行 0 の親（`nextrel0`）。"""
    for p in range(j - 1, -1, -1):
        if S[p][0] < S[j][0]:
            return p
    return None


def shiftr0(Q, d):
    return [(c[0] + d, c[1], c[2]) for c in Q]


def tower(Q, d0, d1, n):
    """concat_{k<n} Lift1 (shiftr01 (k*d0) 0 Q) (k*d1)."""
    out = []
    for k in range(n):
        out += lift1(shiftr0(Q, k * d0), k * d1)
    return out


def run(DS, BS, CS, VS, ZS, TS, CAPB, CAPC, LS, label, NS=(1, 2, 3, 4)):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    tot = Counter(); q1 = Counter(); q2 = Counter(); q3 = Counter()
    bad = {}
    t0 = time.time()
    for L in LS:
        for Mt in itertools.product(COL, repeat=L):
            M = list(Mt)
            for v in VS:
                for z in ZS:
                    for t in TS:
                        dic = set()
                        for b in CAPB:
                            for c in CAPC:
                                S = lift1([(0, v, z)] + cap(M, b, c), t)
                                j1 = len(S) - 1
                                br, j0, i1, d0, d1 = shape(S)
                                if br == 'noparent':
                                    dic.add('noparent')
                                    ok = all(
                                        trio.expand(list(S), n) == S[:-1]
                                        for n in NS)
                                    tot['P3/' + ('ok' if ok else 'VIOL')] += 1
                                    if not ok:
                                        bad.setdefault('P3', (M, v, z, b, c, t, S))
                                    continue
                                if br != 'copy':
                                    tot['branch/' + br] += 1
                                    continue
                                dic.add(j0 == 0)
                                if j0 >= 1:
                                    ok = True
                                    for n in NS:
                                        E = trio.expand(list(S), n)
                                        if not E or tuple(E[0]) != tuple(S[0]):
                                            ok = False; break
                                        if [tuple(x) for x in E] != \
                                           [tuple(S[0])] + [tuple(x) for x in
                                                            trio.expand(list(S[1:]), n)]:
                                            ok = False; break
                                    tot['P1/' + ('ok' if ok else 'VIOL')] += 1
                                    if not ok:
                                        bad.setdefault('P1', (M, v, z, b, c, t, S, j0))
                                else:
                                    Q = S[:j1]
                                    ok = all(
                                        [tuple(x) for x in trio.expand(list(S), n)]
                                        == [tuple(x) for x in tower(Q, d0, d1, n)]
                                        for n in NS)
                                    tot['P2/' + ('ok' if ok else 'VIOL')] += 1
                                    if not ok:
                                        bad.setdefault('P2', (M, v, z, b, c, t, S, d0, d1,
                                                              [tuple(x) for x in trio.expand(list(S), 2)],
                                                              [tuple(x) for x in tower(Q, d0, d1, 2)]))
                                    p1 = rowparent0(S, j1)
                                    q1['j0=0 & p1=0' if p1 == 0 else 'j0=0 & p1>=1'] += 1
                                    q3[(i1, z)] += 1
                        d = {x for x in dic if x is not 'noparent'}
                        q2['const' if len(dic) == 1 else 'mixed'] += 1
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s)')
    for k in sorted(tot):
        print(f'  {k:16s} {tot[k]:10d}')
    print('  -- (Q1) j0=0 は行 0 の親 p1=0 と同値か --')
    for k in sorted(q1):
        print(f'     {k:16s} {q1[k]:10d}')
    print('  -- (Q2) 二分 (j0=0 / j0>=1 / noparent) は (b,c) に依存するか --')
    for k in sorted(q2):
        print(f'     {k:16s} {q2[k]:10d}')
    print('  -- (Q3) j0=0 のときの (i1=srow, z) --')
    for k in sorted(q3):
        print(f'     i1={k[0]} z={k[1]} : {q3[k]:10d}')
    for k in sorted(bad):
        print(f'  ⚠ {k}: {bad[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=3)
    a = ap.parse_args()
    run((1, 2, 3), (0, 1, 2), (0, 1), (0, 1, 2), (0, 1), (0, 1, 2),
        (0, 1, 2, 3), (0, 1, 2), tuple(range(1, a.L + 1)),
        f'R89b 形の検算 |M|<={a.L}')
