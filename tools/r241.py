# -*- coding: utf-8 -*-
"""**課題 (NBHER) ＋ (SROWSPLIT)。**

## 母集団（1 行で再掲）

消費側の `Q`（`Lift1 ((0,v,z) :: R.dropLast) t`）で `TowerP''`（`0<|Q|` / `hr0` / `hz0`）＋ `d>0`
＋ **`hnbQ(Q)` 成立**。`(d,e)` は `dOf`/`eOf`。**`n` を振る（本命は 5, 10, 20）。**

    `hnbQ(X) ＝ ∀ i, 0 < i < |X| → entry X 1 0 < entry X 1 i`
      （`mTowerClosed_of_snocStepSameBlock` の `hnb` の逐語形）

## ★ 予想（教訓 45）

> **⚠ (NBHER-a) `h1out` より強い条件なので遺伝率は下がると予想。§R220 では 99.62〜99.75%。**
> **⚠ (NBHER-b) team-lead の論法（`hnbQ` は `blocker_of_large_k` の前提 `houtj` をかわす）が
>   正しければ **`n` で悪化しない**。⚠ ただし**窓の根が変わる**ので私は自信が無い。
>   ⟹ **見積もりを書かない**（直近 3 回外している）。**測って答える。****
> **⚠ (SROWSPLIT) H12 の定理が正しければ **`srow = 1` の破れは 0 件**。**
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r169 import domT
from r201 import dOf, eOf
from r206 import hr0


def hnbQ(X):
    return all(X[0][1] < X[i][1] for i in range(1, len(X)))


def run(L, R1, VS, ZS, TS, NS, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    c = Counter(); ex = []; t0 = time.time()
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        if srow(R, len(R) - 1) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q = M[:-1]
                    if len(Q) < 2: continue
                    d, e = dOf(M), eOf(M)
                    if not (d > 0 and hr0(Q) and Q[0][2] == 0): continue
                    if not hnbQ(Q): continue          # ★ 分母: hnbQ(Q) 成立
                    LQ = len(Q)
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(LQ):
                            S = T + B[:j + 1]
                            lastx = len(S) - 1
                            i1 = srow(S, lastx)
                            par = trio.parent(S, i1, lastx)
                            if par is None: continue
                            V = [tuple(x) for x in S[par:lastx]]
                            if len(V) < 2: continue
                            c[(n, '★ 分母: 窓')] += 1
                            if hnbQ(V):
                                c[(n, '★ (NBHER-a) hnbQ(V) 成立')] += 1
                            else:
                                c[(n, '⛔ 破れ')] += 1
                                c[('(SROWSPLIT) 破れの srow', i1)] += 1
                                bad = [i for i in range(1, len(V))
                                       if not (V[0][1] < V[i][1])]
                                anc = [i for i in bad if trio.is_ancestor(V, 0, 0, i)]
                                c[('(SROWSPLIT) 破る列', i1,
                                   'le0 祖先' if anc else '非 le0 祖先')] += 1
                                # 型 B か
                                tb = (len(V) == 3 and V[1][1] == 0 and
                                      V[2][1] <= V[0][1] and all(p[2] == 0 for p in V))
                                c[(n, '  型 B と同型' if tb else '  型 B でない')] += 1
                                if len(ex) < 6:
                                    ex.append((n, Q, d, e, j, V, i1, 'B' if tb else '-'))
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    print(f'    {"n":>4s} {"★ 分母":>10s} {"★ hnbQ(V) 成立":>18s} {"⛔ 破れ":>12s} '
          f'{"型B同型":>8s}')
    for n in NS:
        D = c[(n, '★ 分母: 窓')]
        if not D: continue
        print(f'    {n:4d} {D:10d} {c[(n,"★ (NBHER-a) hnbQ(V) 成立")]:11d} '
              f'({100*c[(n,"★ (NBHER-a) hnbQ(V) 成立")]/D:7.4f}%) {c[(n,"⛔ 破れ")]:7d} '
              f'({100*c[(n,"⛔ 破れ")]/D:6.4f}%) {c[(n,"  型 B と同型")]:8d}')
    print('  (SROWSPLIT) 破れの `srow`: ',
          dict(sorted((k[1], c[k]) for k in c
                      if isinstance(k, tuple) and k[0] == '(SROWSPLIT) 破れの srow')))
    print('  (SROWSPLIT) 破る列（`srow` 別）: ',
          {(k[1], k[2]): c[k] for k in c if len(k) == 3 and k[0] == '(SROWSPLIT) 破る列'})
    for x in ex:
        print(f'      ⛔ 破れ例 n={x[0]} Q={x[1]} d={x[2]} e={x[3]} j={x[4]} ⟹ V={x[5]} '
              f'srow={x[6]} 型={x[7]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3,5,10,20), '消費側 |R|=3 行1<3')
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3,5,10,20), '★ 消費側 |R|=3 行1<5')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,3,5,10,20), '★ 消費側 |R|=4 行1<3')
