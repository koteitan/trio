# -*- coding: utf-8 -*-
"""**課題 (DEPTH) —— 深さを増やして `h1out` の遺伝率を追う。**

## team-lead の機構（私の実測と完全に一致）

`Lift1 X t` は **`le1 X 0 j`（錐の中）の列だけ**に `t` を足す（`Wset:927`）。
根は反射で必ず錐の中 ⟹ **根は `+e` される**。`h1out` の相手は**錐の外** ⟹ **持ち上がらない**。
⟹ **差が毎段 `e` ずつ縮む**。

⚠ だが §R193 では 深さ1 99.1291% → 深さ2 99.7433% と**良くなっている**。
⟹ **窓が短くなる効果と競争している。** ⟹ 深さ 3,4,5 を追う。

## 母集団と作り方（明記）

消費側の `Q`（`Lift1 ((0,v,z) :: R.dropLast) t`）で `TowerP''`（`0<|Q|` / `hr0` / `hz0`）＋ `d>0`。
`(d,e)` は `dOf`/`eOf`、以後は `oper` が決める。**`h1out` を満たす窓だけを次段に送る**
（＝ 帰納の中で実際に到達する状態）。⚠ ビーム幅つき（明記）。

## ★ 予想（教訓 45）

> **⚠ 深さ 3,4,5 でも **100% に近づく**と予想（99.1 → 99.7 → …）。**
> **⚠ 理由: 窓が短くなるほうが速い。⚠ ただし私は直近 2 回見立てを外している。**
> **⚠ (DEPTH-c) 破れた段の `|V|` は小さい（1〜2）と予想。**
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r169 import domT
from r171 import step_det
from r201 import dOf, eOf
from r206 import hr0
from r234 import h1out_bad


def gap(V):
    """`min over 錐の外の列 j` of `entry V 1 j - entry V 1 0`（差。負なら破れ）。"""
    g = None
    for j in range(1, len(V)):
        if trio.is_ancestor(V, 1, 0, j): continue
        if V[j][2] != 0 or V[j][1] == 0: continue
        dd = V[j][1] - V[0][1]
        g = dd if g is None else min(g, dd)
    return g


def run(L, R1, VS, ZS, TS, NS, depth, beam, seed, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    rnd = random.Random(seed); c = Counter(); t0 = time.time()
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
                    if h1out_bad(Q): continue
                    front = [(tuple(Q), d, e)]
                    for dep in range(1, depth + 1):
                        nxt = []
                        for (X, dd, ee) in front:
                            for n in NS:
                                for j in range(len(X)):
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    V = [tuple(y) for y in r[0]]
                                    c[(dep, '★ 分母: 窓')] += 1
                                    bad = h1out_bad(V)
                                    g = gap(V)
                                    c[(dep, '  |V| の合計')] += len(V)
                                    if g is not None:
                                        c[(dep, '  差の合計')] += g
                                        c[(dep, '  差の件数')] += 1
                                    if bad:
                                        c[(dep, '⛔ h1out(V) 破れ')] += 1
                                        c[(dep, '⛔ 破れた段の |V|', min(len(V), 5))] += 1
                                    else:
                                        c[(dep, '★ h1out(V) 成立')] += 1
                                        nxt.append((tuple(V), r[1], r[2]))
                        if not nxt: break
                        random.Random(seed + dep).shuffle(nxt)
                        front = nxt[:beam]
    print(f'### {tag}  深さ<={depth} ビーム{beam}  [{time.time()-t0:.1f}s]')
    print(f'    {"深さ":>4s} {"★ 分母":>10s} {"★ h1out 成立":>16s} {"⛔ 破れ":>12s} '
          f'{"平均 |V|":>9s} {"平均の差":>9s}')
    for dep in range(1, depth + 1):
        D = c[(dep, '★ 分母: 窓')]
        if not D: continue
        gn = c[(dep, '  差の件数')]
        print(f'    {dep:4d} {D:10d} {c[(dep,"★ h1out(V) 成立")]:9d} '
              f'({100*c[(dep,"★ h1out(V) 成立")]/D:7.4f}%) {c[(dep,"⛔ h1out(V) 破れ")]:7d} '
              f'({100*c[(dep,"⛔ h1out(V) 破れ")]/D:6.4f}%) '
              f'{c[(dep,"  |V| の合計")]/D:9.3f} '
              f'{(c[(dep,"  差の合計")]/gn if gn else float("nan")):9.3f}')
        rows = [(k[2], c[k]) for k in c if len(k) == 3 and k[0] == dep]
        if rows: print(f'         (DEPTH-c) 破れた段の |V|（5 は 5 以上）: {dict(sorted(rows))}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 5, 200, 961, '消費側 |R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 5, 120, 963, '★ 消費側 |R|=4 行1<3')
