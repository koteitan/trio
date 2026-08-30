# -*- coding: utf-8 -*-
"""**R89 その 6 —— `argOK` はどこで破れるか（I3 の起点）。**

R89c で「尾の `argOK` は木の下で 5.6% 破れる」と分かった。`oper_cons_nat` は
`argOK R` を要求するので、**どの分岐が argOK を壊すのか**が分かれば場合分けが閉じる。

予想（定義からの算術）: **`d0 = 0`（= `srow = 0`）の根つき塔だけが壊す。**
  * P3 (dropLast) は部分列 ⟹ argOK 保存
  * P1 (cons 保存) のコピーは深さ `entry R 0 j + k*d0 >= 1` ⟹ argOK 保存
  * P2 (根つき塔) のコピー k は深さ `k*d0` から始まる。
    `d0 >= 1` なら `k>=1` で深さ >= 1 ⟹ 保存。**`d0 = 0` のときだけ深さ 0 の列が内部に出る**

これを実測で確かめる（親が argOK・子が非 argOK になる「起点」を分岐別に数える）。
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r89 import lift1, shape, cap, lev

NS = (1, 2, 3)


def walk(S, a, depth, maxlen, seen, stat, bad):
    key = (tuple(tuple(c) for c in S), a)
    if key in seen:
        return
    seen.add(key)
    if len(S) <= 1:
        return
    ok_here = all(c[0] >= 1 for c in S[1:])
    br, j0, i1, d0, d1 = shape(S)
    tag = br if br != 'copy' else ('tower/srow=%d' % i1 if j0 == 0 else 'cons')
    if depth <= 0 or len(S) > maxlen:
        stat['budget/cut'] += 1
        return
    for n in NS:
        C = trio.expand(list(S), n)
        if len(C) > 1:
            ok_child = all(c[0] >= 1 for c in C[1:])
            if ok_here and not ok_child:
                stat['起点/' + tag + '/n=%d' % n] += 1
                bad.setdefault(tag, (tuple(tuple(c) for c in S), n,
                                     tuple(tuple(c) for c in C)))
            stat['遷移/' + tag + '/' + ('ok->ok' if ok_here and ok_child else
                                        'ok->VIOL' if ok_here else
                                        'VIOL->ok' if ok_child else 'VIOL->VIOL')] += 1
        walk(C, a, depth - 1, maxlen, seen, stat, bad)


ap = argparse.ArgumentParser()
ap.add_argument('--L', type=int, default=2)
ap.add_argument('--depth', type=int, default=9)
a = ap.parse_args()
COL = [(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2) for c in (0, 1)]
stat = Counter(); bad = {}; seen = set()
t0 = time.time()
for L in range(1, a.L + 1):
    for Mt in itertools.product(COL, repeat=L):
        M = list(Mt)
        for v in (0, 1, 2):
            for z in (0, 1):
                for t in (0, 1, 2):
                    for b in (0, 1, 2, 3):
                        for c in (0, 1, 2):
                            S = lift1([(0, v, z)] + cap(M, b, c), t)
                            walk(S, 2 * (v + t) + z, a.depth, 26, seen, stat, bad)
print(f'### R89e argOK の破れの起点 |M|<={a.L} depth={a.depth}  ({time.time()-t0:.1f}s)')
for k in sorted(stat):
    print(f'  {k:34s} {stat[k]:12d}')
for k in sorted(bad):
    print(f'  ex {k}: {bad[k]}')
