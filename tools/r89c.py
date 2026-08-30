# -*- coding: utf-8 -*-
"""**R89 その 3 —— 展開の木を全部降りて、現れる「形」を数え上げる。**

R89b で `CoreCap` の入口 `S = Lift1 ((0,v,z) :: cap M b c) t` の展開が
3 分岐しかないこと（P1/P2/P3、破れ 0）を確かめた。ここでは **木の全ノード**で
同じことを確かめ、次の不変量を検算する:

  (I1) 木のどのノードも **`(0, v+t, z)` を先頭に持つ cons 形**（根が変わらない）
  (I2) 根の `lev` = `2(v+t)+z` = 段 `a` のまま（段を食わない）
  (I3) 尾 `R = ノード.tail` は `argOK`（行 0 >= 1）
  (I4) `A ++ B`（`WCat` 形＝ **空でない土台に、独立な W 元を連結する**）は現れない
       ⟹ 現れる連結は「cons 保存」か「根つき塔 `tow`」のどちらかしかない

⚠ 神託ゼロ。すべて `oper` の計算結果の照合。所属判定 `inW` は
`Wchar.lean` の厳密な特徴づけ（`mem_iff_oper_mem` / `mem_iff_lev_le`）のみを使う。
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter

from r89 import lift1, shape, cap, lev

NS = (1, 2, 3)


def walk(S, a, depth, maxlen, seen, stat, bad, root):
    """展開の木を降りて、各ノードの分岐と不変量を数える。"""
    key = (tuple(tuple(c) for c in S), a)
    if key in seen:
        return
    seen.add(key)
    if len(S) == 0:
        stat['leaf/nil'] += 1; return
    if len(S) == 1:
        stat['leaf/single/' + ('fits' if lev(S[0]) <= a else 'OVER')] += 1
        if lev(S[0]) > a:
            bad.setdefault('lev>a', (S, a))
        return
    # ---- 不変量 ----
    if tuple(S[0]) != root:
        stat['I1/VIOL'] += 1; bad.setdefault('I1', (S, root))
    else:
        stat['I1/ok'] += 1
    if lev(S[0]) != a:
        stat['I2/VIOL'] += 1; bad.setdefault('I2', (S, a))
    else:
        stat['I2/ok'] += 1
    i3 = all(c[0] >= 1 for c in S[1:])
    stat['I3/ok' if i3 else 'I3/VIOL'] += 1
    if not i3:
        bad.setdefault('I3', tuple(tuple(c) for c in S))
    br, j0, i1, d0, d1 = shape(S)
    if not i3:
        stat['I3viol/branch/' + br] += 1
        if all(c[0] == 0 for c in S):
            stat['I3viol/all-depth-0'] += 1
        elif S[-1][0] == 0:
            stat['I3viol/last-depth-0'] += 1
        else:
            stat['I3viol/other'] += 1
            bad.setdefault('I3-other', tuple(tuple(c) for c in S))
    stat['node/' + br + ('' if br != 'copy' else ('/j0=0' if j0 == 0 else '/j0>=1'))] += 1
    if br == 'copy' and j0 == 0:
        stat['tower/i1=%d' % i1] += 1
    if depth <= 0 or len(S) > maxlen:
        stat['budget/cut'] += 1
        return
    for n in NS:
        walk(trio.expand(list(S), n), a, depth - 1, maxlen, seen, stat, bad, root)


def run(DS, BS, CS, VS, ZS, TS, CAPB, CAPC, LS, depth, maxlen, label):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    stat = Counter(); bad = {}
    seen = set()          # 全入口で共有（ノードは自分の根を決めるので不変量は壊れない）
    t0 = time.time(); ninst = 0
    for L in LS:
        for Mt in itertools.product(COL, repeat=L):
            M = list(Mt)
            for v in VS:
                for z in ZS:
                    for t in TS:
                        for b in CAPB:
                            for c in CAPC:
                                S = lift1([(0, v, z)] + cap(M, b, c), t)
                                a = 2 * (v + t) + z
                                walk(S, a, depth, maxlen, seen, stat, bad,
                                     tuple(S[0]))
                                ninst += 1
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s, 入口 {ninst} 件)')
    for k in sorted(stat):
        print(f'  {k:24s} {stat[k]:12d}')
    for k in sorted(bad):
        print(f'  ⚠ {k}: {bad[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=2)
    ap.add_argument('--depth', type=int, default=7)
    ap.add_argument('--maxlen', type=int, default=24)
    a = ap.parse_args()
    run((1, 2, 3), (0, 1, 2), (0, 1), (0, 1, 2), (0, 1), (0, 1, 2),
        (0, 1, 2, 3), (0, 1, 2), tuple(range(1, a.L + 1)),
        a.depth, a.maxlen, f'R89c 木の不変量 |M|<={a.L} depth={a.depth}')
