# -*- coding: utf-8 -*-
"""**課題 (ZERO2) ＋ (LOCHER)。**

## 母集団（1 行で再掲）

消費側の `Q`（`Lift1 ((0,v,z) :: R.dropLast) t`）で `TowerP''`（`0<|Q|` / `hr0` / `hz0`）＋ `d>0`。
`(d,e)` は `dOf`/`eOf`。**接頭辞は帰納の実際の形 `A' = mTower Q d e n ++ B.take p`。**

## 測るもの

    **(ZERO2)** 型 B の破れで、**`A'` の行 2 が全部 0** か（H12 の `prefix_mem_of_zeroRow2` の前提）
    **(LOCHER-a)** 窓 `V` の**全列**（`j >= 1`）で `hloc`（＝ `hasParent (V.take (j+1)) (srow V j) j`）
    **(LOCHER-b)** `Q` の言葉の条件
      `LOC(X) ＝ ∀ j >= 1, ∃ y < j, le0 X y j ∧ entry X 1 y < entry X 1 j`
      の**成立率**と**遺伝率**
    **(LOCHER-c)** `n` を 5, 10, 20 にしても同じか

## ★ 予想（教訓 45）

> **⚠ (ZERO2) **100% にならない**と予想。`hz0(Q)` は**根**の行 2 しか言わないので、
>   `Q` の他の列が行 2 = 1 なら塔にも入り、`A'` に混ざる。**
> **⚠ (LOCHER-a)(b) は見積もりを書かない（直近で外している）。測って答える。**
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
from r234 import h1out_bad


def hloc_bad(V):
    """`hloc` が破れる列（`j >= 1`）。"""
    return [j for j in range(1, len(V))
            if trio.parent(V[:j + 1], srow(V, j), j) is None]


def LOC(X):
    """`∀ j >= 1, ∃ y < j, le0 X y j ∧ entry X 1 y < entry X 1 j`。破れる列を返す。"""
    bad = []
    for j in range(1, len(X)):
        ok = any(trio.is_ancestor(X, 0, y, j) and X[y][1] < X[j][1] for y in range(j))
        if not ok: bad.append(j)
    return bad


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
                    LQ = len(Q)
                    # (LOCHER-b) `Q` 側の成立率
                    c['(LOCHER-b) Q の分母'] += 1
                    lq = not LOC(Q)
                    if lq: c['★ (LOCHER-b) LOC(Q) 成立'] += 1
                    for n in NS:
                        P = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(1, LQ):
                            S = P + B[:j + 1]
                            lastx = len(S) - 1
                            par = trio.parent(S, srow(S, lastx), lastx)
                            if par is None: continue
                            p = par - len(P) if par >= len(P) else None
                            V = [tuple(x) for x in S[par:lastx]]
                            if len(V) < 2: continue
                            c[(n, '★ 分母: 窓')] += 1
                            # (LOCHER-a)
                            hb = hloc_bad(V)
                            if not hb: c[(n, '★ (LOCHER-a) hloc が全列で立つ')] += 1
                            else:
                                c[(n, '⛔ (LOCHER-a) hloc の破れ')] += 1
                                for jb in hb: c[('(LOCHER-a) 破れの srow', srow(V, jb))] += 1
                            # (LOCHER-b) 遺伝
                            if lq:
                                c[(n, '(LOCHER-b) 分母: LOC(Q) 成立')] += 1
                                if not LOC(V): c[(n, '★ (LOCHER-b) LOC(V) も成立')] += 1
                                else: c[(n, '⛔ (LOCHER-b) LOC(V) 破れ')] += 1
                            # (ZERO2) 型 B の破れで `A'` の行 2
                            bad = h1out_bad(V)
                            tb = (bad == [2] and len(V) == 3 and
                                  trio.parent(V[:3], srow(V, 2), 2) is not None)
                            if tb and p is not None:
                                A2 = P + B[:p]
                                c['★ (ZERO2) 型 B の分母'] += 1
                                if all(q[2] == 0 for q in A2):
                                    c['Z2OK'] += 1
                                else:
                                    c['Z2NG'] += 1
                                    if len(ex) < 4:
                                        ex.append((Q, d, e, n, j, p, V,
                                                   [q for q in A2 if q[2] > 0][:3]))
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    qd = c['(LOCHER-b) Q の分母']
    print(f'  (LOCHER-b) `LOC(Q)` 成立 {c["★ (LOCHER-b) LOC(Q) 成立"]} / {qd} '
          f'({100*c["★ (LOCHER-b) LOC(Q) 成立"]/max(qd,1):8.4f}%)')
    print(f'    {"n":>4s} {"★ 分母":>10s} {"★ hloc 全列":>16s} {"LOC(Q)の分母":>12s} '
          f'{"★ LOC(V) 遺伝":>16s}')
    for n in NS:
        D = c[(n, '★ 分母: 窓')]
        if not D: continue
        ld = c[(n, '(LOCHER-b) 分母: LOC(Q) 成立')]
        print(f'    {n:4d} {D:10d} {c[(n,"★ (LOCHER-a) hloc が全列で立つ")]:11d} '
              f'({100*c[(n,"★ (LOCHER-a) hloc が全列で立つ")]/D:7.4f}%) {ld:12d} '
              f'{c[(n,"★ (LOCHER-b) LOC(V) も成立")]:11d} '
              f'({100*c[(n,"★ (LOCHER-b) LOC(V) も成立")]/max(ld,1):7.4f}%)')
    print('  (LOCHER-a) 破れの srow: ', dict(sorted((k[1], c[k]) for k in c
              if isinstance(k, tuple) and k[0] == '(LOCHER-a) 破れの srow')))
    zd = c['★ (ZERO2) 型 B の分母']
    print('  ★ (ZERO2) 型 B の分母 %d   ★ A2 の行 2 が全部 0 %d (%8.4f%%)   ⛔ 行 2 > 0 がある %d'
          % (zd, c['Z2OK'], 100 * c['Z2OK'] / max(zd, 1), c['Z2NG']))
    for x in ex:
        print('      ⛔ (ZERO2) 例 Q=%s d=%d e=%d n=%d j=%d p=%s V=%s  A2 の行2>0 の列=%s' % x)
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3,5,10,20), '消費側 |R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3,5,10), '★ 消費側 |R|=4 行1<3')
