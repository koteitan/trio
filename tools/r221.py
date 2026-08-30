# -*- coding: utf-8 -*-
"""**課題 (y3') —— `HeredZ2` を末尾列の `srow` で切る。**

## 的（L3 の定義から）

```lean
def HeredZ2 : Prop :=
  ∀ (P B : TrioSeq) (j p : ℕ), j < B.length → p < j →
    hasParent (P ++ B.take (j+1)) (srow …) (…length - 1) →
    parent (P ++ B.take (j+1)) (srow …) (…length - 1) = P.length + p →
    entry (wnd P B j p) 2 0 = 0
```

窓は位置 `P.length + p`（＝親）から始まる ⟹ **`entry (wnd) 2 0 = entry B 2 p`**
（`p < j < |B|` なので添字 `P.length + p` は `B` の第 `p` 列）。

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ `srow = 2` の枝: `nextrel2` は `entry M 2 (親) < entry M 2 (末尾)` を要求（`Trio.lean:62`）。
>   `zle1` で `entry M 2 (末尾) <= 1` ⟹ **`entry M 2 (親) = 0`** ⟹ **100%、しかも恒真**。**
> **⚠ `srow <= 1` の枝: 親は行 0／行 1 で選ばれ、行 2 は縛られない ⟹ **破れる**。
>   見積もり **60〜95%**。**
> **⚠ (y3'c) 前件が `hasParent` なので **孤児枝とは排他**のはず。確かめる。**
> **⚠ (y3'e) 対照 ＝ `srow = 2`（100% のはず）と `srow <= 1`（破れるはず）の**差**。**

## 分母（`Q` 側に課したもの）

**`TowerP''` の 5 本**（`0<|Q|` / `0<d` / `0<e` / `hr0` / `hz0`）を満たす消費側の `Q`。
`P = mTower Q d e n`、`B = Lift1 (shiftr01 (d*n) 0 Q) (e*n)`、`j` は `1..|Q|-1`。
**親が `P.length + p`（`p < j`、＝同じブロックの中）の組だけが分母。**
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
                    if not (len(Q) >= 1 and d > 0 and e > 0 and hr0(Q) and Q[0][2] == 0):
                        continue
                    LQ = len(Q)
                    for n in NS:
                        P = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(1, LQ):
                            S = P + B[:j + 1]
                            last = len(S) - 1
                            i1 = srow(S, last)
                            par = trio.parent(S, i1, last)
                            c['全組 (P,B,j)'] += 1
                            if par is None:
                                c['ORPH'] += 1
                                continue
                            if par < len(P):
                                c['INTOWER'] += 1
                                continue
                            p = par - len(P)
                            if p >= j:
                                c['PGEJ'] += 1
                                continue
                            key = 'srow = %d' % i1
                            c[(key, '★ 分母')] += 1
                            z2 = B[p][2]        # ＝ entry (wnd) 2 0
                            if z2 == 0:
                                c[(key, '★ HeredZ2 成立')] += 1
                            else:
                                c[(key, '⛔ 破れ')] += 1
                                c[(key, '  親の列の行 2', z2)] += 1
                                c[(key, '  窓の長さ', min(last - par, 5))] += 1
                                if key == 'srow <= 1' and len(ex) < 5:
                                    ex.append((Q, d, e, n, j, p, i1, z2, B, S[par:last]))
    print(f'### {tag}  全組 {c["全組 (P,B,j)"]}  [{time.time()-t0:.1f}s]')
    print('    射程外: 孤児 %d   親が塔の中 %d   ⚠ p>=j %d'
          % (c['ORPH'], c['INTOWER'], c['PGEJ']))
    for key in ('srow = 0', 'srow = 1', 'srow = 2'):
        D = c[(key, '★ 分母')]
        if not D: continue
        print(f'  {key}   ★ 分母 {D}')
        print(f'      ★ HeredZ2 成立 {c[(key,"★ HeredZ2 成立")]:9d} '
              f'({100*c[(key,"★ HeredZ2 成立")]/D:8.4f}%)   '
              f'⛔ 破れ {c[(key,"⛔ 破れ")]:8d} ({100*c[(key,"⛔ 破れ")]/D:8.4f}%)')
        rows = [(k[2], c[k]) for k in c if len(k) == 3 and k[0] == key and k[1].strip() == '親の列の行 2']
        if rows: print('      (y3d) 親の列の行 2 の値: %s' % dict(sorted(rows)))
        rows2 = [(k[2], c[k]) for k in c if len(k) == 3 and k[0] == key and k[1].strip() == '窓の長さ']
        if rows2: print('      ★ 破れたときの窓の長さ（5 は 5 以上）: %s' % dict(sorted(rows2)))
    for x in ex:
        print(f'      ⛔ (y3b) 破れ例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} p={x[5]} '
              f'srow={x[6]} 親の行2={x[7]}')
        print(f'            B={x[8]}  窓={x[9]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '消費側 |R|=3 行1<3')
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), '消費側 |R|=3 行1<5')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '★ 消費側 |R|=4 行1<3')
