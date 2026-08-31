# -*- coding: utf-8 -*-
"""**課題 (o1)（team-lead の依頼）—— 「ずれ 2」＝ `Lift1` と `oper` の可換の射程。**

## `LiftInner` の逐語（`Wset.lean:4028`）

    **`def LiftInner : Prop :=`**
    **`  ∀ (v z t n : ℕ) (R : TrioSeq), argOK R → R ≠ [] →`**
    **`    hasParent R (srow R (R.length - 1)) (R.length - 1) →`**
    **`    (Lift1 ((0,v,z) :: R) t)⟦n⟧ = Lift1 (((0,v,z) :: R)⟦n⟧) t`**

⟹ **「悪根が内側」＝ `hasParent R (srow R (|R|-1)) (|R|-1)` ＝ `HasParentInBlock R`。**
⟹ **`argOK R`（全列の行 0 が 1 以上）も前提。**

## ★ 予想を先に書く（教訓 45）＋ 見積もり

**(o1a)** §R132 で「ブロック内で孤児」は 51.8 〜 70.8% だった ⟹ **`HasParentInBlock R` は 29 〜 48%。**
> **⚠ 見積もり 30 〜 50%。**

**(o1c) ★ 本命**: **条件が破れても等式が成り立つのでは。**
`Lift1` は行 1 だけを動かし、`oper` の `d1` は `srow` で決まる。
> **⚠ 見積もり: 条件が破れても 50 〜 80% で等式は成立。**
> **⟹ そうなら `LiftInner` は前提を弱められる ＝ 「ずれ 2」は小さい。**

**箱と単位**: 単位 `(R, v, z, t, n)`。箱 = `R` の列は 行0 ∈ 1..3（`argOK`）、行1<3、行2<=1、
`|R| = 2..4`、`v ∈ 0..2`、`z ∈ {0,1}`、`t ∈ 0..2`、`n ∈ 1..6`。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r163 import Lift1
from r98 import oper_lean


def hasPB(R):
    j = len(R) - 1
    return trio.parent(R, srow(R, j), j) is not None


def run(L, VS, ZS, TS, NS, R1, cm):
    COL = [(a, b, c) for a in range(1, 4) for b in range(R1) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        inner = hasPB(R)
        c[('(o1a) 悪根が内側', inner)] += 1
        # (o1b) 内側でないとき、`(0,v,z)::R` の悪根はどこか
        for v in VS:
            for z in ZS:
                M = [(0, v, z)] + R
                jM = len(M) - 1
                pM = trio.parent(M, srow(M, jM), jM)
                if not inner:
                    c[('(o1b) M の悪根', '孤児' if pM is None else
                       ('根' if pM == 0 else '内側'))] += 1
                for t in TS:
                    for n in NS:
                        lhs = oper_lean(Lift1(M, t), n)
                        rhs = Lift1([tuple(x) for x in oper_lean(M, n)], t)
                        ok = (lhs == rhs)
                        c[('★ 等式', inner, ok)] += 1
                        c[('(o1c) n 別', n, inner, ok)] += 1
                        if not ok:
                            ex.setdefault(inner, (R, v, z, t, n))
    ia = c[('(o1a) 悪根が内側', True)]; ib = c[('(o1a) 悪根が内側', False)]
    print(f'### |R|={L} 行1<{R1} 行2<={cm}  `R` {ia+ib} 本  [{time.time()-t0:.1f}s]')
    print(f'  **(o1a) 悪根が内側（`HasParentInBlock R`）… {ia} / {ia+ib} ({100*ia/(ia+ib):6.2f}%)**')
    print('  **(o1b) 内側でないときの `M` の悪根**: ', dict(sorted((k[1], c[k]) for k in c
                                                    if isinstance(k, tuple) and k[0] == '(o1b) M の悪根')))
    for inner in (True, False):
        y = c[('★ 等式', inner, True)]; nn = c[('★ 等式', inner, False)]
        if y + nn:
            lab = '★ 内側（`LiftInner` の射程）' if inner else '⚠ 内側でない（射程外）'
            print(f'  **{lab}: 等式成立 {y:9d} / {y+nn} ({100*y/(y+nn):6.2f}%)**  破れ {nn}')
    print('  **(o1c) `n` 別（射程外のみ）**: ', {n: (c[('(o1c) n 別', n, False, True)],
                                             c[('(o1c) n 別', n, False, True)] + c[('(o1c) n 別', n, False, False)])
                                           for n in NS})
    for k in sorted(ex, key=str):
        print(f'      破れの例（内側={k}）: R={ex[k][0]} v={ex[k][1]} z={ex[k][2]} '
              f't={ex[k][3]} n={ex[k][4]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for L in range(2, a.L + 1):
        run(L, (0, 1, 2), (0, 1), (0, 1, 2), (1, 2, 3, 4, 5, 6), 3, 1)
