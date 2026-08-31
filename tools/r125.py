# -*- coding: utf-8 -*-
"""**課題 R124 —— `oper_mTower` を「`d,e` が `R` から決まる形」にして `hblk` を落とせるか。**

⚠ **これは列の等式なので、私の計器で壊せる**（`MTowerClosedS` の `W` 所属とは違う。§R94/§R95）。

決め打ちの形（`oper_eq_mTower`（`L105Cap:5228`）の `d0,d1` を `M := X` で展開した）:

    `X = (0,v,z) :: R`
    **`d = entry X 0 (|X|-1) - entry X 0 0 = entry R 0 (|R|-1)`**
    **`e = entry X 1 (|X|-1) - entry X 1 0 = entry R 1 (|R|-1) - v`**（`srow X (|X|-1) > 1` のとき。他は 0）
    `Q = X.dropLast = (0,v,z) :: R.dropLast`

    結論（`oper_mTower`、`L105Cap:5360`）:
      **`(mTower Q d e (n+1))⟦m⟧ = mTower Q d e n ++ (Lift1 (shiftr01 (d*n) 0 Q) (e*n))⟦m⟧`**

    前提のうち **`hblk : HasParentInBlock Q` を落とす。**

★ **測る前に書く（教訓 45）。反例の形**: 「`hblk` を落とすと等式が破れる `R`」。
  **予想**: §R129 で塔の場面（`argOK` ∧ `domT` ∧ `srow=2` ∧ `hasParent X`）では
  506,889 件・破れ 0 だった。⟹ **場面の条件をどこまで削ると壊れるか**を階段で測る。
  **`d,e` が `R` から決まるだけでは足りず、`argOK` か `domT` が要る**のではないか。

**前提の階段**（上から順に弱める。**単位** `(R,v,z,n,m)` の事例、**全数**）:

    (A) `argOK R` ∧ `domT R m` ∧ `srow R (|R|-1) = 2` ∧ `hasParent X …`   ← 塔の場面（§R129）
    (B) (A) から **`srow = 2`** を落とす（`srow = 1` も許す）
    (C) (B) から **`hasParent X`** を落とす
    (D) (C) から **`domT R m`** を落とす
    (E) (D) から **`argOK R`** を落とす（＝ `d,e` が `R` から決まるだけ）
"""
import sys, itertools, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r113 import Lift1, sh, mTower
from r98 import oper_lean


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def hasP(N):
    if len(N) < 2:
        return False
    j = len(N) - 1
    return trio.parent(N, srow(N, j), j) is not None


def run(COL, Ls, VS, ZS, NS, MS, label):
    c = Counter(); ex = {}
    for L in Ls:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            argok = all(p[0] >= 1 for p in R)
            jR = len(R) - 1
            iR = srow(R, jR)
            domt = (trio.parent(R, iR, jR) is None) and lev(R[jR]) >= 1
            for v in VS:
                for z in ZS:
                    X = [(0, v, z)] + R
                    jX = len(X) - 1
                    iX = srow(X, jX)
                    hpX = trio.parent(X, iX, jX) is not None
                    j0 = trio.parent(X, iX, jX)
                    # `oper_eq_mTower` は `parent = 0` が前提。そこは外せない
                    if j0 != 0:
                        continue
                    d = (X[jX][0] - X[0][0]) if iX > 0 else 0
                    e = (X[jX][1] - X[0][1]) if iX > 1 else 0
                    Q = X[:-1]
                    if len(Q) < 2:
                        continue
                    hb = hasP(Q)
                    if hb:
                        continue                     # `hblk` を落とした側だけ見る
                    tiers = []
                    if argok and domt and iR == 2 and hpX:
                        tiers.append('(A) 塔の場面')
                    if argok and domt and hpX:
                        tiers.append('(B) srow を外す')
                    if argok and domt:
                        tiers.append('(C) hasParent X を外す')
                    if argok:
                        tiers.append('(D) domT を外す')
                    tiers.append('(E) argOK も外す')
                    for n in NS:
                        for m in MS:
                            lhs = oper_lean(mTower(Q, d, e, n + 1), m)
                            rhs = ([tuple(x) for x in mTower(Q, d, e, n)]
                                   + oper_lean(Lift1(sh(Q, d * n), e * n), m))
                            ok = (lhs == rhs)
                            for t in tiers:
                                c[(t, 'ok' if ok else '**破れる**')] += 1
                                if not ok:
                                    ex.setdefault(t, (R, v, z, d, e, n, m))
    print(f'### {label}')
    for t in ('(A) 塔の場面', '(B) srow を外す', '(C) hasParent X を外す',
              '(D) domT を外す', '(E) argOK も外す'):
        o = c[(t, 'ok')]; b = c[(t, '**破れる**')]
        if o + b:
            print(f'  {t:22s} 分母 {o+b:9d}  ok {o:9d}  **破れる {b:8d}**  '
                  f'({100*b/(o+b):5.2f}%)')
    for k in sorted(ex):
        print(f'  ★ {k} の最小反例: R={ex[k][0]} v={ex[k][1]} z={ex[k][2]} '
              f'd={ex[k][3]} e={ex[k][4]} n={ex[k][5]} m={ex[k][6]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=3)
    a = ap.parse_args()
    for cm in (1, 2, 3):
        run([(d, b, cc) for d in (0, 1, 2) for b in (0, 1, 2)
             for cc in range(cm + 1)],
            tuple(range(2, a.L + 1)), (0, 1, 2), (0, 1), (1, 2), (1, 2),
            f'R124 `hblk` を落とした版（`d,e` は `R` から決め打ち）箱 行2<={cm}')
