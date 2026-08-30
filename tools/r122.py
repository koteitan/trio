# -*- coding: utf-8 -*-
"""**課題 R120 —— `LiftTower1`（`srow = 1`）の偵察。**

⚠ 定義を `file:line` から写した（教訓 1 ＋ 2 ＋ 24）:

    `oper_eq_mTower`（`L105Cap:5228`、緑）
      `M⟦n⟧ = mTower M.dropLast (if 0 < srow … then entry M 0 (|M|-1) - entry M 0 0 else 0)
                               (**if 1 < srow … then entry M 1 (|M|-1) - entry M 1 0 else 0**) n`
    `oper`（`Trio.lean:108`）  `d1 := if 1 < i1 then … else 0`

    `LiftTower1`（`Wset:4036`）    前提に **`Aop W u0 Wstar2 R`** ＋ `srow R (|R|-1) = 1`
    `LiftTowerExp2`（`Wset:4046`） 前提に **`∀ n>=1, R⟦n⟧ ∈ Wstar2`** ＋ `srow R (|R|-1) = 2`
    ⚠ どちらも **`R ≠ []`** だけで **`2 <= |R|` は無い**

★ **測る前に書く予想**（team-lead の読みの検算を含む）:

  (t1) **`srow = 1` ⟹ `1 < 1` は偽 ⟹ `e = 0`。定義から即座**（測定不要。検算だけ）
  (t2) `e = 0` ⟹ ブロック `k` は `Lift1 (shiftr01 (d*k) 0 Q) 0 = shiftr01 (d*k) 0 Q`
       ⟹ 根は `(Q[0].0 + d*k, Q[0].1, Q[0].2)` ⟹ **`lev` は `k` に依らず `lev Q 0`。定義から即座**
  (t3) ⚠ **team-lead の「`Aop` のほうが強い前提」は逆**のはず。
       `Aop = 節1 ∨ 節2 ∨ 節3` なので **節2 ⟹ `Aop`** ⟹ **`Aop` は弱い前提** ⟹
       **`LiftTower1` のほうが強い主張**（証明が難しい側）。
       ただし **§R98 より `domT` ＋ `|R|>=2` では 節3 ⟹ 節2**（`y := []`）で、
       **節1 は場面で常に偽**（`domT` より `lev R (|R|-1) > 0`）
       ⟹ **`|R| >= 2` では `Aop` ⟺ 節2。差は `|R| = 1` だけ**のはず。
  **反例の形**: 「`srow=1` なのに `e ≠ 0`」／「ブロック根の `lev` が `k` で動く」／
              「場面で節 1 が成り立つ」／「`|R|>=2` で 節3 が成り立つのに節2 が成り立たない」

**箱**: 行0∈[1,3]×行1∈[0,3]×**行2∈[0,cmax]**（`cmax`=1,2,3）、`v∈[0,2]`、`z∈[0,1]`、`t∈[0,2]`。
**母集団**: `LiftTower1` の場面 ＝ `argOK R` ∧ `R≠[]` ∧ `z<=1` ∧ `domT R m` ∧
`srow R (|R|-1)=1` ∧ `hasParent ((0,v,z)::R) 1 |R|`。**単位**: `(R,v,z,t)` の事例。
`|R|<=3` 全数、4 は 10 万文脈の標本。⚠ `Wstar2` 所属は判定しない（有限では不可、R94）。
"""
import sys, itertools, random, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r98 import oper_lean


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def Lift1(X, d):
    return [(c[0], c[1] + (d if trio.is_ancestor(X, 1, 0, i) else 0), c[2])
            for i, c in enumerate(X)]


def params(M):
    """`oper_eq_mTower` の `(d0, e)` を定義どおり計算。"""
    j1 = len(M) - 1
    i1 = srow(M, j1)
    d0 = (M[j1][0] - M[0][0]) if i1 > 0 else 0
    e = (M[j1][1] - M[0][1]) if i1 > 1 else 0
    return d0, e, i1


def run(cmax, Ls, want_srow, label, sample_from=4, sample=100000):
    rng = random.Random(20260830)
    COL = [(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2, 3)
           for c in range(cmax + 1)]
    c = Counter(); ex = {}
    for L in Ls:
        smp = sample if L >= sample_from else None
        src = ([rng.choice(COL) for _ in range(L)] for _ in range(smp)) if smp \
            else (list(x) for x in itertools.product(COL, repeat=L))
        for R in src:
            R = list(R)
            if any(p[0] < 1 for p in R):
                continue
            jR = len(R) - 1
            iR = srow(R, jR)
            if iR != want_srow:
                continue
            if trio.parent(R, iR, jR) is not None or lev(R[jR]) - 1 < 0:
                continue                                   # domT
            for v in (0, 1, 2):
                for z in (0, 1):
                    if trio.parent([(0, v, z)] + R, iR, len(R)) is None:
                        continue
                    for t in (0, 1, 2):
                        X = Lift1([(0, v, z)] + R, t)
                        c['分母'] += 1
                        jX = len(X) - 1
                        if trio.parent(X, srow(X, jX), jX) != 0:
                            c['**悪根が根でない（mTower の前提外）**'] += 1
                            continue
                        d0, e, i1 = params(X)
                        c[f'srow(X)={i1}'] += 1
                        # (t1)
                        c['(t1) e=0' if e == 0 else f'**(t1) e={e}（予想外）**'] += 1
                        if want_srow == 1 and e != 0:
                            ex.setdefault('t1 破れ', (R, v, z, t, e))
                        # (t2) ブロック根の lev が k に依らないか
                        Q = X[:-1]
                        levs = {lev((Q[0][0] + d0 * k, Q[0][1] + e * k, Q[0][2]))
                                for k in range(4)}
                        c['(t2) ブロック根の lev が一定' if len(levs) == 1
                          else f'**(t2) lev が動く（{len(levs)} 通り）**'] += 1
                        if len(levs) > 1 and want_srow == 1:
                            ex.setdefault('t2 破れ', (R, v, z, t, sorted(levs)))
                        # (t3) 節 1 が場面で成り立つか
                        c['**(t3) 節 1 が成立（予想外）**' if (len(R) <= 1 and lev(R[0]) == 0)
                          else '(t3) 節 1 は偽'] += 1
                        # (t3) |R|>=2 で 節3 ⟹ 節2（`graft R [] = R.dropLast = R⟦n⟧`）
                        if len(R) >= 2:
                            gl = [tuple(x) for x in R[:-1]]
                            ok = all(oper_lean(R, n) == gl for n in (1, 2, 3))
                            c['(t3) |R|>=2: graft R [] = R⟦n⟧ = R.dropLast/' +
                              ('ok' if ok else '**破れる**')] += 1
                            if not ok:
                                ex.setdefault('t3 破れ', (R, v, z, t))
                        else:
                            c['(t3) |R|=1（節3 ⟹ 節2 が言えない側）'] += 1
    print(f'### {label}')
    n = c['分母']
    for k in sorted(c, key=str):
        if k == '分母':
            continue
        print(f'  {k:46s} {c[k]:9d}  ({100*c[k]/max(n,1):5.2f}%)')
    print(f'  分母 {n}')
    for k in sorted(ex):
        print(f'  ★ {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    Ls = tuple(range(1, a.L + 1))
    for cm in (1, 3):
        run(cm, Ls, 1, f'R120 `srow=1`（`LiftTower1`）箱 行2<={cm}')
    run(3, Ls, 2, 'R120 **対照** `srow=2`（`LiftTowerExp2`）箱 行2<=3')
