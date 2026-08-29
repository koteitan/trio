# -*- coding: utf-8 -*-
"""**(k2)(k3) 改: 母集団を `LiftTowerExp2`（`Wset.lean:4046`、逐語）に直して測り直す。**

⚠ h83.py は母集団を間違えていた（`TowerExpBigRow2` の `∃p∈R.dropLast, p.2.2 ≠ z` を
　誤って入れ、`argOK R` と `hQmem : Q ∈ W a` を落としていた）。教訓 25 の再発。

**`Wset.lean:4046` `LiftTowerExp2` の前提（逐語）:**

    argOK R,  R ≠ [],  z ≤ 1,  2*(v+t)+z ≤ a,
    (∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar2),  (∀ k, k < R.length → R.take k ∈ Wstar2),
    (∃ m, domT R m),  srow R (R.length-1) = 2,
    hasParent ((0,v,z) :: R) (srow R (R.length-1)) R.length

**消費側（`L105Cap.lean:5666`）が作る `Q`:**

    Q = Lift1 ((0,v,z) :: R.dropLast) t     かつ  `hQmem : Q ∈ W a`

**測るもの** —— `h2`（`L105Cap.lean:11588` 逐語）:

    ∀ j, j < Q.length → 0 < entry Q 2 j → hasParent (Q.take (j+1)) 2 j

    (k3) `z = 1` の具体的な反例
    (A)  弱めた `h2'`（`1 <= j`）でも救えるか
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, argOK, Lift1
from collections import Counter

ref = wref.Ref(maxnodes=4000)


def h2_full(Q):
    return all(has_parent(Q[:j + 1], 2, j)
               for j in range(len(Q)) if entry(Q, 2, j) > 0)


def h2_prime(Q):
    return all(has_parent(Q[:j + 1], 2, j)
               for j in range(1, len(Q)) if entry(Q, 2, j) > 0)


def main(lens=(2, 3), tmax=3, vmax=3):
    cols = [(d, b, c) for d in range(1, 3) for b in range(3) for c in range(2)]
    print('## (k2)(k3) 改: 母集団 = `LiftTowerExp2`（`Wset.lean:4046`）')
    print()
    print('列 = 行0∈[1,2]・行1<3・行2<2、`v<%d`、`z<=1`、`t<%d`、`a = 2(v+t)+z`。'
          % (vmax, tmax))
    print()
    filt = Counter()
    rows = {}
    ex3, exA = [], []
    for L in lens:
        for z in (0, 1):
            den = ok = okp = 0
            for R in itertools.product(cols, repeat=L):
                R = list(R)
                if not argOK(R):
                    filt['`argOK R` を満たさない'] += 1
                    continue
                if dom_m(R) is None:
                    filt['`∃m, domT R m` を満たさない'] += 1
                    continue
                if srow(R, len(R) - 1) != 2:
                    filt['`srow R (|R|-1) = 2` を満たさない'] += 1
                    continue
                for v in range(vmax):
                    if not has_parent([(0, v, z)] + R, 2, len(R)):
                        filt['`hasParent ((0,v,z)::R) 2 |R|` を満たさない'] += 1
                        continue
                    for t in range(tmax):
                        Q = Lift1([(0, v, z)] + R[:-1], t)
                        a = 2 * (v + t) + z
                        if ref.inW(Q, a) is not True:
                            filt['`hQmem : Q ∈ W a` を満たさない/未確定'] += 1
                            continue
                        filt['**前提を全部満たした（分母）**'] += 1
                        den += 1
                        f, p = h2_full(Q), h2_prime(Q)
                        ok += f
                        okp += p
                        if not f and z == 1 and len(ex3) < 3:
                            ex3.append((R, v, z, t, a, Q))
                        if not p and len(exA) < 4:
                            exA.append((R, v, z, t, a, Q))
            rows[(L, z)] = (den, ok, okp)
    print('| `|R|` | `z` | **分母** | `h2` 成立 | `h2` 率 | `h2\'`(`1<=j`) 成立 | `h2\'` 率 |')
    print('|--:|--:|--:|--:|--:|--:|--:|')
    for (L, z), (den, ok, okp) in sorted(rows.items()):
        print('| %d | %d | **%d** | %d | **%.1f%%** | %d | **%.1f%%** |'
              % (L, z, den, ok, 100.0 * ok / max(den, 1),
                 okp, 100.0 * okp / max(den, 1)))
    print()
    wref.tally(filt, '前提の充足（教訓 23: 分母を必ず出す）')
    print('### (k3) `z = 1` で `h2` が破れる具体例')
    print()
    if ex3:
        for R, v, z, t, a, Q in ex3:
            print('    R=`%s`  v=%d  z=%d  t=%d  a=%d' % (fmt(R), v, z, t, a))
            print('        Q = `%s`  (entry Q 2 0 = %d > 0、`hasParent (Q.take 1) 2 0` は常に偽)'
                  % (fmt(Q), entry(Q, 2, 0)))
    else:
        print('> ⚠ **`z = 1` はこの箱では 1 件も母集団に入らなかった。**')
    print()
    print('### (A) 弱めた `h2\'`（`1 <= j`）が破れる例')
    print()
    if exA:
        for R, v, z, t, a, Q in exA:
            bad = [j for j in range(1, len(Q))
                   if entry(Q, 2, j) > 0 and not has_parent(Q[:j + 1], 2, j)]
            print('    ⛔ R=`%s` v=%d z=%d t=%d a=%d Q=`%s`  破れる j = %s'
                  % (fmt(R), v, z, t, a, fmt(Q), bad))
    else:
        print('> **`h2\'` の反例ゼロ。**')
    print()


if __name__ == '__main__':
    main(lens=(2, 3), tmax=3, vmax=3)
