# -*- coding: utf-8 -*-
"""**R120 —— `oper_mTower`（`L105Cap.lean:5360`、緑）の前提が塔の場面で成り立つ割合。**

⚠ 教訓 24（先に `grep`）: **L3 が「測るなら」と挙げた
「`operTower` の展開が最後のブロックだけを削る形か」は、既に緑の定理**だった:

    `oper_mTower` （`L105Cap.lean:5360`）前提を `file:line` から写した:
      `hQne : Q ≠ []` ∧ **`hQ2 : |Q| - 1 ≠ 0`（＝ `|Q| >= 2`）** ∧
      **`hlev : lev Q (|Q|-1) ≠ 0`** ∧ **`hblk : L53.HasParentInBlock Q`**
      結論 `(mTower Q d e (n+1))⟦m⟧ = mTower Q d e n ++ (Lift1 (shiftr01 (d*n) 0 Q) (e*n))⟦m⟧`

    `L53.HasParentInBlock N`（`L53Subst.lean:913`）＝ `hasParent N (srow N (|N|-1)) (|N|-1)`

⟹ **測る価値があるのは「定理の内容」ではなく「前提が場面でどれだけ成り立つか」。**

★ **測る前に書く予想**: `Q = (0,v,z) :: R.dropLast` の最終列は `R` の**最後から 2 番目**の列。
  `domT R` が言うのは **`R` の最終列**が孤児だということで、**`Q` の最終列については何も言わない**。
  ⟹ **`HasParentInBlock Q` は自動ではないはず。** 割合を測る。
  **反例の形 ＝「`Q` の最終列が孤児」。その件数を数える。**

⚠ `HasParentInBlock` は `srow` を通じて**行 2 に直接依存する**（`srow=2 ⟺ 行2>0`）
  ⟹ **私の教訓 4 より行 2 の軸を 3 段振る。**

**箱**: 行0∈[1,3]×行1∈[0,3]×**行2∈[0,cmax]**（`cmax`=1,2,3）、`v∈[0,2]`、`z∈[0,1]`。
**母集団**: 塔の場面 ＝ `argOK R` ∧ `2<=|R|` ∧ `domT R m` ∧ `srow R (|R|-1)=2` ∧
`hasParent ((0,v,z)::R) 2 |R|`。**単位**: `(R,v,z)` の事例。
`|R|<=3` 全数、4,5 は 12 万文脈の標本。⚠ `R.dropLast ∈ Wstar` は落とした**上位集合**。
"""
import sys, itertools, random, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def hasParentInBlock(N):
    if len(N) < 2:
        return False
    j = len(N) - 1
    return trio.parent(N, srow(N, j), j) is not None


def run(cmax, Ls, sample_from=4, sample=120000):
    rng = random.Random(20260830)
    COL = [(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2, 3)
           for c in range(cmax + 1)]
    print(f'  -- 列の行 2 <= {cmax}（列数 {len(COL)}） --')
    for L in Ls:
        smp = sample if L >= sample_from else None
        src = ([rng.choice(COL) for _ in range(L)] for _ in range(smp)) if smp \
            else (list(x) for x in itertools.product(COL, repeat=L))
        c = Counter(); ex = {}
        for R in src:
            R = list(R)
            if any(p[0] < 1 for p in R):
                continue
            j = len(R) - 1
            i1 = srow(R, j)
            if i1 != 2 or trio.parent(R, i1, j) is not None or lev(R[j]) - 1 < 0:
                continue
            for v in (0, 1, 2):
                for z in (0, 1):
                    if trio.parent([(0, v, z)] + R, i1, len(R)) is None:
                        continue
                    Q = [(0, v, z)] + R[:-1]
                    c['分母'] += 1
                    c['hQ2 (|Q|>=2)' if len(Q) >= 2 else '**hQ2 破れ**'] += 1
                    c['hlev (lev≠0)' if lev(Q[-1]) != 0 else '**hlev 破れ**'] += 1
                    hb = hasParentInBlock(Q)
                    c['**hblk (HasParentInBlock Q)**' if hb
                      else '**hblk 破れ（Q の最終列が孤児）**'] += 1
                    if len(Q) >= 2 and lev(Q[-1]) != 0 and hb:
                        c['★ 前提が全部成り立つ'] += 1
                    if not hb:
                        ex.setdefault('hblk 破れ', (R, v, z, Q))
        n = c['分母']
        if not n:
            continue
        tag = '' if smp is None else '*'
        print(f'     |R|={L}{tag} 分母 {n:8d}: '
              f'**前提が全部成り立つ {100*c["★ 前提が全部成り立つ"]/n:5.2f}%**   '
              f'(hblk {100*c["**hblk (HasParentInBlock Q)**"]/n:5.2f}% / '
              f'hlev {100*c["hlev (lev≠0)"]/n:5.2f}% / '
              f'hQ2 {100*c["hQ2 (|Q|>=2)"]/n:5.2f}%)')
        for k in sorted(ex):
            print(f'        ex {k}: {ex[k]}')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=5)
    a = ap.parse_args()
    print('### R120 `oper_mTower`（緑）の前提が塔の場面で成り立つ割合')
    print('  ⚠ L3 が「測るなら」と挙げたものは既に緑の定理（教訓 24 で `grep` して発見）')
    print('  ⟹ 代わりに**前提の成立率**を測る。単位: (R,v,z) の事例')
    for cmax in (1, 2, 3):
        run(cmax, tuple(range(2, a.L + 1)))
