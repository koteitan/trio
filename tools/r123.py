# -*- coding: utf-8 -*-
"""**課題 R121 —— `hblk` が破れる 3〜4 割は本当に「無料」か。**

⚠ **前提を `file:line` から写した（教訓 1・2・25）。主語が違う:**

    `L53.HasParentInBlock N`（`L53Subst:913`）  ＝ `hasParent N (srow N (|N|-1)) (|N|-1)`
    `Wtower2.lift_oper_of_noParent`（`:525`）
      前提 `2 <= |X|` ∧ **`¬ hasParent X (srow X (|X|-1)) (|X|-1)`**
      結論 `(Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d`

⚠ **`hblk` は `Q = (0,v,z) :: R.dropLast` についての条件。
   塔の場面の主語は `X = (0,v,z) :: R`（`Q` はその `dropLast`）。**
⟹ **team-lead の「`hblk` 破れ ⟹ `lift_oper_of_noParent` が当たる」は主語が違う可能性がある。**

★ **測る前に書く予想（「はい」に寄せない）**:

  **`hasParent X (srow X (|X|-1)) (|X|-1)` は塔の場面の前提そのもの ⟹ 常に真。**
  ⟹ **`lift_oper_of_noParent` を `X` に当てることはできない**（前提が偽）。
  ⟹ **(u1) の答えは「いいえ」になるはず。**
  ★ ただし別の逃げ道: `hblk` 破れ ＝ `Q` の最終列が孤児。
    `Lift1`・`shiftr01` は `hasParent` を保つ（`hasParent_Lift1` が `lift_oper_of_noParent` の
    証明中で使われている）⟹ **`mTower Q d e n` の最終列も孤児**かもしれない
    ⟹ そのとき `(mTower …)⟦m⟧ = Pred (mTower …)` ＝ 末尾を落とすだけ ＝ **別の意味で無料**
  **⟹ (u1) は 2 通りに分けて測る。反例の形は「`mTower` の最終列に親がある」。**

**箱** 行0∈[1,3]×行1∈[0,3]×**行2∈[0,cmax]**（`cmax`=1,2,3。**3 段**）、`v∈[0,2]`、`z∈[0,1]`
／**母集団** 塔の場面（`argOK R` ∧ `2<=|R|` ∧ `domT R m` ∧ `srow R (|R|-1)=2` ∧ `hasParent`）
の中で **`hblk` が破れるもの**／**単位** 事例／`|R|<=3` 全数、4 は 10 万文脈の標本
／⚠ 所属の判定はしない。
"""
import sys, itertools, random, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r113 import Lift1, sh, mTower


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def hasP(N):
    if len(N) < 2:
        return False
    j = len(N) - 1
    return trio.parent(N, srow(N, j), j) is not None


def run(cmax, Ls, sample_from=4, sample=100000):
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
            if iR != 2 or trio.parent(R, iR, jR) is not None or lev(R[jR]) - 1 < 0:
                continue
            for v in (0, 1, 2):
                for z in (0, 1):
                    X = [(0, v, z)] + R
                    if trio.parent(X, iR, len(R)) is None:
                        continue
                    Q = X[:-1]
                    if hasP(Q):
                        continue                       # `hblk` が成り立つ側は対象外
                    c['分母（hblk 破れ）'] += 1
                    # (u1a) `lift_oper_of_noParent` を X に当てられるか
                    c['(u1a) `¬hasParent X` が成立（当てられる）' if not hasP(X)
                      else '**(u1a) `hasParent X` が成立 ⟹ 当てられない**'] += 1
                    # (u1b) mTower の最終列は孤児か（⟹ oper が Pred で無料）
                    jX = len(X) - 1
                    d0 = X[jX][0] - X[0][0]
                    e = X[jX][1] - X[0][1] if srow(X, jX) > 1 else 0
                    for n in (2, 3):
                        T = mTower(Q, d0, e, n)
                        if len(T) < 2:
                            continue
                        orph = not hasP(T)
                        c[f'(u1b) n={n}: mTower の最終列が孤児（⟹ Pred で無料）' if orph
                          else f'**(u1b) n={n}: mTower の最終列に親がある（残差）**'] += 1
                        if not orph:
                            ex.setdefault(f'残差 n={n}', (R, v, z, T[-3:]))
                    # (u3) hlev 破れ（lev Q (|Q|-1) = 0）の側
                    if lev(Q[-1]) == 0:
                        c['(u3) hlev も破れる（lev Q = 0 ⟹ srow Q = 0）'] += 1
    n = c['分母（hblk 破れ）']
    print(f'  -- 列の行 2 <= {cmax}（分母 {n}） --')
    for k in sorted(c, key=str):
        if k.startswith('分母'):
            continue
        print(f'     {k:52s} {c[k]:9d}')
    for k in sorted(ex):
        print(f'     ★ {k}: {ex[k]}')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    print('### R121 `hblk` 破れの 3〜4 割は無料か（「はい」に寄せない）')
    for cm in (1, 2, 3):
        run(cm, tuple(range(2, a.L + 1)))
