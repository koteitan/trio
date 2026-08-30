# -*- coding: utf-8 -*-
"""**課題 R119 —— 私の (s1) の分岐と L3 の (A)(B)(C) は同じ分割か。**

L3 の §67（team-lead 経由）:

    (A) `¬ hasParent X (srow X (|X|-1)) (|X|-1)`            ⟹ 可換（`lift_oper_of_noParent`）
    (B) `hasParent R (srow R (|R|-1)) (|R|-1)`               ⟹ 可換（`Lcone.liftInner_holds`）
    (C) どちらでもない（＝ 悪根が根）                          ⟹ **残差**

私の (s1)（`X = (0,v,z) :: R` の `oper` の分岐）:

    `noparent` ／ 塔（`j0 = 0`）／ cons 保存（`j0 >= 1`）

★ **測る前に書く予想**: 一致するはず。
    (A) ＝ `noparent`（`hasParent X` の否定そのもの）
    (B) ＝ cons 保存（`nextR_cons_last` で `hasParent X` の親 `>= 1` ⟺ `hasParent R`）
    (C) ＝ 塔（`hasParent X` かつ親が 0）
  **反例の形**: 「(A) かつ (B)」（両立するなら排他でない）／「どれでもない」（網羅でない）。
  **両方の件数を数える。**

⚠ team-lead の暗算「`srow=0` の 19.58% は `snoc_flat_root` で無料」について:
  **`Wtower2.snoc_flat_root` の主語は `C ++ [p]`（末尾に 1 列足す形）**であって
  **`(0,v,z) :: R`（先頭に 1 列足す形）ではない**。⟹ **そのまま当たるかは自明でない。**
  §R89-6 で確かめた `srow=0` の無料の根拠は
  **`W_flatMap_copies`（`Wset:2551`）＋ `rsum_self_cons`（`:2539`）**のほう。**そちらで数える。**

**箱** 2 つ（行 2 の軸）／**母集団** `argOK R` ∧ `∃p∈R, p.2.1=0`（`LiftTieCore` の `v=0` 場面）
／**単位** `(R,z)` の事例／`|R|<=3` 全数、4,5 は 12 万文脈の標本
／⚠ `X ∈ W z` は落とした**上位集合**。**所属の判定はしない。**
"""
import sys, itertools, random, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def run(COL, Ls, label, sample_from=4, sample=120000):
    rng = random.Random(20260830)
    c = Counter(); ex = {}
    for L in Ls:
        smp = sample if L >= sample_from else None
        src = ([rng.choice(COL) for _ in range(L)] for _ in range(smp)) if smp \
            else (list(x) for x in itertools.product(COL, repeat=L))
        for R in src:
            R = list(R)
            if any(p[0] < 1 for p in R):
                continue
            if not any(p[1] == 0 for p in R):
                continue
            jR = len(R) - 1
            iR = srow(R, jR)
            hasP_R = trio.parent(R, iR, jR) is not None
            for z in (0, 1):
                X = [(0, 0, z)] + R
                jX = len(X) - 1
                iX = srow(X, jX)
                pX = trio.parent(X, iX, jX)
                mine = ('noparent' if pX is None
                        else '塔 (j0=0)' if pX == 0 else 'cons 保存 (j0>=1)')
                l3 = ('(A) ¬hasParent X' if pX is None
                      else '(B) hasParent R' if hasP_R else '(C) 残差')
                c[(L, '分母')] += 1
                c[(L, mine)] += 1
                c[(L, l3)] += 1
                pair = {'noparent': '(A) ¬hasParent X',
                        'cons 保存 (j0>=1)': '(B) hasParent R',
                        '塔 (j0=0)': '(C) 残差'}[mine]
                c[(L, '★ 一致' if pair == l3 else f'**不一致 {mine}/{l3}**')] += 1
                if pair != l3:
                    ex.setdefault(f'不一致 {mine}/{l3}', (R, z))
                # 排他性・網羅性の検査（反例の形）
                if pX is None and hasP_R:
                    c[(L, '**(A) かつ (B)（排他でない）**')] += 1
                    ex.setdefault('A∧B', (R, z))
                # (C) の中の srow 別（srow=0 は W_flatMap_copies で無料）
                if l3 == '(C) 残差':
                    c[(L, f'  (C) srow={iX}')] += 1
    print(f'### {label}')
    for L in sorted({k[0] for k in c}):
        den = c[(L, '分母')]
        print(f'  -- |R|={L}（分母 {den}） --')
        for k in sorted({k[1] for k in c if k[0] == L}, key=str):
            if k == '分母':
                continue
            print(f'     {k:34s} {c[(L, k)]:9d}  ({100*c[(L, k)]/den:5.2f}%)')
        cs = sum(c[(L, f'  (C) srow={i}')] for i in (0, 1, 2))
        if cs:
            res = c[(L, '  (C) srow=1')] + c[(L, '  (C) srow=2')]
            print(f'     ★ **残差（(C) から srow=0 を除く）** {res:9d}  '
                  f'({100*res/den:5.2f}% of 分母)')
    for k in sorted(ex):
        print(f'  ★ {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=5)
    a = ap.parse_args()
    run([(d, b, c) for d in (1, 2) for b in (0, 1, 2) for c in (0, 1)],
        tuple(range(2, a.L + 1)), 'R119 (a) 箱 行2<=1')
    run([(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2, 3) for c in (0, 1, 2)],
        (2, 3, 4), 'R119 (b) 箱 **行2<=2**')
