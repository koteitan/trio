# -*- coding: utf-8 -*-
"""**課題 R112 —— (δ) を `v = 0` と `v >= 1` で割る。**

H12 が前提を写して見つけた点:
`L53.liftTie_case_tieFree`（`L53Subst.lean:2615`）は **`1 <= entry X 1 0`（＝ `v >= 1`）** を要求。
⟹ `v = 0` では (β) が使えない。

★ **紙の上での予想（測る前に書く）**:

    `v = 0` では **ブロッカー（行 1 <= 0）⟺ 行 1 = 0 ⟺ タイ（行 1 = v）**
    ⟹ **`v=0` では「ブロッカーあり」と「タイあり」が同値。**
    ⟹ (α)（ブロッカーが全部 `< v`）は **`v=0` では起こりえない**（行 1 < 0 は無い）
    ⟹ (β) も `v>=1` を要求 ⟹ 使えない
    ⟹ (γ) は構造的に空虚（H12 ＋ 私の §R111）
    ⟹ **`v = 0` では「ブロッカーあり」がそのまま (δ)。無料の枝が 1 本も無い。**

  (w1) (δ) を `v=0` / `v>=1` で割った割合
  (w2) `v=0` のとき根は `(0,0,z)`、`lev = z <= 1`。段の状況を出す
  (w3) `v=0` のタイ（行 1 = 0 の列）の割合
"""
import sys, itertools, random, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r111 import srow, lev, classify, tiefree

KEYS = ['0 ブロッカー無（一様シフト ⟹ W_shift で無料）',
        '(α) タイ無し（liftStage_of_noTie）',
        '(β) タイ ∧ TieFree（liftTie_case_tieFree）',
        '(γ) 行 2 ≡ 0（liftStage_of_zeroRow2）',
        '(δ) **LiftTieCore ← 本当の残核**']


def run(COL, VS, ZS, Ls, label, sample_from=5):
    rng = random.Random(20260830)
    print(f'### {label}')
    print(f'  {"|R|":>4s} {"分母":>9s} | {"v=0 の分母":>10s} {"v=0 の(δ)":>10s} {"率":>7s}'
          f' | {"v>=1 の分母":>11s} {"v>=1 の(δ)":>11s} {"率":>7s}'
          f' | {"(δ) 全体":>9s} {"うち v=0":>9s}')
    for L in Ls:
        smp = 300000 if L >= sample_from else None
        src = ([rng.choice(COL) for _ in range(L)] for _ in range(smp)) if smp \
            else (list(x) for x in itertools.product(COL, repeat=L))
        c = Counter()
        for R in src:
            if any(p[0] < 1 for p in R):
                continue
            j = len(R) - 1
            i1 = srow(R, j)
            if i1 != 2 or trio.parent(R, i1, j) is not None or lev(R[j]) - 1 < 0:
                continue
            for v in VS:
                for z in ZS:
                    if trio.parent([(0, v, z)] + R, i1, len(R)) is None:
                        continue
                    if not any(p[2] != z for p in R[:-1]):
                        continue
                    g = 'v=0' if v == 0 else 'v>=1'
                    c[(g, 'n')] += 1
                    B = [(0, v, z)] + R[:-1]
                    k = classify(B, v)
                    c[(g, k)] += 1
                    # 予想の検算（v=0 でブロッカー ⟺ タイ）
                    if v == 0:
                        blk = any(p[1] <= 0 for p in R[:-1])
                        tie = any(p[1] == 0 for p in R[:-1])
                        c[('v=0', 'ブロッカー⟺タイ/' +
                           ('ok' if blk == tie else '**破れる**'))] += 1
                        if blk:
                            c[('v=0', 'ブロッカーあり')] += 1
        n0, n1 = c[('v=0', 'n')], c[('v>=1', 'n')]
        d0, d1 = c[('v=0', KEYS[4])], c[('v>=1', KEYS[4])]
        tot = n0 + n1
        if tot == 0:
            continue
        tag = '' if smp is None else '*'
        print(f'  {str(L)+tag:>4s} {tot:9d} | {n0:10d} {d0:10d} '
              f'{100*d0/max(n0,1):6.2f}% | {n1:11d} {d1:11d} '
              f'{100*d1/max(n1,1):6.2f}% | {d0+d1:9d} '
              f'**{100*d0/max(d0+d1,1):7.2f}%**')
    print('  （* は 30 万文脈の標本。最右列は「(δ) のうち `v=0` が占める割合」）')
    print()


def detail(COL, VS, ZS, L, label):
    """`v=0` の内訳と予想の検算。"""
    c = Counter()
    for R in itertools.product(COL, repeat=L):
        R = list(R)
        if any(p[0] < 1 for p in R):
            continue
        j = len(R) - 1
        i1 = srow(R, j)
        if i1 != 2 or trio.parent(R, i1, j) is not None or lev(R[j]) - 1 < 0:
            continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, i1, len(R)) is None:
                    continue
                if not any(p[2] != z for p in R[:-1]):
                    continue
                B = [(0, v, z)] + R[:-1]
                k = classify(B, v)
                c[('v=0' if v == 0 else 'v>=1', k)] += 1
                if v == 0:
                    blk = any(p[1] <= 0 for p in R[:-1])
                    tie = any(p[1] == 0 for p in R[:-1])
                    c[('検算', 'ブロッカー⟺タイ/' +
                       ('ok' if blk == tie else '**破れる**'))] += 1
                    c[('検算', f'根の lev = z = {z}（段 a >= {z}）')] += 1
    print(f'### {label}（`|R|={L}` の全数、内訳）')
    for g in ('v=0', 'v>=1', '検算'):
        sub = {k: n for (gg, k), n in c.items() if gg == g}
        s = sum(sub.values())
        if not s:
            continue
        print(f'  -- {g}（{s} 件） --')
        for k in sorted(sub):
            print(f'     {k:44s} {sub[k]:9d}  ({100*sub[k]/s:5.2f}%)')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=6)
    a = ap.parse_args()
    H12 = [(d, b, c) for d in (1, 2) for b in (0, 1, 2) for c in (0, 1)]
    R2 = [(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2, 3) for c in (0, 1)]
    run(H12, (0, 1, 2), (0, 1), tuple(range(2, a.L + 1)), '**H12 の箱**')
    run(R2, (0, 1, 2, 3), (0, 1), tuple(range(2, a.L + 1)), '**R2 の箱**')
    detail(H12, (0, 1, 2), (0, 1), 4, '**H12 の箱**')
