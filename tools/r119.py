# -*- coding: utf-8 -*-
"""**課題 R118 —— `v = 0` の `n >= 2` の枝。`v=0` は入口だけか、それとも再生産されるか。**

⚠ **測る前に書く（教訓 45）。反例の形と予想:**

  **§R94 の定理より `oper` は第 1 列を落とさない** ⟹ `X⟦n⟧` の根は **`(0,0,z)` のまま**。
  ⟹ **「根の行 1 ＝ `v`」は展開では 0 のまま。`v` は変わらない。**
  ⟹ team-lead の (s2)「次の段では `v=0` の問題でなくなるのでは」は
     **`X⟦n⟧` については成り立たない**はず（根が保存されるので）。
  ★ **ただし `Lift1 X 1` の根は `(0,1,z)`**（根は必ず自分の錐に入る）⟹ **そちらは `v=1`**。
  ⟹ **区別が要る**: 「前提側の展開 `X⟦n⟧`」は `v=0` のまま、
     「結論側の主語 `Lift1 X 1`」は `v=1`。

  **本題 (s3)**: `X⟦n⟧ = (0,0,z) :: R'` として、**`R'` が `argOK` かつ タイあり**
  （＝ `LiftTieCore` の `v=0` の場面に戻る）か。
  **反例の形 ＝「タイが消える」または「`argOK` が破れる」。両方の件数を数える。**

**箱**（2 つ。行 2 の軸を振る）:
  (a) 列 行0∈[1,2]×行1∈[0,2]×**行2∈[0,1]**  (b) 列 行0∈[1,3]×行1∈[0,3]×**行2∈[0,2]**
**母集団**: `LiftTieCore` の `v=0` の場面 ＝ `argOK R` ∧ `∃p∈R, p.2.1 = 0`。
⚠ `X ∈ W z` は有限で判定できない（R94）ので落とした**上位集合**。**所属の判定はしない。**
**単位**: `(R, z, n)` の組。**分母**を明記。`|R|<=3` は全数、それ以上は標本。
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


def shape(S):
    j1 = len(S) - 1
    if j1 == 0:
        return ('ident', None, None, 0, 0)
    if S[j1][0] == 0 and S[j1][1] == 0 and S[j1][2] == 0:
        return ('zero', None, None, 0, 0)
    i1 = srow(S, j1)
    j0 = trio.parent(S, i1, j1)
    if j0 is None:
        return ('noparent', None, i1, 0, 0)
    d0 = (S[j1][0] - S[j0][0]) if i1 > 0 else 0
    d1 = (S[j1][1] - S[j0][1]) if i1 > 1 else 0
    return ('copy', j0, i1, d0, d1)


def run(COL, Ls, NS, label, sample_from=4, sample=120000):
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
                continue                                  # タイ（v=0）
            for z in (0, 1):
                X = [(0, 0, z)] + R
                # 結論側の主語の根（Lift1 は根を必ず錐に入れる）
                Y0 = (X[0][0], X[0][1] + 1, X[0][2])
                c[('参考', f'Lift1 X 1 の根 = {Y0}（行 1 = 1）')] += 1
                for n in NS:
                    T = oper_lean(X, n)
                    c[('分母', f'z={z}')] += 1
                    br, j0, i1, d0, d1 = shape(X)
                    c[('s1 X の分岐', br if br != 'copy'
                       else ('塔 (j0=0)' if j0 == 0 else 'cons 保存 (j0>=1)'))] += 1
                    if br == 'copy' and j0 == 0:
                        c[('s1 塔の (d0,d1)',
                           f'd0={"e" if d0 == X[len(X)-1][0] else d0} '
                           f'd1={"row1(末尾)" if d1 == X[len(X)-1][1] else d1}')] += 1
                    if not T:
                        c[('s2 X⟦n⟧ の根', '空')] += 1
                        continue
                    # (s2) 根は保存されるか
                    c[('s2 X⟦n⟧ の根', 'X[0] と同じ（v=0 のまま）'
                       if tuple(T[0]) == tuple(X[0]) else f'**変わる {T[0]}**')] += 1
                    # (s3) v=0 の場面に戻るか
                    Rp = T[1:]
                    if not Rp:
                        c[('s3 X⟦n⟧ の尾', '空（単元）')] += 1
                        continue
                    ag = all(p[0] >= 1 for p in Rp)
                    tie = any(p[1] == 0 for p in Rp)
                    c[('s3 argOK(R\')', 'ok' if ag else '**破れる**')] += 1
                    c[('s3 タイ(R\')', 'ある' if tie else '**消える**')] += 1
                    c[('s3 場面に戻るか', '戻る（argOK ∧ タイ）' if (ag and tie)
                       else '**戻らない**')] += 1
                    if not tie:
                        ex.setdefault('タイが消える', (R, z, n, T))
                    if not ag:
                        ex.setdefault('argOK が破れる', (R, z, n, T))
    print(f'### {label}')
    for key in ('分母', 's1 X の分岐', 's1 塔の (d0,d1)', 's2 X⟦n⟧ の根',
                's3 argOK(R\')', 's3 タイ(R\')', 's3 場面に戻るか'):
        sub = {k[1]: n for k, n in c.items() if k[0] == key}
        if not sub:
            continue
        s = sum(sub.values())
        print(f'  -- {key}（分母 {s}） --')
        for k in sorted(sub, key=str):
            print(f'     {str(k):40s} {sub[k]:9d}  ({100*sub[k]/s:5.2f}%)')
    for k in sorted(ex):
        print(f'  ★ {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    run([(d, b, c) for d in (1, 2) for b in (0, 1, 2) for c in (0, 1)],
        tuple(range(1, a.L + 1)), (2, 3, 4),
        f'R118 (a) 箱 行2<=1／`v=0` の `LiftTieCore` 場面／|R|<={a.L}／n=2..4')
    run([(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2, 3) for c in (0, 1, 2)],
        (1, 2, 3), (2, 3, 4),
        'R118 (b) 箱 **行2<=2**／|R|<=3／n=2..4／全数')
