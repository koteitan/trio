# -*- coding: utf-8 -*-
"""**課題 R136（L3 の §120 で鋭くしたもの）—— どのブロッカーが親か。**

**場面**: `(T1)` ＝ `S = shTower Q e n ++ [r]`、`r = (entry Q 0 0 + n*e, entry Q 1 0, entry Q 2 0)`。
**射程は `z = 0 ∧ v >= 1`**（`v = entry Q 1 0`。`v = 0` なら `srow r = 0` で行 0 の親の話になる）。

**L3 の §120（緑）**: `shTower` では `r` の行 1 が **`entry Q 1 0` ちょうど**
⟹ 塔の根もどのブロックの根も行 1 が `r` と同じ ⟹ `nextrel1` の狭義増加が破れる
⟹ **親になれるのは「行 1 が `entry Q 1 0` より狭義に小さい列」＝ ブロッカーの像だけ。**

**ブロッカーの定義（2 通りあるので両方数える）:**

    **`B<`  … `y != 0` ∧ `entry Q 1 y <  entry Q 1 0`**（**親になれる**候補）
    `B<=` … `y != 0` ∧ `entry Q 1 y <= entry Q 1 0`（`Lcone.le1_zero_iff` の証人）

## ★ 反例の形を先に書く（教訓 45）＋ 充足率の見積もり（L3 の §105.2）

> **L3 の予想: 親は「最も右のブロッカーの像」**（`nextrel1` は添字最大を選ぶ）。
>
> **⚠ 私の反例の形: 「最も右のブロッカーの像が `r` の行 0 祖先でない」場合。**
> `nextrel1` は候補を**行 0 の祖先に限る**ので、行 1 だけで最も右を選んでも親にならない。
>
> **⚠ 充足率の私の見積もり: 20 〜 50%。**
> ブロッカーは行 1 で決まり、行 0 の祖先性は別条件なので、そこそこ外れるはず。

**測るもの**: (m1) 親 ＝ 最も右のブロッカーの像か ／ (m2) `d0 == e` の割合と `Lb` ／
(m3) ブロッカーの個数 ／ (m4) 親のブロック（`n` 依存）。

**箱と単位**: 単位 `(Q, e, n)`。`Q` の根 `= (0, v, 0)`、**`v >= 1`**、他の列は行0 >= 1。
箱 = 行0<4, 行1<4, `|Q| = 2..5`、`e ∈ 1..3`、`n ∈ 1..4`。母集団 = **根が狭義最浅**。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow


def shTower(Q, e, n):
    return [(c[0] + k * e, c[1], c[2]) for k in range(n) for c in Q]


def run(L, VS, ES, NS, R1):
    COL = [(a, b, 0) for a in range(1, 4) for b in range(R1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for v in VS:
        for t in itertools.product(COL, repeat=L - 1):
            Q = [(0, v, 0)] + list(t)
            blk_lt = [y for y in range(1, L) if Q[y][1] < v]
            blk_le = [y for y in range(1, L) if Q[y][1] <= v]
            c[('(m3) ブロッカー B< の本数', min(len(blk_lt), 3))] += 1
            for e in ES:
                for n in NS:
                    S = shTower(Q, e, n) + [(Q[0][0] + n * e, Q[0][1], Q[0][2])]
                    j = len(S) - 1
                    i = srow(S, j)
                    if i != 1:
                        c[('⚠ srow != 1', i)] += 1
                        continue
                    p = trio.parent(S, i, j)
                    c['分母'] += 1
                    if p is None:
                        c['★ 孤児（ブロッカー無しのはず）'] += 1
                        c[('孤児なのに B< あり', bool(blk_lt))] += 1
                        continue
                    kp, qp = divmod(p, L)
                    c[('親の列 q がブロッカーか', qp in blk_lt)] += 1
                    # (m1) 最も右のブロッカーの像か（同じブロックの中で最大の添字）
                    rightmost = max(blk_lt) if blk_lt else None
                    c[('★ (m1) 親 = 最も右のブロッカーの像', qp == rightmost)] += 1
                    if qp != rightmost:
                        ex.setdefault('m1 破れ', (Q, e, n, p, qp, rightmost, blk_lt))
                    # (m4) 親のブロック
                    c[('(m4) 親のブロック戻り', (n - 1) - kp)] += 1
                    d0 = S[j][0] - S[p][0]; Lb = j - p
                    c[('(m2) d0 == e', d0 == e)] += 1
                    c[('(m2) Lb', min(Lb, L + 2))] += 1
                    # 私の反例の形: 最も右のブロッカーの像が行 0 祖先でないか
                    if rightmost is not None:
                        img = kp * L + rightmost      # 親と同じブロックでの像
                        anc = trio.is_ancestor(S, 0, img, j)
                        c[('★ 私の反例の形（最右ブロッカーの像が行0祖先でない）', not anc)] += 1
    tot = c['分母']
    print(f'### |Q|={L} 行1<{R1}  分母 {tot:9d}  [{time.time()-t0:.1f}s]')
    print('  (m3) ブロッカー `B<` の本数: ', dict(sorted((k[1], c[k]) for k in c
                                              if isinstance(k, tuple) and k[0] == '(m3) ブロッカー B< の本数')))
    orp = c['★ 孤児（ブロッカー無しのはず）']
    print(f'  孤児 {orp:9d} ({100*orp/max(tot,1):6.2f}%)  '
          f'うち `B<` があるのに孤児 **{c[("孤児なのに B< あり", True)]}**')
    ok = c[('★ (m1) 親 = 最も右のブロッカーの像', True)]
    ng = c[('★ (m1) 親 = 最も右のブロッカーの像', False)]
    print(f'  **(m1) 親 = 最も右のブロッカーの像: {ok:9d} / {ok+ng} ({100*ok/max(ok+ng,1):6.2f}%)**')
    print(f'      親の列がブロッカー: {c[("親の列 q がブロッカーか", True)]} / '
          f'{c[("親の列 q がブロッカーか", True)]+c[("親の列 q がブロッカーか", False)]}')
    y = c[('★ 私の反例の形（最右ブロッカーの像が行0祖先でない）', True)]
    nn = y + c[('★ 私の反例の形（最右ブロッカーの像が行0祖先でない）', False)]
    print(f'  **私の反例の形の充足率: {y} / {nn} ({100*y/max(nn,1):6.2f}%)**（見積もりは 20〜50%）')
    print(f'  **(m2) `d0 == e`: {c[("(m2) d0 == e", True)]} / {ok+ng} '
          f'({100*c[("(m2) d0 == e", True)]/max(ok+ng,1):6.2f}%)**  '
          f'`Lb` ' + str(dict(sorted((k[1], c[k]) for k in c
                                 if isinstance(k, tuple) and k[0] == '(m2) Lb'))))
    print('  **(m4) 親のブロック戻り**: ', dict(sorted((k[1], c[k]) for k in c
                                           if isinstance(k, tuple) and k[0] == '(m4) 親のブロック戻り')))
    for k in sorted(ex):
        print(f'      {k} の例: Q={ex[k][0]} e={ex[k][1]} n={ex[k][2]} 親={ex[k][3]}'
              f'（列 {ex[k][4]}）最右ブロッカー={ex[k][5]} B<={ex[k][6]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=5)
    a = ap.parse_args()
    for R1 in (3, 4):
        for L in range(2, a.L + 1):
            run(L, range(1, R1), (1, 2, 3), (1, 2, 3, 4), R1)
