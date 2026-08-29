# -*- coding: utf-8 -*-
"""**課題 R134（L3 の依頼）—— `TowerSnocRoot` の構造。**

    **`Q ∈ W u` ＋ `2 <= |Q|` ＋ 根が狭義最浅
     ⟹ `Q ++ [(entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0)] ∈ W u`**

**足す列** `p = (Q[0][0] + d, Q[0][1] + e, Q[0][2])`。**`S = Q ++ [p]`、`j = |Q|`。**

**無料の枝（緑）と、その前提を逐語で写した:**

    `L105Cap:144` **`snoc_orphan_W`** (hC : C ∈ W u) (hCne) (hnp : ¬ hasParent (C++[p]) (srow …) |C|)
      ⟹ **孤児なら無料**
    `Wtower2:2208` **`snoc_flat_root`** (hC) (hCne)
      **(hsr : srow (C++[p]) |C| = 0)** ← ⚠ **足す列がフラット**  (hbp : parent … = 0)  (hpar)
      ⟹ **「親が根」だけでは足りない**（§R135 で確認済み）

**(g3) L3 の反例の形「足した列が `Q` の中に親を持ち、展開が `Q` の導出の外に出る」の充足率**
＝ **上の 2 枝に入らない割合**（＝ 残差）。**先に数える（教訓 23）。**

**私の予想（教訓 45、先に書く）**: §R139 と同じ構造になるはず。すなわち

    **`z = 0` ∧ `e >= 1` … 孤児 0%（親は必ず根）⟹ 残差の主**
    **`z >= 1`          … `srow p = 2` ⟹ 行 2 の親が要る ⟹ 大半が孤児で無料**

**箱と単位**: 単位 `(Q, d, e)`。箱 = 行0<4, 行1<3, 行2<=cm（**3 段**）、`|Q| = 2..4`、
`d, e ∈ 0..3`。母集団 = `2<=|Q|` ∧ **根が狭義最浅**。**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow


def run(cm, L, DE):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            z = root[2]
            for d in DE:
                for e in DE:
                    p = (Q[0][0] + d, Q[0][1] + e, Q[0][2])
                    S = Q + [p]
                    j = L
                    i = srow(S, j)
                    par = trio.parent(S, i, j)
                    ek = 'e=0' if e == 0 else 'e>=1'
                    c[('分母', z, ek)] += 1
                    c[('srow(p)', z, i)] += 1
                    if par is None:
                        c[('★ 孤児（snoc_orphan_W）', z, ek)] += 1
                        continue
                    c[('親の位置', par if par <= 2 else '>=3')] += 1
                    if par == 0:
                        c[('親 = 根', z, ek)] += 1
                        if i == 0:
                            c[('★★ snoc_flat_root の全前提', z, ek)] += 1
                        else:
                            c[('⚠ 親=根 だが srow!=0（残差）', z, ek)] += 1
                    else:
                        c[('⚠ 親が内部（残差）', z, ek)] += 1
                        ex.setdefault((z, ek), (Q, d, e, par, i))
    print(f'### 行2<={cm} |Q|={L}  [{time.time()-t0:.1f}s]')
    for z in range(cm + 1):
        for ek in ('e=0', 'e>=1'):
            tot = c[('分母', z, ek)]
            if not tot:
                continue
            orp = c[('★ 孤児（snoc_orphan_W）', z, ek)]
            flat = c[('★★ snoc_flat_root の全前提', z, ek)]
            r1 = c[('⚠ 親=根 だが srow!=0（残差）', z, ek)]
            r2 = c[('⚠ 親が内部（残差）', z, ek)]
            print(f'  z={z} {ek}: 分母 {tot:8d}  **孤児 {orp:8d} ({100*orp/tot:6.2f}%)**  '
                  f'flat_root {flat:7d} ({100*flat/tot:5.2f}%)  '
                  f'**残差 {r1+r2:8d} ({100*(r1+r2)/tot:6.2f}%)**'
                  f'（親=根だが srow!=0 {r1} ／ 親が内部 {r2}）')
    print('  srow(p) の分布: ', {(z, i): c[('srow(p)', z, i)] for z in range(cm + 1)
                              for i in (0, 1, 2) if c[('srow(p)', z, i)]})
    print('  **(g1) 親の位置**: ', dict(sorted(((k[1], c[k]) for k in c
                                          if isinstance(k, tuple) and k[0] == '親の位置'), key=str)))
    for k in sorted(ex, key=str)[:4]:
        print(f'      残差の例 {k}: Q={ex[k][0]} d={ex[k][1]} e={ex[k][2]} 親={ex[k][3]} srow={ex[k][4]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(2, a.L + 1):
            run(cm, L, range(4))
