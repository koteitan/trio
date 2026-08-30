# -*- coding: utf-8 -*-
"""**課題 (r1')(r2')(r3')（L3 の予測を壊しにいく）—— (n0) の 7% の内訳。**

**場面**（§R164 の (n0) と同じ）: `Q` の列 `j` が `Q.take (j+1)` の中で**行 2 の孤児**。
塔 `T = mTower Q d e n` の位置 `b = k*|Q| + j`（`k >= 1`）で `parent (T.take (b+1)) 2 b`。

## ★ 予想を先に書く（教訓 45）＋ 見積もり

**(r1')** L3 の §176 の機構: **錐の外 ⟹ 鎖は根に届かない ⟹ ブロック内で終わる ⟹ 無料**／
**錐の中 ⟹ 鎖は根から手前のブロックへ出る**。
> **⟹ 予想: 破れ（塔では親あり）は**錐の中**に集中。**錐の外は 0%**。見積もり 0 〜 5%。**

**(r2')** 断片では「錐の中で行 2 の孤児」には `entry Q 2 0 >= entry Q 2 j` が要る
⟹ `entry Q 2 0 = 1` ＝ **`z = 1`**。
> **⟹ 予想: 破れの `z = 1` が **100%**。見積もり 90 〜 100%。**

**(r3')** 「行 1 の等号」＝ `Q` に `entry Q 1 y == entry Q 1 0` の列 `y != 0` があるか
（H12 の (h1)「等号もブロッカー」と同じ形）。
> **⚠ 見積もり 30 〜 70%。**

**箱と単位**: 単位 `(Q,d,e,n,k,j)`。箱 = 行0<4, 行1<3, 行2<=cm、`|Q| = 3..4`、
`d,e ∈ 0..3`、`n ∈ 2..5`。**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import le1_root
from r113 import mTower


def run(cm, L, DE, NS):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            orph = [j for j in range(L) if Q[j][2] > 0
                    and trio.parent(Q[:j + 1], 2, j) is None]
            if not orph:
                continue
            eqblk = any(Q[y][1] == Q[0][1] for y in range(1, L))   # (r3') 行 1 の等号
            z = Q[0][2]
            for d in DE:
                for e in DE:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        for k in range(1, n):
                            for j in orph:
                                b = k * L + j
                                p = trio.parent(T[:b + 1], 2, b)
                                cone = le1_root(Q, j)
                                key = '錐の中' if cone else '錐の外'
                                c[(key, '分母')] += 1
                                c[(key, '★ 塔では親あり', p is not None)] += 1
                                if p is not None:
                                    c[('(r2\') 破れの z', z)] += 1
                                    c[('(r3\') 破れの行1等号', eqblk)] += 1
                                    c[('破れの錐', key)] += 1
                                    ex.setdefault(key, (Q, d, e, n, k, j, p))
    print(f'### 行2<={cm} |Q|={L}  [{time.time()-t0:.1f}s]')
    tb = 0
    for key in ('錐の中', '錐の外'):
        tot = c[(key, '分母')]
        if not tot:
            continue
        y = c[(key, '★ 塔では親あり', True)]
        tb += y
        mark = '  ★★ L3 の予測は 0%' if key == '錐の外' else ''
        print(f'  {key}: 分母 {tot:9d}  **塔では親あり {y:9d} ({100*y/tot:6.3f}%)**{mark}')
    if tb:
        zdist = dict(sorted((k[1], c[k]) for k in c
                            if isinstance(k, tuple) and k[0] == "(r2') 破れの z"))
        zpos = sum(v for kk, v in zdist.items() if kk >= 1)
        eq = c[("(r3') 破れの行1等号", True)]
        print('  **(r2) 破れの `z` 別**: ' + str(zdist)
              + '   ==> `z >= 1` の割合 %6.2f%%' % (100 * zpos / tb))
        print('  **(r3) 破れのうち「`Q` に行 1 の等号の列がある」… %d / %d (%6.2f%%)**'
              % (eq, tb, 100 * eq / tb))
        print('  破れの錐の内訳: ', dict(sorted((k[1], c[k]) for k in c
                                       if isinstance(k, tuple) and k[0] == '破れの錐')))
    for k in sorted(ex):
        print(f'      破れの例（{k}）: Q={ex[k][0]} d={ex[k][1]} e={ex[k][2]} n={ex[k][3]} '
              f'k={ex[k][4]} j={ex[k][5]} 親={ex[k][6]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(3, a.L + 1):
            run(cm, L, range(4), (2, 3, 4, 5))
