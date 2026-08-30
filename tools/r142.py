# -*- coding: utf-8 -*-
"""**(T1) 底の snoc の構造**（`z=0` の残り 1 本。SESSION §399/§401）。

    **(T1)** `shTower Q e n ++ [(entry Q 0 0 + n*e, entry Q 1 0, entry Q 2 0)]`

**主語（逐語）**: `Wtower2:1688` **`shTower Q e n = (List.range n).flatMap fun k => shiftr01 (k*e) 0 Q`**
⟹ **行 0 だけ `k*e` ずらす。行 1・行 2 は動かさない**（`Lift1` が無い）。
⟹ 足す列 `p = (Q[0][0] + n*e, Q[0][1], Q[0][2])` は **ブロック `n` の根**そのもの。

**team-lead の §401 の注意（そのまま写す）:**
> **(T1) でも `d0` は `d` に決まらない可能性がある。`oper_eq_gexp_gen` を読むとき
> `d0` を `d` と置かず、`entry M 0 last − entry M 0 j0` のままで進めるよう指示した。**

**私の導出（先に書く。教訓 45）**: `S = shTower Q e n ++ [p]`、`j = n*|Q|`。
`j0` がブロック `n-1` の根（index `(n-1)*|Q|`）なら `d0 = n*e − (n-1)*e = e`。
`j0` が内部（列 `q >= 1`）なら `d0 = n*e − (Q[q][0] + (n-1)*e) = e − Q[q][0] < e`
（根が狭義最浅なので `Q[q][0] >= 1`）。
⟹ **`d0 = e` ⟺ `j0 = (n-1)*|Q|`。R132 の (e1') とまったく同じ構造。**

**測るもの**: (t1) `p` が孤児か（`snoc_orphan_W` で無料）／(t2) 親の位置／
(t3) **`d0 = e` の割合**／(t4) `srow p` と `snoc_flat_root` の適用率。

**箱と単位**: 単位 `(Q, e, n)`。`Q` の根 `= (0, v, z)`、他の列は行0 >= 1。
箱 = 行0<4, 行1<3, 行2<=cm（**3 段**）、`|Q| = 2..4`、`e ∈ 1..3`、`n ∈ 1..4`。
母集団 = `2<=|Q|` ∧ **根が狭義最浅**。**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow


def shTower(Q, e, n):
    return [(c[0] + k * e, c[1], c[2]) for k in range(n) for c in Q]


def run(cm, L, ES, NS):
    COL = [(a, b, c) for a in range(1, 4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for v in range(3):
        for z in range(cm + 1):
            for t in itertools.product(COL, repeat=L - 1):
                Q = [(0, v, z)] + list(t)
                for e in ES:
                    for n in NS:
                        T = shTower(Q, e, n)
                        p = (Q[0][0] + n * e, Q[0][1], Q[0][2])
                        S = T + [p]
                        j = len(S) - 1
                        i = srow(S, j)
                        j0 = trio.parent(S, i, j)
                        key = (z, 'v=0' if v == 0 else 'v>=1')
                        c[(key, '分母')] += 1
                        c[('srow(p)', z, 'v=0' if v == 0 else 'v>=1', i)] += 1
                        if j0 is None:
                            c[(key, '★ 孤児')] += 1
                            continue
                        kp, qp = divmod(j0, L)
                        d0 = S[j][0] - S[j0][0]
                        c[(key, '★ d0 == e' if d0 == e else '⚠ d0 != e')] += 1
                        c[('親のブロック戻り', (n - 1) - kp)] += 1
                        c[('親の列 q', qp)] += 1
                        c[('Lb', min(j - j0, L + 1))] += 1
                        if j0 == 0:
                            c[(key, '親 = 全体の根')] += 1
                            if i == 0:
                                c[(key, '★★ snoc_flat_root の全前提')] += 1
                        if qp != 0:
                            ex.setdefault(key, (Q, e, n, j0, qp, d0, i))
    print(f'### 行2<={cm} |Q|={L}  [{time.time()-t0:.1f}s]')
    for z in range(cm + 1):
        for vk in ('v=0', 'v>=1'):
            key = (z, vk); tot = c[(key, '分母')]
            if not tot:
                continue
            orp = c[(key, '★ 孤児')]; ok = c[(key, '★ d0 == e')]; ng = c[(key, '⚠ d0 != e')]
            print(f'  z={z} {vk:5s}: 分母 {tot:8d}  **孤児 {orp:8d} ({100*orp/tot:6.2f}%)**  '
                  f'親あり {ok+ng:8d} → **`d0 == e` {ok:8d} ({100*ok/max(ok+ng,1):6.2f}%)**  '
                  f'親=根 {c[(key, "親 = 全体の根")]:7d}  flat_root {c[(key, "★★ snoc_flat_root の全前提")]:6d}')
    print('  srow(p): ', {(z, vk, i): c[('srow(p)', z, vk, i)] for z in range(cm + 1)
                          for vk in ('v=0', 'v>=1') for i in (0, 1, 2)
                          if c[('srow(p)', z, vk, i)]})
    print('  **親のブロック戻り**: ', dict(sorted((k[1], c[k]) for k in c
                                          if isinstance(k, tuple) and k[0] == '親のブロック戻り')))
    print('  **親の列 q**: ', dict(sorted((k[1], c[k]) for k in c
                                    if isinstance(k, tuple) and k[0] == '親の列 q')))
    print('  `Lb` の分布: ', dict(sorted((k[1], c[k]) for k in c
                                    if isinstance(k, tuple) and k[0] == 'Lb')))
    for k in sorted(ex, key=str)[:3]:
        print(f'      `d0 != e` の例 {k}: Q={ex[k][0]} e={ex[k][1]} n={ex[k][2]} '
              f'j0={ex[k][3]}（列 {ex[k][4]}）d0={ex[k][5]} srow={ex[k][6]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(2, a.L + 1):
            run(cm, L, (1, 2, 3), (1, 2, 3, 4))
