# -*- coding: utf-8 -*-
"""**課題 R132（訂正後の仕様）—— `j = 0` の段。`M = mTower Q d e n ++ [r]` の展開。**

`r` ＝ ブロック `n` の根。**写し間違い防止のため `mTower Q d e (n+1)` の位置 `n*|Q|` を直接取る。**

**測るもの（team-lead の訂正後の指示）:**

    **(e1')** `j0 = parent M (srow M (|M|-1)) (|M|-1)` の分布。`(n-1)*|Q|` ちょうどか内部か
    **(e2')** 軸: 「ブロック `n-1` に `r` より浅い列が根以外にあるか」
              ＝ `∃ q >= 1, entry Q 0 q < entry Q 0 0 + d`
              L3 の予想: **無ければ `j0 = (n-1)*|Q|`、あれば内部**
    **(e3')** `Lb = |M| - 1 - j0` の分布。**`Lb <= |Q|` は L3 の定理（検算）**
    **(e4')** `d0` と `d1` の値を `z` 別に。L3 の予想:
              **`z=0 ⟹ srow r = 1 ⟹ d1 = 0`** ／ **`z=1 ⟹ srow r = 2 ⟹ d1 = e`**
    **(e5')** 展開の式: `M⟦m⟧ = M.take j0 ++ (Lb 列の塊の写しを m 個)`
              ⚠ これは `oper` の定義そのもの（`Trio.lean:98`）なので**恒真**。
              **非自明なのは `M.take j0 = mTower Q d e (n-1)`、すなわち (e1')。**

**(e6') 反例の形を先に（教訓 45）**: `d1 != e`（`z=1`）になるのは
`entry M 1 j0` が「ブロック `n-1` の根の行 1」でないとき、すなわち **`j0` が内部のとき**。
⟹ **(e1') が内部になる場合と (e4') が外れる場合は同じ集合のはず。**

**箱と単位**: 単位 `(Q,d,e,n)`。`Q` の根は `(0,v,z)`（塔の場面: `entry Q 0 0 = 0`）、
他の列は行0 >= 1。箱 = 行0<4, 行1<3, 行2<=cm（**3 段**）、`|Q| = 2..4`、
`d ∈ 1..3`、`e ∈ 0..3`、**`n ∈ 1..5`**。**`W` 所属は判定しない。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower


def run(cm, L, DS, ES, NS):
    COL = [(a, b, c) for a in range(1, 4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for v in range(3):
        for z in range(cm + 1):
            for t in itertools.product(COL, repeat=L - 1):
                Q = [(0, v, z)] + list(t)
                # (e2') の軸: ブロック n-1 に `r` より浅い列が根以外にあるか
                for d in DS:
                    inner_cand = any(Q[q][0] < Q[0][0] + d for q in range(1, L))
                    ax = '内部候補あり' if inner_cand else '根だけ'
                    for e in ES:
                        for n in NS:
                            big = [tuple(x) for x in mTower(Q, d, e, n + 1)]
                            M = big[:n * L] + [big[n * L]]
                            last = len(M) - 1
                            i = srow(M, last)
                            j0 = trio.parent(M, i, last)
                            c[('分母', ax)] += 1
                            c[('srow(r)', z, i)] += 1
                            if j0 is None:
                                c[('★ 孤児', ax)] += 1
                                continue
                            off = j0 - (n - 1) * L
                            Lb = last - j0
                            c[('j0 の位置', ax, 'ちょうど' if off == 0
                               else ('内部' if off > 0 else '⛔ もっと前'))] += 1
                            c[('Lb', min(Lb, L + 1))] += 1
                            if Lb > L:
                                c['⛔ Lb > |Q|（L3 の定理に反する）'] += 1
                                ex.setdefault('Lb', (Q, d, e, n, j0, Lb))
                            d0 = M[last][0] - M[j0][0]
                            d1 = (M[last][1] - M[j0][1]) if i > 1 else 0
                            c[('d0 == d', z, d0 == d)] += 1
                            c[('d1', z, ('=0' if d1 == 0 else ('=e' if d1 == e else '★ その他')))] += 1
                            if off > 0:
                                c[('内部のとき d1', '=e' if d1 == e else '★ その他')] += 1
                                ex.setdefault('内部', (Q, d, e, n, j0, off, Lb, d0, d1, i))
    print(f'### 行2<={cm} |Q|={L}  [{time.time()-t0:.1f}s]')
    for ax in ('根だけ', '内部候補あり'):
        tot = c[('分母', ax)]
        if not tot:
            continue
        print(f'  **(e2) axis={ax}: 分母 {tot:8d}  孤児 {c[("★ 孤児", ax)]:7d}**')
        for k in ('ちょうど', '内部', '⛔ もっと前'):
            n_ = c[('j0 の位置', ax, k)]
            if n_:
                print(f'      **(e1\') j0 が {k}: {n_:8d} ({100*n_/tot:6.2f}%)**')
    print('  **(e3\') `Lb` の分布**: ', dict(sorted((k[1], c[k]) for k in c
                                              if isinstance(k, tuple) and k[0] == 'Lb')),
          f'  ⛔ `Lb > |Q|`: {c["⛔ Lb > |Q|（L3 の定理に反する）"]}')
    for z in range(cm + 1):
        sr = {i: c[('srow(r)', z, i)] for i in (0, 1, 2) if c[('srow(r)', z, i)]}
        d0ok = c[('d0 == d', z, True)]; d0ng = c[('d0 == d', z, False)]
        d1 = {k[2]: c[k] for k in c if isinstance(k, tuple) and k[0] == 'd1' and k[1] == z}
        print(f'  **(e4\') z={z}: srow(r)={sr}  d0==d {d0ok}/{d0ok+d0ng}  d1 {d1}**')
    print('  内部のときの `d1`: ', dict((k[1], c[k]) for k in c
                                   if isinstance(k, tuple) and k[0] == '内部のとき d1'))
    for k in sorted(ex):
        print(f'      例 {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(2, a.L + 1):
            run(cm, L, (1, 2, 3), (0, 1, 2, 3), (1, 2, 3, 4, 5))
