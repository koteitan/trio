# -*- coding: utf-8 -*-
"""**R127 (a3) 正しい版 —— `le1_mTower_block`（`L105Cap:6572`）の前提を全部写して検算。**

⚠ **最初の版で前提を 4 つ落としていた**（自分で気づいて捨てた。§R115 と同じ失敗の再発防止）。

**前提（`L105Cap:6572-6579` から逐語）:**

    `hM2   : 2 <= M.length`
    `hup   : ∀ l, 0 < l → l <= |M.dropLast| → entry M 0 0 < entry M 0 l`
    **`hd0pos : 0 < d`**
    **`hd1pos : 0 < e`**
    **`hd0e  : entry M 0 (|M.dropLast|) = entry M 0 0 + d`**   ← `d` は `M` から決まる
    `hr0   : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l`
    **`hlp   : le1 M 0 (|M.dropLast|)`**                       ← `M` の末尾列が根の錐の中
    `hk : k < n`   `hq : q < |M.dropLast|`

    結論 `le1 (mTower M.dropLast d e n) 0 (k*|Q|+q) ↔ le1 M.dropLast 0 q`

**単位** `(M, e, n, k, q)`。**箱** 行0<4, 行1<3, 行2<=cm、`|M| = L+1`。
**陰性対照**: `hd1pos`（e=0）／`hd0pos`（d=0 になる M）／`hlp` を 1 つずつ落とす。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r126 import le1_root
from r113 import mTower


def run(cm, L, ES, NS, label):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product(COL, repeat=L):      # M = root + L 列（|M| = L+1）
            M = [root] + list(t)
            Lb = L                                       # |M.dropLast|
            Q = M[:-1]
            # hup / hr0: 根が狭義最浅（`M` 全体で）
            if not all(M[0][0] < M[l][0] for l in range(1, L + 1)):
                continue
            d = M[Lb][0] - M[0][0]                       # hd0e で決まる
            hd0pos = d > 0
            hlp = le1_root(M, Lb)
            for e in ES:
                hd1pos = e > 0
                tiers = []
                if hd0pos and hd1pos and hlp:
                    tiers.append('(全前提)')
                if hd1pos and hlp:
                    tiers.append('陰性対照 hd0pos を落とす')
                if hd0pos and hlp:
                    tiers.append('陰性対照 hd1pos を落とす')
                if hd0pos and hd1pos:
                    tiers.append('陰性対照 hlp を落とす')
                if not tiers:
                    continue
                for n in NS:
                    T = [tuple(x) for x in mTower(Q, d, e, n)]
                    base = [le1_root(Q, q) for q in range(Lb)]
                    for k in range(n):
                        for q in range(Lb):
                            ok = (le1_root(T, k * Lb + q) == base[q])
                            for ti in tiers:
                                c[(ti, 'ok' if ok else '**破れ**')] += 1
                                if not ok:
                                    ex.setdefault(ti, (M, d, e, n, k, q, base[q]))
    print(f'### {label}  箱 行0<4 行1<3 行2<={cm}  |M|={L+1}  [{time.time()-t0:.1f}s]')
    for ti in ('(全前提)', '陰性対照 hd0pos を落とす', '陰性対照 hd1pos を落とす',
               '陰性対照 hlp を落とす'):
        o = c[(ti, 'ok')]; b = c[(ti, '**破れ**')]
        if o + b:
            print(f'  {ti:26s} 分母 {o+b:9d}  ok {o:9d}  **破れ {b:8d}** '
                  f'({100*b/(o+b):6.2f}%)')
    for k in sorted(ex):
        M, d, e, n, kk, q, bq = ex[k]
        print(f'    ★ 例 {k}: M={M} d={d} e={e} n={n} k={kk} q={q}（Q 側 {bq}）')
    print()


if __name__ == '__main__':
    for cm in (1, 2):
        for L in (2, 3):
            run(cm, L, (0, 1, 2, 3), (2, 3), 'R127 (a3) `le1_mTower_block` 全前提つき検算')
    run(1, 4, (0, 1, 2), (2,), 'R127 (a3) `|M|=5` まで伸ばす（教訓 21）')
