# -*- coding: utf-8 -*-
"""**(CONS-CHK) ＋ (M3-D0)。**

## (CONS-CHK) 保存量の正体は「根の行 1」か

    `max_j amin M j = entry M 1 0` か。⟹ ★ 等しければ **ほぼ自明**、違えば **本物**。

## (M3-D0) L3 の読解「`d = 0` が越境を構造的に禁じる」を実測で

⚠ 母集団を 1 行で（**組み立ての形**）: `M` の最終列 `x`、`t = srow M x`、`r = parent M t x`、
**`A = M[:r]`**、**`T = (oper M n)[r:]`**、**`d = entry M 0 x - entry M 0 r`（`t > 0` のとき、
`t = 0` なら `d = 0`）**。⟹ `A ++ T = oper M n`。

    (a) **`T` の列の行 0 の親が `A` の中にあるか**（＝ 越境）を **`d = 0` と `d > 0` で分ける**
    (b) 越境が起きる手の **`d` の値の分布**と、**越境の深さ**（`A` のどこまで戻るか）
    (c) `oper` の手で **`d` は減るか**（★ 手を 2 種に分けて）
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from trio import expand
from collections import Counter
from r126 import srow
from r263 import load
from r272 import subwins
from r273 import anc0chain


def dof(M):
    x = len(M) - 1
    t = srow(M, x)
    r = trio.parent(M, t, x)
    if r is None: return None, None
    return (M[x][0] - M[r][0]) if t > 0 else 0, r


def cons_chk(S, tag):
    c = Counter()
    for X in S:
        Y = [tuple(v) for v in X]
        am = [min(Y[y][1] for y in anc0chain(Y, j)) for j in range(len(Y))]
        c['分母'] += 1
        if max(am) == Y[0][1]: c['★ max amin = 根の行 1'] += 1
        else: c['⛔ **違う**'] += 1
        if min(am) == min(v[1] for v in Y): c['★ min amin = 大域の行 1 の最小'] += 1
        else: c['⛔ min が違う'] += 1
    d = c['分母']
    print(f'  {tag}: 分母 {d}   ★ **max amin = 根の行 1** '
          f'{c["★ max amin = 根の行 1"]} ({100*c["★ max amin = 根の行 1"]/max(d,1):8.4f}%)   '
          f'⛔ 違う {c["⛔ **違う**"]}')
    print(f'      ★ min amin = 大域の行 1 の最小 {c["★ min amin = 大域の行 1 の最小"]} '
          f'({100*c["★ min amin = 大域の行 1 の最小"]/max(d,1):8.4f}%)   '
          f'⛔ 違う {c["⛔ min が違う"]}')


def m3d0(Ms, NS, tag):
    c = Counter(); t0 = time.time()
    for M0 in Ms:
        M = [tuple(v) for v in M0]
        if len(M) < 3: continue
        d, r = dof(M)
        if d is None: continue
        for n in NS:
            E = [tuple(v) for v in expand([list(v) for v in M], n)]
            if len(E) <= r: continue
            g = 'd=0' if d == 0 else ('d=1' if d == 1 else 'd>=2')
            c[f'[{g}] 手'] += 1
            cross = 0; deep = 0
            for k in range(r, len(E)):
                p = trio.parent(E[:k + 1], 0, k)
                c[f'[{g}] 塔の列'] += 1
                if p is not None and p < r:
                    cross += 1; deep = max(deep, r - p)
                    c[f'[{g}] ⛔ **行 0 の越境**'] += 1
            if cross:
                c[f'[{g}] ⛔ 越境を含む手'] += 1
                c[f'   [{g}] 越境の深さ {min(deep,5)}'] += 1
            # ---------- (c) d は減るか ----------
            d2, r2 = dof(E)
            if d2 is None: continue
            grp = '⛔ 接頭辞に逃げる手' if r2 < r else '★ ブロックの中の手'
            c[f'{grp} d 分母'] += 1
            c[f'{grp} d ' + ('減' if d2 < d else ('同' if d2 == d else '増'))] += 1
    print(f'### (M3-D0)  {tag}  [{time.time()-t0:.1f}s]')
    for g in ('d=0', 'd=1', 'd>=2'):
        h, col = c[f'[{g}] 手'], c[f'[{g}] 塔の列']
        if not h: continue
        print(f'  **{g}**: 手 {h}  塔の列 {col}  ⛔ **行 0 の越境** '
              f'{c[f"[{g}] ⛔ **行 0 の越境**"]} '
              f'({100*c[f"[{g}] ⛔ **行 0 の越境**"]/max(col,1):8.4f}%)   '
              f'⛔ 越境を含む手 {c[f"[{g}] ⛔ 越境を含む手"]} '
              f'({100*c[f"[{g}] ⛔ 越境を含む手"]/max(h,1):8.4f}%)')
    for k in sorted(c):
        if k.startswith('   ['): print(f'      {k}: {c[k]}')
    for grp in ('⛔ 接頭辞に逃げる手', '★ ブロックの中の手'):
        dd = c[f'{grp} d 分母']
        print(f'  (c) {grp}: 分母 {dd}  d 減 {100*c[f"{grp} d 減"]/max(dd,1):7.3f}%  '
              f'同 {100*c[f"{grp} d 同"]/max(dd,1):7.3f}%  '
              f'増 {100*c[f"{grp} d 増"]/max(dd,1):7.3f}%')
    print()


if __name__ == '__main__':
    Ms = [list(m) for m in load()]
    print('## ★★ (CONS-CHK)')
    cons_chk({tuple(tuple(v) for v in M) for M in Ms}, 'シート行列そのもの')
    cons_chk(subwins(Ms, 8), '★★ シートの全 drop/take')
    print()
    m3d0(Ms, (1, 2, 3), '★ シート行列そのもの')
    m3d0([list(x) for x in subwins(Ms, 8)], (1, 2, 3), '★★ シートの drop/take')
