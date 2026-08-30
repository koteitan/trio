# -*- coding: utf-8 -*-
"""**R94 —— 健全な反証器は「根の段だけ」しか反証できない（定理）。**

`Wchar.lean` の厳密な特徴づけを使う反証器（`probe_cap2.py` / `h1/h57.py` / `r89.py`）は

    |S| >= 2  ⟹ (S ∈ W a ⟺ ∀ n>=1, S⟦n⟧ ∈ W a)
    [(d,v,z)] ∈ W a ⟺ 2v+z <= a

だけを使う。⟹ **確定した非所属は「展開の木が `lev > a` の単元に届いたとき」だけ。**

★ ところが `oper`（`Trio.lean:98`）は **第 1 列を絶対に落とさない**:

    j1 = 0            → M そのもの
    末尾が全零 / 親なし → `Pred M = M.dropLast`（|M|>=2 なので第 1 列は残る）
    それ以外           → `M.take j0 ++ ...`。`j0>=1` なら `M[0]` が先頭。
                         `j0=0` なら `take 0 = []` だが flatMap の `k=0, j=0` の項が
                         `(entry M 0 0 + 0*d0, entry M 1 0 + 0*d1, entry M 2 0) = M[0]`

⟹ **木のどのノードも先頭列は `S[0]`。届く単元は `[S[0]]` だけ。**
⟹ **反証器が鳴る ⟺ `lev S 0 > a`。それ以外の非所属は原理的に検出できない。**

（これは `Wset.lean:2161` `lev_root_le_of_mem_W` の docstring が言っていることと同じ。
  さらに `Wtower2.lean:2990` `mem_Wself_iff`: `M ∈ W u ⟺ M ∈ Wself ∧ lev M 0 <= u`。
  ⟹ 段の情報はすべて根にある。反証できるのは段の部分だけで、`Wself` の部分は
  最小不動点なので有限の検査では反証できない。）

**帰結（H12 の反証器スイープに効く）**: `WCat` / `WSnoc` などの核は
「`A ∈ W u` かつ `B ∈ W u` ⟹ `A ++ B ∈ W u`」の形なので、
`lev (A++B) 0 = lev A 0 <= u`（`A ∈ W u` より）が**自動で成り立つ**。
⟹ **これらの核はこの反証器では原理的に反証できない。**「違反ゼロ」は空虚である。

以下はこの定理の実測での裏づけ。
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r89 import inW, lev

rng = random.Random(20260830)
r = Counter()
mismatch = []
memo = {}
t0 = time.time()
N = 40000
for _ in range(N):
    L = rng.randint(1, 6)
    S = [(rng.randint(0, 4), rng.randint(0, 4), rng.randint(0, 3)) for _ in range(L)]
    a = rng.randint(0, 12)
    x = inW(S, a, 8, memo, 24)
    root_bad = lev(S[0]) > a
    key = ('False' if x is False else 'True' if x is True else 'None')
    r[f'{key} / lev S0 > a = {root_bad}'] += 1
    if (x is False) != root_bad:
        if len(mismatch) < 5:
            mismatch.append((S, a, x, root_bad))
print(f'### R94 反証器は「根の段」以外を鳴らすか  ({N} 件, {time.time()-t0:.1f}s)')
for k in sorted(r):
    print(f'  {k:34s} {r[k]:8d}')
print(f'  **反証器の False と (lev S0 > a) の不一致: {len(mismatch)} 件**')
for m in mismatch:
    print('   ', m)

# 先頭列の保存を全数で検算
r2 = Counter()
for _ in range(20000):
    L = rng.randint(2, 7)
    S = [(rng.randint(0, 4), rng.randint(0, 4), rng.randint(0, 3)) for _ in range(L)]
    for n in (1, 2, 3, 4):
        E = trio.expand(list(S), n)
        if not E:
            r2['展開が空'] += 1
        else:
            r2['先頭列 = S[0]' if tuple(E[0]) == tuple(S[0]) else '**先頭列が変わった**'] += 1
print('### 先頭列の保存（乱択 20000 列 x n=1..4）')
for k in sorted(r2):
    print(f'  {k:24s} {r2[k]:10d}')
