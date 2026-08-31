# -*- coding: utf-8 -*-
"""**H49-0 の続き —— 正しい母集団（`R` は自然、`v` は自由）で `TieFree` を測り直す。**

⚠ H48 §100 の母集団は「`(0,v,z) :: R` **全体がシートの行**」という作り方だった。
シートの標準形は必ず `(0,0,0)` で始まるので **`v = 0` しか出ない**。
しかし `Wstar_closed` では `R` が `Aop` の資料、`v` は**全称**で `R` と独立。
⟹ **正しい母集団は「`R` は自然（標準形の接尾辞）、`v` は条件を満たす全部」。**
"""
import sys, io, contextlib, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio, h50
import probe_tiefree_tower as PT
import wcert as wc
from collections import Counter

rng = random.Random(20260829)
seen, fr = set(), []
for v in range(5):
    S = tuple(tuple(c) for c in trio.diag(3, v, zcap=1))
    if S:
        seen.add(S); fr.append(S)
while fr and len(seen) < 60000:
    S = fr.pop()
    for n in (1, 2, 3):
        T = tuple(tuple(c) for c in trio.expand(list(S), n))
        if T and len(T) <= 10 and T not in seen:
            seen.add(T); fr.append(T)
P = list(seen)

scenes = []
for M in P:
    for j in range(1, len(M)):
        R = list(M[j:])
        if not all(p[0] > 0 for p in R):
            continue
        for v in range(9):
            if h50.ok_scene(R, v, 0):
                scenes.append((M, j, R, v))
print('正しい母集団: 標準形 %d 本の接尾辞から **%d 件の場面**' % (len(P), len(scenes)))
print('   `v` の分布: %s' % dict(sorted(Counter(s[3] for s in scenes).items())))
print()
S = scenes if len(scenes) <= 30000 else rng.sample(scenes, 30000)
print('**`TieFree ((0,v,0) :: R)` を `v` 別に**（標本 %d 件）' % len(S))
c = Counter()
ex = {}
for M, j, R, v in S:
    X = [(0, v, 0)] + R
    try:
        t = PT.tiefree(X)
    except AssertionError:
        c[(v, 'assert')] += 1
        continue
    c[(v, t)] += 1
    if not t and v not in ex:
        ex[v] = (M, j, R, v)
print('   | `v` | `TieFree` 成立 / 全体 |')
print('   |--:|---|')
for v in sorted({k[0] for k in c}):
    a, b = c[(v, True)], c[(v, False)]
    if a + b:
        print('   | %d | **%d / %d (%.1f%%)** |' % (v, a, a + b, 100.0 * a / (a + b)))
A = sum(x for k, x in c.items() if k[1] is True)
B = sum(x for k, x in c.items() if k[1] is False)
print('   | **合計** | **%d / %d (%.1f%%)** |' % (A, A + B, 100.0 * A / max(1, A + B)))
print()
print('**`v >= 1` に絞ると**')
A1 = sum(x for k, x in c.items() if k[1] is True and k[0] >= 1)
B1 = sum(x for k, x in c.items() if k[1] is False and k[0] >= 1)
print('   `TieFree` 成立 **%d / %d (%.1f%%)**' % (A1, A1 + B1, 100.0 * A1 / max(1, A1 + B1)))
print()
print('**予想「`TieFree` ⟺ `∀ p ∈ R, entry p 1 != v`」の検算**')
bad = 0
n = 0
for M, j, R, v in S:
    X = [(0, v, 0)] + R
    try:
        t = PT.tiefree(X)
    except AssertionError:
        continue
    n += 1
    if t != all(p[1] != v for p in R):
        bad += 1
print('   食い違い **%d / %d**' % (bad, n))
print()
print('**破れる最小の例（`v` 別）**')
for v in sorted(ex):
    M, j, R, vv = ex[v]
    print('   v=%d  R=%s  （標準形 %s の j=%d 以降）'
          % (v, ''.join('(%d,%d,%d)' % q for q in R),
             ''.join('(%d,%d,%d)' % q for q in M), j))
print()
print('**退化検査**')
wc.audit(S, lambda s: PT.tiefree([(0, s[3], 0)] + s[2]),
         lambda s: all(p[1] != s[3] for p in s[2]), 'TieFree vs 「行 1 = v の列が無い」')
wc.audit(S, lambda s: PT.tiefree([(0, s[3], 0)] + s[2]),
         lambda s: s[3] == 0, 'TieFree vs 「v = 0」')
wc.audit(S, lambda s: PT.tiefree([(0, s[3], 0)] + s[2]),
         lambda s: len(s[2]) <= 2, 'TieFree vs 「|R| <= 2」')
