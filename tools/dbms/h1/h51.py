# -*- coding: utf-8 -*-
"""**課題 H50 —— 無タイの伝播（L2 の債務 3）。**

塔の 1 段（`probe_tiefree_tower.py` の `hstep`、Lean 側は `Wtower2`）:

    X = (0,v,z) :: R,   t = d1 = entry R 1 (|R|-1) - v
    **X⟦n+1⟧ = (0,v,z) :: graft R (Lift1 (X⟦n⟧) t)**
    R_n := graft R (Lift1 (X⟦n⟧) t)          （＝ X⟦n+1⟧ の 1 列目以降）

測るのは
    1. `R_n` が `argOK`（行 0 が全部 > 0）
    2. `(0,v,z) :: R_n` が**無タイ**（`∀ p ∈ R_n, p.2.1 != v`）

母集団は **H49-0 の正しい作り方**（`R` は自然な標準形の接尾辞、`v` は `R` と独立に全称）。
"""
import sys, io, contextlib, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio, h50
import probe_tiefree_tower as PT
import wcert as wc
from collections import Counter

N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
rng = random.Random(20260829)

# ---- 母集団（H49-0 の正しい作り方）---------------------------------
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
notie = [s for s in scenes if all(p[1] != s[3] for p in s[2])]
print('母集団（H49-0 の正しい作り方）: 場面 **%d 件**、うち**無タイ %d 件 (%.1f%%)**'
      % (len(scenes), len(notie), 100.0 * len(notie) / len(scenes)))
print('   無タイの `v` の分布: %s'
      % dict(sorted(Counter(s[3] for s in notie).items())))
print()
S = notie if len(notie) <= 20000 else rng.sample(notie, 20000)

# ---- hstep の検算 --------------------------------------------------
print('**まず `hstep` の検算**（`X⟦n+1⟧ = (0,v,0) :: graft R (Lift1 (X⟦n⟧) t)`）')
okh = badh = skip = 0
exh = []
for M, j, R, v in S[:4000]:
    X = [(0, v, 0)] + R
    t = R[-1][1] - v
    for n in range(1, 4):
        A = [tuple(c) for c in trio.expand(list(X), n)]
        B = [tuple(c) for c in trio.expand(list(X), n + 1)]
        if not A or len(B) > 400:
            skip += 1
            continue
        pred = [(0, v, 0)] + PT.graft(list(R), PT.Lift1(A, t))
        if [tuple(c) for c in pred] == B:
            okh += 1
        else:
            badh += 1
            if len(exh) < 3:
                exh.append((M, j, R, v, n))
print('   一致 **%d / %d**（省略 %d）' % (okh, okh + badh, skip))
if exh:
    print('   食い違いの例:')
    for M, j, R, v, n in exh:
        print('      v=%d n=%d R=%s' % (v, n, ''.join('(%d,%d,%d)' % q for q in R)))
print()

# ---- 伝播 ----------------------------------------------------------
print('**伝播: `R_n` は `argOK` か / 無タイを保つか**（標本 %d 件）' % len(S))
res = {}
for n in range(1, N + 1):
    ca = cb = tot = 0
    exa, exb = [], []
    for M, j, R, v in S:
        X = [(0, v, 0)] + R
        Y = [tuple(c) for c in trio.expand(list(X), n + 1)]
        if not Y or len(Y) > 500:
            continue
        Rn = list(Y[1:])
        tot += 1
        if all(p[0] > 0 for p in Rn):
            ca += 1
        elif len(exa) < 3:
            exa.append((M, j, R, v, n))
        if all(p[1] != v for p in Rn):
            cb += 1
        elif len(exb) < 3:
            bad = [(i, p) for i, p in enumerate(Rn) if p[1] == v]
            exb.append((M, j, R, v, n, bad[:2]))
    res[n] = (ca, cb, tot, exa, exb)
    print('   n=%-2d  **`argOK R_n` %d / %d (%.2f%%)**   **無タイ %d / %d (%.2f%%)**'
          % (n, ca, tot, 100.0 * ca / max(1, tot), cb, tot, 100.0 * cb / max(1, tot)))
print()
for lab, idx in (('`argOK` が破れる', 3), ('**無タイが破れる**', 4)):
    print('**%s 最小の例**' % lab)
    got = False
    for n in range(1, N + 1):
        for e in res[n][idx]:
            print('   n=%d v=%d R=%s%s'
                  % (e[4], e[3], ''.join('(%d,%d,%d)' % q for q in e[2]),
                     ('  破れる列 %s' % (e[5],)) if len(e) > 5 else ''))
            got = True
            break
        if got:
            break
    if not got:
        print('   **無し（全 n で保たれた）**')
    print()
print('**退化検査**')
wc.audit(S, lambda s: all(p[1] != s[3] for p in
                          list(trio.expand([(0, s[3], 0)] + s[2], 2))[1:]),
         lambda s: True, '無タイ伝播(n=1) vs 恒真')
wc.audit(S, lambda s: all(p[1] != s[3] for p in
                          list(trio.expand([(0, s[3], 0)] + s[2], 2))[1:]),
         lambda s: s[3] == 0, '無タイ伝播(n=1) vs 「v = 0」')
