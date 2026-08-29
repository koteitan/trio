# -*- coding: utf-8 -*-
"""**H53-d —— タイを戻すのに何が要るか。**"""
import sys, io, contextlib, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import h51
import trio, h50, h53
import probe_tiefree_tower as PT
from collections import Counter

rng = random.Random(3)
tie = [s for s in h51.scenes if not all(p[1] != s[3] for p in s[2])]
S = tie if len(tie) <= 6000 else rng.sample(tie, 6000)
print('タイの場面 %d 件（標本 %d）' % (len(tie), len(S)))
print()

print('**(1) `coneV \\ le1` の正体**（`TieFree` が破れる列）')
c = Counter()
for M, j, R, v in S:
    X = [(0, v, 0)] + R
    C1 = PT.cone(X)
    gap = [k for k in range(len(X)) if PT.amin(X, k) >= v and k not in C1]
    tset = {i + 1 for i, p in enumerate(R) if p[1] == v}
    c[('はみ出す列 %d 本' % len(gap),
       'タイの列だけ' if set(gap) == tset else
       ('タイを含むがもっと有る' if tset <= set(gap) else '**タイ以外**'))] += 1
for k, v2 in c.most_common(6):
    print('   %-38s %5d' % (str(k), v2))
print()

print('**(2) `Lift1` と `mlift` の差**')
c2 = Counter()
for M, j, R, v in S:
    X = [(0, v, 0)] + R
    t = R[-1][1] - v
    C1 = PT.cone(X)
    L = [(q[0], q[1] + (t if k in C1 else 0), q[2]) for k, q in enumerate(X)]
    Mm = [(q[0], q[1] + (t if PT.amin(X, k) >= v else 0), q[2])
          for k, q in enumerate(X)]
    c2[sum(1 for a, b in zip(L, Mm) if a != b)] += 1
print('   食い違う列の本数の分布: %s' % dict(sorted(c2.items())))
print()

print('**(3) `R` の展開 `R⟦n⟧` はタイを失うか**（clause 2 の道）')
c3 = Counter()
for M, j, R, v in S:
    for n in (1, 2, 3):
        Y = [tuple(q) for q in trio.expand(list(R), n)]
        if not Y or len(Y) > 300:
            c3[(n, '長さ切れ')] += 1
            continue
        c3[(n, '**タイが消える**' if all(p[1] != v for p in Y)
            else 'タイが残る')] += 1
for k in sorted(c3, key=str):
    print('   n=%s %-16s %5d' % (k[0], k[1], c3[k]))
print()

print('**(4) `graft R z`（clause 3）でタイは消えるか**')
c4 = Counter()
for M, j, R, v in S:
    ti = [i for i, p in enumerate(R) if p[1] == v]
    c4['タイが末尾（`dropLast` で消える）' if max(ti) == len(R) - 1
       else '**タイは `R.dropLast` に残る**'] += 1
for k, v2 in c4.most_common():
    print('   %-36s %5d (%.1f%%)' % (k, v2, 100.0 * v2 / len(S)))
print()

print('**(5) 根の `v` を変えると（参考）**')
c5 = Counter()
for M, j, R, v in S:
    ok = [w for w in range(9) if h50.ok_scene(R, w, 0)]
    nt = [w for w in ok if all(p[1] != w for p in R)]
    c5[('場面になる `v` の個数 %d' % len(ok),
        '無タイになる `v` がある' if nt else '**どの `v` でもタイ**')] += 1
for k, v2 in c5.most_common(6):
    print('   %-46s %5d' % (str(k), v2))
print()

print('**(6) タイの列の位置（末尾からの距離）**')
c6 = Counter()
for M, j, R, v in S:
    ti = [i for i, p in enumerate(R) if p[1] == v]
    c6[min(len(R) - 1 - max(ti), 5)] += 1
print('   %s' % dict(sorted(c6.items())))
