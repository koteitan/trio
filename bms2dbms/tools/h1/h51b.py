# -*- coding: utf-8 -*-
"""H50 の対照実験 ＋ タイ側の帰納が止まるか。"""
import sys, io, contextlib, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import h51
import trio, h50
import probe_tiefree_tower as PT
from collections import Counter

rng = random.Random(1)
scenes = h51.scenes
notie = h51.notie
tie = [s for s in scenes if not all(p[1] != s[3] for p in s[2])]
print('**陽性対照 1: タイのある場面では伝播が破れるか**（タイ %d 件）' % len(tie))
T = tie if len(tie) <= 6000 else rng.sample(tie, 6000)
for n in (1, 2, 3):
    a = b = tot = 0
    for M, j, R, v in T:
        X = [(0, v, 0)] + R
        Y = [tuple(c) for c in trio.expand(list(X), n + 1)]
        if not Y or len(Y) > 500:
            continue
        Rn = list(Y[1:])
        tot += 1
        a += all(p[0] > 0 for p in Rn)
        b += all(p[1] != v for p in Rn)
    print('   n=%d  `argOK` %d / %d (%.1f%%)   **無タイ %d / %d (%.1f%%)**'
          % (n, a, tot, 100.0 * a / max(1, tot), b, tot, 100.0 * b / max(1, tot)))
print('   ⟹ タイのある場面では**破れる** ⟹ 計器は破れを検出できる')
print()

print('**陽性対照 2: 持ち上げ量 `t` をずらすと伝播が壊れるか**（無タイ %d 件の標本）'
      % len(notie))
S = rng.sample(notie, min(4000, len(notie)))
for dt in (-1, 0, 1):
    ok = tot = 0
    for M, j, R, v in S:
        X = [(0, v, 0)] + R
        t = R[-1][1] - v + dt
        if t < 0:
            continue
        A = [tuple(c) for c in trio.expand(list(X), 1)]
        pred = [(0, v, 0)] + PT.graft(list(R), PT.Lift1(A, t))
        B = [tuple(c) for c in trio.expand(list(X), 2)]
        tot += 1
        ok += ([tuple(c) for c in pred] == B)
    print('   `t %+d` : `hstep` が成立 **%d / %d (%.1f%%)**'
          % (dt, ok, tot, 100.0 * ok / max(1, tot)))
print()

print('**`n` をもっと伸ばす（無タイ、標本 3000）**')
S2 = rng.sample(notie, min(3000, len(notie)))
for n in (6, 8, 10, 12):
    a = b = tot = 0
    for M, j, R, v in S2:
        X = [(0, v, 0)] + R
        Y = [tuple(c) for c in trio.expand(list(X), n + 1)]
        if not Y or len(Y) > 2000:
            continue
        Rn = list(Y[1:])
        tot += 1
        a += all(p[0] > 0 for p in Rn)
        b += all(p[1] != v for p in Rn)
    print('   n=%-3d `argOK` %d / %d   **無タイ %d / %d**' % (n, a, tot, b, tot))
print()

print('**タイ側の帰納は止まるか**（分解 `R = R1 ++ [tie] ++ R2` を繰り返す）')
c = Counter()
mx = 0
for M, j, R, v in (tie if len(tie) <= 6000 else rng.sample(tie, 6000)):
    cur = list(R)
    k = 0
    while True:
        ti = [i for i, p in enumerate(cur) if p[1] == v]
        if not ti:
            break
        k += 1
        cur = cur[:max(ti)]
        if k > 20:
            k = -1
            break
    c[k] += 1
    mx = max(mx, k)
print('   分解を繰り返した回数の分布: %s' % dict(sorted(c.items())))
print('   **最大 %d 回で必ずタイが 0 になる**（打ち切り %d 件）' % (mx, c[-1]))
print('   最後に `R1 = []` になる割合: 測定 —— ', end='')
e = z = 0
for M, j, R, v in (tie if len(tie) <= 6000 else rng.sample(tie, 6000)):
    cur = list(R)
    while True:
        ti = [i for i, p in enumerate(cur) if p[1] == v]
        if not ti:
            break
        cur = cur[:max(ti)]
    e += 1
    z += (len(cur) == 0)
print('**%d / %d (%.1f%%)**' % (z, e, 100.0 * z / max(1, e)))
