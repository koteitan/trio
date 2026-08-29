# -*- coding: utf-8 -*-
"""**課題 H55 —— `MliftR`（閾値を `v0-1` から `v0` へ 1 段）を測る。**

    coneVR X w j := ∀ y, RTG nextrel0 y j → **y != 0** → w < entry X 1 y
    mliftR X w d := 行 1 に `coneVR X w j` なら `d` を足す
    証明ずみ: `w < entry X 1 0` なら `mliftR X w d ∈ W (m+2d)`（`mlift` と一致）
    核 `MliftR`: **`w = entry X 1 0` でも運ぶか**（`∀w` の形）

母集団は H49-0 の正しい作り方（`R` は自然、`v` は独立に全部）。
"""
import sys, io, contextlib, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import h51
import trio, h53
import probe_tiefree_tower as PT
from collections import Counter

rng = random.Random(20260829)
scenes = h51.scenes
S = scenes if len(scenes) <= 20000 else rng.sample(scenes, 20000)


def coneVR(X, w):
    """{ j | 根以外の行 0 祖先が全部 行 1 > w }。根 j=0 は常に入る。"""
    out = set()
    for j in range(len(X)):
        anc = [y for y in PT.anc0(X, j) if y != 0]
        if all(w < X[y][1] for y in anc):
            out.add(j)
    return out


def mliftR(X, w, d):
    C = coneVR(X, w)
    return [(q[0], q[1] + (d if k in C else 0), q[2]) for k, q in enumerate(X)]


print('母集団: 場面 **%d 件**（標本 %d）' % (len(scenes), len(S)))
print()

# ---- H55-a ---------------------------------------------------------
print('**H55-a `w = v0-1` と `w = v0` で錐がどう変わるか**')
c = Counter()
cw = Counter()
for M, j, R, v in S:
    X = [(0, v, 0)] + R
    v0 = X[0][1]
    a = coneVR(X, v0 - 1) if v0 >= 1 else None
    b = coneVR(X, v0)
    if a is None:
        c['`v0 = 0`（`w = v0-1` が取れない）'] += 1
        cw[('v0=0', len(b))] += 1
        continue
    d = a - b
    c['**錐が変わらない**（既存定理でそのまま）' if not d
      else '錐が %d 本縮む' % len(d)] += 1
    cw[('v0>=1', len(b))] += 1
n = sum(c.values())
for k, v2 in c.most_common(6):
    print('   %-38s %5d (%.1f%%)' % (k, v2, 100.0 * v2 / n))
print()
print('   ⚠ `v0 = 0` では `w = v0-1` が自然数で取れない（`0-1 = 0` になる）ので')
print('      **既存定理 `mliftR_mem_W_of_lt` は `v0 = 0` では 1 件も使えない**。')
c0 = c['`v0 = 0`（`w = v0-1` が取れない）']
print('      該当 **%d / %d (%.1f%%)**' % (c0, n, 100.0 * c0 / n))
print()

# ---- w を振る -------------------------------------------------------
print('**閾値 `w` を上げると錐はどう縮むか**（`|coneVR|` の平均）')
tab = Counter()
cnt = Counter()
for M, j, R, v in S[:4000]:
    X = [(0, v, 0)] + R
    v0 = X[0][1]
    for dw in (-2, -1, 0, 1, 2, 5):
        w = v0 + dw
        if w < 0:
            continue
        tab[dw] += len(coneVR(X, w))
        cnt[dw] += 1
print('   | `w` | 平均 `|coneVR|` |')
print('   |---|--:|')
for dw in sorted(tab):
    print('   | `v0%+d` | %.2f |' % (dw, tab[dw] / cnt[dw]))
print('   （`j = 0`（根）は `w` に依らず必ず入る ⟹ 下限は 1）')
print()

# ---- H55-b ---------------------------------------------------------
print('**H55-b `mliftR X v0 d` と `mliftR X (v0-1) d` の差**')
cb = Counter()
same = 0
for M, j, R, v in S:
    X = [(0, v, 0)] + R
    v0 = X[0][1]
    if v0 < 1:
        continue
    d = R[-1][1] - v
    A = mliftR(X, v0 - 1, d)
    B = mliftR(X, v0, d)
    diff = [(k, p, q) for k, (p, q) in enumerate(zip(A, B)) if p != q]
    cb[('差の列 %d 本' % len(diff),
        '行 1 だけ' if all((p[0], p[2]) == (q[0], q[2]) for _, p, q in diff)
        else '行 0 か行 2 も')] += 1
    if not diff:
        same += 1
for k, v2 in cb.most_common(6):
    print('   %-34s %5d' % (str(k), v2))
print()
print('   **`Lift1` vs `mlift` の差（H53 §135）と同じものか**')
eq = tot = 0
for M, j, R, v in S:
    X = [(0, v, 0)] + R
    v0 = X[0][1]
    if v0 < 1:
        continue
    d = R[-1][1] - v
    tot += 1
    eq += (PT.Lift1(X, d) == mliftR(X, v0, d) and
           [(q[0], q[1] + (d if PT.amin(X, k) >= v0 else 0), q[2])
            for k, q in enumerate(X)] == mliftR(X, v0 - 1, d))
print('   `Lift1 X d == mliftR X v0 d` かつ `mlift X (v0-1) d == mliftR X (v0-1) d`:'
      ' **%d / %d**' % (eq, tot))
print()

# ---- H55-c ---------------------------------------------------------
print('**H55-c 健全性の傍証**')
ok = tot = 0
for M, j, R, v in S:
    X = [(0, v, 0)] + R
    v0 = X[0][1]
    d = R[-1][1] - v
    B = mliftR(X, v0, d)
    tot += 1
    ok += (len(B) == len(X) and
           all((a[0], a[2]) == (b[0], b[2]) and a[1] <= b[1] + d
               for a, b in zip(B, X)) and
           2 * B[0][1] + B[0][2] == 2 * (X[0][1] + d) + X[0][2])
print('   `mliftR X v0 d` は 行 0・行 2・長さを保ち、根の `lev` はちょうど `+2d`:'
      ' **%d / %d**' % (ok, tot))
print('   ⟹ 根の `lev` は `w` に依らず必ず `+2d`（根は常に錐に入る）')
print('   ⟹ 唯一の健全な非所属判定 `lev M[0] > u` は `w` を区別できない')
print('   ⟹ **原理的に反例は出せない**（教訓 13）')
