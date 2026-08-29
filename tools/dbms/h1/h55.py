# -*- coding: utf-8 -*-
"""**課題 H54 —— `Row1DownLocal` / `Row1DownRoot0` を測る。**

    `mlift X v0 d` の行 1 = `Lift1 X d` の行 1 + (`coneV \\ le1` の列なら `d`)
    行 0・行 2・長さは完全一致（H53 §135 の実測）

母集団は H49-0 の正しい作り方（`R` は自然、`v` は `R` と独立に全部振る）。
"""
import sys, io, contextlib, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import h51
import trio, h50, h53
import probe_tiefree_tower as PT
from collections import Counter

rng = random.Random(20260829)
scenes = h51.scenes


def mlift(X, v0, d):
    return [(q[0], q[1] + (d if PT.amin(X, k) >= v0 else 0), q[2])
            for k, q in enumerate(X)]


def gap(X, v):
    C = PT.cone(X)
    return [k for k in range(len(X)) if PT.amin(X, k) >= v and k not in C]


tie = [s for s in scenes if gap([(0, s[3], 0)] + s[2], s[3])]
print('母集団: 場面 **%d 件**（`R` は自然、`v` は独立に全部）' % len(scenes))
print('   `coneV \\ le1` が空でない（＝ `Row1Down*` が要る）: **%d (%.1f%%)**'
      % (len(tie), 100.0 * len(tie) / len(scenes)))
print()

# ---- R72-d の訂正の確認 --------------------------------------------
print('**R72-d の訂正の確認: `R` ごとに「タイになる `v`」が存在するか**')
byR = {}
for M, j, R, v in scenes:
    byR.setdefault(tuple(R), []).append(v)
n1 = n2 = 0
for R, vs in byR.items():
    n1 += 1
    if any(gap([(0, v, 0)] + list(R), v) for v in vs):
        n2 += 1
print('   相異なる `R` %d 本のうち、**タイになる `v` がある: %d (%.1f%%)**'
      % (n1, n2, 100.0 * n2 / n1))
print('   ⟹ `Wstar` は `∀v` なので、**その `R` ではタイの枝を通る必要がある**')
print()

# ---- H54-a ---------------------------------------------------------
print('**H54-a どちらの版が要るか**')
c = Counter()
for M, j, R, v in tie:
    c['`Row1DownRoot0`（根の行 1 = 0）' if v == 0
      else '`Row1DownLocal`（根の行 1 >= 1）'] += 1
for k, v2 in c.most_common():
    print('   %-34s **%5d (%.1f%%)**' % (k, v2, 100.0 * v2 / len(tie)))
print('   `v` の分布: %s' % dict(sorted(Counter(s[3] for s in tie).items())))
print()

# ---- H54-b ---------------------------------------------------------
print('**H54-b `coneV \\ le1` の列の性質（`∀v` の母集団で）**')
cn = Counter()
cv = Counter()
cp = Counter()
for M, j, R, v in tie:
    X = [(0, v, 0)] + R
    g = gap(X, v)
    cn[len(g)] += 1
    for k in g:
        cv['行 1 = `v`' if X[k][1] == v else '行 1 > `v`'] += 1
        cp['先頭（根の隣）' if k == 1 else
           ('末尾' if k == len(X) - 1 else '中')] += 1
print('   本数の分布: %s' % dict(sorted(cn.items())))
print('   **最大 %d 本**' % max(cn))
print('   その列の行 1: %s' % dict(cv))
print('   `R` の中の位置: %s' % dict(cp))
print('   `v` 別の最大本数:')
mx = {}
for M, j, R, v in tie:
    g = gap([(0, v, 0)] + R, v)
    mx[v] = max(mx.get(v, 0), len(g))
print('      %s' % dict(sorted(mx.items())))
print()

# ---- H54-c ---------------------------------------------------------
print('**H54-c 健全性の傍証 —— 反例は作れるか**')
print('   §R33-0 / H36 §8.3: **健全な非所属判定は `lev M[0] > u` だけ**。')
same = diff = 0
for M, j, R, v in (tie if len(tie) <= 8000 else rng.sample(tie, 8000)):
    X = [(0, v, 0)] + R
    d = R[-1][1] - v
    L = PT.Lift1(X, d)
    Mm = mlift(X, v, d)
    if (2 * L[0][1] + L[0][2]) == (2 * Mm[0][1] + Mm[0][2]):
        same += 1
    else:
        diff += 1
print('   `lev (Lift1 X d) 0 == lev (mlift X v d) 0`: **%d / %d**' % (same, same + diff))
print('   （根は両方の錐に反射的に入るので、行 1 は必ず同じだけ上がる）')
print()
print('   ⟹ **唯一の健全な反証器が両者を区別できない ⟹ 原理的に反例は出せない**（教訓 13）。')
print()
print('   意味論の傍証: `Lift1 X d` は `mlift X v d` の行 1 を数本**下げた**もの。')
print('   BMS の順序では行 1 を下げると行列は小さくなるので、段が上がらないのは自然。')
print('   実測: 行 0・行 2・長さが完全一致するのは:')
ok = tot = 0
for M, j, R, v in (tie if len(tie) <= 8000 else rng.sample(tie, 8000)):
    X = [(0, v, 0)] + R
    d = R[-1][1] - v
    L = PT.Lift1(X, d)
    Mm = mlift(X, v, d)
    tot += 1
    ok += (len(L) == len(Mm) and
           all((a[0], a[2]) == (b[0], b[2]) and a[1] <= b[1]
               for a, b in zip(L, Mm)))
print('      行 0・行 2 が一致 かつ `Lift1` の行 1 <= `mlift` の行 1: **%d / %d**'
      % (ok, tot))
