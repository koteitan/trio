# -*- coding: utf-8 -*-
"""**課題 H49 —— タイの 3.8% を割る。**

H48 の母集団（`TowerOK2` の場面 624 本 × `v = 0..4` の持ち上げ = 3120 件）のうち
**`TieFree` が破れる 120 件**（＝ `R` に行 1 = `v` の列がある）を調べる。
"""
import sys, io, contextlib
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import h48
import trio
import probe_tiefree_tower as PT
import wcert as wc
from collections import Counter

S2 = [s for s in h48.sites if s[6] == 2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def hp(S, j):
    return trio.parent([tuple(c) for c in S], srow(S, j), j) is not None


def shift(R, v):
    return [(p[0], p[1] + v, p[2]) for p in R]


# 母集団（H48 §104 と同じ）
inst = []
for row, M, ocf, v0, z0, R, sr in S2:
    for v in range(5):
        Rv = shift(R, v)
        Mv = [(0, v, 0)] + Rv
        j = len(Rv) - 1
        if srow(Rv, j) != 2 or hp(Rv, j) or not hp(Mv, len(Rv)):
            continue
        X = [tuple(c) for c in trio.expand(list(Mv), 1)]
        if not X or len(X) > 400:
            continue
        try:
            tf = PT.tiefree(X)
        except AssertionError:
            continue
        inst.append((row, ocf, v, Rv, Mv, tf))
tie = [x for x in inst if not x[5]]
print('母集団 **%d 件**（`TowerOK2` の場面 × `v=0..4`）、うち **タイ %d 件 (%.1f%%)**'
      % (len(inst), len(tie), 100.0 * len(tie) / len(inst)))
print()

# ---- H49-a-1 タイの本数 -------------------------------------------
print('**H49-a-1 タイの本数の分布**')
c = Counter(sum(1 for p in R if p[1] == v) for row, ocf, v, R, M, tf in tie)
for k in sorted(c):
    print('   %d 本 : **%d 件 (%.1f%%)**' % (k, c[k], 100.0 * c[k] / len(tie)))
print()

# ---- H49-a-2 タイは持ち上げの壁か ---------------------------------
print('**H49-a-2 タイの列は `le1` 錐（`Lift1` のマスク）に入るか / 壁になるか**')
cc = Counter()
wall = Counter()
for row, ocf, v, R, M, tf in tie:
    X = [tuple(c) for c in M]           # X = (0,v,z) :: R（展開前で見る）
    C = PT.cone(X)                      # {j | le1 X 0 j}
    ti = [i for i, p in enumerate(R) if p[1] == v]
    for i in ti:
        cc['タイの列が `le1` 錐に**入る**' if (i + 1) in C
           else 'タイの列は `le1` 錐に**入らない**'] += 1
    last = max(ti)
    right = [i for i in range(last + 1, len(R))]
    inr = [i for i in right if (i + 1) in C]
    wall[('右に列が無い' if not right else
          ('**右も全部 錐の外**' if not inr else '右に錐の中の列がある(%d/%d)'
           % (len(inr), len(right))))] += 1
for k, v2 in cc.most_common():
    print('   %-36s %5d' % (k, v2))
print()
print('   **最後のタイより右の列は錐に入るか**（＝ タイが壁になるか）')
for k, v2 in wall.most_common():
    print('   %-36s %5d (%.1f%%)' % (k, v2, 100.0 * v2 / len(tie)))
print()

# ---- H49-a-3 R1 / R2 の分解 ----------------------------------------
print('**H49-a-3 最後のタイで `R = R1 ++ [tie] ++ R2` と切ったとき**')
sp = Counter()
for row, ocf, v, R, M, tf in tie:
    ti = [i for i, p in enumerate(R) if p[1] == v]
    t = max(ti)
    R1, R2 = R[:t], R[t + 1:]
    sp['`R2` にタイが無い'] += all(p[1] != v for p in R2)
    sp['`R1` のタイの本数が真に減る'] += (sum(1 for p in R1 if p[1] == v) < len(ti))
    sp['`R1` が `argOK`'] += all(p[0] > 0 for p in R1)
    sp['`R2` が `argOK`'] += all(p[0] > 0 for p in R2)
    sp['`R2` != []'] += (len(R2) > 0)
    sp['`R1` != []'] += (len(R1) > 0)
    if R2:
        sp['`R2` の末尾が `R2` 内で孤児'] += (not hp(R2, len(R2) - 1))
        sp['`srow R2 (末尾) = 2`'] += (srow(R2, len(R2) - 1) == 2)
print('   | 性質 | 成り立つ / %d |' % len(tie))
print('   |---|--:|')
for k in ('`R1` != []', '`R2` != []', '`R1` が `argOK`', '`R2` が `argOK`',
          '`R2` にタイが無い', '`R1` のタイの本数が真に減る',
          '`R2` の末尾が `R2` 内で孤児', '`srow R2 (末尾) = 2`'):
    print('   | %s | **%d (%.1f%%)** |' % (k, sp[k], 100.0 * sp[k] / len(tie)))
print()

# ---- H49-b 共通形 ---------------------------------------------------
print('**H49-b タイの 120 件の共通形**')
for nm, g in (('タイの列の `z`（行 2）', lambda R, v, i: R[i][2]),
              ('タイの列の行 0 − 根の行 0', lambda R, v, i: R[i][0]),
              ('タイの列の位置（先頭/中/末尾）',
               lambda R, v, i: '先頭' if i == 0 else
               ('末尾' if i == len(R) - 1 else '中')),
              ('タイの本数', lambda R, v, i: sum(1 for p in R if p[1] == v))):
    cc2 = Counter()
    for row, ocf, v, R, M, tf in tie:
        for i, p in enumerate(R):
            if p[1] == v:
                cc2[g(R, v, i)] += 1
    print('   %-26s %s' % (nm, dict(sorted(cc2.items(), key=str))))
print()
print('   **最小の行 331 の構造**')
e = [x for x in tie if x[0] == 331 and x[2] == 0]
if e:
    row, ocf, v, R, M, tf = e[0]
    X = [tuple(c) for c in M]
    C = PT.cone(X)
    print('      OCF = %s' % ocf)
    print('      `X = (0,%d,0) :: R` = %s' % (v, ''.join('(%d,%d,%d)' % q for q in X)))
    print('      `le1` 錐（`Lift1` のマスク）= %s' % sorted(C))
    print('      `coneV(v-1)` 錐 = %s'
          % sorted(j for j in range(len(X)) if PT.amin(X, j) >= X[0][1]))
    for j, q in enumerate(X):
        print('        j=%d %s  行0祖先=%s  amin=%d  le1=%s'
              % (j, q, PT.anc0(X, j), PT.amin(X, j), j in C))
print()

# ---- H49-c d1 との交差 ---------------------------------------------
print('**H49-c 持ち上げ量 `d1 = w - v` とタイの交差**')
cx = Counter()
for row, ocf, v, R, M, tf in inst:
    d1 = R[-1][1] - v
    cx[(min(d1, 3), 'タイ' if not tf else '`TieFree`')] += 1
print('   | `d1` | `TieFree` | **タイ** |')
print('   |--:|--:|--:|')
for d in sorted({k[0] for k in cx}):
    print('   | %s | %d | **%d** |'
          % (d, cx[(d, '`TieFree`')], cx[(d, 'タイ')]))
print()
print('**退化検査**')
wc.audit(inst, lambda x: not x[5],
         lambda x: any(p[1] == x[2] for p in x[3]), 'タイ判定 vs 「行 1 = `v` の列がある」')
wc.audit(inst, lambda x: not x[5], lambda x: len(x[3]) <= 3, 'タイ判定 vs 「`|R|` <= 3」')
wc.audit(inst, lambda x: not x[5], lambda x: x[3][-1][1] - x[2] >= 2,
         'タイ判定 vs 「`d1` >= 2」')
