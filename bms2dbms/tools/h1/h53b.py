# -*- coding: utf-8 -*-
"""H52 の続き: シート全数で連鎖を通し、2 行 / 3 行の境目を出す。"""
import sys, io, contextlib
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import r66
import trio, h50, h53
from collections import Counter

T = r66.load_ladder()
print('**シート %d 行を連鎖に通す**' % len(T))
depth = Counter()
branch = Counter()
bad = []
for row, M, ocf in T:
    cur = [tuple(c) for c in M]
    k = 0
    while cur:
        A, P = h53.split_lastMin(cur)
        p0, R = P[0], P[1:]
        Rp = [(q[0] - p0[0], q[1], q[2]) for q in R]
        if not (h53.rsum(A, P) and all(P[0][0] < q[0] for q in P[1:])
                and all(q[0] > 0 for q in Rp)):
            bad.append((row, ocf, k, cur))
            break
        v, z = p0[1], p0[2]
        if not Rp:
            branch['節 1（底）`R\' = []`'] += 1
        else:
            j = len(Rp) - 1
            sr = h50.srow(Rp, j)
            dom = (2 * Rp[j][1] + Rp[j][2] > 0) and not h50.hp(Rp, j)
            X = [(0, v, z)] + Rp
            rev = trio.parent([tuple(q) for q in X], sr, len(Rp)) is not None
            if not dom:
                branch['`domT` 偽 ⟹ 節 2（展開）'] += 1
            elif not rev:
                branch['復活しない ⟹ 節 3（graft）'] += 1
            elif sr <= 1:
                branch['**`TowerOK1`**（srow<=1、証明ずみ）'] += 1
            else:
                notie = all(q[1] != v for q in Rp)
                strict = all(v < q[1] for q in Rp)
                branch['**`TowerOK2` / 狭義**' if strict else
                       ('**`TowerOK2` / 無タイ**' if notie else
                        '**`TowerOK2` / タイ**')] += 1
        cur = A
        k += 1
    depth[k] += 1
print('   **仮定が破れた行: %d 件**%s' % (len(bad), '' if not bad else str(bad[:2])))
print('   降りきるまでの段数の分布: %s' % dict(sorted(depth.items())))
print('   **最大 %d 段**' % max(depth))
print()
tot = sum(branch.values())
print('**全 %d 個の節点が落ちる枝**' % tot)
print('| 枝 | 件数 | 割合 |')
print('|---|--:|--:|')
for k, v in branch.most_common():
    print('| %s | %d | %.1f%% |' % (k, v, 100.0 * v / tot))
print()
n2 = sum(v for k, v in branch.items() if 'TowerOK2' in k)
print('   **`TowerOK2` に落ちるのは %d / %d (%.1f%%)**' % (n2, tot, 100.0 * n2 / tot))
print()
print('**2 行 / 3 行の境目**')
print('   `srow = 2` ⟺ その列の行 2 が非零 ⟺ **3 行目を使っている**')
c = Counter()
for row, M, ocf in T:
    cur = [tuple(c2) for c2 in M]
    while cur:
        A, P = h53.split_lastMin(cur)
        p0, R = P[0], P[1:]
        Rp = [(q[0] - p0[0], q[1], q[2]) for q in R]
        if Rp:
            j = len(Rp) - 1
            sr = h50.srow(Rp, j)
            c[(sr, '行 2 に 1 がある' if any(q[2] > 0 for q in Rp) else '行 2 ≡ 0')] += 1
        cur = A
for k in sorted(c):
    print('   `srow` 末尾 = %d かつ %s : %d' % (k[0], k[1], c[k]))
print()
print('   `D_1` と 2 行版の比較:')
for lab, M in (('`D_1` = 3 行版', [(0, 0, 0), (1, 1, 1)]),
               ('2 行版（z を 0 に）', [(0, 0, 0), (1, 1, 0)])):
    A, P = h53.split_lastMin(M)
    p0, R = P[0], P[1:]
    Rp = [(q[0] - p0[0], q[1], q[2]) for q in R]
    sr = h50.srow(Rp, len(Rp) - 1)
    print('      %-18s R\'=%s  srow=%d ⟹ **%s**'
          % (lab, h53.sh(Rp), sr, 'TowerOK2（3 行で初めて要る）' if sr == 2
             else 'TowerOK1（2 行で済む・証明ずみ）'))
