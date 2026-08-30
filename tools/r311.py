# -*- coding: utf-8 -*-
"""**(ROW2-2)(ROW2-3) —— 残差群の形。★ 「末尾の行 1 = 根の行 1」か。**"""
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r260 import reach
from r111 import tiefree
from r310 import build_plus, hr0s, row2, orphan, lev0, green

pct = lambda a, b: 100.0 * a / b if b else float('nan')

t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
SP = build_plus(RC, (1, 2, 3), rounds=3, cap=400000)
print('|Reach+| = %d' % len(SP))

# ⚠ まず根の分布（正規化の罠の確認）
rz = Counter(); rv = Counter()
for Q in SP:
    if len(Q) < 2: continue
    rz['根の行 2 = %d' % Q[0][2]] += 1
    rv['根の行 1 = %s' % (Q[0][1] if Q[0][1] <= 4 else '>=5')] += 1
print()
print('== ⚠ 母集団の根の分布（罠の確認）==')
for k in sorted(rz): print('   %-14s %8d  %7.4f%%' % (k, rz[k], pct(rz[k], sum(rz.values()))))
for k in sorted(rv): print('   %-14s %8d  %7.4f%%' % (k, rv[k], pct(rv[k], sum(rv.values()))))

core = []
for Q in SP:
    Q = list(Q)
    if len(Q) < 2: continue
    if hr0s(Q) and row2(Q) and orphan(Q): core.append(Q)
n = len(core)
print()
print('== ★ 残差 %d 件の形 ==' % n)
c = Counter()
for Q in core:
    L = len(Q); last = Q[L - 1]; root = Q[0]
    c['srow=%d' % srow(Q, L - 1)] += 1
    c['★ 末尾の行1 = 根の行1'] += (last[1] == root[1])
    c['  末尾の行1 > 根の行1'] += (last[1] > root[1])
    c['  末尾の行1 < 根の行1'] += (last[1] < root[1])
    c['★ 末尾の行2 = 根の行2'] += (last[2] == root[2])
    c['末尾の行2 = 0'] += (last[2] == 0)
    c['|Q| = %s' % (L if L <= 10 else '>=11')] += 1
    ps = [j for j in range(L) if Q[j][2] > 0]
    d = L - 1 - max(ps)
    c['行2列との距離 %s' % (d if d <= 3 else '>=4')] += 1
    c['行 2 列の数 %s' % (len(ps) if len(ps) <= 2 else '>=3')] += 1
    c['⛔ D_v 型 (i,i,1) がある'] += any(q[0] == q[1] and q[2] > 0 for q in Q)
    c['行 0 が 0,1,2,… の階段'] += all(Q[j][0] == j for j in range(L))
    c['★ 根と同じ行1 の列が 2 本以上'] += (sum(1 for q in Q if q[1] == root[1]) >= 2)
    c['★ argOK（根以外の行0が正）'] += all(q[0] > 0 for q in Q[1:])
for k in sorted(c):
    print('   %-30s %7d  %8.4f%%' % (k, c[k], pct(c[k], n)))

print()
print('== ⚠ 対照: 残差でない群（(a)∧(b) は満たすが孤児でない）==')
c2 = Counter(); m = 0
for Q in SP:
    Q = list(Q)
    if len(Q) < 2: continue
    if not (hr0s(Q) and row2(Q)) or orphan(Q): continue
    m += 1; last = Q[len(Q) - 1]; root = Q[0]
    c2['末尾の行1 = 根の行1'] += (last[1] == root[1])
    c2['末尾の行1 > 根の行1'] += (last[1] > root[1])
    c2['末尾の行1 < 根の行1'] += (last[1] < root[1])
for k in sorted(c2):
    print('   %-24s %8d  %8.4f%%' % (k, c2[k], pct(c2[k], m)))
print('   （分母 %d）' % m)

print()
print('   ★ 残差の例（|Q| 小さい順に 6 件）:')
for Q in sorted(core, key=len)[:6]:
    print('     |Q|=%d srow=%d 根=%s 末尾=%s  %s'
          % (len(Q), srow(Q, len(Q) - 1), Q[0], Q[-1], ' '.join('(%d,%d,%d)' % q for q in Q)))
print('（%.1f 秒）' % (time.time() - t0))
