# -*- coding: utf-8 -*-
"""**(PREV-3) 仕上げ —— 親の位置の完全分類。**

    ★ 仮説 (PREV-A): `entry C 1 (k-1) = p.2.1` ⟹ 親 = `parent C 1 (k-1)`
    ⟹ `h0` は要るか。`parent C 1 (k-1)` は必ず存在するか。
    ⟹ `前 > p` / `前 < p` の場合は、行 1 の祖先鎖の何段目か。
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r263 import load
from r126 import srow

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def chain1(C, j):
    """行 1 の祖先鎖 j, parent(C,1,j), ... （j を 0 段目とする）"""
    out = [j]; cur = j; seen = {j}
    while True:
        nx = trio.parent(C, 1, cur)
        if nx is None or nx in seen: break
        out.append(nx); seen.add(nx); cur = nx
    return out


M = [[tuple(v) for v in X] for X in load()]
G = {}
un = []
for X in M:
    for k in range(1, len(X)):
        C = X[:k]; p = X[k]; T = X[:k + 1]
        if not any(q[2] > 0 for q in C): continue
        sr = srow(T, k)
        if sr == 0: continue
        c = trio.parent(T, sr, k)
        if c is None: continue
        q = C[k - 1]
        h0 = q[0] < p[0]; h1 = q[1] < p[1]
        rel = '前=p' if q[1] == p[1] else ('前>p' if q[1] > p[1] else '前<p')
        key = '%s / h0=%s' % (rel, h0)
        g = G.setdefault(key, Counter())
        g['n'] += 1
        g['c=k-1'] += (c == k - 1)
        A = trio.parent(C, 1, k - 1) if k >= 1 else None
        g['A なし'] += (A is None)
        g['c=A'] += (A is not None and c == A)
        ch = chain1(C, k - 1)
        g['c が行1祖先鎖上'] += (c in ch)
        if c in ch: g['鎖の段 %d' % min(ch.index(c), 3)] += 1
        elif len(un) < 8:
            un.append((k, sr, c, ch[:5], q, p, h0))
        gg = G.setdefault(rel, Counter())
        gg['n'] += 1; gg['c=k-1'] += (c == k - 1)
        gg['c=A'] += (A is not None and c == A)
        gg['c が行1祖先鎖上'] += (c in ch)
        gg['h0'] += h0

print('== 親の位置の完全分類（開いている場面 8,042 件）==')
print('%-18s %8s %10s %10s %14s %10s' % ('群', '分母', 'c=k-1', 'c=A(前の行1親)', 'c が行1祖先鎖上', 'h0'))
for key in ('前=p', '前>p', '前<p'):
    g = G.get(key)
    if not g: continue
    n = g['n']
    print('%-18s %8d %9.4f%% %9.4f%% %13.4f%% %9.4f%%'
          % (key, n, pct(g['c=k-1'], n), pct(g['c=A'], n), pct(g['c が行1祖先鎖上'], n), pct(g['h0'], n)))

print()
print('== h0 で分けたとき ==')
print('%-18s %8s %10s %10s %14s %10s' % ('群', '分母', 'c=k-1', 'c=A', 'c が行1祖先鎖上', 'A なし'))
for key in sorted(k for k in G if '/' in k):
    g = G[key]; n = g['n']
    print('%-18s %8d %9.4f%% %9.4f%% %13.4f%% %9.4f%%'
          % (key, n, pct(g['c=k-1'], n), pct(g['c=A'], n), pct(g['c が行1祖先鎖上'], n), pct(g['A なし'], n)))

print()
print('== 鎖の段の分布（c が鎖上のとき）==')
for key in sorted(k for k in G if '/' in k):
    g = G[key]
    tot = g['c が行1祖先鎖上']
    if not tot: continue
    print('  %-18s: 0段(=k-1) %.2f%% / 1段 %.2f%% / 2段 %.2f%% / 3段以上 %.2f%%'
          % (key, pct(g['鎖の段 0'], tot), pct(g['鎖の段 1'], tot), pct(g['鎖の段 2'], tot), pct(g['鎖の段 3'], tot)))

print()
print('  ⛔ 鎖上ですらない例（先頭 8 件）:')
for (k, sr, c, ch, q, p, h0) in un:
    print('    k=%d srow=%d 親c=%d 鎖=%s 前=%s p=%s h0=%s' % (k, sr, c, ch, q, p, h0))
if not un: print('    （無し）')
