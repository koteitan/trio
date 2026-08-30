# -*- coding: utf-8 -*-
"""**(ROW2-1)(2)(3) 修正版 —— 根が `(0,v,z)`（`v>0` / `z>0`）の `Q` を必ず混ぜる。**

## ⛔ r309 の欠陥（自己申告、正規化の罠 4 回目）

シート由来の `Q` の根は**全部 `(0,0,0)`** ⟹ 根の行 1 = 0。
`srow >= 1` の孤児は「**行 0 の祖先すべてで行 1（行 2）が末尾以上**」を要求し、
`hr0` の下では**根が必ず行 0 の祖先**になるので、**根の行 1 = 0 なら孤児は原理的に起きません**。
⟹ **`(a)∧(c) = 0` は測定ではなく定義**でした。

## ★ 直し方: 健全に根を上げる

    `Reach+` := `Reach`（`Om_mem_W` ＋ `oper_closed` ＋ 接頭辞）に、
    **仮定ゼロの持ち上げ 4 本**（狭義／無タイ／TieFree／行2≡0）を当てて `oper`・接頭辞で閉じたもの。
    ⟹ **`Reach+ ⊆ W` は健全**で、**根が `(0,v,0)`（`v>0`）の元を含みます**。

⟹ ★ **根の lev（＝ `2*v+z`）が 0 の群と正の群を、必ず並べて出します**。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio, itertools
from collections import Counter
from r263 import load
from r126 import srow
from r113 import Lift1
from r260 import reach
from r111 import tiefree

pct = lambda a, b: 100.0 * a / b if b else float('nan')
hr0s = lambda Q: all(Q[0][0] < Q[j][0] for j in range(1, len(Q)))
row2 = lambda Q: any(p[2] > 0 for p in Q)
lev0 = lambda Q: 2 * Q[0][1] + Q[0][2]


def orphan(Q):
    j = len(Q) - 1
    return trio.parent(Q, srow(Q, j), j) is None


def green(X):
    if not X or X[0][0] != 0: return None
    R = X[1:]; v = X[0][1]
    if all(p[2] == 0 for p in X): return 'z'
    if not all(p[0] > 0 for p in R): return None
    if all(v < p[1] for p in R): return 's'
    if all(p[1] != v for p in R): return 'n'
    if v >= 1 and tiefree(list(X)): return 't'
    return None


def build_plus(seeds, ns, rounds, cap):
    S = set(seeds)
    for _ in range(rounds):
        new = set()
        for X in list(S):
            if len(S) + len(new) > cap: break
            if green(list(X)):
                for d in (1, 2):
                    L = tuple(tuple(q) for q in Lift1(list(X), d))
                    if L not in S: new.add(L)
        S |= new
        new2 = set()
        for X in list(S):
            if len(S) + len(new2) > cap: break
            for n in ns:
                try: T = tuple(tuple(q) for q in trio.expand([list(q) for q in X], n))
                except Exception: continue
                if T and T not in S: new2.add(T)
        for T in list(new2):
            for k in range(1, len(T) + 1): new2.add(T[:k])
        S |= new2
    return S


def scan(QS, tag, examples=0):
    G = {}
    ex = []
    for Q in QS:
        Q = list(Q)
        if len(Q) < 2: continue
        a = hr0s(Q); b = row2(Q); o = orphan(Q)
        key = '根 lev=0' if lev0(Q) == 0 else '根 lev>0'
        for kk in ('全', key):
            g = G.setdefault(kk, Counter())
            g['n'] += 1
            g['a'] += a; g['b'] += b; g['c'] += o
            g['ab'] += (a and b); g['ac'] += (a and o)
            g['★残差'] += (a and b and o)
            if a and b: g['ab分母'] += 1; g['ab中の孤児'] += o
            if a and b and o: g['srow=%d' % srow(Q, len(Q) - 1)] += 1
        if a and b and o and len(ex) < examples:
            ex.append(Q)
    print('  [%s]' % tag)
    print('     %-10s %8s %9s %9s %9s %11s %14s' % ('群', '分母', '(a)hr0', '(b)行2', '(c)孤児', '★残差(abc)', '(a∧b)中の孤児'))
    for kk in ('全', '根 lev=0', '根 lev>0'):
        g = G.get(kk)
        if not g: continue
        n = g['n']
        print('     %-10s %8d %8.4f%% %8.4f%% %8.4f%% %10.4f%% %13.4f%%'
              % (kk, n, pct(g['a'], n), pct(g['b'], n), pct(g['c'], n),
                 pct(g['★残差'], n), pct(g['ab中の孤児'], g['ab分母'])))
    g = G.get('全', Counter())
    m = g['★残差']
    if m:
        print('     ⟹ 残差の srow: 0 が %.4f%% / 1 が %.4f%% / 2 が %.4f%%'
              % (pct(g['srow=0'], m), pct(g['srow=1'], m), pct(g['srow=2'], m)))
    for Q in ex:
        print('     ★ 残差例: |Q|=%d srow=%d 根lev=%d  %s'
              % (len(Q), srow(Q, len(Q) - 1), lev0(Q), ' '.join('(%d,%d,%d)' % q for q in Q)))
    return G


t0 = time.time()
# (i) シート接頭辞
seen = set(); SH = []
for M in load():
    X = [tuple(v) for v in M]
    for k in range(2, len(X) + 1):
        if tuple(X[:k]) not in seen: seen.add(tuple(X[:k])); SH.append(X[:k])
scan(SH, 'シート接頭辞 %d 本（健全: W_take）' % len(SH))

# (ii) Reach
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
scan([list(x) for x in RC], 'Reach %d 本（健全）' % len(RC))

# (iii) Reach+（根が上がる）
SP = build_plus(RC, (1, 2, 3), rounds=3, cap=400000)
scan([list(x) for x in SP], 'Reach+ %d 本（健全、根が (0,v,0) を含む）' % len(SP), examples=6)

# (iv) 負の対照: 人工総当たり（W ではない列も入る）
COL = [(a, b, z) for a in range(0, 4) for b in range(0, 3) for z in (0, 1)]
ART = [[(0, v, z)] + list(t) for v in (0, 1, 2) for z in (0, 1)
       for t in itertools.product([c for c in COL if c[0] >= 1], repeat=3)]
scan(ART, '⛔ 負の対照: 人工 %d 本（W ではない）' % len(ART), examples=3)
print('（%.1f 秒）' % (time.time() - t0))
