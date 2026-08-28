# -*- coding: utf-8 -*-
"""`WSnoc` の事例が **何段の展開で「孤児の塔」に落ちるか**を測る。

R50 で分かったこと: `Wlo`（孤児の塔）は健全だが弱い。
`(0,0,0)(1,0,0)` は `W 0` の元だが `Wlo` は落とす
（最後の列 `(1,0,0)` は行 0 に親を持つので孤児でない）。
ただしその展開 `(0,0,0)^n` は全部 `Wlo`。つまり **1 段降りれば塔になる**。

そこで「段数」を測る:

    cert(M, 0) := Wlo(M)                                   （健全）
    cert(M, d) := Wlo(M) or (forall n in 1..N, cert(M[n], d-1))

`forall n` を 1..N に切っているので `cert = True` は「n <= N の範囲で」の意味。
段数 d が**小さく**て一様なら、Lean 側で `WSnoc` を帰納で閉じられる見込みが立つ。
"""
import sys, time
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from r49 import Wlo, has_parent, towers_deep, towers

N = int(sys.argv[1]); DMAX = int(sys.argv[2]); CAP = int(sys.argv[3])
DEEP = len(sys.argv) > 4 and sys.argv[4] == 'deep'
MAXLEN = 40
COLS = [(a, b, c) for a in range(6) for b in range(8) for c in range(2)]
T = towers_deep(COLS, 4, 12, CAP) if DEEP else towers(COLS, 6, CAP)
print('C: 孤児の塔 %d 個  長さ %s  n = 1..%d  段数の上限 %d'
      % (len(T), dict(sorted(Counter(len(C) for C in T).items())), N, DMAX),
      flush=True)


def depth_needed(M, memo):
    """`cert(M, d)` が立つ最小の d（DMAX 以内に無ければ None）。"""
    M = tuple(tuple(x) for x in M)
    if M in memo:
        return memo[M]
    memo[M] = None
    if Wlo(M):
        memo[M] = 0
        return 0
    if len(M) > MAXLEN:
        return None
    best = 0
    for n in range(1, N + 1):
        E = trio.expand(list(M), n)
        d = depth_needed(E, memo) if len(E) < len(M) or True else None
        if d is None:
            memo[M] = None
            return None
        best = max(best, d)
    r = best + 1 if best + 1 <= DMAX else None
    memo[M] = r
    return r


sys.setrecursionlimit(100000)
c = Counter(); ex = {}; t0 = time.time(); memo = {}
for i, C in enumerate(T):
    if time.time() - t0 > 1200:
        c['**時間切れ（C %d / %d）**' % (i, len(T))] += 1; break
    if len(memo) > 2000000:
        memo.clear()
    for p in [q for q in COLS if has_parent(C + (q,), len(C))]:
        try:
            d = depth_needed(C + (p,), memo)
        except RecursionError:
            memo.clear(); c['再帰が深すぎ'] += 1; continue
        c['段数 %s' % (d if d is not None else '決まらず')] += 1
        if d is not None and d not in ex:
            ex[d] = (C, p)
print('--- 結果 (%.0fs)' % (time.time() - t0))
for k in sorted(c, key=lambda s: (len(s), s)):
    print('    %-24s %d' % (k, c[k]))
for d in sorted(ex):
    print('    段数 %d の例  C=%s  p=%s'
          % (d, ''.join(map(str, ex[d][0])), ex[d][1]))
