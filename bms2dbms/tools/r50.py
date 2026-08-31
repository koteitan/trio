# -*- coding: utf-8 -*-
"""`WSnoc` を**孤児の塔の上で証明できるか**を測る。

`Wlo`（孤児の塔）は `W u` の健全な下界だった（R29-5）。もし

    C が孤児の塔  かつ  p が `C ++ [p]` で親を持つ
      ⟹  **`(C ++ [p])[n]` もまた孤児の塔（すべての n >= 1）**

なら、節 2 がそのまま立つので `C ++ [p] in W u` が出る。つまり
**`WSnoc` は孤児の塔の上では定理**になる。docstring の
「親が付くと `C` の窓の塔になる」を、`Wlo` という健全な形で言い直したもの。

`n` は 1..N しか見られないが、n によらない一様な形が出れば Lean 側の
帰納の当てになる。"""
import sys, time, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from r49 import Wlo, has_parent, towers_deep, towers, lev_at

N = int(sys.argv[1]) if len(sys.argv) > 1 else 8
CAP = int(sys.argv[2]) if len(sys.argv) > 2 else 400
DEEP = len(sys.argv) > 3 and sys.argv[3] == 'deep'
COLS = [(a, b, c) for a in range(6) for b in range(8) for c in range(2)]
T = towers_deep(COLS, 4, 12, CAP) if DEEP else towers(COLS, 6, CAP)
print('C: 孤児の塔 %d 個  長さ分布 %s  n = 1..%d  p は 96 列のうち親が付くもの全部'
      % (len(T), dict(sorted(Counter(len(C) for C in T).items())), N), flush=True)
assert all(Wlo(C) for C in T), '陽性対照が落ちた'
print('  陽性対照: C 全部で Wlo = True  OK', flush=True)

c = Counter(); bad = []; t0 = time.time()
for i, C in enumerate(T):
    if time.time() - t0 > 1200:
        c['**時間切れ（C %d / %d）**' % (i, len(T))] += 1; break
    for p in [q for q in COLS if has_parent(C + (q,), len(C))]:
        S = C + (p,)
        ok = True
        for n in range(1, N + 1):
            E = tuple(tuple(x) for x in trio.expand(list(S), n))
            if not Wlo(E):
                ok = False
                c['**n=%d で孤児の塔でない**' % n] += 1
                if len(bad) < 8: bad.append((C, p, n, E))
                break
        if ok:
            c['n=1..%d すべて孤児の塔' % N] += 1
print('--- 結果 (%.0fs)' % (time.time() - t0))
for k in sorted(c, key=str):
    print('    %-40s %d' % (k, c[k]))
for C, p, n, E in bad:
    print('    反例 C=%s p=%s n=%d' % (''.join(map(str, C)), p, n))
    print('          (C+[p])[%d] = %s' % (n, ''.join(map(str, E))))
