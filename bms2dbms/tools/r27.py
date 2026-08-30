# -*- coding: utf-8 -*-
"""(D0') を **もっと広い母数**で数える。行列は 3 バイト/列の `bytes` で持つ
（`len<=12` の 800 万個でも 1GB 未満）。像も順序も作らない。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, trio
from rows3 import b2d3
from collections import Counter, deque

v, L = int(sys.argv[1]), int(sys.argv[2])
COUNT_ONLY = len(sys.argv) > 3 and sys.argv[3] == 'count'


def enc(M):
    return bytes(x for c in M for x in c)


def dec(b):
    return tuple((b[i], b[i + 1], b[i + 2]) for i in range(0, len(b), 3))


t0 = time.time()
seen = set(); fr = deque()
for k in range(v + 1):
    D = tuple(tuple(c) for c in trio.diag(3, k, zcap=1))
    e = enc(D)
    if e not in seen:
        seen.add(e); fr.append(D)
while fr:
    S = fr.popleft()
    for n in (1, 2, 3):
        T = tuple(tuple(c) for c in trio.expand(list(S), n))
        if T and len(T) <= L:
            e = enc(T)
            if e not in seen:
                seen.add(e); fr.append(T)
    if len(seen) % 500000 == 0:
        core._exp_memo.clear()
print('母集団 ST_TS v<=%d len<=%d  **%d 個**  (%.0fs)  seen のメモリは bytes'
      % (v, L, len(seen), time.time() - t0), flush=True)
if COUNT_ONLY:
    sys.exit(0)

t0 = time.time(); c = Counter(); ex = []
for i, e in enumerate(seen):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    M = dec(e)
    rows3._DMAP_TRACE = []
    b2d3(list(M))
    bad = False
    for off, k, dd, old in rows3._DMAP_TRACE:
        cl = tuple(kk for kk in range(k + 1, len(old)) if old[kk] <= dd)
        if cl:
            bad = True
            c['署名 (k=%d, dd=%d, 段=%s)' % (k, dd, cl)] += 1
    rows3._DMAP_TRACE = None
    if bad:
        c["**(D0') 違反を持つ行列**"] += 1
        if len(ex) < 4:
            ex.append(M)
    else:
        c["(D0') 違反なし"] += 1
print('  (D0\') を測った %.0fs' % (time.time() - t0))
for k in sorted(c, key=str):
    print('   %-46s %d' % (k, c[k]))
for M in ex:
    print('   例 %s' % ''.join(str(x).replace(' ', '') for x in M))
