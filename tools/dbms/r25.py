# -*- coding: utf-8 -*-
"""課題 R13 (3) の正しい形: CM は「接頭辞 x 次の柱 x **継続**」で測る。

`conv3` の綴りは継続に依存するので、`(P, c)` に対して**到達しうる柱の集合**
`H(P,c)` を取る（継続を長さ `k` まで全数）。CM は

    c1 < c2  ->  max H(P,c1) <= min H(P,c2)

母数 = (接頭辞, 柱) の組。行列の対を 188 万個なめるより桁違いに小さい。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, provc
from rows3 import gen3, key
from core import isstd
from collections import Counter


def legal_next(P, zcap=1):
    amax = P[-1][0] + 1
    return sorted((a, b, cz) for a in range(amax + 1) for b in range(a + 1)
                  for cz in range(min(b, zcap) + 1)
                  if isstd(P + ((a, b, cz),), 'BMS'))


def conts(P, k):
    """`P` から長さ `k` までの合法な継続（自分自身も含む）。"""
    out = [P]; cur = [P]
    for _ in range(k):
        nxt = []
        for S in cur:
            for x in legal_next(S):
                nxt.append(S + (x,))
        out += nxt; cur = nxt
    return out


def pillars(M, j):
    C, PR = provc.b2d3p(list(M))
    for i, e in enumerate(PR):
        if e[1] == j:
            return tuple(C[i])
    return None


def run(pop, K, name, verbose=4):
    c = Counter(); ex = []
    seen = set(); t0 = time.time()
    for i, M in enumerate(pop):
        if i % 2000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        for j in range(1, len(M) + 1):
            P = tuple(M[:j])
            if P in seen:
                continue
            seen.add(P)
            cs = legal_next(P)
            if len(cs) < 2:
                continue
            H = {}
            for x in cs:
                s = set()
                for T in conts(P + (x,), K):
                    h = pillars(T, j)
                    if h is not None:
                        s.add(h)
                H[x] = s
            c['_束'] += 1
            for t in range(len(cs) - 1):
                a, b = H[cs[t]], H[cs[t + 1]]
                if not a or not b:
                    continue
                c['_隣'] += 1
                if max(a) <= min(b):
                    c['単調'] += 1
                else:
                    c['**CM の破れ**'] += 1
                    if len(ex) < verbose:
                        ex.append((P, cs[t], sorted(a), cs[t + 1], sorted(b)))
    print('== %s  継続の深さ K=%d  束 %d  隣 %d  %.0fs'
          % (name, K, c['_束'], c['_隣'], time.time() - t0))
    for k in sorted(c, key=str):
        if not k.startswith('_'):
            print('   %-20s %d' % (k, c[k]))
    for P, c1, a, c2, b in ex:
        print('   ### CM の破れ')
        print('      P  = %s' % ''.join(str(x).replace(' ', '') for x in P))
        print('      c1 = %s -> 到達しうる柱 %s' % (c1, a))
        print('      c2 = %s -> 到達しうる柱 %s' % (c2, b))
    return c


if __name__ == '__main__':
    lim = int(sys.argv[1]); K = int(sys.argv[2])
    P = [tuple(map(tuple, M)) for M in sorted(gen3('BMS', lim, zcap=1), key=key)]
    run(P, K, 'gen3 <=%d の接頭辞' % lim)
