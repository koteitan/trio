# -*- coding: utf-8 -*-
"""(y2d) 決着 —— 核が増えるのは **`|Q|` のせいか、値域のせいか**。

r196 は `|Q|` と値域を**同時に**動かしていた（私の設計ミス。切り分ける）。
**(i) 値域を固定して `|Q|` を動かす／(ii) `|Q|` を固定して値域を動かす。**
＋ 核の `|V|` の分布（例が全部 `|V| = 2` に見えるので）。
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r195 import h2cone


def cell(E, L, NS, DE, nsamp, seed):
    rnd = random.Random(seed); c = Counter(); vl = Counter(); tries = 0
    while c['Q'] < nsamp and tries < nsamp * 300:
        tries += 1
        a = rnd.randrange(E - 1)
        Q = [(a, rnd.randrange(E), rnd.randrange(2))] + \
            [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        if h2cone(Q): continue
        c['Q'] += 1
        d, e = rnd.choice(DE), rnd.choice(DE)
        for n in NS:
            for j0 in range(L):
                T = [tuple(x) for x in mTower(Q, d, e, n)]
                S = T + block(Q, d, e, n)[:j0 + 1]
                last = len(S) - 1
                par = trio.parent(S, srow(S, last), last)
                if par is None: continue
                V = [tuple(x) for x in S[par:last]]
                if len(V) < 2: continue
                c['段'] += 1
                if len(V) < L: c['減る段'] += 1
                if h2cone(V):
                    c['核'] += 1
                    if len(V) < L: c['減る段の核'] += 1
                    vl[min(len(V), 8)] += 1
    return c, vl


def grid(fixE, Ls, fixL, Es, NS, nsamp, seed):
    print(f'#### (i) 値域を **<{fixE}** に固定して `|Q|` を動かす')
    print(f'    {"|Q|":>5s} {"段":>9s} {"核":>8s} {"核の率":>10s} {"減る段の核の率":>14s}')
    for L in Ls:
        c, _ = cell(fixE, L, NS, range(fixE), nsamp, seed + L)
        print(f'    {L:5d} {c["段"]:9d} {c["核"]:8d} '
              f'{100*c["核"]/max(c["段"],1):9.4f}% {100*c["減る段の核"]/max(c["減る段"],1):13.4f}%')
    print(f'#### (ii) `|Q|` を **{fixL}** に固定して値域を動かす')
    print(f'    {"値域":>5s} {"段":>9s} {"核":>8s} {"核の率":>10s} {"減る段の核の率":>14s}')
    for E in Es:
        c, _ = cell(E, fixL, NS, range(E), nsamp, seed + E)
        print(f'    {E:5d} {c["段"]:9d} {c["核"]:8d} '
              f'{100*c["核"]/max(c["段"],1):9.4f}% {100*c["減る段の核"]/max(c["減る段"],1):13.4f}%')
    print()


if __name__ == '__main__':
    grid(9, (3, 4, 6, 8, 10, 12, 16), 6, (4, 6, 9, 12, 16, 20, 28),
         (1, 2, 3, 4), 2500, 301)
    print('#### 核の `|V|` の分布（値域<9、|Q|=8）')
    c, vl = cell(9, 8, (1, 2, 3, 4), range(9), 3000, 401)
    tot = sum(vl.values())
    print('    ', {k: f'{100*v/max(tot,1):.1f}%' for k, v in sorted(vl.items())},
          f'  (核 {tot} 本)')
