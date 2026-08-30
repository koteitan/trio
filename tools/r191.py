# -*- coding: utf-8 -*-
"""(w4) の補足: 窓の根の行 2 = 1 を `j` と「非減少か」で切る。"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r183 import hr0, hz0


def run(E, LS, NS, DE, nsamp, seed):
    rnd = random.Random(seed); c = Counter()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        a = rnd.randrange(E - 1)
        Q = [(a, rnd.randrange(E), 0)] + \
            [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        assert hr0(Q) and hz0(Q)
        d, e = rnd.choice(DE), rnd.choice(DE)
        for n in NS:
            for j in range(L):
                T = [tuple(x) for x in mTower(Q, d, e, n)]
                S = T + block(Q, d, e, n)[:j + 1]
                last = len(S) - 1
                i1 = srow(S, last)
                par = trio.parent(S, i1, last)
                if par is None: continue
                nd = (last - par) >= L
                keys = [('j=0' if j == 0 else 'j>=1'),
                        ('非減少' if nd else '減る'),
                        ('j=0 ∧ 非減少' if (j == 0 and nd) else None)]
                for k in keys:
                    if k is None: continue
                    c[(k, '母')] += 1
                    if S[par][2] == 1: c[(k, '⚠ 根の行2=1')] += 1
    print(f'### (w4 補足) `hr0∧hz0` 値域<{E} |Q|∈{LS}')
    for k in ['j=0', 'j>=1', '減る', '非減少', 'j=0 ∧ 非減少']:
        t = c[(k, '母')]
        if not t: continue
        print(f'    {k:16s} 母集団 {t:8d}   ⚠ 窓の根の行 2 = 1 … '
              f'{c[(k,"⚠ 根の行2=1")]:8d} ({100*c[(k,"⚠ 根の行2=1")]/t:7.3f}%)')
    print()


if __name__ == '__main__':
    run(6, (3,4,5,6,8), (1,2,3,4,5), range(6), 12000, 201)
    run(9, (4,6,8,10),  (1,2,3,4,6), range(9),  8000, 203)
    run(12,(5,8,12),    (1,2,3,5,8), range(12), 5000, 205)
