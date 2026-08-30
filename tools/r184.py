# -*- coding: utf-8 -*-
"""(u1) の詰め。**どの前提が効いているか**と (u1b) 2 段の鎖の `j`。

r183: 無条件で `j>=1` の非減少が 17 / 43 件出たが、**全部 `hz0` を持っていない**
（内訳が `hr0` と `hr0hnb` だけ）。⟹ **`hz0`（`entry Q 2 0 = 0`）が鍵か。**

**(u1d)** 前提を 1 つずつ課して切り分ける。
**(u1b)** 2 段続く非減少の 1 段目と 2 段目の `j`。
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r171 import step_det
from r183 import hr0, hnb, hz0, probe


def sift(E, LS, NS, DE, nsamp, seed):
    COL = [(x, y, z) for x in range(E) for y in range(E) for z in (0, 1)]
    rnd = random.Random(seed); c = Counter()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
        if not hi: continue
        Q = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d, e, n = rnd.choice(DE), rnd.choice(DE), rnd.choice(NS)
        conds = {'前提なし': True, 'hr0 だけ': hr0(Q), 'hnb だけ': hnb(Q),
                 'hz0 だけ': hz0(Q), 'hr0∧hnb': hr0(Q) and hnb(Q),
                 'hr0∧hz0': hr0(Q) and hz0(Q), 'hnb∧hz0': hnb(Q) and hz0(Q),
                 '3 つ全部': hr0(Q) and hnb(Q) and hz0(Q)}
        for j in range(1, L):
            r = probe(Q, d, e, n, j)
            if r is None: continue
            lv, par, inblk = r
            for k, ok in conds.items():
                if not ok: continue
                c[(k, '段')] += 1
                if lv >= L: c[(k, '⚠ 非減少')] += 1
                if not inblk: c[(k, '⚠ 親がブロックの外')] += 1
    print(f'### (u1d) 前提を 1 つずつ課す  値域<{E} |Q|∈{LS}  （`j>=1` の段だけ）')
    print(f'    {"前提":12s} {"段":>9s} {"⚠ 非減少":>12s} {"⚠ 親がブロックの外":>20s}')
    for k in ['前提なし', 'hr0 だけ', 'hnb だけ', 'hz0 だけ', 'hr0∧hnb', 'hr0∧hz0',
              'hnb∧hz0', '3 つ全部']:
        t = c[(k, '段')]
        if not t: continue
        print(f'    {k:12s} {t:9d} {c[(k,"⚠ 非減少")]:7d} ({100*c[(k,"⚠ 非減少")]/t:6.4f}%) '
              f'{c[(k,"⚠ 親がブロックの外")]:9d} ({100*c[(k,"⚠ 親がブロックの外")]/t:6.4f}%)')
    print()


def two_step(E, LS, NS, DE, nsamp, seed):
    """(u1b) 2 段続く非減少の 1 段目と 2 段目の `j`。`(d,e)` は `oper` 決め打ち。"""
    COL = [(x, y, z) for x in range(E) for y in range(E) for z in (0, 1)]
    rnd = random.Random(seed); c = Counter()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
        if not hi: continue
        Q = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d, e = rnd.choice(DE), rnd.choice(DE)
        for n1 in NS:
            for j1 in range(L):
                r = step_det(Q, d, e, n1, j1)
                if r is None or len(r[0]) < L: continue
                c[('1 段目の j', j1)] += 1; c['1 段目の非減少'] += 1
                V, d2, e2 = r
                for n2 in NS:
                    for j2 in range(len(V)):
                        r2 = step_det(V, d2, e2, n2, j2)
                        if r2 and len(r2[0]) >= len(V):
                            c[('2 段続いたときの (j1, j2)', (j1, j2))] += 1
                            c['2 段続いた'] += 1
    print(f'### (u1b) 2 段続く非減少の `j`  値域<{E} |Q|∈{LS}')
    print(f'    1 段目の非減少 {c["1 段目の非減少"]} 件。その `j` の分布: ',
          dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple)
                      and k[0] == '1 段目の j')))
    print(f'    2 段続いた {c["2 段続いた"]} 件。その `(j1, j2)`: ',
          dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple)
                      and k[0] == '2 段続いたときの (j1, j2)')))
    print()


if __name__ == '__main__':
    sift(6, (3,4,5,6,8), (2,3,4,5), range(6), 60000, 121)
    sift(9, (4,6,8,10),  (2,3,4,5), range(9), 40000, 123)
    two_step(6, (3,4,5,6), (1,2,3,4,5), range(6), 20000, 131)
    two_step(9, (4,6,8),   (1,2,3,4,5), range(9), 12000, 133)
