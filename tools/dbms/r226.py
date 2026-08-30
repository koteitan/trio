# -*- coding: utf-8 -*-
"""**課題 (z1b') —— `OrphOK0` / `OrphOK` は「浅い接頭辞」で破れるか。軸は `min(A の行 0)` vs `entry Q 0 0`。**

## team-lead の指定した反例の形

    `d = 0` の塔、`Q = [(1,1,0), (2,0,0)]`（`entry Q 0 0 = 1`）、`A = [(0,0,0)]`
    ⟹ ブロック根は塔の中で孤児だが、`A` の `(0,0,0)` が `nextrel0` の始点になれる

## ★ 軸（team-lead の指定）: **`min(A の行 0)` と `entry Q 0 0` の関係**

    (a) `A` が空
    (b) `min(A の行 0) >= entry Q 0 0` … **浅くない**
    (c) `min(A の行 0) <  entry Q 0 0` … **★ 浅い**
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r224 import orphan


def axis(A, Q):
    if not A: return '(a) A が空'
    return ('(c) ★ 浅い（min(A の行0) < entry Q 0 0）' if min(p[0] for p in A) < Q[0][0]
            else '(b) 浅くない（min(A の行0) >= entry Q 0 0）')


def demo():
    print('#### ★ team-lead の指定した反例の形をそのまま実行')
    Q = [(1, 1, 0), (2, 0, 0)]
    for d in (0, 1, 2):
        for e in (0, 1):
            for n in (2, 3):
                T = [tuple(x) for x in mTower(Q, d, e, n)]
                for k in range(1, n):
                    idx = k * len(Q)
                    if not orphan(T, idx): continue
                    for A in ([(0, 0, 0)], [(0, 5, 0)], [(1, 0, 0)]):
                        S = A + T
                        i = len(A) + idx
                        o = orphan(S, i)
                        par = trio.parent(S, srow(S, i), i)
                        print('    Q=%s d=%d e=%d n=%d k=%d  塔で孤児 ✓  A=%s '
                              '⟹ %s  親=%s   [%s]'
                              % (Q, d, e, n, k, A,
                                 '孤児のまま' if o else '⛔ 親ができる', par, axis(A, Q)))
    print()


def run(E, LS, DS, ES, NS, nsamp, seed, jmode):
    """jmode='j0' … ブロック根（`OrphOK0`）／'j1' … ブロック内の `j>=1`（`OrphOK`）"""
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    for _ in range(nsamp):
        L = rnd.randrange(2, 6)
        a0 = rnd.randrange(0, 4)
        Q = [(a0, rnd.randrange(0, E), 0)] + \
            [(rnd.randrange(a0 + 1, a0 + E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        if not all(Q[0][0] < Q[l][0] for l in range(1, L)): continue
        d = rnd.choice(DS); e = rnd.choice(ES); n = rnd.choice(NS)
        T = [tuple(x) for x in mTower(Q, d, e, n)]
        B = block(Q, d, e, n)
        tgts = ([(k * L, T) for k in range(1, n)] if jmode == 'j0'
                else [(len(T) + j, T + B[:j + 1]) for j in range(1, L)])
        for idx, base in tgts:
            if not orphan(base, idx): continue      # ★ 前件
            for A in ([], [(0, 0, 0)],
                      [(rnd.randrange(max(a0, 1)), rnd.randrange(E), rnd.randrange(2))],
                      [(a0 + rnd.randrange(0, 3), rnd.randrange(E), rnd.randrange(2))],
                      [(rnd.randrange(a0 + E), rnd.randrange(E), rnd.randrange(2))
                       for _ in range(3)]):
                ax = axis(A, Q)
                S = A + base
                i = len(A) + idx
                c[(ax, '★ 分母')] += 1
                if orphan(S, i): c[(ax, '★ 孤児のまま')] += 1
                else:
                    c[(ax, '⛔ 親ができる')] += 1
                    if len(ex) < 3 and ax.startswith('(c)'):
                        ex.append((Q, d, e, n, A, trio.parent(S, srow(S, i), i), idx))
    nm = 'OrphOK0（ブロック根、j=0）' if jmode == 'j0' else 'OrphOK（ブロック内 j>=1）'
    print(f'### {nm}  値域<{E} d∈{tuple(DS)} e∈{tuple(ES)} n∈{tuple(NS)}  [{time.time()-t0:.1f}s]')
    for ax in ['(a) A が空', '(b) 浅くない（min(A の行0) >= entry Q 0 0）',
               '(c) ★ 浅い（min(A の行0) < entry Q 0 0）']:
        D = c[(ax, '★ 分母')]
        if not D: continue
        print(f'    {ax:44s} 分母 {D:8d}   ★ 孤児のまま {c[(ax,"★ 孤児のまま")]:8d} '
              f'({100*c[(ax,"★ 孤児のまま")]/D:8.4f}%)   ⛔ 親 {c[(ax,"⛔ 親ができる")]:8d} '
              f'({100*c[(ax,"⛔ 親ができる")]/D:8.4f}%)')
    for x in ex:
        print(f'      ⛔ 反例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} A={x[4]} 親={x[5]} 対象idx={x[6]}')
    print()


if __name__ == '__main__':
    demo()
    for jm in ('j0', 'j1'):
        run(7, None, (0,), (0,1,2), (2,3,4), 60000, 851, jm)   # ★ d = 0
        run(7, None, (1,2,3), (0,1,2), (2,3,4), 60000, 853, jm)  # d > 0
