# -*- coding: utf-8 -*-
"""**課題 (s4) —— `rsum` は遺伝するか。**

## 算術での見当（測る前に）

`A' = P ++ B.take p`（`P = mTower Q d e n`）、`V = (P ++ B.take (j+1))[P.length+p : ...]`
⟹ **`entry V 0 0 = B[p][0] = entry Q 0 p + d*n`**
`A'` は塔を含み、塔の第 0 ブロックの根は行 0 = **`entry Q 0 0`**
⟹ **`d > 0` ∧ `n >= 1` なら `entry Q 0 0 < entry Q 0 p + d*n`** ⟹ **`rsum A' V` は破れる**

> **⚠ 予想: `d > 0` ではほぼ常に破れる（成立 0〜5%）。`d = 0` でも `p >= 1` なら
>   `entry Q 0 0 < entry Q 0 p`（`hr0`）で破れる。⟹ **`p = 0` ∧ `d = 0` のときだけ成立**と予想。**

## (s4c) H12 の二択が一般の `d` でも成り立つか

    (1) `Q` の根が `A` の中に行 0 の親 `a0` を持つ ⟹ **全ブロック根の親が同じ列 `a0`**
    (2) 持たない ⟹ 全ブロック根が孤児
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r169 import domT
from r201 import dOf, eOf
from r206 import hr0


def rsum(A, V):
    """`∀ q ∈ A ++ V, entry V 0 0 <= q.1`（`Wset:1317` の逐語）。"""
    r0 = V[0][0]
    return all(q[0] >= r0 for q in list(A) + list(V))


def run(L, R1, VS, ZS, TS, NS, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    c = Counter(); ex = []; t0 = time.time()
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        if srow(R, len(R) - 1) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q = M[:-1]
                    if len(Q) < 2: continue
                    d, e = dOf(M), eOf(M)
                    if not (len(Q) >= 1 and d > 0 and e > 0 and hr0(Q) and Q[0][2] == 0):
                        continue
                    LQ = len(Q)
                    # 入口の `rsum A Q`（`A = []` なら自明に真）
                    for n in NS:
                        P = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(1, LQ):
                            S = P + B[:j + 1]
                            last = len(S) - 1
                            i1 = srow(S, last)
                            par = trio.parent(S, i1, last)
                            if par is None or par < len(P): continue
                            p = par - len(P)
                            if p >= j: continue
                            A2 = P + B[:p]
                            V = S[par:last]
                            c['DEN'] += 1
                            c[('srow', i1, '分母')] += 1
                            if rsum(A2, V):
                                c['OK'] += 1
                                c[('srow', i1, '★ 成立')] += 1
                            else:
                                c['NG'] += 1
                                if len(ex) < 4:
                                    lo = min(q[0] for q in A2 + V)
                                    ex.append((Q, d, e, n, j, p, i1, V[0][0], lo))
                            if p == 0: c[('p=0', rsum(A2, V))] += 1
                            else:      c[('p>=1', rsum(A2, V))] += 1
    D = c['DEN']
    print('### %s  ★ 分母（1 段の (A2, V)）%d  [%.1fs]' % (tag, D, time.time() - t0))
    print('    ★ (s4a) rsum A2 V 成立 %8d (%8.4f%%)   ⛔ 破れ %8d (%8.4f%%)'
          % (c['OK'], 100 * c['OK'] / max(D, 1), c['NG'], 100 * c['NG'] / max(D, 1)))
    print('    (s4b) srow 別:')
    for i1 in (0, 1, 2):
        dd = c[('srow', i1, '分母')]
        if not dd:
            continue
        print('        srow=%d: 分母 %8d   ★ 成立 %8d (%8.4f%%)'
              % (i1, dd, c[('srow', i1, '★ 成立')],
                 100 * c[('srow', i1, '★ 成立')] / dd))
    for k in ('p=0', 'p>=1'):
        tt = c[(k, True)] + c[(k, False)]
        if tt:
            print('    %-5s: 分母 %8d   ★ 成立 %8d (%8.4f%%)'
                  % (k, tt, c[(k, True)], 100 * c[(k, True)] / tt))
    for x in ex:
        print('      ⛔ 破れ例 Q=%s d=%d e=%d n=%d j=%d p=%d srow=%d  '
              'entry V 0 0 = %d、A2++V の最小の行 0 = %d' % x)
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '消費側 |R|=3 行1<3')
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), '消費側 |R|=3 行1<5')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '★ 消費側 |R|=4 行1<3')
