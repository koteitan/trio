# -*- coding: utf-8 -*-
"""**(ROW2-ORPH) —— 塔の母集団で行 2 の孤児が 0 件か。**

## ⚠ 母集団の作り方（1 行）

`psiI.json` の DBMS 列（1,637 行列）の**全接頭辞**を `Q` として重複を除き、
`|Q| <= LQ` かつ `entry Q 2 0 = 0`（`hz0`）のものを取り、
`S = mTower Q d e n ++ block(Q,d,e,n).take (j+1)`（`1 <= j < |Q|`）を作る。

    **分母** ＝ `S` の列 `c` で **`entry S 2 c > 0`** のもの
    **分子** ＝ そのうち **`parent (S.take (c+1)) 2 c` が無い**もの（＝ 行 2 の孤児）
    ⟹ ★ `d`, `e`, `n` を振る（**とくに `e = 0`** と **`n` を伸ばす**）
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r263 import load


def qs(LQ):
    seen = set()
    for M in load():
        for k in range(2, min(len(M), LQ) + 1):
            Q = tuple(tuple(x) for x in M[:k])
            if Q[0][2] != 0: continue          # hz0
            if Q not in seen: seen.add(Q)
    return [list(q) for q in seen]


def run(LQ, DS, ES, NS, tag):
    Qs = qs(LQ); c = Counter(); ex = []; t0 = time.time()
    for Q in Qs:
        for d in DS:
            for e in ES:
                for n in NS:
                    T = [tuple(x) for x in mTower(Q, d, e, n)]
                    B = [tuple(x) for x in block(Q, d, e, n)]
                    for j in range(1, len(Q)):
                        S = T + B[:j + 1]
                        for cc in range(len(S)):
                            if S[cc][2] == 0: continue
                            c['★ 分母（行 2 > 0 の列）'] += 1
                            c[f'   e={e} 分母'] += 1
                            c[f'   n={n} 分母'] += 1
                            if trio.parent(S[:cc + 1], 2, cc) is not None: continue
                            c['⛔ **行 2 の孤児**'] += 1
                            c[f'   e={e} ⛔孤児'] += 1
                            c[f'   n={n} ⛔孤児'] += 1
                            c[f'   孤児の位置: ' +
                              ('塔の中' if cc < len(T) else 'ブロックの中')] += 1
                            if len(ex) < 5 and len(Q) <= 5:
                                ex.append((Q, d, e, n, j, cc, len(T), S))
    dn = c['★ 分母（行 2 > 0 の列）']; bd = c['⛔ **行 2 の孤児**']
    print(f'### {tag}  Q {len(Qs)} 個  [{time.time()-t0:.1f}s]')
    print(f'  ★★ **分母（行 2 > 0 の列）{dn}**   ⛔ **行 2 の孤児 {bd} '
          f'({100*bd/max(dn,1):8.4f}%)**')
    for k in sorted(c):
        if k.startswith('   e=') or k.startswith('   n=') or k.startswith('   孤児の位置'):
            print(f'      {k}: {c[k]}')
    for x in ex:
        print(f'      ⛔ 例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} '
              f'孤児の番地={x[5]}（塔の長さ={x[6]}） S={x[7]}')
    print()


if __name__ == '__main__':
    run(5, (1, 2), (0, 1), (1, 2), '|Q|<=5, d∈{1,2}, e∈{0,1}, n∈{1,2}')
    run(6, (1, 2, 3), (0, 1, 2), (1, 2, 3, 5), '★ |Q|<=6, d∈{1,2,3}, e∈{0,1,2}, n∈{1,2,3,5}')
