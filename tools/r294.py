# -*- coding: utf-8 -*-
"""**(G1-M)(G1-M2) —— 良い群で `A' ++ mTower V d0 d1 m` は `A ++ mTower Q d e N` の take か。**

## ⚠ 母集団（チェックリスト 5 項目）

1. `entry Q 0 0 > 0`（`u∈{0,1,2}`） 2. 行 1 が全部等しい `Q` 3. 浅い `A`
4. L3 の反例 2 件 5. シート由来
**良い群 ＝ `c >= |A|`**（＝ `|V| <= |Q|` と実測で一致）。

## 測るもの

    (G1-M)  `L = A' ++ mTower V d0 e0 m` が `A ++ mTower Q d e N` の**接頭辞**になる
            **最小の `N`** を `m = 0,1,2,3` で求める ⟹ ★ `n` と `m` の式に当てはめる
    (G1-M2) 良い群で **`(d0, e0) = (d, e)`** は何 %
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r206 import hr0
from r284 import sheetQ
from r291 import AS
from r293 import step1, qsets


def minN(L, A, Q, d, e, NMAX=40, _cache={}):
    """`L` が `A ++ mTower Q d e N` の接頭辞になる最小の N（無ければ None）。
    ★ `mTower` を 1 回だけ作り、長さから最小 N を計算する。"""
    key = (tuple(map(tuple, A)), tuple(map(tuple, Q)), d, e)
    R = _cache.get(key)
    if R is None:
        R = [tuple(x) for x in A] + [tuple(x) for x in mTower(Q, d, e, NMAX)]
        _cache[key] = R
    if len(L) > len(R) or R[:len(L)] != L: return None
    need = max(0, len(L) - len(A))
    return -(-need // len(Q))          # ceil


def main():
    t0 = time.time(); c = Counter(); ex = []
    MS = (0, 1, 2, 3)
    for Q in qsets()[:120]:
        for A in AS:
            for d in (0, 1, 2):
                for e in (0, 1, 2):
                    for n in (1, 2):
                        for j in range(0, len(Q)):
                            r = step1(A, Q, d, e, n, j)
                            if r is None: continue
                            A1, V1, d1, e1, c1, s1, T1 = r
                            good = c1 >= len(A)
                            if not good: continue
                            c['★ 良い群 分母'] += 1
                            c[f'(G1-M2) (d0,e0)=(d,e) ? {(d1,e1)==(d,e)}'] += 1
                            for m in MS:
                                L = [tuple(v) for v in A1] + \
                                    [tuple(x) for x in mTower(V1, d1, e1, m)]
                                N = minN(L, A, Q, d, e)
                                c[f'(G1-M) m={m} 分母'] += 1
                                if N is None:
                                    c[f'(G1-M) m={m} ⛔ **一致しない**'] += 1
                                    if len(ex) < 4:
                                        R = [tuple(x) for x in A] + \
                                            [tuple(x) for x in mTower(Q, d, e, 40)]
                                        k = next((i for i in range(min(len(L), len(R)))
                                                  if L[i] != R[i]), None)
                                        ex.append(('不一致', A, Q, d, e, n, j, m, k,
                                                   L[k] if k is not None else None,
                                                   R[k] if k is not None else None))
                                else:
                                    c[f'(G1-M) m={m} ★N={min(N,9)}'] += 1
                                    c[f'(G1-M) m={m} N vs n+m: '
                                      f'{"<" if N < n+m else ("=" if N == n+m else ">")}'] += 1
                                    c[f'(G1-M) m={m} N<=n ? {N <= n}'] += 1
    print(f'### (G1-M)(G1-M2)  [{time.time()-t0:.1f}s]  ★ 良い群 分母 {c["★ 良い群 分母"]}')
    print('  ★★ (G1-M2) `(d0,e0) = (d,e)` か')
    for b in (True, False):
        v = c[f'(G1-M2) (d0,e0)=(d,e) ? {b}']
        print(f'      {b}: {v} ({100*v/max(c["★ 良い群 分母"],1):8.4f}%)')
    print('  ★★★★ (G1-M) 最小の N')
    for m in MS:
        d = c[f'(G1-M) m={m} 分母']
        if not d: continue
        bad = c[f'(G1-M) m={m} ⛔ **一致しない**']
        print(f'      **m={m}** 分母 {d:7d}  ⛔ 一致しない {bad} ({100*bad/d:7.3f}%)')
        ns = {k.split('N=')[1]: v for k, v in c.items()
              if k.startswith(f'(G1-M) m={m} ★N=')}
        print(f'          N の分布: {dict(sorted(ns.items(), key=lambda t: int(t[0])))}')
        for rel in ('<', '=', '>'):
            v = c[f'(G1-M) m={m} N vs n+m: {rel}']
            if v: print(f'          N {rel} n+m: {v} ({100*v/d:7.3f}%)')
        v = c[f'(G1-M) m={m} N<=n ? True']
        print(f'          ★★ **N <= n**: {v} ({100*v/d:7.3f}%)')
    for x in ex:
        print(f'      ⛔ {x[0]}: A={x[1]} Q={x[2]} d={x[3]} e={x[4]} n={x[5]} j={x[6]} '
              f'm={x[7]} 食い違いは {x[8]} 列目（{x[9]} vs {x[10]}）')


if __name__ == '__main__':
    main()
