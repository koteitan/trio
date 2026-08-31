# -*- coding: utf-8 -*-
"""**(R-D1) 族 β（A1 / A2）—— `f(A)<m>` は `f(A<m+1>)` から何を抜いたものか。**

## ⚠ 定義（`teach.py:96-99` 逐語）

    `fM = rows3.b2d3(list(M))`                       … conv3 の像
    **`T = expand(fM, m)`**                          … 像の DBMS 展開（conv3 の意見は入らない）
    **`E = expand(M, m+1)`** / **`U = rows3.b2d3(E)`** … conv3 の答え

    ★ 族 α では `len(T) == len(U)` で柱ごとに整列できる。
    ⛔ 族 β（A1 / A2）では **長さが揃わない** ⟹ ★ **`T` は `U` から写しを何組か抜いたもの**（BRIEF-v14 追記 5）

## ⚠ 測ること

    (1) `len(T)` と `len(U)`、差
    (2) **`T` は `U` の部分列か**（最長一致で、`U` のどの位置が残るか）
    (3) **抜けた区間の位置と長さ**（規則があるか。いつも先頭 1 組か、`m` に依るか）
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3
from core import expand, show, parse

A1 = ((0, 0, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1), (1, 1, 1))
A2 = ((0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (2, 1, 0))
G1w = ((0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (2, 0, 0), (3, 1, 1), (3, 0, 0), (4, 1, 1))


def col(c): return '(%d,%d,%d)' % tuple(c)
def S(M): return ' '.join(col(c) for c in M)


def sub_align(T, U):
    """`T` が `U` の部分列か。貪欲に前から合わせ、`U` の残す位置を返す。"""
    keep = []; i = 0
    for k, u in enumerate(U):
        if i < len(T) and tuple(T[i]) == tuple(u):
            keep.append(k); i += 1
    return (i == len(T)), keep


def gaps(keep, n):
    """`keep` に入っていない `U` の位置を、連続区間にまとめる。"""
    s = set(keep); out = []; st = None
    for k in range(n):
        if k not in s:
            if st is None: st = k
        else:
            if st is not None: out.append((st, k - st)); st = None
    if st is not None: out.append((st, n - st))
    return out


for name, A in (('A1', A1), ('A2', A2), ('G1 の証人', G1w)):
    print('=' * 78)
    print('★ %s = %s' % (name, S(A)))
    fM = tuple(map(tuple, rows3.b2d3(list(A))))
    print('   conv3(%s) = %s   （|f(A)| = %d）' % (name, S(fM), len(fM)))
    for m in (2, 3, 4, 5):
        T = tuple(map(tuple, expand(fM, m)))
        E = tuple(map(tuple, expand(tuple(map(tuple, A)), m + 1)))
        U = tuple(map(tuple, rows3.b2d3([list(c) for c in E])))
        ok, keep = sub_align(T, U)
        g = gaps(keep, len(U))
        print('   -- m=%d --  |T|=%-4d |U|=%-4d 差=%-4d  部分列か: %s'
              % (m, len(T), len(U), len(U) - len(T), '★ はい' if ok else '⛔ いいえ'))
        if ok:
            print('        抜けた区間（U の位置, 長さ）: %s' % (g if g else '（なし）'))
            for (st, ln) in g[:3]:
                print('          U[%d:%d] = %s' % (st, st + ln, S(U[st:st + ln])))
        else:
            print('        T = %s' % S(T[:14]))
            print('        U = %s' % S(U[:14]))
