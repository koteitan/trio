# -*- coding: utf-8 -*-
"""Lean の `Conv3M.b2d` を `mrf3.b2d` と突き合わせる `#guard` を起こす。

    python3 gen_guard3.py 6            <=6 列を全数（8387 本）
    python3 gen_guard3.py 7 5000       <=7 列から無作為 5000 本

出力を `bms2dbms/lean/AllGuard.lean` に置いて
`leanman check -C bms2dbms/lean AllGuard.lean` が緑なら一致。
"""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mrf3
from rows3 import gen3

lim = int(sys.argv[1]) if len(sys.argv) > 1 else 6
n = int(sys.argv[2]) if len(sys.argv) > 2 else 0
A = [tuple(map(tuple, M)) for M in gen3('BMS', lim, zcap=1)]
if n and n < len(A):
    random.seed(7)
    A = A[:40] + random.sample(A, n)
    A = list(dict.fromkeys(A))
L = lambda M: '[' + ', '.join('(%d,%d,%d)' % c for c in M) + ']'
print('import Conv3M\n\nopen TRIO.Conv3M\n')
for M in A:
    print('#guard b2d %s = %s' % (L(M), L(mrf3.b2d(M))))
