# -*- coding: utf-8 -*-
"""課題 R21: `onto.py` の「外れ」は本物か（`d2b3` が弱いだけではないか）。

`onto.py` は**素の `inv3.d2b3`** を使う（docstring 自身が「外れは非全射の**上界**」
と書いている）。`rows3.preimage_try`（`d2b3` ＋ 双子戻し ＋ 接頭辞の当て直し、
当たりは `conv3 B == T` で検算）に替えると外れがどれだけ減るかを測る。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, inv3
from rows3 import b2d3, preimage_try, gen3, key
from core import isstd, show

LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 8
f = lambda X: [tuple(y) for y in b2d3(X)]
for lim in range(4, LIM + 1):
    t0 = time.time()
    D = sorted(gen3('DBMS', lim, zcap=1), key=key)
    raw = pre = 0
    still = []
    for T in D:
        T = tuple(map(tuple, T))
        B = None
        try:
            B = inv3.d2b3(T)
        except Exception:
            B = None
        okraw = bool(B) and isstd(B, 'BMS') and all(c[2] <= 1 for c in B) \
            and tuple(f(list(B))) == T
        if okraw:
            raw += 1
        P = preimage_try(f, T, inv3.d2b3)
        if P is not None:
            pre += 1
        elif not okraw:
            still.append(T)
    print('<=%d 列: DBMS 標準形 %d 個   素の d2b3 の外れ **%d**   '
          'preimage_try の外れ **%d**  (%.0fs)'
          % (lim, len(D), len(D) - raw, len(D) - pre, time.time() - t0), flush=True)
    if lim >= 6:
        for T in still[:5]:
            print('     残る外れ:', show(list(T)))
