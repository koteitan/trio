"""`convC` の再帰の各段（右端の道）で、BMS の親の位置と dropLast の可換を突き合わせる。

場合分けは `lean/DBMS-STD-PLAN.md` の (a)〜(d):

    ZERO   末尾列 = (0,0)
    親なし  末尾列に親がない
    節点    親が節点そのもの
    中      親が Arg / B の中

実測（BMS 標準形 ≤8 列）:

```
(ZERO,   可換)  9632
(親なし, 可換) 52870      ← 非可換は 0
(節点,   可換) 36401 / 非可換 938
(中,     可換) 52124 / 非可換 1007
```

**場合 (b)（親なし）では dropLast の可換が必ず成り立つ。** これは

* 梯子頭には親が立つ（段 = 親の段 + 1）ので、親がないなら梯子頭でない
* 縮約が消える状況（`Bq = []` かつ `|rest2| = 1`）は、そこでは親が「中」にある

の 2 つによる。`oper_one` と合わせると、場合 (b) は

    (convC M)⟦1⟧ = (convC M).dropLast = convC (M.dropLast) = convC (M⟦n⟧)

で片付く。

使い方: python3 bcase.py [列数上限]
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import show, pim
from rows2 import gen, convC, split, units_split, contrPre


def par(S):
    X = len(S)
    if X <= 1:
        return 'SHORT'
    x = X - 1
    if S[x] == (0, 0):
        return 'ZERO'
    t = 1 if S[x][1] > 0 else 0
    P = pim(tuple(S))
    r = P[x][t]
    return None if r == -1 else r


def fires(p, A, B, s, lad):
    if not lad:
        return False
    U, B2 = units_split(p, B)
    if not B2:
        return False
    q, r2 = B2[0], B2[1:]
    Aq, Bq = split(q, r2)
    if q[1] + 1 != s or q[0] != p[0]:
        return False
    pre = contrPre(p, U, A)
    if list(Aq[:len(pre)]) != pre:
        return False
    rest2 = list(Aq[len(pre):])
    return bool(rest2 and rest2[0][0] == p[0] + 1 and rest2[0][1] < s)


def walk(M, d, plev, first, force, acc):
    if len(M) <= 1:
        return
    p, r = M[0], M[1:]
    s = p[1]
    A, B = split(p, r)
    lad = first and s == plev + 1 and (d <= s or force)
    contr = fires(p, A, B, s, lad)
    jB = par(list(M))
    W = tuple(convC(M, d, plev, first, force))
    V = tuple(convC(list(M[:-1]), d, plev, first, force))
    cls = 'ZERO' if jB == 'ZERO' else ('親なし' if jB is None else ('節点' if jB == 0 else '中'))
    acc[(cls, W[:-1] == V)] += 1
    if contr:
        return
    dd = d + 1 if lad else (s + 1 if (s > 0 and d <= s) else d)
    if B:
        walk(list(B), d, s, False, False, acc)
    elif A:
        walk(list(A), dd + 1, s, True, (not lad) and first and s == plev, acc)


def main(lim=8):
    Ms = gen('BMS', lim)
    acc = collections.Counter()
    for i, M in enumerate(Ms):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._flat_memo.clear()
        walk(list(M), 0, 0, True, False, acc)
    print("lim=%d  (BMS の親, dropLast 可換): %s"
          % (lim, dict(sorted(acc.items(), key=lambda x: str(x)))))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 8)
