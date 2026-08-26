"""展開 `oper` を末尾ブロックに**局所化**できるかを、`convC` の再帰の各段で検査する。

REINDEX を帰納法で証明したいとき、いちばん素直な道は

    A = p :: (Arg ++ B) で B が 2 列以上なら、展開は B の中で閉じる
    A[n] = (p :: Arg) ++ B[n]                            … BMS 側
    (conC A)[m] = (conC A の前半) ++ (convC B ...)[m]     … DBMS 側

として B に帰納法を回すことである。BMS 側は `Pair/Wset.lean` の
`oper_append_gen`（仮定 `rsum`）でそのまま出る。

**DBMS 側は破れる。** 破れるのは梯子（`lad`）を敷いた段だけで、原因は影の列:

    M = (1,1)(2,1)(1,1)(2,1)   （d=1, plev=0, first, force）
    convC M = (1,0)(2,1)(3,1)(2,1)(3,1)          影は先頭の (1,0)
    末尾 (3,1) の 行1 親は (1,0)（index 0）。
    B = (1,1)(2,1) の像 (2,1)(3,1) は index 3 から始まるので、親は外にある。

BMS 側では `(1,1)` の行 1 が 1 なので親がなく `Pred` になる。
DBMS 側では影の `(1,0)` が親になる。**基本列が両者で食い違うのはこれが原因**で、
REINDEX の regime（id / shift / contr）はこの食い違いの分類にほかならない。

実測（`convC` の再帰の全段、BMS 標準形 <=7 列）:

    梯子なし: 4537 段すべて両側で局所化できる
    梯子あり: 1777 段のうち 352 段で DBMS 側の局所化が破れる

使い方: python3 localize.py [列数上限]
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import show, expand
from rows2 import gen, convC, split, units_split, contrPre


def fires(p, A, B, s, lad):
    """縮約が発火するか。"""
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


def walk(M, d, plev, first, force, acc, ex):
    if not M:
        return
    p, r = M[0], M[1:]
    s = p[1]
    A, B = split(p, r)
    lad = first and s == plev + 1 and (d <= s or force)
    contr = fires(p, A, B, s, lad)
    if not contr and len(B) >= 2:
        out = tuple(convC(M, d, plev, first, force))
        outB = tuple(convC(list(B), d, s, False, False))
        pl = len(out) - len(outB)
        okB = all(tuple(expand(tuple(M), n))
                  == tuple(list(M[:len(M) - len(B)]) + list(expand(tuple(B), n)))
                  for n in (1, 2, 3))
        okD = all(tuple(expand(out, n)) == tuple(list(out[:pl]) + list(expand(outB, n)))
                  for n in (1, 2, 3))
        acc[(lad, okB, okD)] += 1
        if not okD and len(ex) < 6:
            ex.append((tuple(M), d, plev, first, force, out, pl))
    if not contr:
        dd = d + 1 if lad else (s + 1 if (s > 0 and d <= s) else d)
        walk(list(A), dd + 1, s, True, (not lad) and first and s == plev, acc, ex)
        walk(list(B), d, s, False, False, acc, ex)


def main(lim=7):
    Ms = gen('BMS', lim)
    acc = collections.Counter()
    ex = []
    for i, M in enumerate(Ms):
        if i % 10000 == 0:
            core._exp_memo.clear(); core._flat_memo.clear()
        walk(list(M), 0, 0, True, False, acc, ex)
    print("lim=%d  (梯子, BMS 局所化, DBMS 局所化): %s" % (lim, dict(acc)))
    for M, d, plev, first, force, out, pl in ex:
        print("   M=%s d=%d plev=%d first=%s force=%s" % (show(M), d, plev, first, force))
        print("     convC M=%s  B の像は index %d から" % (show(out), pl))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
