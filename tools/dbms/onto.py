"""**全射の採点器** — ImgClosedT より 20 倍安く、20 倍鋭い土俵（2026-08-28）。

## なぜこれが ImgClosedT の代わりになるか

    conv3 が DBMS 3 行 z<2 標準形の上に**全射**
      => 任意の A, m で (conv3 A)<m> は DBMS 標準形（conv3 A が標準形で、
         展開は標準形性を保つ）なので、逆像 B がある
      => **ImgClosedT（したがって ImgCofinalT）が自明に成り立つ**

しかも DBMS 標準形は BMS 標準形よりずっと少ない:

    列数    BMS 標準形   DBMS 標準形
    <=4        144           25
    <=5       1018          100
    <=6       8387          528
    <=7      77282         3514

`conv3` は単射（実測、交差衝突 0）なので、全射が言えれば
**conv3 は BMS 標準形と DBMS 標準形の間の全単射**になる。
2 行では Naruyoko 氏の結果があり「全射は両側の共終性だけで出る」。

## 測り方

すべての DBMS 標準形 T について

    B = d2b3(T)   が BMS 3 行 z<2 標準形で、conv3(B) == T

を確かめる。`d2b3` が外したときは逆像が無いとは限らないので、
返り値の「外れ」は**非全射の上界**である（`search` で詰めることはできる）。

## 使い方

    python3 onto.py 7            <=7 列まで採点（数秒）
    python3 onto.py 8            <=8 列（DBMS 標準形 24000 個くらい）

## 実測（v14 h1, 2026-08-28）

    <=4 列    25 個   全射 25   外れ 0
    <=5 列   100 個   全射 100  外れ 0
    <=6 列   528 個   全射 524  外れ **4**
    <=7 列  3514 個   全射 3432 外れ **82**（<=6 列の 4 個の延長）

外れ 4 個はぜんぶ `(0,0,0)(1,0,0)(2,1,0)(3,2,1) X (2,0,0)` の形:

    T      = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(3,0,0)(2,0,0)
    d2b3   = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(1,0,0)   BMS 標準形
    conv3  = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(3,0,0)(1,0,0)
                                                ^^^^^^^ 行 0 が 1 だけ浅い

3 個は**行 0 が浅すぎ**（族 β と同じ病）、1 個は**行 1 が浅すぎ**（族 α の残り）。
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rows3
from inv3 import d2b3
from core import isstd, show


def score(lim=7, zcap=1, f=None, verbose=1):
    """(全射だった個数, DBMS 標準形の総数, 外れのリスト) を返す。"""
    f = f or rows3.b2d3
    t0 = time.time()
    D = sorted(rows3.gen3('DBMS', lim, zcap=zcap), key=rows3.key)
    ok, bad = 0, []
    for T in D:
        T = tuple(map(tuple, T))
        try:
            B = d2b3(T)
        except Exception as e:
            bad.append((T, None, 'd2b3 例外 %s' % e))
            continue
        if not B:
            bad.append((T, None, 'd2b3 が None'))
            continue
        if not isstd(B, 'BMS') or any(c[2] > 1 for c in B):
            bad.append((T, B, 'B が BMS 標準形でない'))
            continue
        U = tuple(f(list(B)))
        if U != T:
            bad.append((T, B, 'conv3(B) != T'))
            continue
        ok += 1
    if verbose:
        print('全射 <=%d 列: DBMS 標準形 %d 個   全射 %d   外れ %d   (%.0fs)'
              % (lim, len(D), ok, len(bad), time.time() - t0))
        for T, B, r in bad[:verbose * 8]:
            print('    ', show(list(T)), ' <-', r)
            if B:
                print('        d2b3 =', show(list(B)))
                print('        像   =', show(list(f(list(B)))))
    return ok, len(D), bad


if __name__ == '__main__':
    for lim in range(4, (int(sys.argv[1]) if len(sys.argv) > 1 else 7) + 1):
        score(lim, verbose=1 if lim >= 6 else 0)
