# -*- coding: utf-8 -*-
"""**課題 H73: `mTower`（ブロック局所マスク）＝ `operTower`（塔全体マスク）か。**

⚠ **定義は `file:line` から写した**（教訓 25）:

    **`L105.mTower`（`L105Cap.lean:4159`）** —— 私の閉じた形
      `mTower Q d0 d1 n = (range n).flatMap fun k => Lift1 (shiftr01 (d0*k) 0 Q) (d1*k)`
      ⟹ マスクは**各ブロックの中（`shiftr01 … Q` の錐）**で計算される

    **`L105.operTower`（`L105Cap.lean:3407`）** —— `oper_cons_tower2` が実際に作る形
      `operTower Q d e 0     = []`
      `operTower Q d e (n+1) = Q ++ shiftr01 d 0 (**Lift1 (operTower Q d e n) e**)`
      ⟹ マスクは**それまでに作った塔全体**の錐で計算される（再帰）

**L3 の指摘**: `Wset.le1_take`（`:908`、緑）は**接頭辞局所性**しか与えないので、
第 `k` ブロック（`k >= 1`）のマスクが `Q` だけで決まることは Lean では**出ない**。
私の §211「マスクは全ブロックで同一」は**その主張の実測にすぎない**。

⟹ **`mTower = operTower` が真なら L3 は `mTower` の形で立て直せる。偽なら塔全体で見続けるしかない。**

## 測るもの（単位を必ず書く ―― 教訓 26）

    (q1) **塔単位**: `mTower Q d e n == operTower Q d e n` の一致率（`n` も振る）
    (q2) **陰性対照**: ブロッカーのある `Q` で、第 2 ブロックのマスクが第 1 と違う例を探す
    (q3) **陽性対照**: わざと壊した版（マスクを 1 列ずらす）が実際に鳴るか
    (q4) `|R|` と `n` を伸ばして壊しにいく（教訓 21）
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, srow, has_parent, dom_m, Lift1, shiftr01
from collections import Counter


def mTower(Q, d0, d1, n):
    """`L105Cap.lean:4159` そのまま。"""
    out = []
    for k in range(n):
        out += Lift1(shiftr01(d0 * k, 0, Q), d1 * k)
    return out


def operTower(Q, d, e, n):
    """`L105Cap.lean:3407` そのまま（再帰）。"""
    if n == 0:
        return []
    return list(Q) + shiftr01(d, 0, Lift1(operTower(Q, d, e, n - 1), e))


def broken(Q, d0, d1, n):
    """(q3) 陽性対照: マスクを 1 列ずらした壊れた版。鳴るべき。"""
    out = []
    for k in range(n):
        B = shiftr01(d0 * k, 0, Q)
        cone = [trio.is_ancestor(list(B), 1, 0, i) for i in range(len(B))]
        cone = [False] + cone[:-1]                     # ← 1 列ずらす
        out += [(c[0], c[1] + (d1 * k if cone[i] else 0), c[2])
                for i, c in enumerate(B)]
    return out


def main(lens=(2, 3, 4), nmax=5):
    cols = [(d, b, c) for d in range(1, 3) for b in range(3) for c in range(2)]
    print('## H73: `mTower` == `operTower` か（**塔単位**の一致率）')
    print()
    print('| `|R|` | `n` | **分母（塔）** | **一致** | 一致率 | 陽性対照（壊した版が鳴る） |')
    print('|--:|--:|--:|--:|--:|--:|')
    ex = []
    for L in lens:
        for n in range(2, nmax + 1):
            den = ok = ctl = 0
            for R in itertools.product(cols, repeat=L):
                R = list(R)
                if dom_m(R) is None:
                    continue
                if srow(R, len(R) - 1) != 2:
                    continue
                for v in range(3):
                    for z in range(2):
                        S = [(0, v, z)] + R
                        if not has_parent(S, 2, len(R)):
                            continue
                        if not any(p[2] != z for p in R[:-1]):
                            continue
                        Q = [(0, v, z)] + R[:-1]
                        d0 = wref.entry(R, 0, len(R) - 1)
                        d1 = wref.entry(R, 1, len(R) - 1) - v
                        den += 1
                        a = mTower(Q, d0, d1, n)
                        b = operTower(Q, d0, d1, n)
                        if a == b:
                            ok += 1
                        elif len(ex) < 5:
                            ex.append((R, v, z, n, Q, a, b))
                        if broken(Q, d0, d1, n) != b:
                            ctl += 1
            print('| %d | %d | **%d** | **%d** | **%.1f%%** | %d (%.1f%%) |'
                  % (L, n, den, ok, 100.0 * ok / max(den, 1), ctl,
                     100.0 * ctl / max(den, 1)))
    print()
    if ex:
        print('**⛔ 食い違いの例:**')
        for R, v, z, n, Q, a, b in ex:
            print('    R=`%s` v=%d z=%d n=%d' % (fmt(R), v, z, n))
            print('        Q       =`%s`' % fmt(Q))
            print('        mTower  =`%s`' % fmt(a))
            print('        operTower=`%s`' % fmt(b))
    else:
        print('> **食い違いゼロ。**')
    print()


if __name__ == '__main__':
    main(lens=(2, 3, 4), nmax=5)
