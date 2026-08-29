# -*- coding: utf-8 -*-
"""**⛔ `LiftFlatMapLocal`（`L105Cap.lean:4634`）は文のままでは偽。前提を探す。**

⚠ **その docstring は私の実測（塔 276,876 / ブロック 1,245,942 / 列 6,846,876、例外 0）を
根拠に挙げているが、私が測ったのは `TowerExpBigRow2` の場面の `(Q,d,e)` だけ**である。
**文は `∀ Q d e n` で前提が 1 つも無い。** ⟹ **私の数字は文の裏づけになっていない。**
H12 の反例（独立に検算した）:

    `Q=(0,0,0)`, `d=0`, `e=1`, `n=2`         左 `(0,1,0)(0,1,0)` / 右 `(0,1,0)(0,2,0)`
    `Q=(0,0,0)(1,0,0)`, `d=2`, `e=1`, `n=2`  左 `…(2,1,0)…` / 右 `…(2,2,0)…`

**足すべき前提の候補を、母集団を絞らずに（`∀ Q d e n` のまま）測る。**

    (P0) 前提なし
    (P1) `d >= 1`
    (P2) 根が行 0 で狭義最浅（`∀ l, 0<l<|Q| → Q[0].0 < Q[l].0`）
    (P3) `d >= 1` ∧ (P2)
    (P4) **ブロッカー無し**（`∀ j>=1, Q[j].1 > v`）—— H12 が「これなら 0」と報告
    (P5) ★ **私の (D)**: `mTower` の全列 `j` について、`j` の行 0 祖先のうち
         **`j` 自身のブロックの外**にあり **`y ≠ 0`** のものは全部 行 1 > `v`
    (P6) (P3) ∧ (P5)

**(P5) が (P4) より真に弱いなら、私の (D) を足すのが正しい形。**
⚠ 「(P5) を満たすが (P4) を満たさない事例」が母集団にあるかを必ず数える（空虚でないことの証拠）。
"""
import sys, itertools, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r113 import Lift1, sh, mTower


def anc0(S, j):
    out = [j]
    while True:
        p = trio.parent(S, 0, out[-1])
        if p is None:
            break
        out.append(p)
    return out


def rhs(Q, d, e, n):
    out = []
    for k in range(n):
        out += Lift1(Lift1(sh(Q, d * k), e * k), e)
    return out


def cond_D(Q, d, e, n):
    """(P5) ＝ 私の (D) を `mTower` の上で。"""
    T = mTower(Q, d, e, n)
    if not T:
        return True
    L = len(Q); v = Q[0][1]
    for j in range(len(T)):
        k = j // L
        for y in anc0(T, j):
            if y != 0 and y // L != k and T[y][1] <= v:
                return False
    return True


def run(COLS, Lq, DS, ES, NS, label):
    c = Counter(); ex = {}
    for lq in Lq:
        for tail in itertools.product(COLS, repeat=lq - 1):
            Q = [(0, 0, 0)] + list(tail)          # `based` なので根の行 0 = 0
            for v in range(0, 3):
                Q[0] = (0, v, 0)
                for d in DS:
                    for e in ES:
                        for n in NS:
                            ok = (Lift1(mTower(Q, d, e, n), e) == rhs(Q, d, e, n))
                            P1 = d >= 1
                            P2 = all(Q[0][0] < Q[l][0] for l in range(1, len(Q)))
                            P4 = all(p[1] > v for p in Q[1:])
                            P5 = cond_D(Q, d, e, n)
                            for nm, p in (('(P0) 前提なし', True), ('(P1) d>=1', P1),
                                          ('(P2) 根が狭義最浅', P2), ('(P3) P1∧P2', P1 and P2),
                                          ('(P4) ブロッカー無し', P4),
                                          ('**(P5) 私の (D)**', P5),
                                          ('(P6) P3∧P5', P1 and P2 and P5)):
                                if p:
                                    c[nm + '/' + ('ok' if ok else '**反例**')] += 1
                            if P5 and not ok and 'P5 反例' not in ex:
                                ex['P5 反例'] = (Q[:], d, e, n)
                            if P5 and not P4:
                                c['(P5) は成り立つが (P4) は成り立たない'] += 1
    print(f'### {label}')
    for k in sorted(c):
        print(f'  {k:42s} {c[k]:10d}')
    for k in sorted(ex):
        print(f'  ★ {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    a = ap.parse_args()
    COLS = [(d, b, 0) for d in (0, 1, 2) for b in (0, 1, 2)]
    run(COLS, (1, 2, 3), (0, 1, 2), (0, 1, 2), (1, 2, 3),
        '⛔ `LiftFlatMapLocal` の前提を探す（`∀ Q d e n`、母集団を絞らない。全数）')
