# -*- coding: utf-8 -*-
"""**課題 H74 (f1)(f2): `LiftFlatMapLocal` の反例は「実際の場面」に届くか。**

§235 で `LiftFlatMapLocal`（`L105Cap.lean:4634`）が**文のままでは偽**と分かった。
残る問いは 2 つ:

    (f2) **`R` から導いた `(Q,d,e)` だけに制限したら反例は 0 件か**  ← **本命**
         0 件なら「`R` から導く形に書き直せば通る」が確定する
    (f1) 自由な反例を `R` に戻したとき、`TowerExpBigRow2` の前提のどれが破れるか

⚠ **`LiftFlatMapLocal` の等式そのものを測る**（`mTower = operTower` とは別の式）。
H73 で測ったのは後者。**前者は誰も測っていない。**

    Lift1 (mTower Q d e n) e  ==  (range n).flatMap fun k => Lift1 (Lift1 (shiftr01 (d*k) 0 Q) (e*k)) e

⚠ 対応（`tower2_eq_operTower` の場面から）:
    `Q = (0,v,z) :: R.dropLast`,  `d = entry R 0 (|R|-1)`,  `e = entry R 1 (|R|-1) - v`
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, argOK, Lift1, shiftr01
from h80 import mTower
from h81 import lhs, rhs
from collections import Counter


def hyps(R, v, z):
    """`TowerExpBigRow2`（`L105Cap.lean:2880`）の前提を 1 つずつ判定して返す。"""
    return {
        '`argOK R`': argOK(R),
        '`2 <= |R|`': len(R) >= 2,
        '`z <= 1`': z <= 1,
        '`domT R m`': dom_m(R) is not None,
        '`srow R (|R|-1) = 2`': srow(R, len(R) - 1) == 2,
        '`hasParent ((0,v,z)::R) 2 |R|`':
            has_parent([(0, v, z)] + list(R), 2, len(R)),
        '`∃p∈R.dropLast, p.2.2 ≠ z`': any(p[2] != z for p in R[:-1]),
    }


def main():
    cols = [(a, b, c) for a in range(1, 3) for b in range(3) for c in range(3)]
    print('## (f2) ★本命: `R` から導いた `(Q,d,e)` で `LiftFlatMapLocal` の等式は成り立つか')
    print()
    print('| `|R|` | `n` | **分母（前提を全部満たす `(R,v,z)`）** | **等式が成立** | **反例** |')
    print('|--:|--:|--:|--:|--:|')
    ex = []
    for L in (2, 3, 4):
        for n in (2, 3, 4, 5):
            den = ok = 0
            for R in itertools.product(cols, repeat=L):
                R = list(R)
                if dom_m(R) is None or srow(R, len(R) - 1) != 2:
                    continue
                for v in range(3):
                    for z in range(2):
                        if not has_parent([(0, v, z)] + R, 2, len(R)):
                            continue
                        if not any(p[2] != z for p in R[:-1]):
                            continue
                        Q = [(0, v, z)] + R[:-1]
                        d = entry(R, 0, len(R) - 1)
                        e = entry(R, 1, len(R) - 1) - v
                        den += 1
                        if lhs(Q, d, e, n) == rhs(Q, d, e, n):
                            ok += 1
                        elif len(ex) < 5:
                            ex.append((R, v, z, Q, d, e, n))
            print('| %d | %d | **%d** | **%d** | **%d** |'
                  % (L, n, den, ok, den - ok))
    print()
    if ex:
        print('**⛔ 実際の場面での反例:**')
        for R, v, z, Q, d, e, n in ex:
            print('    R=`%s` v=%d z=%d ⟹ Q=`%s` d=%d e=%d n=%d'
                  % (fmt(R), v, z, fmt(Q), d, e, n))
            print('        左=`%s`' % fmt(lhs(Q, d, e, n)))
            print('        右=`%s`' % fmt(rhs(Q, d, e, n)))
    else:
        print('> **反例ゼロ ⟹ 「`R` から導く形に書き直せば通る」。**')
    print()

    # ---------------- (f1) 自由な反例を `R` に戻す
    print('## (f1) 自由な反例を `R` に戻すと、どの前提が破れるか')
    print()
    fail = Counter()
    nex = 0
    qcols = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]
    for L in (1, 2):
        for Q in itertools.product(qcols, repeat=L):
            Q = list(Q)
            for d in range(3):
                for e in range(3):
                    for n in (2, 3):
                        if lhs(Q, d, e, n) == rhs(Q, d, e, n):
                            continue
                        nex += 1
                        if Q[0][0] != 0:
                            fail['⛔ `Q` の根の深さが 0 でない（`(0,v,z)::…` の形ですらない）'] += 1
                            continue
                        v, z = Q[0][1], Q[0][2]
                        got = False
                        for c in range(3):
                            R = list(Q[1:]) + [(d, v + e, c)]
                            h = hyps(R, v, z)
                            if all(h.values()):
                                fail['⚠ **全部満たす（到達可能）**'] += 1
                                got = True
                                break
                        if not got:
                            R = list(Q[1:]) + [(d, v + e, 1)]
                            for k, ok2 in hyps(R, v, z).items():
                                if not ok2:
                                    fail['破れる前提: ' + k] += 1
    print('自由な反例（`|Q|<=2`, `d,e<3`, `n∈{2,3}`）: **%d** 件' % nex)
    print()
    wref.tally(fail, '`R` に戻したときに破れる前提（`c` を 0..2 で振って 1 つでも通れば「到達可能」）')


if __name__ == '__main__':
    main()
