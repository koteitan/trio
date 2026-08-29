# -*- coding: utf-8 -*-
"""**課題 H74: `LiftFlatMapLocal`（`L105Cap.lean:4634`）を文のまま検査する。**

⚠ **前提が 1 つも無い `∀ Q d e n`**。私も R2 も `TowerExpBigRow2` の母集団に限って
測っていたので、**文のままの検査は誰もしていなかった**。

    def LiftFlatMapLocal : Prop :=
      ∀ (Q : TrioSeq) (d e n : ℕ),
        Lift1 (mTower Q d e n) e
          = (List.range n).flatMap fun k => Lift1 (Lift1 (shiftr01 (d*k) 0 Q) (e*k)) e

⟹ **文のままでは偽**（反例あり）。前提を足しても、直るのは
**「ブロッカー無し」を足したときだけ**で、それは §210 で既に無料の場合。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, Lift1, shiftr01
from h80 import mTower


def lhs(Q, d, e, n):
    return Lift1(mTower(Q, d, e, n), e)


def rhs(Q, d, e, n):
    out = []
    for k in range(n):
        out += Lift1(Lift1(shiftr01(d * k, 0, Q), e * k), e)
    return out


def rootmin(Q):
    return all(Q[0][0] < Q[j][0] for j in range(1, len(Q)))


def noblk(Q):
    return all(Q[j][1] > Q[0][1] for j in range(1, len(Q)))


def main():
    cols = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]
    conds = [('（現状の文＝前提なし）', lambda Q, d: True),
             ('`d >= 1`', lambda Q, d: d >= 1),
             ('根が狭義最浅', lambda Q, d: bool(Q) and rootmin(Q)),
             ('**`d>=1` ∧ 根が狭義最浅**', lambda Q, d: d >= 1 and Q and rootmin(Q)),
             ('**`d>=1` ∧ 根が狭義最浅 ∧ ブロッカー無し**',
              lambda Q, d: d >= 1 and Q and rootmin(Q) and noblk(Q))]
    print('| 足した前提 | 検査した `(Q,d,e,n)` | **反例** |')
    print('|---|--:|--:|')
    for tag, ok in conds:
        n_tot = 0
        bad = []
        for L in (1, 2, 3):
            for Q in itertools.product(cols, repeat=L):
                Q = list(Q)
                for d in range(3):
                    if not ok(Q, d):
                        continue
                    for e in range(3):
                        for n in (2, 3, 4):
                            n_tot += 1
                            if lhs(Q, d, e, n) != rhs(Q, d, e, n) and len(bad) < 3:
                                bad.append((Q, d, e, n))
        print('| %s | %d | **%d** |' % (tag, n_tot, len(bad)))
        for Q, d, e, n in bad[:2]:
            print('    ⛔ Q=`%s` d=%d e=%d n=%d' % (fmt(Q), d, e, n))
            print('        左=`%s`  右=`%s`'
                  % (fmt(lhs(Q, d, e, n)), fmt(rhs(Q, d, e, n))))


if __name__ == '__main__':
    main()
