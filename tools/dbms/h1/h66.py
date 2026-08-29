# -*- coding: utf-8 -*-
"""**課題 H57-i: `GraftFromExp`（＝「`Aop` の節 2 から節 3 を作る」）を測る。**

    def GraftFromExp : Prop :=
      ∀ (m) (R), R ≠ [] → argOK R → domT R m →
        (∀ n ≥ 1, R⟦n⟧ ∈ Wstar) →                    ← `domT` より **`R.dropLast ∈ Wstar`**
        ∀ y ∈ W m, based y → **graft R y ∈ Wstar**

`TowerGraft2`（`Wset:4498`）と `TowerExp`（`Wset:4507`）はこの前後をつなぐ 2 本で、
`TowerExp` の仮定は h59 の「節 2」の場合そのもの、`TowerGraft2` の仮定は
`GraftFromExp` の**結論**そのものである。⟹ ここを測ると 3 本まとめて効く。

**陰性対照**: `y ∈ W m` を落として `lev y 0 > m` の `y` を使う ⟹ 違反が出るべき。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import Ref, fmt, argOK, graft, dom_m, srow, has_parent, levM
from collections import Counter

VMAX = 2


def wstar(ref, X, vmax=VMAX):
    if not argOK(X):
        return 'yes'
    out = 'yes'
    for w in range(vmax + 1):
        for y in range(2):
            r = ref.inW([(0, w, y)] + list(X), 2 * w + y)
            if r is False:
                return 'no'
            if r is None:
                out = '?'
    return out


def main(lens=(1, 2, 3)):
    ref = Ref(ns=(1, 2, 3), maxdepth=9, maxlen=34, maxnodes=1500)
    wref.print_controls(ref)
    rcols = [(a, b, c) for a in range(1, 4) for b in range(3) for c in range(2)]
    ycols = [(a, b, c) for a in range(2) for b in range(2) for c in range(2)]
    yhead = [(0, b, c) for b in range(3) for c in range(2)]
    ys = [[]]
    for L in (1, 2):
        for h in yhead:
            for rest in itertools.product(ycols, repeat=L - 1):
                ys.append([h] + list(rest))
    Rs = []
    for L in lens:
        for R in itertools.product(rcols, repeat=L):
            R = list(R)
            if dom_m(R) is None:
                continue
            Rs.append(R)
    print('## 母集団')
    print()
    print('`R`（`argOK`、`∃m domT R m`、長さ %s）: **%d** 本' % (list(lens), len(Rs)))
    print()
    print('データ `y`（`based`、長さ 0..2）: **%d** 本' % len(ys))
    print()

    st = Counter()
    keep = []
    for R in Rs:
        X = R[:-1] if len(R) >= 2 else R
        s = wstar(ref, X)
        st[s] += 1
        if s == 'yes':
            keep.append(R)
    wref.tally(st, '仮定（節 2 = `R.dropLast ∈ Wstar`、`v <= %d` で確認）' % VMAX)
    import random as _r
    if len(keep) > 100:
        keep = _r.Random(3).sample(keep, 100)
        print('⟹ 仮定が通った `R` から無作為 **100** 本で測る')
        print()

    tot = Counter()
    ctl = Counter()
    ex = []
    for R in keep:
        m = dom_m(R)
        for y in ys:
            r = ref.inW(y, m)
            G = graft(R, y)
            if len(G) > 7:
                continue
            if r is True:
                s = wstar(ref, G)
                k = ('**違反**' if s == 'no'
                     else 'OK' if s == 'yes' else '未判定')
                tot[k] += 1
                if s == 'no' and len(ex) < 6:
                    ex.append((R, m, y))
            elif r is False:
                s = wstar(ref, G)          # 陰性対照: `y ∈ W m` を落とす
                ctl['**違反**' if s == 'no'
                    else 'OK' if s == 'yes' else '未判定'] += 1
    wref.tally(tot, '**`GraftFromExp`**（`y ∈ W m`、`based y` ⟹ `graft R y ∈ Wstar`）')
    for R, m, y in ex:
        print('    **反例**: R=`%s` m=%d y=`%s` ⟹ graft=`%s`'
              % (fmt(R), m, fmt(y), fmt(graft(R, y))))
    if ex:
        print()
    wref.tally(ctl, '陰性対照（`y ∈ W m` を確定で破る `y`。違反が出るべき）')


if __name__ == '__main__':
    main(lens=(2, 3))
