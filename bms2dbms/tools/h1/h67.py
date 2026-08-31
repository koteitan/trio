# -*- coding: utf-8 -*-
"""**課題 H57-j: `TowerOK2`（`srow = 2` の枝）だけを予算を上げて測る。**

`h59` の素朴な走りは **`srow = 2` の 800 事例が全部「未判定」**だった。
`srow = 2` こそが残核（`STATUS.md` の「唯一の核」）なので、**そこが全部未判定では
測ったことにならない**。ここでは母集団を `srow = 2` に絞り、節点予算を大きく取る。

    `h59`   `maxnodes = 1500`   ⟹ srow=2 は **OK 0 / 未判定 800**
    ここ    `maxnodes = 40000`  ⟹ 下の表

**陰性対照**は同じ母集団で段を 1 下げた版（`h63` と同じ壊し方）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import Ref, fmt, argOK, dom_m, srow, has_parent
from collections import Counter

VMAX = 3
NSC = (1, 2, 3)


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


def main(nodes=40000, lens=(1, 2, 3)):
    ref = Ref(ns=NSC, maxdepth=11, maxlen=40, maxnodes=nodes)
    wref.print_controls(ref)
    cols = [(a, b, c) for a in range(1, 4) for b in range(3) for c in range(2)]
    Rs = []
    for L in lens:
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            if dom_m(R) is None:
                continue
            if srow(R, len(R) - 1) != 2:        # ← **`TowerOK2` の枝だけ**
                continue
            Rs.append(R)
    print('## 母集団: `srow R (|R|-1) = 2` の `R` だけ（`maxnodes = %d`）' % nodes)
    print()
    print('`∃m domT R m` かつ `srow = 2` の `R`: **%d** 本' % len(Rs))
    print()

    wcache = {}
    keep = []
    st = Counter()
    for R in Rs:
        X = R[:-1] if len(R) >= 2 else R
        k = tuple(map(tuple, X))
        if k not in wcache:
            wcache[k] = wstar(ref, list(X))
        st[wcache[k]] += 1
        if wcache[k] == 'yes':
            keep.append(R)
    wref.tally(st, '`Aop` の節 2（`R.dropLast ∈ Wstar` を `v <= %d` で確認）' % VMAX)

    tot = Counter()
    ctl = Counter()
    ex = []
    rows = []
    for R in keep:
        s = 2
        for v in range(3):
            for z in range(2):
                M = [(0, v, z)] + R
                if not has_parent(M, s, len(R)):
                    continue
                for da in (0, 1):
                    a = 2 * v + z + da
                    verd = 'OK'
                    for n in NSC:
                        r = ref.inW(trio.expand(list(M), n), a)
                        if r is False:
                            verd = '**違反**'
                            break
                        if r is None:
                            verd = '未判定'
                    tot[verd] += 1
                    if da == 0:
                        rows.append((verd, M))
                    if verd == '**違反**' and len(ex) < 8:
                        ex.append((R, v, z, a))
                # 陰性対照: 段を 1 下げる
                a0 = 2 * v + z
                if a0 >= 1:
                    cv = 'OK'
                    for n in NSC:
                        r = ref.inW(trio.expand(list(M), n), a0 - 1)
                        if r is False:
                            cv = '**違反**'
                            break
                        if r is None:
                            cv = '未判定'
                    ctl[cv] += 1
    wref.tally(tot, '**`TowerOK2`**（`srow = 2`、`Aop` 節 2 が通る `R`）')
    for R, v, z, a in ex:
        print('    **反例**: R=`%s` v=%d z=%d a=%d' % (fmt(R), v, z, a))
        print('              M=`%s`' % fmt([(0, v, z)] + R))
    if ex:
        print()
    wref.tally(ctl, '陰性対照（同じ母集団で段を 1 下げた版。違反が出るべき）')
    wref.degeneracy(rows)


if __name__ == '__main__':
    main(nodes=40000, lens=(1, 2))
    print()
    main(nodes=40000, lens=(3,))
