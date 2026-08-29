# -*- coding: utf-8 -*-
"""**課題 H57-h: 予算検査 —— 「未判定」は切り詰めのせいで違反を隠していないか。**

`h58`〜`h64` はどれも「違反 0・未判定あり」で終わった。**未判定が違反を隠している
可能性**を潰すため、同じ母集団を**予算だけ変えて**測り直す:

    基準   `NS=(1,2,3)`  深さ 9   長さ 34  節点 60000
    増強   `NS=(1,2,3,4,5)` 深さ 18  長さ 68  節点 600000   ← **節点 10 倍**

見るのは 2 つ:

    1. **違反の数が動かないこと**（増えたら基準の予算では隠れていた）
    2. 未判定が減ること（減らなければ、その事例は原理的に決まらない可能性が高い）

⚠ 予算を上げると `NS` も広がるので **True は減りうる**（`∀ n` を多く見るため）。
つまり「未判定が増える」向きにも動く。**違反の数だけが健全な比較対象**である。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
import h61
from wref import (Ref, fmt, entry, argOK, Lift1, srow, has_parent,
                  has_parent_last, dom_m, levM, graft)
from collections import Counter

AMAX = 12


def verd(r):
    return '**違反**' if r is False else 'OK' if r is True else '未判定'


def sweep(ref, cols, lens):
    """4 本の核を同じ母集団で測る（予算を変えて 2 回呼ぶ）。"""
    pool = []
    for L in lens:
        for S in itertools.product(cols, repeat=L):
            pool.append(list(S))
    dec = [(S, ref.minstage(S, AMAX)) for S in pool]
    dec = [(S, u) for S, u in dec if u is not None]
    res = {'（段が確定した列）': Counter({'本': len(dec)})}

    def note(name, r):
        res.setdefault(name, Counter())[verd(r)] += 1

    for S, u in dec:
        note('`LiftStage`', ref.inW(Lift1(S, 1), u + 2))
        for M2 in h61.variants_row1(S):
            note('`Row1Mono`', ref.inW(M2, u))
        for p in cols[:9]:
            T = S + [p]
            if has_parent(T, srow(T, len(S)), len(S)):
                note('`WSnoc`', ref.inW(T, u))
    # TowerOK（節 2 が通る `R` だけ、`v ≤ 2`）
    rcols = [(a, b, c) for a in range(1, 3) for b in range(3) for c in range(2)]
    for L in (1, 2):
        for R in itertools.product(rcols, repeat=L):
            R = list(R)
            if dom_m(R) is None:
                continue
            X = R[:-1] if len(R) >= 2 else R
            if not all(ref.inW([(0, w, y)] + X, 2 * w + y) is True
                       for w in range(3) for y in range(2)):
                continue
            s = srow(R, len(R) - 1)
            for v in range(3):
                for z in range(2):
                    M = [(0, v, z)] + R
                    if not has_parent(M, s, len(R)):
                        continue
                    a = 2 * v + z
                    out = True
                    for n in (1, 2, 3):
                        r = ref.inW(trio.expand(list(M), n), a)
                        if r is False:
                            out = False
                            break
                        if r is None:
                            out = None
                    note('`TowerOK`', out)
    return res


def main():
    cols = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]
    base = Ref(ns=(1, 2, 3), maxdepth=9, maxlen=34, maxnodes=60000)
    big = Ref(ns=(1, 2, 3, 4, 5), maxdepth=18, maxlen=68, maxnodes=600000)
    wref.print_controls(base)
    for lens in ((1, 2), (3,)):
        print('## 長さ %s' % list(lens))
        print()
        rb = sweep(base, cols, lens)
        rg = sweep(big, cols, lens)
        print('| 核 | 判定 | 基準 | 増強（節点 10 倍・`NS` 5 本） |')
        print('|---|---|--:|--:|')
        for name in sorted(rb):
            for k in ('**違反**', 'OK', '未判定', '本'):
                if rb[name].get(k) or rg[name].get(k):
                    print('| %s | %s | %d | %d |'
                          % (name, k, rb[name].get(k, 0), rg[name].get(k, 0)))
        print()


if __name__ == '__main__':
    main()
