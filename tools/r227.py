# -*- coding: utf-8 -*-
"""**(z1b'') r226 の前件の誤りを直して測り直す。**

## ⚠ r226 の誤り（自分で発見）

`OrphOK` の前件は「**ブロック `B.take (j+1)` の中で**列 `j` が孤児」。
r226 は前件を「**塔＋ブロック**で孤児」にしていた ⟹ **`A = 空` の行が同語反復**（自明に 100%）。
⟹ 軸 (b)(c) の数字も別の主張を測っていた。**直す。**

## 正しい形

    前件: `orphan(B.take (j+1), j)`（`OrphOK`）／`orphan(1 ブロック分, 0)`（`OrphOK0`）
    後件: `orphan(A ++ mTower Q d e n ++ B.take (j+1), |A| + n*|Q| + j)`

## 軸（変えない）: `(a) A 空` ／ `(b) min(A 行0) >= entry Q 0 0` ／ `(c) 浅い`
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r224 import orphan
from r226 import axis


def run(E, DS, ES, NS, nsamp, seed, jmode, tag):
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    for _ in range(nsamp):
        L = rnd.randrange(2, 6)
        a0 = rnd.randrange(0, 4)
        Q = [(a0, rnd.randrange(0, E), 0)] + \
            [(rnd.randrange(a0 + 1, a0 + E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        if not all(Q[0][0] < Q[l][0] for l in range(1, L)): continue
        d = rnd.choice(DS); e = rnd.choice(ES); n = rnd.choice(NS)
        T = [tuple(x) for x in mTower(Q, d, e, n)]
        B = block(Q, d, e, n)
        if jmode == 'j0':
            # `OrphOK0`: ブロック根 ＝ ブロックの第 0 列。**1 列なので必ず孤児**（前件が自明）
            # ⟹ L3 の形は「塔の中でブロック根が孤児」なので、そちらを前件にする（§R200 の教訓）
            tgts = [(k * L, T, orphan(T, k * L)) for k in range(1, n)]
        else:
            tgts = [(len(T) + j, T + B[:j + 1], orphan(B[:j + 1], j))
                    for j in range(1, L)]
        for idx, base, prem in tgts:
            if not prem: continue                    # ★ 正しい前件
            for A in ([], [(0, 0, 0)],
                      [(rnd.randrange(max(a0, 1)), rnd.randrange(E), rnd.randrange(2))],
                      [(a0 + rnd.randrange(0, 3), rnd.randrange(E), rnd.randrange(2))],
                      [(rnd.randrange(a0 + E), rnd.randrange(E), rnd.randrange(2))
                       for _ in range(3)]):
                ax = axis(A, Q)
                S = A + base
                i = len(A) + idx
                c[(ax, '★ 分母')] += 1
                if orphan(S, i): c[(ax, '★ 孤児のまま')] += 1
                else:
                    c[(ax, '⛔ 親ができる')] += 1
                    if len(ex) < 6:
                        ex.append((ax[:3], Q, d, e, n, idx, A,
                                   trio.parent(S, srow(S, i), i)))
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for ax in ['(a) A が空', '(b) 浅くない（min(A の行0) >= entry Q 0 0）',
               '(c) ★ 浅い（min(A の行0) < entry Q 0 0）']:
        D = c[(ax, '★ 分母')]
        if not D: continue
        print(f'    {ax:44s} 分母 {D:8d}   ★ 孤児のまま {c[(ax,"★ 孤児のまま")]:8d} '
              f'({100*c[(ax,"★ 孤児のまま")]/D:8.4f}%)   ⛔ 親 {c[(ax,"⛔ 親ができる")]:8d} '
              f'({100*c[(ax,"⛔ 親ができる")]/D:8.4f}%)')
    for x in ex:
        print(f'      ⛔ 反例 [{x[0]}] Q={x[1]} d={x[2]} e={x[3]} n={x[4]} idx={x[5]} '
              f'A={x[6]} 親={x[7]}')
    print()


if __name__ == '__main__':
    run(7, (0,),      (0,1,2), (2,3,4), 60000, 861, 'j0', '★ OrphOK0（塔の中でブロック根が孤児）d=0')
    run(7, (1,2,3),   (0,1,2), (2,3,4), 60000, 863, 'j0', '★ OrphOK0 d>0')
    run(7, (0,),      (0,1,2), (2,3,4), 60000, 865, 'j1', '★★ OrphOK（前件＝ブロック内で孤児）d=0')
    run(7, (1,2,3),   (0,1,2), (2,3,4), 60000, 867, 'j1', '★★ OrphOK d>0')
