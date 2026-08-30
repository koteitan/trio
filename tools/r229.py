# -*- coding: utf-8 -*-
"""**課題 (s5) —— `j >= 1` の破れで、親はどこにいるか。**

## 分母（明記）

`hr0` を満たすランダムな `Q`（根の行 0 は 0..3 で振る）、`d > 0`、`A` は 3 種。
**「ブロック `B.take (j+1)` の中で列 `j` が孤児」かつ「`A ++ 塔 ++ B.take (j+1)` では親がいる」組**
（＝ §R209 の 3.5% の中身）。

## ★ 予想（教訓 45）

> **⚠ team-lead の読み（反例の親 15 は塔の最後のブロック）から **(B) 1 ブロック手前が支配的**。**
> **⚠ (C) 2 ブロック以上手前は **0** と予想（§R196 の「飛び越えない」と整合）。**
> **⚠ (s5b) `|V| <= |Q|` は **100%** と予想（§R173/§R191 の「`|V| > |Q|` は 0.0000%」）。**
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


def run(E, DS, ES, NS, nsamp, seed, tag):
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
        for j in range(1, L):
            Bt = B[:j + 1]
            if not orphan(Bt, j): continue           # ★ 前件: ブロック内で孤児
            for am, A in (('A 空', []),
                          ('A 浅くない（rsum 成立）',
                           [(a0 + rnd.randrange(0, 3), rnd.randrange(E), rnd.randrange(2))
                            for _ in range(rnd.randrange(1, 4))]),
                          ('A 浅い（rsum 破れ）',
                           [(rnd.randrange(max(a0, 1)), rnd.randrange(E), rnd.randrange(2))
                            for _ in range(rnd.randrange(1, 4))])):
                S = A + T + Bt
                nA = len(A); idx = nA + len(T) + j
                if orphan(S, idx): continue          # ★ 破れた組だけ
                c[(am, '★ 分母: 破れた組')] += 1
                par = trio.parent(S, srow(S, idx), idx)
                if par < nA:
                    w = '(D) A の中'
                elif par >= nA + len(T):
                    w = '(A) 新しいブロックの中'
                else:
                    k = (par - nA) // L             # 塔の何ブロック目か
                    back = (n - 1) - k              # 何ブロック手前か（0 = 最後のブロック）
                    w = ('(B) 1 ブロック手前' if back == 0
                         else '(C) ⛔ %d ブロック以上手前' % (back + 1))
                c[(am, w)] += 1
                V = idx - par                        # 窓の長さ
                c[(am, ('|V| <= |Q|' if V <= L else '⛔ |V| > |Q|'))] += 1
                if w.startswith('(C)') and len(ex) < 4:
                    ex.append((am, Q, d, e, n, j, A, par, V, L))
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for am in ('A 空', 'A 浅くない（rsum 成立）', 'A 浅い（rsum 破れ）'):
        D = c[(am, '★ 分母: 破れた組')]
        if not D: continue
        print(f'  {am}   ★ 分母（破れた組）{D}')
        for w in ['(A) 新しいブロックの中', '(B) 1 ブロック手前', '(D) A の中']:
            print(f'      {w:24s} {c[(am,w)]:8d} ({100*c[(am,w)]/D:8.4f}%)')
        cs = [(k[1], c[k]) for k in c if k[0] == am and k[1].startswith('(C)')]
        print(f'      (C) ⛔ 2 ブロック以上手前 … {sum(v for _, v in cs)}  {dict(cs)}')
        for w in ['|V| <= |Q|', '⛔ |V| > |Q|']:
            print(f'      {w:24s} {c[(am,w)]:8d} ({100*c[(am,w)]/D:8.4f}%)')
    for x in ex:
        print(f'      ⛔ (C) の例 [{x[0]}] Q={x[1]} d={x[2]} e={x[3]} n={x[4]} j={x[5]} '
              f'A={x[6]} 親={x[7]} |V|={x[8]} |Q|={x[9]}')
    print()


if __name__ == '__main__':
    run(7, (1,2,3), (0,1,2), (2,3,4), 80000, 911, '値域<7 d∈(1,2,3) e∈(0,1,2) n∈(2,3,4)')
    run(12, (1,3,5), (0,2,4), (2,3,5), 50000, 913, '★ 箱拡張 値域<12 d∈(1,3,5) n∈(2,3,5)')
