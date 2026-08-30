# -*- coding: utf-8 -*-
"""**課題 (s8) —— L3 の 3 分割で `OrphOK` の破れを分類。**

## 3 分割（team-lead が L3 から渡した形）

    (i)   親が**行 0** で選ばれた            … ★ 0 件のはず（L3 の緑）
    (ii)  親が**行 1** で、**的の行 1 が塔の根以下**  … ここに集まるはず
    (iii) 親が**行 2** で、**的の行 2 が塔の根以下**  … `zle1 ＋ hz0` で潰せるはず
    (iv)  上のどれでもない（親の行はあるが「塔の根以下」でない）← ★ 私が足した受け皿

## ⚠ 先に算術（測る前に）

的がブロック根 `k`（`k >= 1`）なら 行 1 ＝ `Q[0][1] + e*k`、塔の根の行 1 ＝ `Q[0][1]`
⟹ **「的の行 1 が塔の根以下」⟺ `e*k = 0` ⟺ `e = 0`**
⟹ **`e > 0` の破れは (ii) に入らない**はず ⟹ **(iv) が要る**。⟹ `e` で切って測る。

## 母集団（(s6) と同じ ＋ 対照）

`hr0` のランダムな `Q`（根の行 0 >= 1）、`d > 0`、`A` は **浅い**（本命）と **浅くない**（対照 (s8c)）。
分母 = **塔の中でブロック根（`k>=1`）が孤児**な組。
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r224 import orphan


def run(E, DS, ES, NS, nsamp, seed, tag):
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    for _ in range(nsamp):
        L = rnd.randrange(2, 6)
        a0v = rnd.randrange(1, 5)
        Q = [(a0v, rnd.randrange(0, E), 0)] + \
            [(rnd.randrange(a0v + 1, a0v + E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        if not all(Q[0][0] < Q[l][0] for l in range(1, L)): continue
        d = rnd.choice(DS); e = rnd.choice(ES); n = rnd.choice(NS)
        T = [tuple(x) for x in mTower(Q, d, e, n)]
        for am, A in (('★ 浅い A（本命）',
                       [(rnd.randrange(0, a0v), rnd.randrange(E), rnd.randrange(2))
                        for _ in range(rnd.randrange(1, 4))]),
                      ('対照: 浅くない A（rsum）',
                       [(a0v + rnd.randrange(0, 3), rnd.randrange(E), rnd.randrange(2))
                        for _ in range(rnd.randrange(1, 4))])):
            S = A + T; nA = len(A)
            root = T[0]                      # 塔の根
            for k in range(1, n):
                idx = k * L
                if not orphan(T, idx): continue       # ★ 前件
                ekey = 'e = 0' if e == 0 else 'e > 0'
                c[(am, ekey, '★ 分母')] += 1
                i = nA + idx
                i1 = srow(S, i)
                par = trio.parent(S, i1, i)
                if par is None:
                    c[(am, ekey, '★ 孤児のまま')] += 1
                    continue
                c[(am, ekey, '⛔ 破れ')] += 1
                tgt = S[i]
                if i1 == 0:
                    w = '⛔⛔ (i) 親が行 0'
                elif i1 == 1:
                    w = ('(ii) 親が行 1 ∧ 的の行 1 <= 塔の根' if tgt[1] <= root[1]
                         else '★ (iv) 親が行 1 だが 的の行 1 > 塔の根')
                else:
                    w = ('(iii) 親が行 2 ∧ 的の行 2 <= 塔の根' if tgt[2] <= root[2]
                         else '★ (iv) 親が行 2 だが 的の行 2 > 塔の根')
                c[(am, ekey, w)] += 1
                if w.startswith('⛔⛔') and len(ex) < 4:
                    ex.append((am, Q, d, e, n, k, A, i1, par))
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    KEYS = ['★ 孤児のまま', '⛔ 破れ', '⛔⛔ (i) 親が行 0',
            '(ii) 親が行 1 ∧ 的の行 1 <= 塔の根', '★ (iv) 親が行 1 だが 的の行 1 > 塔の根',
            '(iii) 親が行 2 ∧ 的の行 2 <= 塔の根', '★ (iv) 親が行 2 だが 的の行 2 > 塔の根']
    for am in ('★ 浅い A（本命）', '対照: 浅くない A（rsum）'):
        for ekey in ('e = 0', 'e > 0'):
            D = c[(am, ekey, '★ 分母')]
            if not D: continue
            print(f'  {am} / {ekey}   ★ 分母 {D}')
            for w in KEYS:
                print(f'      {w:38s} {c[(am,ekey,w)]:9d} ({100*c[(am,ekey,w)]/D:8.4f}%)')
    for x in ex:
        print(f'      ⛔⛔ (i) の例 [{x[0]}] Q={x[1]} d={x[2]} e={x[3]} n={x[4]} k={x[5]} '
              f'A={x[6]} srow={x[7]} 親={x[8]}')
    print()


if __name__ == '__main__':
    run(7, (1,2,3), (0,1,2), (2,3,4), 100000, 941, '値域<7 d∈(1,2,3) e∈(0,1,2) n∈(2,3,4)')
    run(12, (1,3,5), (0,2,4), (2,3,5), 60000, 943, '★ 箱拡張 値域<12')
