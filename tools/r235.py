# -*- coding: utf-8 -*-
"""**課題 (V=Q) / (SROW) / (LE0ROOT)。**

## 母集団（⚠ 3.5% が住んでいるほう ＝ ランダムな `Q`）

`hr0 ∧ hz0 ∧ d>0` のランダムな `Q`（消費側ではない。§R209 の 3.5% はこちらで測った）。
**(V=Q)(SROW) の分母 = 「`j >= 1` かつブロック内で孤児だが塔＋ブロックでは親がいる」段**。
**(LE0ROOT) の分母 = 塔＋ブロックの全段**（`A` つき）。

## ★ 予想（教訓 45）

> **⚠ (V=Q) … **0 件**（§R191「`|V| = |Q|` の例は全部 `j = 0`」から）。**
> **⚠ (SROW) … `srow = 0` は **0 件**（L3 の `orphOK_row0`、緑）。**
> **⚠ (LE0ROOT) … `0 < d` なら **100%**（`hr0` で塔の根が行 0 最小 ⟹ 鎖は必ず根に入る）。**
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
        A = [(a0 + rnd.randrange(0, 3), rnd.randrange(E), rnd.randrange(2))
             for _ in range(rnd.randrange(0, 3))]        # 浅くない `A`（`rsum`）
        nA = len(A)
        for j in range(1, L):
            Bt = B[:j + 1]
            S = A + T + Bt
            j1 = len(T) + j                              # `T ++ Bt` の中での添字
            idx = nA + j1
            i1 = srow(S, idx)
            # ---------- (LE0ROOT) ----------
            c['(LE0ROOT) 分母'] += 1
            if trio.is_ancestor(S, 0, nA, idx): c['★ (LE0ROOT) 塔の根が le0 祖先'] += 1
            else:
                c['⛔ (LE0ROOT) 違う'] += 1
                if len(ex) < 3: ex.append(('LE0ROOT', Q, d, e, n, j, A))
            if trio.is_ancestor(S, 1, nA, idx): c['★ (LE0ROOT) le1 版も'] += 1
            else: c['⛔ (LE0ROOT) le1 版が違う'] += 1
            # ---------- (V=Q) / (SROW) ----------
            if not orphan(Bt, j): continue               # ブロック内で孤児
            par = trio.parent(S, i1, idx)
            if par is None: continue                     # ★ 破れた段だけ
            c['★ 分母: j>=1 の破れ'] += 1
            V = idx - par
            c[('(V=Q) 窓', '<' if V < L else ('=' if V == L else '>'))] += 1
            c[('(SROW) 破れの srow', i1)] += 1
            if i1 == 0 and len(ex) < 6:
                ex.append(('SROW=0', Q, d, e, n, j, A, par))
            if i1 == 1:
                # 的が錐の外（＝ ブロッカー）か
                out = not trio.is_ancestor(S, 1, nA, idx)
                c[('(SROW) srow=1 の的', '錐の外' if out else '錐の中')] += 1
            if V == L and len(ex) < 9:
                ex.append(('V=Q', Q, d, e, n, j, A, par, i1))
    D = c['★ 分母: j>=1 の破れ']; LD = c['(LE0ROOT) 分母']
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    print(f'  (LE0ROOT) 分母 {LD}   ★ 塔の根が `le0` 祖先 {c["★ (LE0ROOT) 塔の根が le0 祖先"]} '
          f'({100*c["★ (LE0ROOT) 塔の根が le0 祖先"]/max(LD,1):8.4f}%)   '
          f'⛔ 違う {c["⛔ (LE0ROOT) 違う"]}')
    print(f'            ★ `le1` 版 {c["★ (LE0ROOT) le1 版も"]} '
          f'({100*c["★ (LE0ROOT) le1 版も"]/max(LD,1):8.4f}%)   '
          f'⛔ 違う {c["⛔ (LE0ROOT) le1 版が違う"]}')
    print(f'  ★ 分母（`j>=1` かつ破れ）{D}')
    print('    (V=Q) 窓の長さ vs |Q|: ',
          dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple) and k[0] == '(V=Q) 窓')))
    print('    (SROW) 破れの srow: ',
          dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple)
                      and k[0] == '(SROW) 破れの srow')))
    print('    (SROW) srow=1 の的: ',
          dict((k[1], c[k]) for k in c if isinstance(k, tuple) and k[0] == '(SROW) srow=1 の的'))
    for x in ex: print('      ⛔ 例', x)
    print()


if __name__ == '__main__':
    run(7, (1,2,3), (0,1,2), (1,2,3,4), 120000, 951, '値域<7 d∈(1,2,3) e∈(0,1,2) n∈(1..4)')
    run(12, (1,3,5), (0,2,4), (1,2,3,5), 80000, 953, '★ 箱拡張 値域<12')
