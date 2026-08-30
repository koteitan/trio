# -*- coding: utf-8 -*-
"""**課題 (s10)(s11)。**

## (s10) `j >= 1` の段で `|V| = |Q|` は何件か

**分母 = 「`j >= 1` かつ `hloc` が破れる段」**（＝ ブロック内で孤児だが塔＋ブロックでは親がいる）。
> **⚠ 予想: **0 件**（§R191 の「`|V| = |Q|` の例は全部 `j = 0`」から）。**

## (s11) `h1out` の遺伝が破れるとき、ブロッカーは窓の外に落ちているか

H12 の `outOfCone_dichotomy`: **(a) `j` 自身がブロッカー** ⟹ `h1out` 破れ／
**(b) 手前にブロッカー `y`** ⟹ `h1out` 自動。ブロッカーは **`le0` の祖先**（`L105Cap:7149`）。
> **⚠ 予想: `Q` のブロッカーが `y < p` で**窓の外**に落ちるのが主因。見積もり 60〜100%。**
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r169 import domT
from r201 import dOf, eOf
from r206 import hr0
from r224 import orphan


def h1out_bad(X):
    """訂正後の `h1out` の破れる列。"""
    return [j for j in range(1, len(X))
            if not trio.is_ancestor(X, 1, 0, j) and X[j][2] == 0
            and X[j][1] > 0 and not (X[0][1] < X[j][1])]


def run(L, R1, VS, ZS, TS, NS, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    c = Counter(); ex = []; t0 = time.time()
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        if srow(R, len(R) - 1) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q = M[:-1]
                    if len(Q) < 2: continue
                    d, e = dOf(M), eOf(M)
                    if not (d > 0 and hr0(Q) and Q[0][2] == 0): continue
                    LQ = len(Q)
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        # ---------- (s10) ----------
                        for j in range(1, LQ):
                            Bt = B[:j + 1]
                            if not orphan(Bt, j): continue      # ブロック内で孤児
                            S = T + Bt; idx = len(S) - 1
                            par = trio.parent(S, srow(S, idx), idx)
                            if par is None: continue            # ★ hloc が破れた段だけ
                            c['(s10) ★ 分母'] += 1
                            V = idx - par
                            if V < LQ:   c['(s10) ★ |V| < |Q|'] += 1
                            elif V == LQ:
                                c['(s10) ⛔ |V| = |Q|'] += 1
                                c[('(s10b) srow', srow(S, idx))] += 1
                                if len(ex) < 3: ex.append(('s10', Q, d, e, n, j, par, V))
                            else:        c['(s10) ⛔⛔ |V| > |Q|'] += 1
                        # ---------- (s11) ----------
                        for j in range(1, LQ):
                            S1 = T + B[:j + 1]; last1 = len(S1) - 1
                            par1 = trio.parent(S1, srow(S1, last1), last1)
                            if par1 is None: continue
                            Vw = [tuple(x) for x in S1[par1:last1]]
                            if len(Vw) < 2: continue
                            if not h1out_bad(Q):                # `Q` 側は `h1out` 成立
                                bad = h1out_bad(Vw)
                                if not bad: continue
                                c['(s11) ★ 分母: h1out(Q) 成立だが h1out(V) 破れ'] += 1
                                for jp in bad:
                                    c['(s11) 破れる列'] += 1
                                    # 窓の中の絶対位置
                                    absj = par1 + jp
                                    # `le0` の祖先鎖を全体で辿り、ブロッカー（行1 <= 窓の根の行1）を探す
                                    root1 = Vw[0][1]
                                    y = absj; found = None
                                    while True:
                                        y = trio.parent(S1, 0, y)
                                        if y is None: break
                                        if S1[y][1] <= root1: found = y; break
                                    if found is None:
                                        c['(s11) ブロッカーが鎖上に無い'] += 1
                                    elif found < par1:
                                        c['★ (s11) ブロッカーが窓の外（< p）'] += 1
                                    else:
                                        c['⛔ (s11) ブロッカーが窓の中'] += 1
                                        if len(ex) < 6:
                                            ex.append(('s11', Q, d, e, n, j, par1, Vw, jp, found))
    D = c['(s10) ★ 分母']
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    print(f'  (s10) ★ 分母（`j>=1` かつ `hloc` が破れる段）{D}')
    for k in ['(s10) ★ |V| < |Q|', '(s10) ⛔ |V| = |Q|', '(s10) ⛔⛔ |V| > |Q|']:
        print(f'      {k:24s} {c[k]:9d} ({100*c[k]/max(D,1):8.4f}%)')
    print('      (s10b) `|V|=|Q|` のときの srow: ',
          dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple))))
    E = c['(s11) ★ 分母: h1out(Q) 成立だが h1out(V) 破れ']
    print(f'  (s11) ★ 分母（`h1out(Q)` 成立だが `h1out(V)` 破れ）{E}   破れる列 {c["(s11) 破れる列"]}')
    for k in ['★ (s11) ブロッカーが窓の外（< p）', '⛔ (s11) ブロッカーが窓の中',
              '(s11) ブロッカーが鎖上に無い']:
        print(f'      {k:34s} {c[k]:9d} ({100*c[k]/max(c["(s11) 破れる列"],1):8.4f}%)')
    for x in ex:
        print('      ⛔ 例', x)
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '消費側 |R|=3 行1<3')
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), '★ 消費側 |R|=3 行1<5')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '★ 消費側 |R|=4 行1<3')
