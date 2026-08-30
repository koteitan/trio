# -*- coding: utf-8 -*-
"""**(HZ0) ＋ (C1)(C2)(C3) の (a)(b)。**

## (HZ0) `hz0(V)` が偽の 4,836 件は L3 の 2 つの段の**中か外か**

    段の判別: `srow(Sj, last)`（消費した列の `srow`）と、親 `p` の位置
      `p == br`（**ブロックの根**＝ `p_rel = 0`）／ `p > br`（ブロックの中）／ `p < br`（塔の中）

## 候補条件（`Q` の中で判定）

    (C1) `∀ i, 0 < i → 0 < entry Q 1 i`        行 1 = 0 の列が無い
    (C2) `∀ i, i < |Q| → le1 Q 0 i`            全列が錐の中
    (C3) `∀ i, 0 < i → entry Q 1 0 < entry Q 1 i`  ブロッカーが無い

## (a) 中核の形 `D_v = (0,0,0)(1,1,1)(2,2,1)...(v,v,1)` で真か  ⟹ ⛔ 偽なら即中止
## (b) `Q` で真なら窓 `V` でも真か（遺伝）
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

C1 = lambda X: all(X[i][1] > 0 for i in range(1, len(X)))
C2 = lambda X: all(trio.is_ancestor(X, 1, 0, i) for i in range(len(X)))
C3 = lambda X: all(X[0][1] < X[i][1] for i in range(1, len(X)))
CS = (('C1 行1=0 の列が無い', C1), ('C2 全列が錐の中', C2), ('C3 ブロッカーが無い', C3))


def Dv(v):
    return [(0, 0, 0)] + [(i, i, 1) for i in range(1, v + 1)]


def part_a():
    print('## (a) 中核の形 D_v で真か')
    for v in range(1, 8):
        D = Dv(v)
        print(f'   D_{v} = {D}')
        print('       ' + '   '.join(f'{nm}: {"★真" if f(D) else "⛔偽"}'
                                     for nm, f in CS))


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
                    hits = [(nm, f(Q)) for nm, f in CS]
                    for n in NS:
                        S0 = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bk = [tuple(x) for x in block(Q, d, e, n)]
                        br = len(S0)
                        for j in range(1, len(Q)):
                            Sj = S0 + Bk[:j + 1]
                            lastx = len(Sj) - 1
                            sr = srow(Sj, lastx)
                            p = trio.parent(Sj, sr, lastx)
                            if p is None or lastx - p < 2: continue
                            V = [tuple(x) for x in Sj[p:lastx]]
                            # ---------- (HZ0) ----------
                            c['(HZ0) 窓'] += 1
                            if V[0][2] != 0:
                                c['⛔ (HZ0) hz0(V) が偽'] += 1
                                pos = ('ブロックの根 (p_rel=0)' if p == br else
                                       ('ブロックの中' if p > br else '塔の中'))
                                c[f'   srow={sr} / 親の位置={pos}'] += 1
                                if sr == 2 or p == br:
                                    c['★ (HZ0) L3 の段の**中**'] += 1
                                else:
                                    c['⛔ (HZ0) L3 の段の**外**'] += 1
                                    if len(ex) < 4:
                                        ex.append((Q, d, e, n, j, sr, p - br, V))
                            # ---------- (b) 遺伝 ----------
                            for (nm, ok), (_, f) in zip(hits, CS):
                                if not ok: continue
                                c[f'(b) {nm}: Q で真'] += 1
                                if f(V): c[f'★ (b) {nm}: V でも真'] += 1
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    hb = c['⛔ (HZ0) hz0(V) が偽']
    print(f'  (HZ0) 窓 {c["(HZ0) 窓"]}  ⛔ hz0(V) が偽 {pc(hb, c["(HZ0) 窓"])}')
    print(f'      ★ **L3 の段の中**（srow=2 または p_rel=0） {pc(c["★ (HZ0) L3 の段の**中**"], hb)}'
          f'   ⛔ **段の外** {pc(c["⛔ (HZ0) L3 の段の**外**"], hb)}')
    for k in sorted(c):
        if k.startswith('   srow='): print(f'      {k}: {c[k]}')
    for nm, _ in CS:
        dq = c[f'(b) {nm}: Q で真']
        print(f'  (b) **{nm}**: Q で真 {dq}  ★ **V でも真** {pc(c[f"★ (b) {nm}: V でも真"], dq)}')
    for x in ex:
        print(f'      ⛔ (HZ0) 段の外の例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} '
              f'srow={x[5]} p_rel={x[6]} V={x[7]}')
    print()


if __name__ == '__main__':
    part_a()
    print()
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2), '|R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2), '★ |R|=4 行1<3')
    run(4, 4, (0,1,2,3), (0,1), (0,1,2), (1,2), '★★ |R|=4 行1<4')
