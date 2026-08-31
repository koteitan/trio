# -*- coding: utf-8 -*-
"""**R127 (a1)(a2)(a3) を「場面の母集団」（`le1_mTower_block` の全前提）で測る。**
結果は `r127c.log`。形の確定と陰性対照は `r127d.log`（下の `--shape` / `--ctrl`）。

母集団: `|M| = L+1`、`hr0`（根が狭義最浅）、`d = entry M 0 Lb - entry M 0 0`、
`hlp : le1 M 0 Lb`、`e >= 1`。単位 = 位置 `q`（`1 <= q < Lb`）。**`W` 所属は判定しない。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r126 import le1_root
from r113 import mTower


def scene(cm, L):
    """場面の `M` を生成（全前提つき）。"""
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    for root in COL:
        for t in itertools.product(COL, repeat=L):
            M = [root] + list(t)
            if not all(M[0][0] < M[l][0] for l in range(1, L + 1)):
                continue                                   # hr0（= hup）
            d = M[L][0] - M[0][0]
            if d <= 0:
                continue                                   # hd0pos（hr0 から自動）
            if not le1_root(M, L):
                continue                                   # hlp
            yield M, d


def a12(cm, L):
    c = Counter(); ex = {}; t0 = time.time()
    for M, d in scene(cm, L):
        Q = M[:-1]; c['M の本数'] += 1
        for q in range(1, L):
            c['位置の分母'] += 1
            if le1_root(Q, q):
                continue
            c['錐の外'] += 1
            if Q[q][1] <= Q[0][1]:
                c['G1 行1が根以下'] += 1; ex.setdefault('G1', (M, q))
            else:
                c['★ G2 ブロッカーの向こう'] += 1; ex.setdefault('G2', (M, q))
    tot = c['位置の分母']; out = c['錐の外']
    print(f'  行2<={cm} |M|={L+1}: M {c["M の本数"]:8d} 本  位置の分母 {tot:9d}  '
          f'**錐の外 {out:8d} ({100*out/max(tot,1):6.2f}%)**  [{time.time()-t0:.1f}s]')
    if out:
        print(f'      G1 行1が根以下          {c["G1 行1が根以下"]:8d} ({100*c["G1 行1が根以下"]/out:6.2f}%)')
        print(f'      **★ G2 ブロッカーの向こう {c["★ G2 ブロッカーの向こう"]:8d} '
              f'({100*c["★ G2 ブロッカーの向こう"]/out:6.2f}%)**')
    for k in sorted(ex):
        print(f'      最小例 {k}: M={ex[k][0]} q={ex[k][1]}')


def a3(cm, L):
    c = Counter()
    for M, d in scene(cm, L):
        Q = M[:-1]
        for e in (1, 2, 3):
            for n in (2, 3, 4):
                T = [tuple(x) for x in mTower(Q, d, e, n)]
                for k in range(n):
                    for q in range(1, L):
                        c[(k, '外' if not le1_root(T, k * L + q) else '中')] += 1
    for k in range(4):
        i = c[(k, '中')]; o = c[(k, '外')]
        if i + o:
            print(f'  k={k}: 分母 {i+o:9d}  **錐の外 {o:9d} ({100*o/(i+o):6.2f}%)**')


def shape(cm, L, shallow=True):
    """**錐の外 ⟺ 行 1 の親鎖上に「行 1 が根以下」の列がある** の検算。"""
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = None
    if shallow:
        gen = ([root] + list(t) for root in COL
               for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1))
    else:
        gen = (list(t) for t in itertools.product(COL, repeat=L))
    for Q in gen:
        for q in range(1, L):
            if le1_root(Q, q):
                continue
            chain = []; p = q
            while p is not None:
                chain.append(p); p = trio.parent(Q, 1, p)
            c['錐の外'] += 1
            if Q[chain[-1]][1] <= Q[0][1]:
                c['成立'] += 1
            else:
                c['**破れ**'] += 1
                if ex is None:
                    ex = (Q, q, chain)
            c[('止まり', '=q' if chain[-1] == q else '>q（G2）')] += 1
    o = c['錐の外']
    print(f'  行2<={cm} |Q|={L} 最浅={shallow}: 錐の外 {o:9d}  成立 {100*c["成立"]/max(o,1):6.2f}%  '
          f'**破れ {c["**破れ**"]:8d}**  （止まりが q 自身 {c[("止まり","=q")]} / q より上 {c[("止まり",">q（G2）")]}）'
          + (f'   例 Q={ex[0]} q={ex[1]} 鎖={ex[2]}' if ex else ''))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--mode', default='all')
    a = ap.parse_args()
    if a.mode in ('all', 'a12'):
        print('### R127 場面の母集団（M ベース・全前提）で (a1)(a2)')
        for cm in (1, 2, 3):
            for L in (2, 3, 4):
                if cm == 3 and L == 4:
                    continue
                a12(cm, L)
    if a.mode in ('all', 'a3'):
        print('\n### (a3) `k` 別の「錐の外」割合（全前提つき）')
        a3(1, 3)
    if a.mode in ('all', 'shape'):
        print('\n### (a2) 形の確定 ＋ 陰性対照')
        for cm in (1, 2):
            for L in (3, 4, 5):
                shape(cm, L, True)
        for cm in (1, 2):
            for L in (3, 4):
                shape(cm, L, False)
