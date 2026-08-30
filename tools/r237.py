# -*- coding: utf-8 -*-
"""**(DEPTH-b) 鎖ごとの「どちらが先か」 ＋ (HNBQ)。**

## (DEPTH-b) 鎖ごとに、先に起きるのはどれか

    (1) ⛔ 差 <= 0（`h1out` が破れる）
    (2) ★ `|V| = 1`（錐の外の列が無い ⟹ 空虚に真）
    (3) ★ 錐の外で「行 2 = 0 ∧ 行 1 > 0」の列が無くなる（**前件が空虚**）
    (4) 段が尽きる（親なし）

## (HNBQ)（H12 の検算）

    `hnbQ(X)` ＝ `∀ l, 0 < l < |X| → entry X 1 0 < entry X 1 l`
      （`mTowerClosed_of_snocStepSameBlock` の `hnb` の逐語形）
    (あ) `hnbQ(Q)` のとき `hnbQ(V)` も成り立つか
    (う) `hnbQ` の成立率（H12 の 54.4% 前後と合うか）
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r169 import domT
from r171 import step_det
from r201 import dOf, eOf
from r206 import hr0
from r234 import h1out_bad


def hnbQ(X):
    return all(X[0][1] < X[l][1] for l in range(1, len(X)))


def outside_targets(V):
    """`h1out` の前件を満たす列（錐の外・行2=0・行1>0）。"""
    return [j for j in range(1, len(V))
            if not trio.is_ancestor(V, 1, 0, j) and V[j][2] == 0 and V[j][1] > 0]


def run(L, R1, VS, ZS, TS, NS, cap, seed, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
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
                    # ---------- (HNBQ-う) 成立率 ----------
                    c['(HNBQ) Q の分母'] += 1
                    if hnbQ(Q): c['★ (HNBQ-う) hnbQ(Q) 成立'] += 1
                    # ---------- 鎖を 1 本（貪欲・ランダム）----------
                    X, dd, ee = list(Q), d, e
                    if h1out_bad(X): continue
                    c['★ 鎖の本数'] += 1
                    for s in range(cap):
                        cand = []
                        for n in NS:
                            for j in range(len(X)):
                                r = step_det(X, dd, ee, n, j)
                                if r and len(r[0]) >= 1: cand.append(r)
                        if not cand:
                            c[('(DEPTH-b) 先に起きた', '(4) 段が尽きる')] += 1
                            c[('  そのときの段数', min(s, 6))] += 1
                            break
                        r = rnd.choice(cand)
                        V, dd, ee = [tuple(y) for y in r[0]], r[1], r[2]
                        # ---------- (HNBQ-あ) ----------
                        if hnbQ(X):
                            c['(HNBQ-あ) 分母: hnbQ(Q) 成立の段'] += 1
                            if hnbQ(V): c['★ (HNBQ-あ) hnbQ(V) も成立'] += 1
                            else:
                                c['⛔ (HNBQ-あ) hnbQ(V) が破れる'] += 1
                                bad = [l for l in range(1, len(V)) if not (V[0][1] < V[l][1])]
                                anc = [l for l in bad if trio.is_ancestor(V, 0, 0, l)]
                                c[('(HNBQ-い) 破る列', 'le0 祖先' if anc else '非 le0 祖先')] += 1
                        X = V
                        outs = outside_targets(X)
                        if len(X) == 1:
                            c[('(DEPTH-b) 先に起きた', '★ (2) |V| = 1')] += 1
                            c[('  そのときの段数', min(s + 1, 6))] += 1
                            break
                        if not outs:
                            c[('(DEPTH-b) 先に起きた', '★ (3) 前件が空虚')] += 1
                            c[('  そのときの段数', min(s + 1, 6))] += 1
                            break
                        if h1out_bad(X):
                            c[('(DEPTH-b) 先に起きた', '⛔ (1) 差 <= 0（h1out 破れ）')] += 1
                            c[('  そのときの段数', min(s + 1, 6))] += 1
                            c[('  ⛔ (DEPTH-c) そのときの |V|', min(len(X), 5))] += 1
                            if len(ex) < 4: ex.append((Q, d, e, s + 1, X, len(X)))
                            break
                    else:
                        c[('(DEPTH-b) 先に起きた', 'cap まで何も起きず')] += 1
    print(f'### {tag}  cap={cap}  [{time.time()-t0:.1f}s]')
    qd = c['(HNBQ) Q の分母']
    print(f'  (HNBQ-う) `hnbQ(Q)` 成立 … {c["★ (HNBQ-う) hnbQ(Q) 成立"]} / {qd} '
          f'({100*c["★ (HNBQ-う) hnbQ(Q) 成立"]/max(qd,1):8.4f}%)')
    ad = c['(HNBQ-あ) 分母: hnbQ(Q) 成立の段']
    print(f'  (HNBQ-あ) 分母 {ad}   ★ `hnbQ(V)` も成立 {c["★ (HNBQ-あ) hnbQ(V) も成立"]} '
          f'({100*c["★ (HNBQ-あ) hnbQ(V) も成立"]/max(ad,1):8.4f}%)   '
          f'⛔ 破れ {c["⛔ (HNBQ-あ) hnbQ(V) が破れる"]}')
    print('  (HNBQ-い) 破る列: ', dict((k[1], c[k]) for k in c
                                  if isinstance(k, tuple) and k[0] == '(HNBQ-い) 破る列'))
    n = c['★ 鎖の本数']
    print(f'  ★ 鎖の本数 {n}')
    print('  (DEPTH-b) 先に起きたこと: ',
          dict(sorted((k[1], c[k]) for k in c
                      if isinstance(k, tuple) and k[0] == '(DEPTH-b) 先に起きた')))
    print('     そのときの段数: ', dict(sorted((k[1], c[k]) for k in c
                      if isinstance(k, tuple) and k[0] == '  そのときの段数')))
    print('     ⛔ (DEPTH-c) `h1out` が破れたときの `|V|`: ',
          dict(sorted((k[1], c[k]) for k in c
                      if isinstance(k, tuple) and k[0] == '  ⛔ (DEPTH-c) そのときの |V|')))
    for x in ex: print(f'      ⛔ (1) の例 Q={x[0]} d={x[1]} e={x[2]} 段={x[3]} V={x[4]} |V|={x[5]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 12, 971, '消費側 |R|=3 行1<3')
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), 12, 973, '★ 消費側 |R|=3 行1<5')
