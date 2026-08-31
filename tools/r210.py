# -*- coding: utf-8 -*-
"""**課題 (w1)(w2)(w3) —— `Q` だけの条件 4 本が窓 `V` で成り立つか。**

## 的（team-lead が L3 から渡した 4 本）

    (g1) `hlp`  … `le1 M 0 |Q|`（`M = Q ++ [c]`。§R190 で主語確認ずみ）
    (g2) `hz0`  … `entry Q 2 0 = 0`
        **`hz0'`** … `∀ l < |Q|, entry Q 2 0 <= entry Q 2 l`（行 2 版の `hr0`、**弱めた版**）
    (g3) `h2`   … `∀ j >= 1, 0 < entry Q 2 j → hasParent (Q.take (j+1)) 2 j`
    (g4) `h1`   … `∀ j, 0 < entry Q 1 j → entry Q 1 0 < entry Q 1 j`（ブロッカーでない）

⚠ **`j >= 1`** は `block_blockParent_all'`（`L105Cap:11366`）の `hj1 : 0 < j` から。

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ `hlp(V)` … 100%（§R187 で既測、`0 < d` の下で）**
> **⚠ `hz0(V)` … 98.7〜100%（§R187 で既測）**
> **⚠ `hz0'(V)` … **`hz0 ⟹ hz0'`** なので必ず `hz0` 以上。見積もり 99.5〜100%。**
> **⚠ (g4) `h1(V)` … ブロッカーは §R133 でよく見た形。見積もり **40〜80%**。**
> **⚠ (g3) `h2(V)` … §R193 で一様な箱では 37〜41% 破れた。消費側では低いはず。見積もり 70〜95%。**
> **⚠ 反例の形: (g4) なら「行 1 が正なのに根の行 1 以下」の列。そのまま貼る。**
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
from r207 import hlp_ok


def hz0(V):   return V[0][2] == 0
def hz0p(V):  return all(V[0][2] <= V[l][2] for l in range(len(V)))
def h2_bad(V):
    return [j for j in range(1, len(V))
            if V[j][2] > 0 and trio.parent(V[:j + 1], 2, j) is None]
def h1_bad(V):
    return [j for j in range(1, len(V)) if V[j][1] > 0 and not (V[0][1] < V[j][1])]
def outside(V, j):
    return not trio.is_ancestor(V, 1, 0, j)


def run(L, R1, VS, ZS, TS, NS, depth, beam, seed):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex1 = []; ex2 = []; t0 = time.time()
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
                    front = [(tuple(Q), dOf(M), eOf(M))]
                    for dep in range(1, depth + 1):
                        nxt = set()
                        for (X, dd, ee) in front:
                            for n in NS:
                                for j in range(len(X)):
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    V, d0 = [tuple(y) for y in r[0]], r[1]
                                    nxt.add((tuple(V), d0, r[2]))
                                    c['窓 V'] += 1
                                    # (w1)
                                    if d0 > 0:
                                        c['(w1) 分母: 0<d0'] += 1
                                        if hlp_ok(V, d0): c['★ (w1) hlp(V)'] += 1
                                    # (w2)
                                    if hz0(V):  c['★ (w2) hz0(V)'] += 1
                                    if hz0p(V): c['★ (w2) hz0\'(V)（弱めた版）'] += 1
                                    # (w3) 全体
                                    b2, b1 = h2_bad(V), h1_bad(V)
                                    if not b2: c['★ (w3) h2(V)'] += 1
                                    if not b1: c['★ (w3) h1(V)'] += 1
                                    else:
                                        if len(ex1) < 3: ex1.append((V, b1))
                                    if b2 and len(ex2) < 3: ex2.append((V, b2))
                                    # (w3) 分母を「j>=1 かつ錐の外の列」に絞る
                                    out = [j2 for j2 in range(1, len(V)) if outside(V, j2)]
                                    if out:
                                        c['(w3) 分母: 錐の外の列がある V'] += 1
                                        if not [j2 for j2 in out if V[j2][2] > 0
                                                and trio.parent(V[:j2+1], 2, j2) is None]:
                                            c['★ (w3) h2（錐の外の列だけ）'] += 1
                                        if not [j2 for j2 in out if V[j2][1] > 0
                                                and not (V[0][1] < V[j2][1])]:
                                            c['★ (w3) h1（錐の外の列だけ）'] += 1
                        if not nxt: break
                        front = list(nxt)
                        if len(front) > beam:
                            rnd.shuffle(front); front = front[:beam]
    t = c['窓 V']
    print(f'### 消費側 |R|={L} 行1<{R1} 深さ<={depth}   窓 `V` {t}  [{time.time()-t0:.1f}s]')
    dn = c['(w1) 分母: 0<d0']
    print(f'    ★ (w1) hlp(V)         {c["★ (w1) hlp(V)"]:9d} / {dn} ({100*c["★ (w1) hlp(V)"]/max(dn,1):8.4f}%)  [分母 = 0<d0]')
    for k in ['★ (w2) hz0(V)', "★ (w2) hz0'(V)（弱めた版）", '★ (w3) h2(V)', '★ (w3) h1(V)']:
        print(f'    {k:28s} {c[k]:9d} / {t} ({100*c[k]/max(t,1):8.4f}%)')
    do = c['(w3) 分母: 錐の外の列がある V']
    print(f'    （分母を「錐の外の列がある `V`」に絞ると … {do}）')
    for k in ['★ (w3) h2（錐の外の列だけ）', '★ (w3) h1（錐の外の列だけ）']:
        print(f'    {k:28s} {c[k]:9d} / {do} ({100*c[k]/max(do,1):8.4f}%)')
    for V, b in ex1: print(f'      ⚠ (g4) h1 の反例 V={V} 破れる列={b}（根の行1={V[0][1]}）')
    for V, b in ex2: print(f'      ⚠ (g3) h2 の反例 V={V} 破れる列={b}')
    print()


if __name__ == '__main__':
    run(2, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 2, 150, 421)
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 2, 100, 423)
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), 1, 60, 425)
