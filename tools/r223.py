# -*- coding: utf-8 -*-
"""**課題 (z3) —— `HeredZ2` の破れから長さ 1・2 を除いた真の残差。**

## ⚠ 規模（先に数えた）

`|R|=5` の全数は `18^5 × (v,z,t) ≈ 3,400 万` ⟹ 無理。
⟹ **`|R| >= 5` は `R` を無作為抽出**（母集団が「全数」から「標本」に変わる。明記する）。
`|R| = 3, 4` は全数（§R203 と同じ）。

## 測るもの

    (z3a) `HeredZ2` の破れから**長さ 1** を除いた残差（分母 = 組の総数）
    (z3b) さらに**長さ 2** も除いた残差
    (z3c) ★ **長さの分布が `|Q|` とともにどう動くか**（team-lead が先に見たいもの）

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ 長さ 1 の割合は `|Q|=3` で 100%、`|Q|=4` で 82.4/81.3% ⟹ **下がり続ける**と予想。
>   見積もり `|Q|=5` で **65〜78%**、`|Q|=6` で **55〜72%**。**
> **⟹ ⚠ そうなら `MTowerSingle` だけでは足りない。**
> **⚠ (z3b) 長さ 1+2 を除いた残差は **0 にならない**と予想。**
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r169 import domT
from r201 import dOf, eOf
from r206 import hr0


def gen(L, R1, exhaustive, nsamp, seed):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    if exhaustive:
        for Rt in itertools.product(COL, repeat=L):
            yield list(Rt)
    else:
        rnd = random.Random(seed)
        for _ in range(nsamp):
            yield [rnd.choice(COL) for _ in range(L)]


def run(L, R1, VS, ZS, TS, NS, exhaustive, nsamp, seed, tag):
    c = Counter(); ex = []; t0 = time.time()
    for R in gen(L, R1, exhaustive, nsamp, seed):
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
                    if not (len(Q) >= 1 and d > 0 and e > 0 and hr0(Q) and Q[0][2] == 0):
                        continue
                    LQ = len(Q)
                    for n in NS:
                        P = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(1, LQ):
                            S = P + B[:j + 1]
                            last = len(S) - 1
                            i1 = srow(S, last)
                            par = trio.parent(S, i1, last)
                            if par is None or par < len(P): continue
                            p = par - len(P)
                            if p >= j: continue
                            c['★ 分母: HeredZ2 の組'] += 1
                            if B[p][2] == 0: continue
                            c['⛔ 破れ'] += 1
                            wl = last - par            # 窓の長さ
                            c[('破れの窓の長さ', min(wl, 6))] += 1
                            if wl >= 2: c['(z3a) 長さ 1 を除いた残差'] += 1
                            if wl >= 3:
                                c['(z3b) 長さ 1,2 を除いた残差'] += 1
                                if len(ex) < 4:
                                    ex.append((Q, d, e, n, j, p, i1, wl, S[par:last]))
    D = c['★ 分母: HeredZ2 の組']; Bk = c['⛔ 破れ']
    mode = '全数' if exhaustive else f'無作為抽出 {nsamp} 本'
    print(f'### {tag}（{mode}）  分母 {D}   ⛔ 破れ {Bk} ({100*Bk/max(D,1):7.4f}%)  '
          f'[{time.time()-t0:.1f}s]')
    rows = [(k[1], c[k]) for k in c if isinstance(k, tuple)]
    tot = sum(v for _, v in rows)
    print('    (z3c) 破れの窓の長さ（6 は 6 以上）: ',
          {k: f'{v} ({100*v/max(tot,1):.2f}%)' for k, v in sorted(rows)})
    print(f'    (z3a) 長さ 1 を除いた残差   {c["(z3a) 長さ 1 を除いた残差"]:8d} / {D} '
          f'({100*c["(z3a) 長さ 1 を除いた残差"]/max(D,1):8.4f}%)   '
          f'（破れの {100*c["(z3a) 長さ 1 を除いた残差"]/max(Bk,1):6.2f}%）')
    print(f'    (z3b) 長さ 1,2 を除いた残差 {c["(z3b) 長さ 1,2 を除いた残差"]:8d} / {D} '
          f'({100*c["(z3b) 長さ 1,2 を除いた残差"]/max(D,1):8.4f}%)   '
          f'（破れの {100*c["(z3b) 長さ 1,2 を除いた残差"]/max(Bk,1):6.2f}%）')
    for x in ex:
        print(f'      ⛔ 長さ 3 以上の破れ Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} p={x[5]} '
              f'srow={x[6]} 窓の長さ={x[7]}')
        print(f'            窓={x[8]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), True,  0,     0,   '|Q|=3（|R|=3 行1<3）')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), True,  0,     0,   '|Q|=4（|R|=4 行1<3）')
    run(5, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), False, 40000, 601, '★ |Q|=5（|R|=5 行1<3）')
    run(6, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), False, 40000, 603, '★ |Q|=6（|R|=6 行1<3）')
