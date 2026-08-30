# -*- coding: utf-8 -*-
"""**課題 (TYPEB) ＋ (検2) の深さ追跡（`(d,e)` の引き継ぎを保つ）。**

## 母集団（1 行で再掲）

消費側の `Q`（`TowerP''` ＋ `d>0` ＋ `h1out(Q)` 成立）から、**`(d,e)` を `oper` で正しく引き継いで**
`h1out` を保つ窓だけ降りた段。ビーム幅つき。

## 測るもの

    (検2) 各段で `|V|`・`k`（窓の根のブロック番号）・`e`・**予算 `e*k`**・**距離** を同時に記録
    (TYPEB-a) 型 B（`|V|=3` ∧ 破れる列 `j=2` ∧ 親あり）の `(d0, e0)`
    (TYPEB-b) 型 B からさらに 1 段降りて、**型 B が型 B を生むか**
    (TYPEB-c) `|R|=4` でも同じ形か

## ★ 予想（教訓 45）

> **⚠ (TYPEB-a) 型 B は行 2 が全部 0 ⟹ `srow <= 1` ⟹ **`e0 = 0`** と予想（100%）。**
> **⚠ (TYPEB-b) 予算 0 ⟹ 新しく破れない ⟹ **型 B は自己再生しない**と予想。**
> **⚠ (検2) 深さとともに `e*k` の平均は上がるが、`|V|` が縮んで釣り合うと予想。**
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
from r234 import h1out_bad


def stepinfo(X, dd, ee, n, j):
    """1 段。`(V, d0, e0, k, p, par)` を返す。"""
    LX = len(X)
    T = [tuple(y) for y in mTower(X, dd, ee, n)]
    S = T + block(X, dd, ee, n)[:j + 1]
    lastx = len(S) - 1
    i1 = srow(S, lastx)
    par = trio.parent(S, i1, lastx)
    if par is None: return None
    d0 = (S[lastx][0] - S[par][0]) if i1 > 0 else 0
    e0 = (S[lastx][1] - S[par][1]) if i1 > 1 else 0
    return [tuple(y) for y in S[par:lastx]], d0, e0, par // LX, par % LX, par


def typeB(V, bad):
    return len(V) == 3 and bad == [2] and \
        trio.parent(V[:3], srow(V, 2), 2) is not None


def run(L, R1, VS, ZS, TS, NS, depth, beam, seed, tag):
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
                    Q0 = M[:-1]
                    if len(Q0) < 2: continue
                    d, e = dOf(M), eOf(M)
                    if not (d > 0 and hr0(Q0) and Q0[0][2] == 0): continue
                    if h1out_bad(Q0): continue
                    front = [(tuple(Q0), d, e)]
                    for dep in range(1, depth + 1):
                        nxt = []
                        for (Xt, dd, ee) in front:
                            X = list(Xt); LX = len(X)
                            for n in NS:
                                for j in range(LX):
                                    r = stepinfo(X, dd, ee, n, j)
                                    if r is None: continue
                                    V, d0, e0, k, p, par = r
                                    if len(V) < 2: continue
                                    bad = h1out_bad(V)
                                    c[(dep, '★ 分母: 段')] += 1
                                    c[(dep, '  |V| 合計')] += len(V)
                                    c[(dep, '  予算 e*k 合計')] += ee * k
                                    c[(dep, '  k 合計')] += k
                                    if bad:
                                        c[(dep, '⛔ 破れ')] += 1
                                        if typeB(V, bad):
                                            c[(dep, '★ 型 B')] += 1
                                            c[('TYPEB (d0,e0)', (min(d0, 3), min(e0, 3)))] += 1
                                            if e0 == 0: c['★ (TYPEB-a) e0 = 0'] += 1
                                            else: c['⛔ (TYPEB-a) e0 > 0'] += 1
                                            # (TYPEB-b) 型 B からさらに 1 段
                                            for n2 in NS:
                                                for j2 in range(len(V)):
                                                    r2 = stepinfo(V, d0, e0, n2, j2)
                                                    if r2 is None: continue
                                                    V2, dd2, ee2 = r2[0], r2[1], r2[2]
                                                    if len(V2) < 2: continue
                                                    b2 = h1out_bad(V2)
                                                    c['(TYPEB-b) 分母'] += 1
                                                    if typeB(V2, b2):
                                                        c['⛔ (TYPEB-b) 型 B が型 B を生む'] += 1
                                                    elif b2:
                                                        c['(TYPEB-b) 破れるが型 B でない'] += 1
                                                    else:
                                                        c['★ (TYPEB-b) 破れない'] += 1
                                            if len(ex) < 6:
                                                ex.append((dep, X, dd, ee, n, j, V, d0, e0))
                                        else:
                                            c[(dep, '型 A ほか')] += 1
                                    else:
                                        nxt.append((tuple(V), d0, e0))
                        if not nxt: break
                        rnd.shuffle(nxt); front = nxt[:beam]
    print(f'### {tag} 深さ<={depth} ビーム{beam}  [{time.time()-t0:.1f}s]')
    print(f'    {"深さ":>4s} {"★ 分母":>10s} {"⛔ 破れ":>10s} {"★ 型 B":>8s} '
          f'{"平均 |V|":>9s} {"平均 k":>8s} {"平均 予算 e*k":>13s}')
    for dep in range(1, depth + 1):
        D = c[(dep, '★ 分母: 段')]
        if not D: continue
        print(f'    {dep:4d} {D:10d} {c[(dep,"⛔ 破れ")]:10d} {c[(dep,"★ 型 B")]:8d} '
              f'{c[(dep,"  |V| 合計")]/D:9.3f} {c[(dep,"  k 合計")]/D:8.3f} '
              f'{c[(dep,"  予算 e*k 合計")]/D:13.3f}')
    print(f'  (TYPEB-a) ★ `e0 = 0` {c["★ (TYPEB-a) e0 = 0"]}   ⛔ `e0 > 0` {c["⛔ (TYPEB-a) e0 > 0"]}')
    print('  (TYPEB) `(d0,e0)` の分布（3 は 3 以上）: ',
          dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple) and k[0] == 'TYPEB (d0,e0)')))
    b = c['(TYPEB-b) 分母']
    print(f'  (TYPEB-b) 分母 {b}   ⛔ 型 B が型 B を生む {c["⛔ (TYPEB-b) 型 B が型 B を生む"]} '
          f'({100*c["⛔ (TYPEB-b) 型 B が型 B を生む"]/max(b,1):7.4f}%)   '
          f'破れるが型 B でない {c["(TYPEB-b) 破れるが型 B でない"]}   '
          f'★ 破れない {c["★ (TYPEB-b) 破れない"]}')
    for x in ex: print(f'      型 B の例 深さ{x[0]} X={x[1]} (d,e)=({x[2]},{x[3]}) n={x[4]} j={x[5]} '
                       f'⟹ V={x[6]} (d0,e0)=({x[7]},{x[8]})')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 5, 200, 1001, '消費側 |R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 4, 60, 1003, '★ 消費側 |R|=4 行1<3')
