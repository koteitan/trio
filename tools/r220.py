# -*- coding: utf-8 -*-
"""**課題 (y3) —— `hz0(V)` が破れる 1〜2% の正体。**

## 分母（`Q` 側に課したものを明記）

**`TowerP''` の 5 本**（`0<|Q|` / `0<d` / `0<e` / `hr0` / `hz0`）を満たす消費側の `Q`
（`Q = Lift1 ((0,v,z) :: R.dropLast) t`、`d = dOf M`、`e = eOf M`）。
そこから `oper` で降りた**窓 `V` 全体**が分母。

## 測るもの

    (y3a) `entry V 2 0 > 0` の `V` を貼る（＋割合）
    (y3b) その窓の根が `Q` のどの列か（ブロック内位置 `p_rel`、`srow`、錐の中/外）
    **(y3c) ★ その `V` からの段が「孤児枝」に落ちるか**
          （i）段のうち親なし（`snoc_orphan_W` が処理）の割合
          （ii）**全段が孤児な `V`** の割合 ⟹ そこは `hz0(V)` が要らない
    (y3d) 陰性対照 ＝ `hz0(V)` が成立する `V` で同じ量（値が違えば計器が生きている）

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ (y3a) 1〜2%（既測 98.4〜99.8% 成立）。**
> **⚠ (y3b) 窓の根は `entry Q 2 p = 1` の列。**錐の外**が多いと予想（§R133 の形）。**
> **⚠ (y3c-ii) **見積もり 30〜80%**。100% とは決めつけない（前回外した方向を根拠にしない）。**
> **⚠ (y3d) 対照は「破れる `V`」と「成立する `V`」で値が**違う**ことを見る。**
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r169 import domT
from r171 import step_det
from r201 import dOf, eOf
from r206 import hr0


def steps_profile(V, d0, e0, NS):
    """`V` からの全段のうち、親なし（孤児枝）の割合。"""
    tot = orph = 0
    for n in NS:
        for j in range(len(V)):
            T = [tuple(x) for x in mTower(V, d0, e0, n)]
            S = T + block(V, d0, e0, n)[:j + 1]
            last = len(S) - 1
            tot += 1
            if trio.parent(S, srow(S, last), last) is None: orph += 1
    return tot, orph


def run(L, R1, VS, ZS, TS, NS, seed):
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
                    if not (len(Q) >= 1 and d > 0 and e > 0 and hr0(Q) and Q[0][2] == 0):
                        continue
                    LQ = len(Q)
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(LQ):
                            S = T + B[:j + 1]
                            last = len(S) - 1
                            par = trio.parent(S, srow(S, last), last)
                            if par is None: continue
                            r = step_det(Q, d, e, n, j)
                            if r is None or len(r[0]) < 2: continue
                            V, d0, e0 = [tuple(y) for y in r[0]], r[1], r[2]
                            c['窓 V（分母）'] += 1
                            bad = V[0][2] > 0
                            key = '⛔ hz0(V) 破れ' if bad else '★ hz0(V) 成立（対照）'
                            c[key] += 1
                            # (y3b) 窓の根の素性
                            p_rel = par % LQ
                            blk = par // LQ
                            inside = trio.is_ancestor(Q, 1, 0, p_rel) if p_rel < LQ else None
                            if bad:
                                c[('(y3b) p_rel', p_rel)] += 1
                                c[('(y3b) 親のブロック（手前へ）', (n - blk))] += 1
                                c[('(y3b) Q[p_rel] の srow', srow(Q, p_rel))] += 1
                                c[('(y3b) 錐', '中' if inside else '外')] += 1
                                if len(ex) < 5:
                                    ex.append((Q, d, e, n, j, par, p_rel, V, d0, e0,
                                               srow(Q, p_rel), '中' if inside else '外'))
                            # (y3c) 段の素性
                            tot, orph = steps_profile(V, d0, e0, NS)
                            c[(key, '段の総数')] += tot
                            c[(key, '孤児の段')] += orph
                            if tot > 0 and orph == tot: c[(key, '★ 全段が孤児')] += 1
    D = c['窓 V（分母）']
    print(f'### 消費側 |R|={L} 行1<{R1}   窓 `V`（分母）{D}  [{time.time()-t0:.1f}s]')
    for key in ('⛔ hz0(V) 破れ', '★ hz0(V) 成立（対照）'):
        k = c[key]
        print(f'  {key} … {k} ({100*k/max(D,1):7.4f}%)')
        tt, oo = c[(key, '段の総数')], c[(key, '孤児の段')]
        print(f'      (y3c-i) 孤児の段 {oo} / {tt} ({100*oo/max(tt,1):8.4f}%)')
        print(f'      (y3c-ii) ★ 全段が孤児な `V` {c[(key,"★ 全段が孤児")]} / {k} '
              f'({100*c[(key,"★ 全段が孤児")]/max(k,1):8.4f}%)')
    print('  (y3b) 破れる `V` の窓の根:')
    for nm in ['(y3b) p_rel', '(y3b) 親のブロック（手前へ）', '(y3b) Q[p_rel] の srow', '(y3b) 錐']:
        rows = [(k[1], c[k]) for k in c if isinstance(k, tuple) and k[0] == nm]
        print('      %s: %s' % (nm, dict(sorted(rows, key=lambda x: str(x[0])))))
    for x in ex:
        print(f'      ⛔ (y3a) 破れ例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} '
              f'親={x[5]}(p_rel={x[6]}) V={x[7]} (d0,e0)=({x[8]},{x[9]}) '
              f'Q[p_rel] の srow={x[10]} 錐の{x[11]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 531)
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), 533)
