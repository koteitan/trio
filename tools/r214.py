# -*- coding: utf-8 -*-
"""**(p3) —— `e = 0` のとき、ブロック根の親は本当に前ブロックを飛び越えるか。**

## ⚠ 矛盾の確認

L3／team-lead:「`e = 0` ⟹ ブロック根の行 1 が全部等しい ⟹ `nextrel1` の最小性を遠い根でも
満たせる ⟹ **親が前ブロックを飛び越えて後ろへ跳ぶ** ⟹ 窓が `|Q|` を超えうる」

⚠ **私の §R173/§R191: `|V| > |Q|` は 0.0000%（全箱、分母 43,612 ＋ 300,960）。**
⟹ **どちらかが誤り。直接測る。**

## 測る量

塔 `mTower V d0 0 m`（`e = 0`）のブロック根 `k*|V|`（`k >= 1`）について、
その `srow` の行での**親の位置**が

    **(A) 前のブロックの中**（`(k-1)*|V| <= par < k*|V|`）… 飛び越えない
    **(B) それより前**（`par < (k-1)*|V|`）… **飛び越える**
    **(C) 親なし**

**分母**: `TowerP''(Q)` を満たす `Q` から出た窓 `V` で **`d1 = 0` ∧ `d0 > 0` ∧ `entry V 1 0 > 0`**
（＝ §R195 の「最後の核」の形）。件数も出す。

## ★ 予想（教訓 45）
> **⚠ 私の `|V| > |Q| = 0.0000%` から、**(B) は 0%** と予想。**
> **⚠ 出れば私の過去の測定が誤り。出なければ L3 の懸念が机上のもの。**
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r169 import domT
from r171 import step_det
from r201 import dOf, eOf
from r212 import conds, K8, K7


def probe_blockroots(V, d0, MS, c, tag):
    """`mTower V d0 0 m` のブロック根 `k*|V|`（1<=k<m）の親の位置を分類。"""
    L = len(V)
    for m in MS:
        T = [tuple(x) for x in mTower(list(V), d0, 0, m)]
        for k in range(1, m):
            idx = k * L
            i1 = srow(T, idx)
            par = trio.parent(T, i1, idx)
            c[(tag, 'ブロック根')] += 1
            c[(tag, 'srow', i1)] += 1
            if par is None:
                c[(tag, '(C) 親なし')] += 1
            elif par >= (k - 1) * L:
                c[(tag, '(A) 前のブロックの中')] += 1
                c[(tag, '  相対位置', par - (k - 1) * L)] += 1
            else:
                c[(tag, '(B) ⚠⚠ 飛び越える')] += 1
                if c[(tag, '(B) ⚠⚠ 飛び越える')] <= 3:
                    print(f'      ⚠⚠ (B) の例 V={V} d0={d0} m={m} k={k} 親={par} '
                          f'(ブロック {par // L}) srow={i1}')


def run(L, R1, VS, ZS, TS, NS, MS, depth, beam, seed):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    rnd = random.Random(seed); c = Counter(); t0 = time.time()
    tag = f'|R|={L} 行1<{R1}'
    seenV = set()
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
                    if not all(conds(Q, d, e)[k] for k in K8): continue
                    front = [(tuple(Q), d, e)]
                    for dep in range(1, depth + 1):
                        nxt = set()
                        for (X, dd, ee) in front:
                            for n in NS:
                                for j in range(len(X)):
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    V2, d0, d1 = [tuple(y) for y in r[0]], r[1], r[2]
                                    if all(conds(V2, d0, d1)[k] for k in K7):
                                        nxt.add((tuple(V2), d0, d1))
                                    # ★ 核の形だけを見る
                                    if d1 == 0 and d0 > 0 and V2[0][1] > 0:
                                        key = (tuple(V2), d0)
                                        if key in seenV: continue
                                        seenV.add(key)
                                        c[(tag, '★ 分母: 核の窓 (d1=0,d0>0,行1の根>0)')] += 1
                                        probe_blockroots(V2, d0, MS, c, tag)
                        if not nxt: break
                        front = list(nxt)
                        if len(front) > beam:
                            rnd.shuffle(front); front = front[:beam]
    den = c[(tag, '★ 分母: 核の窓 (d1=0,d0>0,行1の根>0)')]
    br = c[(tag, 'ブロック根')]
    print(f'### {tag}   ★ 核の窓（重複除去） {den}   ブロック根の総数 {br}  [{time.time()-t0:.1f}s]')
    for k in ['(A) 前のブロックの中', '(B) ⚠⚠ 飛び越える', '(C) 親なし']:
        print(f'    {k:24s} {c[(tag,k)]:9d} ({100*c[(tag,k)]/max(br,1):8.4f}%)')
    print('    ブロック根の srow: ',
          {x[2]: c[x] for x in sorted(y for y in c if len(y) == 3 and y[1] == 'srow')})
    print('    (A) の相対位置（前ブロック内）: ',
          dict(sorted((x[2], c[x]) for x in c if len(x) == 3 and x[1] == '  相対位置')))
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), (2,3,4,5), 2, 100, 461)
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), (2,3,4,5), 2, 60, 463)
