# -*- coding: utf-8 -*-
"""**課題 (w3') —— `h1out` の前件に `entry V 2 j' = 0` を足して測り直す。**
＋ **(h1) を訂正後の `h1out` でやり直す。**

## 訂正（team-lead、`L106:1689` `block_blockParent_all_outcone` の枝から）

    訂正前: `0 < entry V 1 j'` → `entry V 1 0 < entry V 1 j'`
    **訂正後: `entry V 2 j' = 0` → `0 < entry V 1 j'` → `entry V 1 0 < entry V 1 j'`**

⚠ 分母は**列単位**（錐の外・`j >= 1`・前件を満たす列の数）と、**窓単位**の両方を出す。

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ H12 の分布表から分母は **26%** に落ちるはず（`srow = 2` の 12,532 が空虚になる）。**
> **⚠ 成立率は上がる。見積もり **90〜100%**。**
> **⚠ (h1c) は `0 < e` が主犯なので **22〜30% のまま**と予想。7 本版は 87〜96% に微増。**
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


def outside(X, j): return not trio.is_ancestor(X, 1, 0, j)
def hr0(X):  return all(X[0][0] < X[l][0] for l in range(1, len(X)))
def h2out_bad(X):
    return [j for j in range(1, len(X)) if outside(X, j) and X[j][2] > 0
            and trio.parent(X[:j + 1], 2, j) is None]
def h1out_bad_old(X):
    return [j for j in range(1, len(X)) if outside(X, j) and X[j][1] > 0
            and not (X[0][1] < X[j][1])]
def h1out_bad_new(X):
    return [j for j in range(1, len(X)) if outside(X, j) and X[j][2] == 0
            and X[j][1] > 0 and not (X[0][1] < X[j][1])]


def conds(X, d, e, newform=True):
    hb = h1out_bad_new(X) if newform else h1out_bad_old(X)
    return {'1 hM2': len(X) >= 1, '2 0<e': e > 0, '3 hd0e': d > 0,
            '4 hr0': hr0(X), '5 hlp': (d > 0 and hlp_ok(X, d)),
            '6 hz0': X[0][2] == 0, '7 h2out': not h2out_bad(X), '8 h1out': not hb}


K8 = ['1 hM2', '2 0<e', '3 hd0e', '4 hr0', '5 hlp', '6 hz0', '7 h2out', '8 h1out']
K7 = [k for k in K8 if k != '2 0<e']


def run(L, R1, VS, ZS, TS, NS, depth, beam, seed):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    rnd = random.Random(seed); c = Counter(); t0 = time.time()
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
                    if not all(conds(Q, d, e)[k] for k in K8): continue   # 分母 = TowerP''(Q)
                    c['DEN'] += 1
                    front = [(tuple(Q), d, e)]
                    for dep in range(1, depth + 1):
                        nxt = set()
                        for (X, dd, ee) in front:
                            for n in NS:
                                for j in range(len(X)):
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    V, d0, e0 = [tuple(y) for y in r[0]], r[1], r[2]
                                    c[(dep, '窓 V')] += 1
                                    # (w3') 列単位
                                    for jj in range(1, len(V)):
                                        if not outside(V, jj): continue
                                        c[(dep, '列: 錐の外・j>=1')] += 1
                                        if V[jj][1] > 0:
                                            c[(dep, '列: 前件（訂正前）')] += 1
                                            if V[0][1] < V[jj][1]: c[(dep, '列: 結論 ok（訂正前）')] += 1
                                            if V[jj][2] == 0:
                                                c[(dep, '列: 前件（訂正後）')] += 1
                                                if V[0][1] < V[jj][1]:
                                                    c[(dep, '列: 結論 ok（訂正後）')] += 1
                                    # 窓単位
                                    cv = conds(V, d0, e0)
                                    cvo = conds(V, d0, e0, newform=False)
                                    for k in K8:
                                        if cv[k]: c[(dep, k)] += 1
                                    if not cvo['8 h1out']: c[(dep, '窓: h1out 破れ（訂正前）')] += 1
                                    if not cv['8 h1out']:  c[(dep, '窓: h1out 破れ（訂正後）')] += 1
                                    if all(cv[k] for k in K7):
                                        c[(dep, '★ 7 本')] += 1
                                        nxt.add((tuple(V), d0, e0))
                                    if all(cv[k] for k in K8): c[(dep, '★★ 8 本')] += 1
                        if not nxt: break
                        front = list(nxt)
                        if len(front) > beam:
                            rnd.shuffle(front); front = front[:beam]
    print('### 消費側 |R|=%d 行1<%d  分母 TowerP2(Q) … %d  [%.1fs]'
          % (L, R1, c['DEN'], time.time() - t0))
    for dep in range(1, depth + 1):
        t = c[(dep, '窓 V')]
        if not t: continue
        o, nw = c[(dep, '列: 前件（訂正前）')], c[(dep, '列: 前件（訂正後）')]
        print(f'  深さ {dep}（窓 {t}、錐の外・j>=1 の列 {c[(dep,"列: 錐の外・j>=1")]}）')
        print(f'      (w3\') 列単位  訂正前: 分母 {o:8d}  成立 {c[(dep,"列: 結論 ok（訂正前）")]:8d} '
              f'({100*c[(dep,"列: 結論 ok（訂正前）")]/max(o,1):8.4f}%)')
        print(f'      (w3\') 列単位  ★訂正後: 分母 {nw:8d}  成立 {c[(dep,"列: 結論 ok（訂正後）")]:8d} '
              f'({100*c[(dep,"列: 結論 ok（訂正後）")]/max(nw,1):8.4f}%)   '
              f'[分母は訂正前の {100*nw/max(o,1):.1f}%]')
        print(f'      窓単位 h1out 破れ  訂正前 {c[(dep,"窓: h1out 破れ（訂正前）")]:7d} '
              f'({100*c[(dep,"窓: h1out 破れ（訂正前）")]/t:7.4f}%)   '
              f'★訂正後 {c[(dep,"窓: h1out 破れ（訂正後）")]:7d} '
              f'({100*c[(dep,"窓: h1out 破れ（訂正後）")]/t:7.4f}%)')
        for k in K8 + ['★ 7 本', '★★ 8 本']:
            print(f'      {k:10s} {c[(dep,k)]:9d} ({100*c[(dep,k)]/t:8.4f}%)')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 2, 100, 441)
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), 2, 60, 443)
