# -*- coding: utf-8 -*-
"""**課題 (h1)(h2) —— 前提を課したうえでの遺伝率（条件つき）。**

## 分母の訂正（team-lead の指摘。私の教訓「条件付き確率は向きを書いてから測る」の適用）

§R192 は `P(h1out(V))` を**無条件**で測っていた。要るのは
**`P(… (V) | TowerP''(Q))`** ＝ **前提を満たす `Q` から出た `V` だけ**。

## `TowerP''` の 8 本（`M = Q ++ [c]`、`c.0 = Q[0].0 + d` は `hd0e` で決まる）

    1 `hM2`   `1 <= |Q|`
    2 `0 < e`
    3 `hd0e`  ∃ c, `c.0 = Q[0].0 + d`（`0 < d` と一体）
    4 `hr0`   `∀ 0<l<|Q|, Q[0].0 < Q[l].0`
    5 `hlp`   `le1 (Q ++ [c]) 0 |Q|`
    6 `hz0`   `Q[0].2 = 0`
    7 `h2out` `∀ j>=1 錐の外, 0 < Q[j].2 → hasParent (Q.take (j+1)) 2 j`
    8 `h1out` `∀ j>=1 錐の外, 0 < Q[j].1 → Q[0].1 < Q[j].1`

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ (h1c) は **100% になりえない**。§R186 で `0 < e`（＝ `e' = 0`）が **81.153%** 破れると
>   測っている。`e'` は `oper` が決めるので、`Q` に何を課しても変わらない。**
> **⟹ ★ ですから **`0 < e` を除いた 7 本**の遺伝率を並べる。それが実質的な答え。**
> **⚠ 見積もり: 7 本版で 70〜95%。8 本版で 5〜20%。**
> **⚠ (h2a) 破れる列が孤児か … 見積もり 60〜90%（100% にはならないと予想）。**
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
def hz0(X):  return X[0][2] == 0
def h2out_bad(X):
    return [j for j in range(1, len(X)) if outside(X, j) and X[j][2] > 0
            and trio.parent(X[:j + 1], 2, j) is None]
def h1out_bad(X):
    return [j for j in range(1, len(X)) if outside(X, j) and X[j][1] > 0
            and not (X[0][1] < X[j][1])]


def conds(X, d, e):
    """8 本を dict で返す。"""
    return {
        '1 hM2':   len(X) >= 1,
        '2 0<e':   e > 0,
        '3 hd0e':  d > 0,
        '4 hr0':   hr0(X),
        '5 hlp':   (d > 0 and hlp_ok(X, d)),
        '6 hz0':   hz0(X),
        '7 h2out': not h2out_bad(X),
        '8 h1out': not h1out_bad(X),
    }


K8 = ['1 hM2', '2 0<e', '3 hd0e', '4 hr0', '5 hlp', '6 hz0', '7 h2out', '8 h1out']
K7 = [k for k in K8 if k != '2 0<e']


def run(L, R1, VS, ZS, TS, NS, depth, beam, seed):
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
                    cq = conds(Q, d, e)
                    if not all(cq[k] for k in K8): continue    # ★ 分母 = TowerP''(Q)
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
                                    cv = conds(V, d0, e0)
                                    c[(dep, '窓 V')] += 1
                                    for k in K8:
                                        if cv[k]: c[(dep, k)] += 1
                                    if all(cv[k] for k in K7):
                                        c[(dep, '★ 7 本（0<e 抜き）')] += 1
                                        nxt.add((tuple(V), d0, e0))
                                    if all(cv[k] for k in K8):
                                        c[(dep, '★★ 8 本すべて')] += 1
                                    # (h2a) 破れる列は孤児か
                                    for jj in h1out_bad(V) + h2out_bad(V):
                                        c[(dep, '(h2a) 破れる列')] += 1
                                        if trio.parent(V[:jj + 1], srow(V, jj), jj) is None:
                                            c[(dep, '(h2a) ★ その列は孤児')] += 1
                                        elif len(ex) < 4:
                                            ex.append((V, jj, srow(V, jj),
                                                       trio.parent(V[:jj+1], srow(V, jj), jj)))
                        if not nxt: break
                        front = list(nxt)
                        if len(front) > beam:
                            rnd.shuffle(front); front = front[:beam]
    print('### 消費側 |R|=%d 行1<%d  ★ 分母（TowerP2(Q) を満たす Q） … %d  [%.1fs]'
          % (L, R1, c['DEN'], time.time() - t0))
    for dep in range(1, depth + 1):
        t = c[(dep, '窓 V')]
        if not t: continue
        print(f'  深さ {dep}（窓 {t}）')
        for k in K8:
            print(f'      {k:10s} {c[(dep,k)]:9d} ({100*c[(dep,k)]/t:8.4f}%)')
        for k in ['★ 7 本（0<e 抜き）', '★★ 8 本すべて']:
            print(f'      {k:16s} {c[(dep,k)]:9d} ({100*c[(dep,k)]/t:8.4f}%)')
        b = c[(dep, '(h2a) 破れる列')]
        print(f'      (h2a) 破れる列 {b}   ★ そのうち孤児 {c[(dep,"(h2a) ★ その列は孤児")]} '
              f'({100*c[(dep,"(h2a) ★ その列は孤児")]/max(b,1):7.3f}%)')
    for x in ex:
        print(f'      ⚠ (h2a) 親が居るのに破れる例 V={x[0]} 列 j={x[1]} srow={x[2]} 親={x[3]}')
    print()


if __name__ == '__main__':
    run(2, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 3, 150, 431)
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 3, 100, 433)
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), 2, 60, 435)
