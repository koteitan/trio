# -*- coding: utf-8 -*-
"""**課題 (z1) —— 「消費側が供給でき、かつ遺伝する」前提を総当たりで探す。**

## 測り方

候補 `P` ごとに: **母集団 = `P(Q)` を満たす `Q`**、そこからの全段で

    **遺伝率** … `P(V)` が成り立つ割合   ← **100% なら遺伝する**
    **目的達成率** … `h2cone(V)` が成り立つ割合  ← これが本当に要るもの

**両方 100% の候補が答え。** ⚠ 「消費側が供給できるか」は L3 の判断（教訓 43）。
私は**測れる部分**（遺伝と目的）だけを出し、供給可能性は所見として添える。

## 候補（`file:line` つき）

    P1 `hz0`      `entry X 2 0 = 0`                                （`L105Cap:11316` の前提）
    P2 `h2cone`   `∀ j, 0<j → le1 X 0 j → 0 < entry X 2 j → hasParent (X.take (j+1)) 2 j`
    P3 `h2all`    上の錐の制限を外した版
    P4 `zeroRow2` `∀ p ∈ X, p.2.2 = 0`                            （`L105Cap:2054` の前提）
    P5 `cone2`    `∀ j, 0 < entry X 2 j → le1 X 0 j`（行 2 が正の列は全部錐の中）
    P6 `hz0∧cone2`  ← **H12 が「`h2` ⟺ `z=0` ∧ 行 2 が正の列は全部錐の中」と割ったもの**
                     （`L105Cap:11310` の散文）
    P7 `z2mono`   行 2 が非減少（断片では「0 が並んでから 1 が並ぶ」）
    P8 `hz0∧h2cone`

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ P4 `zeroRow2` は **100% 遺伝する**はず（`shiftr01`/`Lift1` は行 2 を変えない、
>   `entry2_shiftr01`(`Core:3416`) / `entry2_Lift1`(`Wset:955`)）。だが L3 の §76.1 で
>   **既に無料**なので新しくない。**
> **⚠ P6 が本命と予想。H12 が `h2` の正体として割った形なので。見積もり 遺伝 85〜100%。**
> **⚠ ほかは全部 90% 台前半で落ちると予想。**
> **⚠ 反例の形: 遺伝 100% だが目的が落ちる、またはその逆。**
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r195 import h2cone, h2all


def hz0(X):      return X[0][2] == 0
def zeroRow2(X): return all(p[2] == 0 for p in X)
def cone2(X):    return all(trio.is_ancestor(X, 1, 0, j)
                            for j in range(len(X)) if X[j][2] > 0)
def z2mono(X):   return all(X[i][2] <= X[i + 1][2] for i in range(len(X) - 1))

CAND = {
    'P1 hz0':        hz0,
    'P2 h2cone':     lambda X: not h2cone(X),
    'P3 h2all':      lambda X: not h2all(X),
    'P4 zeroRow2':   zeroRow2,
    'P5 cone2':      cone2,
    'P6 hz0∧cone2':  lambda X: hz0(X) and cone2(X),
    'P7 z2mono':     z2mono,
    'P8 hz0∧h2cone': lambda X: hz0(X) and not h2cone(X),
    '(対照) 前提なし':   lambda X: True,
}


def run(E, LS, NS, DE, nsamp, seed):
    rnd = random.Random(seed)
    print(f'### 値域<{E} |Q|∈{LS} n∈{tuple(NS)} (d,e)∈0..{max(DE)}   `Q` を {nsamp} 本ずつ')
    print('    %-16s %6s %8s %15s %18s %13s' %
          ('候補', 'Q', '段', '遺伝 P(V)', 'h2cone(V) 成立', '★ 両方'))
    for name, P in CAND.items():
        c = Counter(); tries = 0; t0 = time.time()
        while c['Q'] < nsamp and tries < nsamp * 800:
            tries += 1
            L = rnd.choice(LS)
            a = rnd.randrange(E - 1)
            Q = [(a, rnd.randrange(E), rnd.randrange(2))] + \
                [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
                 for _ in range(L - 1)]
            if not P(Q):
                continue
            c['Q'] += 1
            d, e = rnd.choice(DE), rnd.choice(DE)
            for n in NS:
                for j0 in range(L):
                    T = [tuple(x) for x in mTower(Q, d, e, n)]
                    S = T + block(Q, d, e, n)[:j0 + 1]
                    last = len(S) - 1
                    par = trio.parent(S, srow(S, last), last)
                    if par is None:
                        continue
                    V = [tuple(x) for x in S[par:last]]
                    if len(V) < 2:
                        continue
                    c['seg'] += 1
                    pv = bool(P(V))
                    ok = (len(h2cone(V)) == 0)   # `h2cone` は破れた列のリスト
                    if pv:
                        c['inh'] += 1
                    if ok:
                        c['goal'] += 1
                    if pv and ok:
                        c['both'] += 1
        t = max(c['seg'], 1)
        print('    %-16s %6d %8d %14.4f%% %17.4f%% %12.4f%%   [%.0fs]' %
              (name, c['Q'], c['seg'], 100*c['inh']/t, 100*c['goal']/t,
               100*c['both']/t, time.time()-t0))
    print()


if __name__ == '__main__':
    run(6, (3,4,5,6,8), (1,2,3,4), range(6), 2500, 311)
    print('#### 教訓 21: 箱を広げる')
    run(9, (4,6,8,10),  (1,2,3,4), range(9), 2000, 313)
    run(12,(5,8,12),    (1,2,3,4), range(12),1500, 315)
