# -*- coding: utf-8 -*-
"""**課題 (u1) —— L3 の予測「非減少の段は全部 `j = 0`」を壊しにいく。**

## 前提の逐語（教訓 2）

`L105Cap:13093` **§186 `snocStep_oper_tower`**:

    (hj : j < Q.length) (hpj : p < j)
    (hpe : parent … = n * Q.length + p)
    ⟹ ∃ V d0 d1, V.length = j - p ∧ …⟦m⟧ = (… .take p) ++ mTower V d0 d1 m

    d0 = if 0 < srow T (T.length-1) then entry T 0 (T.length-1) - entry T 0 (n*|Q|+p) else 0
    d1 = if 1 < srow T (T.length-1) then entry T 1 (T.length-1) - entry T 1 (n*|Q|+p) else 0

⟹ **(u1c) 私の `j` と §186 の `j` は同じ。`d0,d1` も私の `step_det` と逐語で同じ。**
⟹ **⚠ §186 は `hpe`（親が**いまのブロックの中**）を**前提に置いている**。定理ではない。**

`L105Cap:11463` **H12 の `mTowerClosed_of_snocStepSameBlock` の前提**:

    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hnb : ∀ l, 0 < l → l < Q.length → entry Q 1 0 < entry Q 1 l)
    (hz0 : entry Q 2 0 = 0)

⟹ **★ 「`j >= 1` なら親は同じブロック」は `hr0 ∧ hnb ∧ hz0` の下でしか主張していない。**

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ 前提を課さなければ `j >= 1` の非減少段は**出る**と予想（(n1) で 0.07〜0.09% を見ている）。**
> **⚠ 前提を課せば **0%** になると予想。⟹ そのとき定理は無傷で、母集団の問題。**
> **⚠ 見積もり: 無条件 0.05〜0.5%、`hr0∧hnb∧hz0` つき 0%。**
> **⚠ 反例の形: `hr0∧hnb∧hz0` を全部満たす `Q` で `j >= 1` かつ `|V| >= |Q|`。出たら緑に反例。**
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block


def hr0(Q):  return all(Q[0][0] < Q[l][0] for l in range(1, len(Q)))
def hnb(Q):  return all(Q[0][1] < Q[l][1] for l in range(1, len(Q)))
def hz0(Q):  return Q[0][2] == 0


def probe(Q, d, e, n, j):
    """`(|V|, par, ブロック内か)` を返す。"""
    L = len(Q)
    T = [tuple(x) for x in mTower(Q, d, e, n)]
    S = T + block(Q, d, e, n)[:j + 1]
    last = len(S) - 1
    par = trio.parent(S, srow(S, last), last)
    if par is None: return None
    return last - par, par, par >= n * L


def gen(rnd, E, L, force):
    """`force` なら `hr0 ∧ hnb ∧ hz0` を**構成的に**満たす `Q` を作る。"""
    if force:
        a, b = rnd.randrange(E - 1), rnd.randrange(E - 1)
        Q = [(a, b, 0)]
        for _ in range(L - 1):
            Q.append((rnd.randrange(a + 1, E), rnd.randrange(b + 1, E), rnd.randrange(2)))
        return Q
    COL = [(x, y, z) for x in range(E) for y in range(E) for z in (0, 1)]
    root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
    if not hi: return None
    return [root] + [rnd.choice(hi) for _ in range(L - 1)]


def run(E, LS, NS, DE, nsamp, seed, force, tag):
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        Q = gen(rnd, E, L, force)
        if Q is None or len(Q) < 2: continue
        d, e, n = rnd.choice(DE), rnd.choice(DE), rnd.choice(NS)
        for j in range(L):
            r = probe(Q, d, e, n, j)
            if r is None: continue
            lv, par, inblk = r
            key = 'j=0' if j == 0 else 'j>=1'
            c[key] += 1
            if not inblk: c[key + ' 親がブロックの外（＝復活）'] += 1
            if lv >= L:
                c[key + ' ★ 非減少 |V|>=|Q|'] += 1
                if j >= 1:
                    c['⚠⚠ j>=1 で非減少'] += 1
                    tags = ('hr0' if hr0(Q) else '') + ('hnb' if hnb(Q) else '') + \
                           ('hz0' if hz0(Q) else '')
                    c['   うち ' + (tags if tags else '前提なし')] += 1
                    if hr0(Q) and hnb(Q) and hz0(Q):
                        c['⚠⚠★ 3 前提すべて満たして j>=1 で非減少'] += 1
                        if len(ex) < 5: ex.append((Q, d, e, n, j, lv, par))
    print(f'### {tag} 値域<{E} |Q|∈{LS} n∈{tuple(NS)} (d,e)∈{tuple(DE)}  [{time.time()-t0:.1f}s]')
    for k in ('j=0', 'j>=1'):
        t = c[k]
        print(f'    {k}: 段 {t}   非減少 {c[k+" ★ 非減少 |V|>=|Q|"]} '
              f'({100*c[k+" ★ 非減少 |V|>=|Q|"]/max(t,1):7.4f}%)   '
              f'親がブロックの外 {c[k+" 親がブロックの外（＝復活）"]} '
              f'({100*c[k+" 親がブロックの外（＝復活）"]/max(t,1):7.4f}%)')
    print(f'    **⚠⚠ `j>=1` で非減少 … {c["⚠⚠ j>=1 で非減少"]}**')
    for k in sorted(x for x in c if isinstance(x, str) and x.startswith('   うち')):
        print(f'    {k:34s} {c[k]}')
    print(f'    **⚠⚠★ `hr0 ∧ hnb ∧ hz0` を全部満たして `j>=1` で非減少 … '
          f'{c["⚠⚠★ 3 前提すべて満たして j>=1 で非減少"]}**')
    for x in ex: print(f'      ⚠ 反例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} |V|={x[5]} par={x[6]}')
    print()


if __name__ == '__main__':
    run(4, (3,4,5,6),   (2,3,4),   range(4), 40000, 111, False, '(A) 前提を課さない（無条件）')
    run(6, (3,4,5,6,8), (2,3,4,5), range(6), 40000, 113, False, '(A) 前提を課さない（広い箱）')
    run(6, (3,4,5,6,8), (2,3,4,5), range(6), 40000, 115, True,  '(B) ★ `hr0∧hnb∧hz0` を構成的に満たす `Q` だけ')
    run(9, (4,6,8,10),  (2,3,4,5), range(9), 30000, 117, True,  '(B) ★ 同上・広い箱（教訓 21）')
