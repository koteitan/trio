# -*- coding: utf-8 -*-
"""(a1d) ★ **3 段目を狙って出しにいく（教訓 21）** ＋ (w4) 窓の根の行 2。

## (a1d) ★ 予想（教訓 45）—— **私の「最大 2 段」を自分で壊しにいく**

§R176 の機構: **`rank(d,e) = (0<d)+(0<e)` が非減少の段ごとに真に減る。ただし `hr0 ∧ hz0` の下で。**

    `srow = 2` の段は **`(d', e') = (d, e)` を保存する**（`Trio.lean:107-108` の `if` が両方通る）
    `srow = 2` が非減少になれるのは **`entry Q 2 0 > 0`（＝ `hz0` を破る）**とき（r188: 0.54〜2.69%）

> **⚠ 予想: `hz0` を**わざと破って** `srow = 2` を狙えば、**3 段以上の鎖が出る**。**
> **⚠ 見積もり: 出る。30 段まで行く鎖も出る。**
> **⟹ そうなら私の結論は「**`hr0 ∧ hz0` の下で最大 2 段**」と条件つきに直す。**

## (w4) 窓の根の行 2

**主語の確認**: 「窓の根」＝ `V[0]` ＝ `S[par]` ＝ **親の列**（`V = S[par:last]`）。
`entry V 2 0 = entry S 2 par`。

> **⚠ L3 は 0% だと言っている。私の予想は**違う**:**
> **`srow = 1` の段では `nextrel1`（`Trio.lean:49`）は行 2 について何も言わない**
> **⟹ 親の行 2 は 1 でありうる。⚠ 見積もり **10〜40%**。**
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r171 import step_det
from r183 import hr0, hnb, hz0


def rank(d, e): return (1 if d > 0 else 0) + (1 if e > 0 else 0)


# ---------- (a1d) 3 段目を狙う ----------
def hunt(E, LS, NS, DE, nsamp, cap, seed, force_z2):
    """`force_z2` なら `entry Q 2 0 = 1`（`hz0` を破る）`Q` を狙って作る。"""
    COL = [(a, b, c) for a in range(E) for b in range(E) for c in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = None; t0 = time.time()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
        if not hi: continue
        if force_z2: root = (root[0], root[1], 1)
        Q = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d, e = rnd.choice(DE), rnd.choice(DE)
        # 非減少の鎖を BFS で伸ばす（状態で重複除去）
        front = [(tuple(map(tuple, Q)), d, e, [rank(d, e)])]
        best = 0; seq = None
        for s in range(cap):
            nxt = {}
            for (V, dd, ee, rk) in front:
                for n in NS:
                    for j in range(len(V)):
                        r = step_det(list(V), dd, ee, n, j)
                        if r is None or len(r[0]) < len(V) or len(r[0]) < 2: continue
                        nxt[(tuple(r[0]), r[1], r[2])] = rk + [rank(r[1], r[2])]
            if not nxt: break
            best = s + 1
            items = list(nxt.items()); rnd.shuffle(items)
            seq = items[0][1]
            front = [(k[0], k[1], k[2], v) for k, v in items[:300]]
        c['鎖の本数'] += 1; c[('最大段数', min(best, 6))] += 1
        if best >= 3:
            c['⚠★ 3 段以上'] += 1
            if ex is None: ex = (Q, d, e, best, seq)
        if best >= cap: c['⚠★★ cap まで'] += 1
    t = c['鎖の本数']
    tag = '`entry Q 2 0 = 1` を狙う' if force_z2 else '狙わない'
    print(f'### (a1d) {tag}  値域<{E} |Q|∈{LS} n∈{tuple(NS)} cap={cap}  '
          f'本数 {t}  [{time.time()-t0:.1f}s]')
    print('    最大段数の分布: ', dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple))))
    print(f'    **⚠★ 3 段以上 … {c["⚠★ 3 段以上"]} / {t} '
          f'({100*c["⚠★ 3 段以上"]/max(t,1):6.3f}%)   cap まで … {c["⚠★★ cap まで"]}**')
    if ex: print(f'      ⚠ 例 Q={ex[0]} (d,e)=({ex[1]},{ex[2]}) 段数={ex[3]} rank の列={ex[4]}')
    print()


# ---------- (w4) 窓の根の行 2 ----------
def w4(E, LS, NS, DE, nsamp, seed, force):
    COL = [(a, b, c) for a in range(E) for b in range(E) for c in (0, 1)]
    rnd = random.Random(seed); c = Counter()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        if force:
            a = rnd.randrange(E - 1)
            Q = [(a, rnd.randrange(E), 0)] + \
                [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
                 for _ in range(L - 1)]
        else:
            root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
            if not hi: continue
            Q = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d, e = rnd.choice(DE), rnd.choice(DE)
        for n in NS:
            for j in range(L):
                T = [tuple(x) for x in mTower(Q, d, e, n)]
                S = T + block(Q, d, e, n)[:j + 1]
                last = len(S) - 1
                i1 = srow(S, last)
                par = trio.parent(S, i1, last)
                if par is None: continue
                c['母集団(親あり)'] += 1
                c[('段の srow', i1)] += 1
                if S[par][2] == 0: c['★ 窓の根の行 2 = 0（hz0(V) 自動）'] += 1
                else:
                    c['⚠ 窓の根の行 2 = 1'] += 1
                    c[('⚠ そのときの srow', i1)] += 1
    t = c['母集団(親あり)']
    tag = '`hr0∧hz0` を構成' if force else '前提なし'
    print(f'### (w4) {tag}  値域<{E} |Q|∈{LS}  母集団 {t}')
    for k in ['★ 窓の根の行 2 = 0（hz0(V) 自動）', '⚠ 窓の根の行 2 = 1']:
        print(f'    {k:38s} {c[k]:8d} ({100*c[k]/max(t,1):7.3f}%)')
    print('    段の srow 分布: ', dict(sorted((k[1], c[k]) for k in c
                                       if isinstance(k, tuple) and k[0] == '段の srow')))
    print('    ⚠ 行 2 = 1 のときの srow: ', dict(sorted((k[1], c[k]) for k in c
                                       if isinstance(k, tuple) and k[0] == '⚠ そのときの srow')))
    print()


if __name__ == '__main__':
    hunt(6, (3,4,5,6),  (1,2,3,4,5), range(6), 4000, 30, 181, False)
    hunt(6, (3,4,5,6),  (1,2,3,4,5), range(6), 4000, 30, 183, True)
    hunt(9, (4,6,8),    (1,2,3,4,6), range(9), 3000, 30, 185, True)
    w4(6, (3,4,5,6,8), (1,2,3,4,5), range(6), 12000, 191, False)
    w4(6, (3,4,5,6,8), (1,2,3,4,5), range(6), 12000, 193, True)
    w4(9, (4,6,8,10),  (1,2,3,4,6), range(9),  8000, 195, True)
