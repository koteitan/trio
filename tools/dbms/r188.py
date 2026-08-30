# -*- coding: utf-8 -*-
"""★★★ (u2b)(u2c) の答え —— **`(d,e)` のランクが非減少の段ごとに真に減る。**

## r187 で見えた機構（仮説）。**測る前に書く（教訓 45）**

段の合成列の**足す列** `S[last]` ＝ ブロック `n` の第 0 列
`= (Q[0][0] + d*n, Q[0][1] + e*n（根は必ずリフト）, Q[0][2])`
親候補のブロック根 `S[(n-1)|Q|] = (Q[0][0] + d*(n-1), Q[0][1] + e*(n-1), Q[0][2])`

    `oper` の `d0 = if 0 < i1 then … else 0`、`d1 = if 1 < i1 then … else 0`（`Trio.lean:107`）

**⟹ 仮説（4 本）**

    **(M1)** 非減少（`|V| = |Q|`、＝ `p_rel = 0`）の段では **足す列の `srow <= 1`**
            （理由: `srow = 2` ならブロック根の行 2 は**全部等しい** `= entry Q 2 0`
             ⟹ `nextrel2` の狭義不等号が取れない ⟹ ブロック根は親になれない）
    **(M2)** そのとき `srow = 1` ⟹ **`e' = 0`**、`srow = 0` ⟹ **`d' = 0` かつ `e' = 0`**
    **(M3)** `(d,e) = (0,0)` からは**非減少の段が無い**
            （塔が `Q` の単純反復 ⟹ 足す列は `Q[0]` と行 0 が等しい ⟹ `nextrel0` が取れない）
    **(M4)** ⟹ **ランク `r(d,e) = (0<d) + (0<e) ∈ {0,1,2}` が非減少の段ごとに真に減る**
            **⟹ 非減少は高々 2 段。⟹ (u2b) の答え。⟹ 不動点も無い ((u2c))。**

**⚠ 見積もり: (M1)(M2)(M3)(M4) はどれも 100%。100% なので教訓 21 で箱を広げて壊しにいく。**
**⚠ 陽性対照: `srow = 2` の段を集めて `p_rel = 0` が本当に 0 か（＋ `|V| = |Q|` が 0 か）。**
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r171 import step_det


def rank(d, e): return (1 if d > 0 else 0) + (1 if e > 0 else 0)


def run(E, LS, NS, DE, nsamp, seed):
    COL = [(a, b, c) for a in range(E) for b in range(E) for c in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []
    for _ in range(nsamp):
        L = rnd.choice(LS)
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
                V, d2, e2 = step_det(Q, d, e, n, j)
                nd = len(V) >= L
                c[('全段 srow', i1)] += 1
                if i1 == 2: c['srow=2 の段'] += 1
                if not nd: continue
                c['★ 非減少の段'] += 1
                c[('非減少の srow', i1)] += 1
                if i1 <= 1: c['  (M1) srow <= 1'] += 1
                else:
                    c['  ⚠ (M1) 破れ srow=2 で非減少'] += 1
                    if len(ex) < 4: ex.append(('M1', Q, d, e, n, j, i1, len(V)))
                if i1 == 1 and e2 == 0: c["  (M2) srow=1 ⟹ e'=0"] += 1
                if i1 == 1 and e2 != 0: c["  ⚠ (M2) 破れ srow=1 なのに e'>0"] += 1
                if i1 == 0 and d2 == 0 and e2 == 0: c["  (M2) srow=0 ⟹ (d',e')=(0,0)"] += 1
                if i1 == 0 and (d2 != 0 or e2 != 0): c["  ⚠ (M2) 破れ srow=0 なのに (d',e')≠(0,0)"] += 1
                if rank(d2, e2) < rank(d, e): c['  ★ (M4) ランクが真に減った'] += 1
                else:
                    c['  ⚠⚠ (M4) 破れ ランクが減らない'] += 1
                    if len(ex) < 8: ex.append(('M4', Q, d, e, n, j, i1, (d2, e2)))
                if (d, e) == (0, 0):
                    c['  ⚠ (M3) 破れ (d,e)=(0,0) から非減少'] += 1
    nd = c['★ 非減少の段']
    print(f'### 値域<{E} |Q|∈{LS} n∈{tuple(NS)} (d,e)∈{tuple(DE)}   非減少の段 {nd}')
    print('    全段の srow 分布: ', dict(sorted((k[1], c[k]) for k in c
                                        if isinstance(k, tuple) and k[0] == '全段 srow')))
    print('    非減少の srow 分布: ', dict(sorted((k[1], c[k]) for k in c
                                        if isinstance(k, tuple) and k[0] == '非減少の srow')),
          f'   ← 陽性対照: 全段には srow=2 が {c["srow=2 の段"]} 件ある')
    for k in sorted(x for x in c if isinstance(x, str) and x.startswith('  ')):
        print(f'    {k:44s} {c[k]:8d} ({100*c[k]/max(nd,1):7.3f}%)')
    for x in ex: print('      ⚠ 破れ例', x)
    print()


if __name__ == '__main__':
    run(4, (3,4,5,6),    (1,2,3,4),   range(4), 20000, 161)
    print('#### 教訓 21: 箱を広げる')
    run(6, (3,4,5,6,8),  (1,2,3,4,5), range(6), 20000, 163)
    run(9, (4,6,8,10),   (1,2,3,4,6), range(9), 12000, 165)
    run(12,(5,8,12),     (1,2,3,5,8), range(12), 6000, 167)
