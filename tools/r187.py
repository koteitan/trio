# -*- coding: utf-8 -*-
"""⚠⚠ (u2b) 危険信号の追跡。**3 段目は本当に無いのか。**

## 算術上の懸念（測る前に書く）

段 1 で `j=0, p_rel=0` なら `par = (n-1)|Q|`, `last = n|Q|`:

    `S[last]` = ブロック n の第 0 列 = `(Q0+d*n, Q1+e*n, Q2)`
    `S[par]`  = ブロック n-1 の第 0 列 = `(Q0+d*(n-1), Q1+e*(n-1), Q2)`  （根は反射で必ずリフト）
    ⟹ **`d' = d`**、**`e' = e` if srow=2 else 0**、`srow = 2 ⟺ entry Q 2 0 > 0`

⟹ `hz0`（`entry Q 2 0 = 0`）なら **`e' = 0`**。
⟹ 段 2 は `e = 0` ⟹ `V' = shiftr01 δ 0 V`（純粋なずらし）、`d'' = d`、`e'' = 0`。
⟹ **`shiftr01` は行 0 を一様にずらすだけ ⟹ `parent`/`srow`/`le0`/`le1` を変えない**
⟹ **★ 段 3 は段 2 と同型のはず ⟹ 無限に続くはず。**

**⚠ ところが r174/r179 の実測は「3 段目 0 件」。どちらかが誤り。至急切り分ける。**

**やること**: 2 段続いた実例を 1 つ取り、**段 3 を手で全部試して**中身を印字する。
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r171 import step_det

COL = [(a, b, c) for a in range(6) for b in range(6) for c in (0, 1)]


def show(Q, d, e, NS, depth, path):
    print(f'  段{depth}: Q={Q} (d,e)=({d},{e})  |Q|={len(Q)}')
    got = []
    for n in NS:
        for j in range(len(Q)):
            r = step_det(Q, d, e, n, j)
            if r is None: continue
            V, d2, e2 = r
            L = len(Q); T = n * L; last = T + j
            S = [tuple(x) for x in mTower(Q, d, e, n)] + block(Q, d, e, n)[:j + 1]
            par = trio.parent(S, srow(S, last), last)
            tag = '★非減少' if len(V) >= len(Q) else '        '
            if len(V) >= len(Q):
                got.append((n, j, V, d2, e2))
                print(f'      {tag} n={n} j={j} par={par} (blk={par//L},p_rel={par%L}) '
                      f'|V|={len(V)} (d\',e\')=({d2},{e2}) V={V}')
    if not got:
        print(f'      ⟹ ⚠ 段{depth} で非減少の手が無い（打ち切り）')
        return
    n, j, V, d2, e2 = got[0]
    if depth < 5:
        show(V, d2, e2, NS, depth + 1, path)


rnd = random.Random(201)
NS = (1, 2, 3, 4, 5)
found = 0
for _ in range(200000):
    L = rnd.choice((3, 4, 5))
    root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
    if not hi: continue
    Q = [root] + [rnd.choice(hi) for _ in range(L - 1)]
    d, e = rnd.randrange(6), rnd.randrange(6)
    ok1 = None
    for n in NS:
        for j in range(L):
            r = step_det(Q, d, e, n, j)
            if r and len(r[0]) >= L: ok1 = r; break
        if ok1: break
    if not ok1: continue
    V, d2, e2 = ok1
    ok2 = any(step_det(V, d2, e2, n, j) and len(step_det(V, d2, e2, n, j)[0]) >= len(V)
              for n in NS for j in range(len(V)))
    if not ok2: continue
    found += 1
    print(f'=== 2 段続いた例 #{found} ===')
    show(Q, d, e, NS, 1, [])
    print()
    if found >= 3: break
