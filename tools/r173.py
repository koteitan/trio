# -*- coding: utf-8 -*-
"""(w1b) の核心。**`(d,e)` を `oper` が決めると `|V|` は減るか。**

## 母集団（ここが肝）

「**実際に到達する状態**」= 1 段展開の**出力** `(V, d', e')`。
`d', e'` は `oper` の定義（`Trio.lean:107-108`）が決めた値であって、選べない。

## 測る量

    `mx(V, d', e') = max over (n, j) of |V'|`     (`V'` = 次の窓)

**`mx < |V|` なら `|V|` は狭義に減る ⟹ 停止測度。**

## ★ 予想（教訓 45）＋ 見積もり

> r171/r172 で 2 段目が 0/600 だったので、**`mx < |V|` が 100% 近い**と予想。
> **⚠ 見積もり 90〜100%。100% なら教訓 21 で箱を広げて壊しに行く。**
> **⚠ 反例の形: `d'` が大きく `V` の行 0 が寝ている状態。`|V'| >= |V|` になる `(n,j)`。**

**陽性対照**: 同じ `V` で `(d,e)` を**自由**にすると `mx >= |V|` が ~50% 出るはず。
**`W` 所属は判定しない。**
"""
import sys, itertools, time, random, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from collections import Counter
from r171 import step_det


def mx(Q, d, e, NS):
    """`(d,e)` 決め打ちで到達できる最大の `|V'|`。到達不能なら -1。"""
    b = -1
    for n in NS:
        for j in range(len(Q)):
            r = step_det(Q, d, e, n, j)
            if r: b = max(b, len(r[0]))
    return b


def mxfree(Q, DE, NS):
    b = -1
    for d in DE:
        for e in DE:
            b = max(b, mx(Q, d, e, NS))
    return b


def run(L, E, NS, DE, nsamp, seed):
    COL = [(a, b, c) for a in range(E) for b in range(E) for c in (0, 1)]
    rnd = random.Random(seed)
    c = Counter(); ex = []; t0 = time.time()
    tries = 0
    while c['母集団'] < nsamp and tries < nsamp * 60:
        tries += 1
        root = rnd.choice(COL)
        hi = [x for x in COL if x[0] > root[0]]
        if not hi: continue
        Q0 = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d0, e0 = rnd.choice(DE), rnd.choice(DE)
        n0, j0 = rnd.choice(NS), rnd.randrange(L)
        r = step_det(Q0, d0, e0, n0, j0)     # ← 1 段展開の出力だけを母集団にする
        if r is None: continue
        V, d, e = r[0], r[1], r[2]
        if len(V) < 2: continue
        c['母集団'] += 1
        m = mx(V, d, e, NS)
        mf = mxfree(V, DE, NS)
        if m < 0:
            c['(a) 次の段が存在しない'] += 1
        elif m < len(V):
            c['(b) ★ `mx` < `|V|`（減る）'] += 1
        else:
            c['(c) ⚠ `mx` >= `|V|`（減らない）'] += 1
            if len(ex) < 4: ex.append((V, d, e, m))
        if mf >= len(V): c['陽性対照 自由なら減らない'] += 1
    tot = c['母集団']
    dec = c['(b) ★ `mx` < `|V|`（減る）'] + c['(a) 次の段が存在しない']
    print(f'### |Q0|={L} 値域<{E} n∈{tuple(NS)} 初期(d,e)∈{tuple(DE)}  母集団 {tot}  [{time.time()-t0:.1f}s]')
    for k in ['(a) 次の段が存在しない', '(b) ★ `mx` < `|V|`（減る）', '(c) ⚠ `mx` >= `|V|`（減らない）']:
        print(f'    {k:34s} {c[k]:7d}  ({100*c[k]/max(tot,1):6.3f}%)')
    print(f'  **★ `|V|` が狭義に減る … {dec} / {tot} ({100*dec/max(tot,1):7.3f}%)**')
    print(f'  陽性対照 `(d,e)` 自由なら減らない … {c["陽性対照 自由なら減らない"]} / {tot} '
          f'({100*c["陽性対照 自由なら減らない"]/max(tot,1):6.2f}%)  ← 鳴るべき')
    for V, d, e, m in ex:
        print(f'      ⚠ 減らない例 V={V} (d,e)=({d},{e}) mx={m} |V|={len(V)}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--n', type=int, default=4000)
    a = ap.parse_args()
    for L in (3, 4, 5, 6):
        run(L, 4, (2, 3), range(4), a.n, 11)
    print('#### 教訓 21: 箱を広げる（値域 6、n を 1..5、初期 (d,e) を 0..5）')
    for L in (4, 6, 8):
        run(L, 6, (1, 2, 3, 4, 5), range(6), a.n, 23)
