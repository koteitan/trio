# -*- coding: utf-8 -*-
"""**(HZ0-HERED) —— 次の窓は `hz0(V)` を満たすか。**

## ⚠ 母集団と定義（1 行ずつ）

★ **シート由来**: `psiI.json` の DBMS 列の全接頭辞 `Q`（重複除去）。
⛔ **一様な箱（対照）**: `Lift1 ((0,v,z)::R) t` の `dropLast`。
`S = mTower Q d e n ++ block.take (j+1)`、`c = parent S (srow S (|S|-1)) (|S|-1)`、
**窓 `V = S[c:|S|-1]`**。

    **`hz0(X) :⟺ entry X 2 0 = 0`**、**`zle1(X) :⟺ ∀ j, entry X 2 j <= 1`**
    **`hr0(X) :⟺ ∀ l, 0 < l → entry X 0 0 < entry X 0 l`**（`L106.lean:162` 逐語）

⟹ ★ `TowerP''` の 3 条件（`hr0 ∧ hz0 ∧ zle1`）を課した群と、外した群を**並べて**出す。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r169 import domT
from r201 import dOf, eOf
from r206 import hr0
from r263 import load

hz0 = lambda X: X[0][2] == 0
zle1 = lambda X: all(q[2] <= 1 for q in X)


def sheetQ(LQ):
    seen = set()
    for M in load():
        for k in range(2, min(len(M), LQ) + 1):
            Q = tuple(tuple(x) for x in M[:k])
            if Q not in seen: seen.add(Q)
    return [list(q) for q in seen]


def boxQ(L, R1):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1, 2)]
    out = []
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        if srow(R, len(R) - 1) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in (0, 1, 2):
            for z in (0, 1, 2):
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in (0, 1):
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q = M[:-1]
                    if len(Q) >= 2 and dOf(M) > 0: out.append(Q)
    return out


def run(Qs, DS, ES, NS, tag):
    c = Counter(); ex = []; t0 = time.time()
    for Q in Qs:
        g3 = hr0(Q) and hz0(Q) and zle1(Q)
        g = "★TowerP''(3条件)" if g3 else '⛔ 外した群'
        for d in DS:
            for e in ES:
                for n in NS:
                    T = [tuple(x) for x in mTower(Q, d, e, n)]
                    B = [tuple(x) for x in block(Q, d, e, n)]
                    for j in range(1, len(Q)):
                        S = T + B[:j + 1]
                        last = len(S) - 1
                        sr = srow(S, last)
                        cc = trio.parent(S, sr, last)
                        if cc is None or last - cc < 2: continue
                        V = [tuple(v) for v in S[cc:last]]
                        ok = hz0(V)
                        c[f'[{g}] 分母'] += 1
                        c[f'[{g}] ★hz0(V)'] += 1 if ok else 0
                        c[f'[{g}][srow={sr}] 分母'] += 1
                        c[f'[{g}][srow={sr}] ★hz0(V)'] += 1 if ok else 0
                        if not ok and len(ex) < 6:
                            ex.append((Q, d, e, n, j, cc, sr, V[:4], g3))
    print(f'### {tag}  Q {len(Qs)} 個  [{time.time()-t0:.1f}s]')
    for g in ("★TowerP''(3条件)", '⛔ 外した群'):
        for suf in ('', '[srow=0]', '[srow=1]', '[srow=2]'):
            key = f'[{g}]{suf}'
            d = c[f'{key} 分母']
            if not d: continue
            ok = c[f'{key} ★hz0(V)']
            m = ' ★★★ **100%**' if ok == d else ' ⛔ **破れあり**'
            print(f'  {key:28s} 分母 {d:8d}  ★ **hz0(V)** {ok:8d} '
                  f'({100*ok/max(d,1):8.4f}%)   ⛔ 破れ {d-ok}{m}')
    for x in ex:
        print(f'      ⛔ hz0(V) 破れ: Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} '
              f'c={x[5]} **srow={x[6]}** 3条件={x[8]}')
        print(f'          V の先頭 = {x[7]}')
    print()


if __name__ == '__main__':
    run(sheetQ(8), (1, 2, 3), (0, 1, 2), (1, 2, 3, 5), '★ シート由来 Q（|Q|<=8）')
    run(sheetQ(10), (1, 2, 3, 4), (0, 1, 2, 3), (1, 2, 3, 5, 8),
        '★★ シート由来 Q（|Q|<=10, d<=4, e<=3, n<=8）')
    run(boxQ(3, 3), (1, 2), (0, 1), (1, 2), '⛔ 一様な箱（対照、行2<=2）')
