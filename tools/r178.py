# -*- coding: utf-8 -*-
"""(w1) の**最後の穴**: `n=1, j=0` の「恒等段」に**不動点**はあるか。

r177 の広い箱で出た「もう 1 段つながる」例は**全部 `n=1, j=0` で `V = Q0`**だった。
もし `(Q, d, e) -> (Q, d, e)` の**不動点**があれば、**非減少の鎖は無限**になり
(w1) の結論（(n2) の撤回）が壊れる。**狙って探す。**

## ★ 予想（教訓 45）
> **⚠ 見積もり: 不動点は**ある**（`e = 0` かつ `srow < 2` なら `d' = d, e' = 0`）。
> ただし `V = Q` が成り立つのは `par = 0` のときだけなので、条件付き。**
> **⚠ もし不動点があれば (w1) の結論は「`n>=2` に限る」と条件を付けて言い直す。**
"""
import sys, time, random, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from collections import Counter
from r171 import step_det

def fixpoints(E, LS, NS, DE, nsamp, seed):
    COL = [(a, b, c) for a in range(E) for b in range(E) for c in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []
    for _ in range(nsamp):
        L = rnd.choice(LS)
        root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
        if not hi: continue
        Q = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d, e = rnd.choice(DE), rnd.choice(DE)
        c['母集団'] += 1
        for n in NS:
            for j in range(L):
                r = step_det(Q, d, e, n, j)
                if r is None: continue
                V, d2, e2 = r
                if [tuple(x) for x in V] == [tuple(x) for x in Q]:
                    c[f'恒等段 V=Q (n={n})'] += 1
                    if (d2, e2) == (d, e):
                        c[f'⚠★ 不動点 (n={n})'] += 1
                        if len(ex) < 6: ex.append((Q, d, e, n, j))
    print(f'### 不動点の探索 値域<{E} |Q0|∈{LS} n∈{tuple(NS)} (d,e)∈{tuple(DE)} 母集団 {c["母集団"]}')
    for k in sorted(c):
        if k != '母集団': print(f'    {k:26s} {c[k]}')
    for x in ex: print(f'      ⚠ 不動点 Q={x[0]} (d,e)=({x[1]},{x[2]}) n={x[3]} j={x[4]}')
    print()
    return ex


def long_chain(Q, d, e, cap, NS):
    """不動点候補から実際に鎖を伸ばす（状態が戻ったら無限）。"""
    seen = {}; cur, dd, ee = [tuple(x) for x in Q], d, e
    for s in range(cap):
        st = (tuple(cur), dd, ee)
        if st in seen: return 'LOOP', s, seen[st]
        seen[st] = s
        got = None
        for n in NS:
            for j in range(len(cur)):
                r = step_det(list(cur), dd, ee, n, j)
                if r and len(r[0]) >= len(cur) and len(r[0]) >= 2:
                    got = r; break
            if got: break
        if got is None: return 'STOP', s, None
        cur, dd, ee = [tuple(x) for x in got[0]], got[1], got[2]
    return 'CAP', cap, None


if __name__ == '__main__':
    for (E, LS, NS, DE, n) in [(4, (3,4,5,6), (1,2,3), range(4), 30000),
                               (6, (4,6,8), (1,2,3,4,5), range(6), 30000),
                               (9, (5,8,12), (1,2,3,4,6), range(9), 20000)]:
        ex = fixpoints(E, LS, NS, DE, n, 61)
        for x in ex[:4]:
            print('      ⟹ その点から鎖を伸ばすと:', long_chain(x[0], x[1], x[2], 200, NS))
        print()
