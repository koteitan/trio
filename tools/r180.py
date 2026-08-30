# -*- coding: utf-8 -*-
"""(w1b) の決め手。**`(d,e)` 決め打ちで `|V|` は「増える」ことがあるか。**

非減少 = 「等しい」か「増える」。**測度になるかは、この区別で決まる。**

    もし `|V'| <= |V|` が常に成り立ち（弱減少）、
    かつ非減少（=等号）の連が最大 2 なら ⟹ **`|V|` は 2 段ごとに真に減る ⟹ 停止測度。**

## ★ 予想（教訓 45）
> **⚠ 見積もり: `|V'| > |V|` は起きる（`n` を大きくすれば塔が伸びるので）。5〜20%。**
> **⚠ 起きなければ（0%）、`|V|` は弱減少 ⟹ L3 に渡せる測度になる。教訓 21 で壊しにいく。**
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from collections import Counter
from r171 import step_det


def run(E, LS, NS, DE, nsamp, seed, det):
    COL = [(a, b, c) for a in range(E) for b in range(E) for c in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []
    for _ in range(nsamp):
        L = rnd.choice(LS)
        root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
        if not hi: continue
        Q0 = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d0, e0 = rnd.choice(DE), rnd.choice(DE)
        if det:
            r = step_det(Q0, d0, e0, rnd.choice(NS), rnd.randrange(L))
            if r is None or len(r[0]) < 2: continue
            Q, d, e = r          # ← `(d,e)` は `oper` が決めた値
        else:
            Q, d, e = Q0, d0, e0  # ← 陽性対照: `(d,e)` は自由に選んだ値
        c['母集団'] += 1
        for n in NS:
            for j in range(len(Q)):
                r2 = step_det(Q, d, e, n, j)
                if r2 is None: continue
                c['段の総数'] += 1
                if len(r2[0]) > len(Q):
                    c['⚠★ |V\'| > |V|（増えた）'] += 1
                    if len(ex) < 4: ex.append((Q, d, e, n, j, len(Q), len(r2[0])))
                elif len(r2[0]) == len(Q): c['|V\'| = |V|'] += 1
                else: c['|V\'| < |V|'] += 1
    t = c['段の総数']
    tag = '決め打ち' if det else '陽性対照(自由)'
    print(f'### {tag} 値域<{E} |Q0|∈{LS} n∈{tuple(NS)} (d,e)∈{tuple(DE)}  '
          f'状態 {c["母集団"]}  段 {t}')
    for k in ["⚠★ |V'| > |V|（増えた）", "|V'| = |V|", "|V'| < |V|"]:
        print(f'    {k:26s} {c[k]:8d} ({100*c[k]/max(t,1):7.4f}%)')
    for x in ex:
        print(f'      ⚠ 増えた例 Q={x[0]} (d,e)=({x[1]},{x[2]}) n={x[3]} j={x[4]} '
              f'{x[5]} -> {x[6]}')
    print()


if __name__ == '__main__':
    run(4, (3,4,5,6),     (2,3),       range(4), 8000,  81, True)
    run(6, (4,6,8),       (1,2,3,4,5), range(6), 8000,  83, True)
    run(9, (6,8,10,12),   (1,2,3,4,6), range(9), 4000,  87, True)
    print('#### 陽性対照: `(d,e)` を自由に選んだ状態なら増えるか')
    run(6, (4,6,8),       (1,2,3,4,5), range(6), 8000,  83, False)
