# -*- coding: utf-8 -*-
"""(w1) の**機構の同定**。「非減少がもう 1 段つながる」2.2% は何をしているのか。

r177 の例は**全部 `n=1, j=0` で `V = Q`（恒等段）、`(d,e) -> (d, 0)`**。
仮説: **`e` が 0 に焼き切れて、そこで止まる。**

**測る**: 「もう 1 段つながる」ケースで
  (H-a) その段は `n=1, j=0` か   (H-b) `V' = V`（恒等）か
  (H-c) `e > 0` から `e' = 0` か  (H-d) さらに 3 段目があるか
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from collections import Counter
from r171 import step_det


def run(E, LS, NS, DE, nsamp, seed):
    COL = [(a, b, c) for a in range(E) for b in range(E) for c in (0, 1)]
    rnd = random.Random(seed); c = Counter(); tries = 0
    while c['母集団(非減少の段の出力)'] < nsamp and tries < nsamp * 300:
        tries += 1
        L = rnd.choice(LS)
        root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
        if not hi: continue
        Q0 = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d0, e0 = rnd.choice(DE), rnd.choice(DE)
        r = step_det(Q0, d0, e0, rnd.choice(NS), rnd.randrange(L))
        if r is None or len(r[0]) < len(Q0) or len(r[0]) < 2: continue
        V, d, e = r
        c['母集団(非減少の段の出力)'] += 1
        hits = []
        for n in NS:
            for j in range(len(V)):
                r2 = step_det(V, d, e, n, j)
                if r2 and len(r2[0]) >= len(V) and len(r2[0]) >= 2:
                    hits.append((n, j, r2))
        if not hits: continue
        c['⚠ もう 1 段つながった'] += 1
        if all(n == 1 for (n, j, _) in hits): c['  (H-a) 全部 n=1'] += 1
        if all(j == 0 for (n, j, _) in hits): c['  (H-a) 全部 j=0'] += 1
        if all([tuple(x) for x in r2[0]] == [tuple(x) for x in V] for (_, _, r2) in hits):
            c["  (H-b) 全部 V'=V（恒等）"] += 1
        if e > 0 and all(r2[2] == 0 for (_, _, r2) in hits): c["  (H-c) e>0 かつ 全部 e'=0"] += 1
        if e == 0: c['  ⚠ e=0 なのにつながった'] += 1
        more = False
        for (_, _, r2) in hits:
            V2, d2, e2 = r2
            for n in NS:
                for j in range(len(V2)):
                    r3 = step_det(V2, d2, e2, n, j)
                    if r3 and len(r3[0]) >= len(V2) and len(r3[0]) >= 2: more = True
        if more: c['  ⚠★ (H-d) さらに 3 段目がある'] += 1
    t = c['母集団(非減少の段の出力)']; h = c['⚠ もう 1 段つながった']
    print(f'### 値域<{E} |Q0|∈{LS} n∈{tuple(NS)} (d,e)∈{tuple(DE)}  母集団 {t}')
    print(f'    ⚠ もう 1 段つながった … {h} / {t} ({100*h/max(t,1):6.3f}%)')
    for k in sorted(c):
        if k.startswith('  '): print(f'    {k:32s} {c[k]:6d} / {h} ({100*c[k]/max(h,1):6.2f}%)')
    print()


if __name__ == '__main__':
    run(6, (4, 6, 8),      (1,2,3,4,5), range(6), 30000, 71)
    run(9, (6, 8, 10, 12), (1,2,3,4,6), range(9), 15000, 73)
