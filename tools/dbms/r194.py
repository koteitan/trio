# -*- coding: utf-8 -*-
"""(y1) 決着 —— **真の核の大きさ。**

`h2_cone`（`L105Cap:11316`）の射程は **`1 <= j` ∧ `0 < entry V 2 j` ∧ `le1 V 0 j`（錐の中）**。
錐の外は H12 が別に片づけている。
⟹ **`hz0(V)` が破れて困るのは、その射程の列だけ。**

**真の核** ＝ `hz0(V)` が破れた段のうち、
  **`1 <= j` ∧ `0 < entry V 2 j` ∧ `le1 V 0 j` ∧ `¬ hasParent (V.take (j+1)) 2 j`**
の列を持つもの。
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r183 import hr0, hz0


def run(E, LS, NS, DE, nsamp, seed):
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        a = rnd.randrange(E - 1)
        Q = [(a, rnd.randrange(E), 0)] + \
            [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        assert hr0(Q) and hz0(Q)
        d, e = rnd.choice(DE), rnd.choice(DE)
        for n in NS:
            for j0 in range(L):
                T = [tuple(x) for x in mTower(Q, d, e, n)]
                S = T + block(Q, d, e, n)[:j0 + 1]
                last = len(S) - 1
                par = trio.parent(S, srow(S, last), last)
                if par is None: continue
                V = [tuple(x) for x in S[par:last]]
                if len(V) < 2: continue
                c['全段'] += 1
                cone = [i for i in range(1, len(V))
                        if V[i][2] > 0 and trio.is_ancestor(V, 1, 0, i)]
                bad = [i for i in cone if trio.parent(V[:i + 1], 2, i) is None]
                if V[0][2] == 0:
                    c['hz0(V) 成立（h2_cone がそのまま使える）'] += 1
                    if bad: c['  ⚠ それでも錐の中で行2の孤児がある（あってはいけない）'] += 1
                    continue
                c['★ hz0(V) が破れた段'] += 1
                if not cone:
                    c['  ★ 射程の列が無い ⟹ hz0(V) は要らない'] += 1
                elif not bad:
                    c['  ★ 射程の列はあるが全部 V の中で行2の親を持つ ⟹ 要らない'] += 1
                else:
                    c['  ⚠⚠★ 真の核（錐の中・行2正・親なし）'] += 1
                    if len(ex) < 3: ex.append((Q, d, e, n, j0, V, bad))
    t = c['全段']; m = c['★ hz0(V) が破れた段']
    print(f'### 値域<{E} |Q|∈{LS} n∈{tuple(NS)}  全段 {t}  [{time.time()-t0:.1f}s]')
    print(f'    hz0(V) 成立 … {c["hz0(V) 成立（h2_cone がそのまま使える）"]} '
          f'({100*c["hz0(V) 成立（h2_cone がそのまま使える）"]/max(t,1):6.2f}%)'
          f'   （うち矛盾 {c["  ⚠ それでも錐の中で行2の孤児がある（あってはいけない）"]} ← 0 のはず）')
    print(f'    ★ hz0(V) が破れた段 … {m} ({100*m/max(t,1):6.3f}%)')
    for k in ['  ★ 射程の列が無い ⟹ hz0(V) は要らない',
              '  ★ 射程の列はあるが全部 V の中で行2の親を持つ ⟹ 要らない',
              '  ⚠⚠★ 真の核（錐の中・行2正・親なし）']:
        print(f'      {k:46s} {c[k]:8d} ({100*c[k]/max(m,1):6.2f}% of 破れ, '
              f'{100*c[k]/max(t,1):6.3f}% of 全段)')
    for x in ex: print(f'      ⚠ 核の例 Q={x[0]} (d,e)=({x[1]},{x[2]}) n={x[3]} j={x[4]} '
                       f'V={x[5]} 孤児の列={x[6]}')
    print()


if __name__ == '__main__':
    run(6,  (3,4,5,6,8), (1,2,3,4,5), range(6),  12000, 231)
    print('#### 教訓 21: 箱を広げる')
    run(9,  (4,6,8,10),  (1,2,3,4,6), range(9),   8000, 233)
    run(12, (5,8,12),    (1,2,3,5,8), range(12),  5000, 235)
