# -*- coding: utf-8 -*-
"""**(ADJ'-e) / (ADJ'-f) / (ROW2 孤児) / (W15)。**

## (W15) H12 の予想を直接測る

    「**接頭辞 `A` は親を供給しない**」
    ⟹ ★ `A ++ Sj` で列 `k` の親を計算し、**その番地が `A` の中に入るか**を数える
    ⟹ ⚠ 対照は `A_bad`（`rsum` を破る ＝ **行 0 が浅い**）＝ ★ **供給できるとしたらこの形**
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
from r247 import A_OK, A_BAD, orphan_in

A_ALL = [('A_ok', A) for A in A_OK] + [('A_bad', A) for A in A_BAD]


def par_in_A(A, S, jab):
    T = [tuple(x) for x in A] + S
    k = len(A) + jab
    pp = trio.parent(T[:k + 1], srow(T, k), k)
    return pp is not None and pp < len(A)


def run(L, R1, VS, ZS, TS, NS, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    c = Counter(); sh = Counter(); t0 = time.time()
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        if srow(R, len(R) - 1) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q = M[:-1]
                    if len(Q) < 2: continue
                    d, e = dOf(M), eOf(M)
                    if not (d > 0 and hr0(Q) and Q[0][2] == 0): continue
                    for n in NS:
                        S0 = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(1, len(Q)):
                            Sj = S0 + B[:j + 1]
                            lastx = len(Sj) - 1
                            p = trio.parent(Sj, srow(Sj, lastx), lastx)
                            if p is None or lastx - p < 2: continue
                            V = [tuple(x) for x in Sj[p:lastx]]
                            # ---------- (W15) 接頭辞は親を供給するか ----------
                            for jab in range(1, lastx):
                                for nm, A in A_ALL:
                                    c[f'(W15) {nm} 分母'] += 1
                                    if par_in_A(A, Sj, jab):
                                        c[f'⛔ (W15) {nm} が親を供給'] += 1
                            # ---------- (ADJ'-e) 第 1 列 ----------
                            if not (V[1][2] == 0 and V[1][1] > 0): continue
                            c['(ADJ-e) 分母'] += 1
                            if V[0][1] < V[1][1]:
                                c['★ (ADJ-e) entry V 1 0 < entry V 1 1'] += 1
                                continue
                            c['⛔ (ADJ-e) 破れ'] += 1
                            a0, b0 = V[0][0], V[0][1]
                            sh[((0, 0, V[0][2]), (V[1][0]-a0, V[1][1]-b0, V[1][2]))] += 1
                            if V[0][1] == V[1][1]: c['   うち 行 1 が等しい'] += 1
                            else:                  c['   うち 行 1 が減る'] += 1
                            jab = p + 1
                            if orphan_in(V, 1):  c['(ADJ-f) (0)窓で孤児'] += 1
                            if orphan_in(Sj, jab): c['★ (ADJ-f) (ii)塔+ブロックで孤児'] += 1
                            else:
                                c['⛔ (ADJ-f) (ii)で親がいる'] += 1
                                pp = trio.parent(Sj[:jab+1], srow(Sj, jab), jab)
                                c[f'   ⛔ 親の位置: ' + ('ブロックの中' if pp >= len(S0)
                                                        else '塔の中')] += 1
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    dn = c['(ADJ-e) 分母']
    print(f'  ★★ (ADJ-e) 分母 {dn}  ★ **entry V 1 0 < entry V 1 1** '
          f'{pc(c["★ (ADJ-e) entry V 1 0 < entry V 1 1"], dn)}  ⛔ 破れ {c["⛔ (ADJ-e) 破れ"]}')
    b = c['⛔ (ADJ-e) 破れ']
    print(f'      行 1 が等しい {pc(c["   うち 行 1 が等しい"], b)}   '
          f'行 1 が減る {pc(c["   うち 行 1 が減る"], b)}')
    print(f'  (ADJ-f) 破れ {b}: (0)窓 {pc(c["(ADJ-f) (0)窓で孤児"], b)}  '
          f'**(ii)塔+ブロック** {pc(c["★ (ADJ-f) (ii)塔+ブロックで孤児"], b)}  '
          f'⛔ 親がいる {c["⛔ (ADJ-f) (ii)で親がいる"]}')
    for k in sorted(c):
        if k.startswith('   ⛔ 親の位置'): print(f'      {k}: {c[k]}')
    print(f'  ★ (ADJ-e) 破れの先頭 2 列（正規化、{len(sh)} 種）:')
    for s, m in sh.most_common(8):
        print(f'      {m:7d}  {list(s)}')
    for nm in ('A_ok', 'A_bad'):
        print(f'  ★★ (W15) **{nm}** 分母 {c[f"(W15) {nm} 分母"]}  '
              f'⛔ **接頭辞が親を供給** '
              f'{pc(c[f"⛔ (W15) {nm} が親を供給"], c[f"(W15) {nm} 分母"])}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2), '|R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2), '★ |R|=4 行1<3')
