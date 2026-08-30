# -*- coding: utf-8 -*-
"""**(H2P-D) / (H2P-OPER) / (H2P-WND)。**

    **(H2P)(X) :⟺ `∀ t, 0 < t < |X|, 0 < entry X 2 t → ∃ y, nextrel1 X y t`**
      ＝ **「行 2 が正の列には、行 1 の親がある」**（L3 §258 `hasParent2_of_row1_parents` の前提）
    **`R1<=R0(X) :⟺ ∀ i, entry X 1 i <= entry X 0 i`**
    **正規化 `norm(X)` ＝ 行 0 から `entry X 0 0` を引く**

## ⚠ 母集団（1 行ずつ）

    ★ シート … `psiI.json` の DBMS 列 1,637 行列
    ⛔ 一様な箱 … `Lift1 ((0,v,z)::R) t` の `dropLast`
    ★ 窓 …… `oper` の親分割 `V = S[p:last]`
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from trio import expand, diag
from collections import Counter
from r126 import srow
from r263 import load
from r267 import boxQ
from r269 import R1R0, norm

H2P = lambda X: all(trio.parent(X[:t + 1], 1, t) is not None
                    for t in range(1, len(X)) if X[t][2] > 0)


def part_D():
    print('## ★★★ (H2P-D) 中核 `D_v` で真か（L3 が騙されかけた箇所）')
    for v in range(1, 8):
        D = [tuple(x) for x in diag(3, v, 1)]
        bad = [t for t in range(1, len(D))
               if D[t][2] > 0 and trio.parent(D[:t + 1], 1, t) is None]
        print(f'   D_{v} = {D}')
        print(f'       (H2P)={"★真" if H2P(D) else "⛔偽"}   '
              f'R1<=R0={"★真" if R1R0(D) else "⛔偽"}   '
              f'正規化後 R1<=R0={"★真" if R1R0(norm(D)) else "⛔偽"}'
              + (f'   ⛔ 破れる列 {bad}' if bad else ''))
    print()


def gate1(Ms, NS, tag):
    c = Counter(); ex = []; t0 = time.time()
    for M in Ms:
        X = [tuple(v) for v in M]
        if len(X) < 2 or not H2P(X): continue
        for n in NS:
            Y = [tuple(v) for v in expand([list(v) for v in X], n)]
            if len(Y) < 2: continue
            c['★ 分母（(H2P) が真な M）'] += 1
            if H2P(Y): c['★★ (門1) oper でも真'] += 1
            else:
                c['⛔ **(門1) oper で壊れる**'] += 1
                if len(ex) < 4 and len(X) <= 7: ex.append((X, n, Y))
    d = c['★ 分母（(H2P) が真な M）']
    print(f'### (H2P-OPER) 門 1  {tag}  [{time.time()-t0:.1f}s]')
    print(f'    ★ 分母 {d}   ★★ **oper でも真** {c["★★ (門1) oper でも真"]} '
          f'({100*c["★★ (門1) oper でも真"]/max(d,1):8.4f}%)   '
          f'⛔ **壊れる** {c["⛔ **(門1) oper で壊れる**"]} '
          f'({100*c["⛔ **(門1) oper で壊れる**"]/max(d,1):8.4f}%)')
    for x in ex: print(f'        ⛔ M={x[0]} n={x[1]} ⟹ oper = {x[2]}')
    print()


def gate2(Ms, NS, tag):
    c = Counter(); ex = []; t0 = time.time()
    for M in Ms:
        S0 = [tuple(v) for v in M]
        if len(S0) < 2: continue
        for n in NS:
            S = [tuple(v) for v in expand([list(v) for v in S0], n)]
            if len(S) < 3 or not H2P(S): continue
            lastx = len(S) - 1
            p = trio.parent(S, srow(S, lastx), lastx)
            if p is None or lastx - p < 2: continue
            V = S[p:lastx]
            c['★ 分母（S が (H2P)）'] += 1
            if H2P(V): c['★ (門2) 窓も真（正規化なし）'] += 1
            else:
                c['⛔ **(門2) 窓で壊れる（正規化なし）**'] += 1
                if len(ex) < 3: ex.append((S0, n, p, V))
            if H2P(norm(V)): c['★ (門2) 窓も真（正規化あり）'] += 1
            else:            c['⛔ (門2) 正規化ありで壊れる'] += 1
    def pc(x, y): return f'{x} ({100*x/max(y,1):8.4f}%)'
    d = c['★ 分母（S が (H2P)）']
    print(f'### (H2P-WND) 門 2  {tag}  [{time.time()-t0:.1f}s]  ★ 分母 {d}')
    print(f'    ★ **正規化なし**で窓も真 {pc(c["★ (門2) 窓も真（正規化なし）"], d)}   '
          f'⛔ 壊れる {c["⛔ **(門2) 窓で壊れる（正規化なし）**"]}')
    print(f'    ★ **正規化あり**で窓も真 {pc(c["★ (門2) 窓も真（正規化あり）"], d)}   '
          f'⛔ 壊れる {c["⛔ (門2) 正規化ありで壊れる"]}')
    for x in ex: print(f'        ⛔ M={x[0]} n={x[1]} p={x[2]} V={x[3]}')
    print()


if __name__ == '__main__':
    part_D()
    S = [list(m) for m in load()]
    B = [Q for Q, d, e in boxQ(4, 3, (0, 1, 2), (0, 1), (0, 1, 2))]
    gate1(S, (1, 2, 3), '★ シート由来 M')
    gate1(B, (1, 2, 3), '⛔ 一様な箱 M')
    gate2(S, (1, 2, 3), '★ シート由来 M')
    gate2(B, (1, 2), '⛔ 一様な箱 M')
