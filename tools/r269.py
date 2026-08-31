# -*- coding: utf-8 -*-
"""**(R1R0-OPER)（門 1）／ (ROOT1) ／ (R1R0-WND)（門 2）。**

    **`R1<=R0(X) :⟺ ∀ i, entry X 1 i <= entry X 0 i`**
    **正規化 `norm(X)` ＝ 行 0 から `entry X 0 0` を引く**（`shiftl0`。**行 1 は動きません**）

## ⚠ 母集団（1 行ずつ）

    ★ シート … `psiI.json` の DBMS 列 1,637 行列（と、その全接頭辞）
    ⛔ 一様な箱 … `Lift1 ((0,v,z)::R) t` の `dropLast`（`R` 一様、`d>0`, `hr0`, `hz0`）
    ★ 窓 …… `oper` の親分割 `V = S[p:last]`（`S` は上の各母集団から作る）
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from trio import expand
from collections import Counter
from r126 import srow
from r263 import load
from r267 import boxQ

R1R0 = lambda X: all(x[1] <= x[0] for x in X)
norm = lambda X: [(a - X[0][0], b, c) for a, b, c in X]


def gate1(Ms, NS, tag):
    """門 1: `R1<=R0(M)` ⟹ `R1<=R0(oper M n)` か。"""
    c = Counter(); ex = []; t0 = time.time()
    for M in Ms:
        X = [tuple(v) for v in M]
        if len(X) < 2 or not R1R0(X): continue
        for n in NS:
            Y = [tuple(v) for v in expand([list(v) for v in X], n)]
            if len(Y) < 2: continue
            c['★ 分母（R1<=R0 が真な M）'] += 1
            if R1R0(Y): c['★★ (門1) oper でも真'] += 1
            else:
                c['⛔ **(門1) oper で壊れる**'] += 1
                if len(ex) < 4 and len(X) <= 6: ex.append((X, n, Y))
    d = c['★ 分母（R1<=R0 が真な M）']
    print(f'### (R1R0-OPER) 門 1  {tag}  [{time.time()-t0:.1f}s]')
    print(f'    ★ 分母 {d}   ★★ **oper でも真** {c["★★ (門1) oper でも真"]} '
          f'({100*c["★★ (門1) oper でも真"]/max(d,1):8.4f}%)   '
          f'⛔ **壊れる** {c["⛔ **(門1) oper で壊れる**"]} '
          f'({100*c["⛔ **(門1) oper で壊れる**"]/max(d,1):8.4f}%)')
    for x in ex: print(f'        ⛔ M={x[0]} n={x[1]} ⟹ oper = {x[2]}')
    print()


def root1_and_gate2(Ms, NS, tag):
    """(ROOT1) 根の行 1 = 0 の率、(R1R0-WND) 門 2。"""
    c = Counter(); ex = []; t0 = time.time()
    for M in Ms:
        S0 = [tuple(v) for v in M]
        if len(S0) < 2: continue
        # ---------- 接頭辞としての Q ----------
        for k in range(2, len(S0) + 1):
            Q = S0[:k]
            c['(ROOT1) 接頭辞 分母'] += 1
            if Q[0][1] == 0: c['★ (ROOT1) 接頭辞 根の行1=0'] += 1
            if R1R0(Q): c['   接頭辞 R1<=R0'] += 1
            if R1R0(norm(Q)): c['   接頭辞 R1<=R0（正規化後）'] += 1
        # ---------- 窓としての Q ----------
        for n in NS:
            S = [tuple(v) for v in expand([list(v) for v in S0], n)]
            if len(S) < 3: continue
            lastx = len(S) - 1
            p = trio.parent(S, srow(S, lastx), lastx)
            if p is None or lastx - p < 2: continue
            V = S[p:lastx]
            c['★★ (ROOT1) 窓 分母'] += 1
            if V[0][1] == 0: c['★ (ROOT1) 窓 根の行1=0'] += 1
            else:
                c['⛔ **(ROOT1) 窓 根の行1>0**'] += 1
                if V[0][1] != 0 and len(ex) < 3: ex.append(('ROOT1', S0, n, p, V))
            if V[0][1] == 0 and norm(V)[0][1] == 0: c['   （正規化しても同じ）'] += 1
            # ---------- (R1R0-WND) 門 2 ----------
            if R1R0(S):
                c['(門2) 分母（S が R1<=R0）'] += 1
                if R1R0(V): c['★ (門2) 窓も R1<=R0（正規化なし）'] += 1
                else:       c['⛔ (門2) 窓で壊れる（正規化なし）'] += 1
                if R1R0(norm(V)): c['★ (門2) 窓も R1<=R0（正規化あり）'] += 1
                else:             c['⛔ **(門2) 正規化すると壊れる**'] += 1
    def pc(x, y): return f'{x} ({100*x/max(y,1):8.4f}%)'
    d1 = c['(ROOT1) 接頭辞 分母']; d2 = c['★★ (ROOT1) 窓 分母']; d3 = c['(門2) 分母（S が R1<=R0）']
    print(f'### (ROOT1)/(R1R0-WND)  {tag}  [{time.time()-t0:.1f}s]')
    print(f'    ★ (ROOT1) **接頭辞** 分母 {d1}  根の行1=0 '
          f'{pc(c["★ (ROOT1) 接頭辞 根の行1=0"], d1)}   '
          f'R1<=R0 {pc(c["   接頭辞 R1<=R0"], d1)}  '
          f'（正規化後）{pc(c["   接頭辞 R1<=R0（正規化後）"], d1)}')
    print(f'    ★★ (ROOT1) **窓** 分母 {d2}  ★ 根の行1=0 '
          f'{pc(c["★ (ROOT1) 窓 根の行1=0"], d2)}   ⛔ **根の行1>0** '
          f'{pc(c["⛔ **(ROOT1) 窓 根の行1>0**"], d2)}')
    print(f'    ★ (門2) 分母 {d3}  正規化なしで窓も真 '
          f'{pc(c["★ (門2) 窓も R1<=R0（正規化なし）"], d3)}   '
          f'⛔ **正規化ありで真** {pc(c["★ (門2) 窓も R1<=R0（正規化あり）"], d3)}')
    for x in ex: print(f'        ⛔ 窓の根の行1>0: M={x[1]} n={x[2]} p={x[3]} V={x[4]}')
    print()


if __name__ == '__main__':
    S = [list(m) for m in load()]
    B = [Q for Q, d, e in boxQ(4, 3, (0, 1, 2), (0, 1), (0, 1, 2))]
    gate1(S, (1, 2, 3), '★ シート由来 M')
    gate1(B, (1, 2, 3), '⛔ 一様な箱 M')
    root1_and_gate2(S, (1, 2, 3), '★ シート由来 M')
    root1_and_gate2(B, (1, 2), '⛔ 一様な箱 M')
