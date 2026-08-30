# -*- coding: utf-8 -*-
"""(z3) の 0% を壊しにいく（教訓 21）。

r201: 深さ 1 で 0.1386 / 0.2887%、深さ 2 で 0.0202 / 0.0130%、**深さ 3,4 で 0.0000%**。
⚠ **ビーム（300）で間引いているので、深さ 3+ の 0% は副作用かもしれない。**

**やること**: 深さ 1・2 で **`h2cone(V)` が破れた `V` だけ**を集め、
**そこからビームなしで**深く降りて、破れが続くか見る。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r169 import domT
from r171 import step_det
from r195 import h2cone
from r201 import dOf, eOf


def run(L, R1, VS, ZS, TS, NS, maxdep):
    COL = [(a, b, c) for a in range(1, 4) for b in range(R1) for c in (0, 1)]
    c = Counter(); bad = set(); t0 = time.time()
    # --- 段階 1: 深さ 1・2 の破れを全部集める（ビームなし、重複除去）---
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt); jR = len(R) - 1
        if srow(R, jR) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q = M[:-1]
                    if len(Q) < 2: continue
                    st = {(tuple(Q), dOf(M), eOf(M))}
                    for dep in (1, 2):
                        nxt = set()
                        for (X, dd, ee) in st:
                            for n in NS:
                                for j in range(len(X)):
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    k = (tuple(r[0]), r[1], r[2])
                                    nxt.add(k)
                                    if h2cone(list(r[0])):
                                        bad.add(k); c[('破れ 深さ', dep)] += 1
                        st = nxt
    print(f'### |R|={L} 行1<{R1}  深さ 1・2 の破れ（重複除去後） {len(bad)} 状態  '
          f'[{time.time()-t0:.1f}s]')
    print('    破れの延べ数: ', dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple))))
    # --- 段階 2: 破れた状態から**ビームなしで**深く降りる ---
    front = set(bad); d2 = Counter()
    for dep in range(1, maxdep + 1):
        nxt = set()
        for (X, dd, ee) in front:
            for n in NS:
                for j in range(len(X)):
                    r = step_det(list(X), dd, ee, n, j)
                    if r is None or len(r[0]) < 2: continue
                    k = (tuple(r[0]), r[1], r[2])
                    nxt.add(k); d2[(dep, '段')] += 1
                    if h2cone(list(r[0])): d2[(dep, '⚠ 破れ')] += 1
        if not nxt:
            print(f'    さらに {dep} 段目: 手が無い（打ち切り）'); break
        front = nxt
        s = d2[(dep, '段')]
        print(f'    ★ 破れた状態からさらに {dep} 段: 段 {s:8d} '
              f'状態 {len(front):7d}  **⚠ 破れ {d2[(dep,"⚠ 破れ")]:7d} '
              f'({100*d2[(dep,"⚠ 破れ")]/max(s,1):7.4f}%)**')
        if len(front) > 20000:
            print('       （状態が多すぎるので打ち切り）'); break
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 6)
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3,4), 6)
