# -*- coding: utf-8 -*-
"""**(CAP-2) —— `CoreCap` の箱に、今日の教訓を当てて測り直す。**

## ★ まず定義の確認（`Lind.lean:176` 逐語）

    CoreCap := ∀ M, **argOK M** → 1 <= |M| → ∀ v z, z <= 1 → CtxOK M v z →
      ∀ b c a t, 2*(v+t)+z <= a → Lift1 ((0,v,z) :: cap M b c) t ∈ W a

    `argOK R := ∀ p ∈ R, 0 < p.1`（`Wset.lean:1314`）
    ⟹ ★★★ **＝「M の全列の行 0 が正」＝「根 `(0,v,z)` より浅い列が無い」＝ `rsum` そのもの**

⟹ ★ ですから **「正規化」は箱の産物ではなく、定理の文と前提そのもの**です。
⟹ ⚠ ただし **§R89-3 の I3 で「`argOK` は木の下で 5.6% 破れる」**と私自身が測っています。
   ⟹ ★★ ですから **今日の `rsum` の罠は、`CoreCap` の再帰にも同じ形である**はずです。

## 測るもの（`argOK` の有無で分ける ＝ 今日の「正規化を外す」に相当）

    I1 先頭列が入口の根 `(0, v+t, z)` のまま
    I2 先頭列の `lev`（= 2*行1 + 行2）が段 `a` のまま
    I3 尾が `argOK`
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from trio import expand
from collections import Counter
from r113 import Lift1

lev = lambda c: 2 * c[1] + c[2]
argOK = lambda R: all(p[0] > 0 for p in R)
cap = lambda M, b, c: [tuple(x) for x in M[:-1]] + [(M[-1][0], b, c)] if M else []


def descend(X, depth, NS, maxlen, c, tag, root):
    """`oper` の木を降りて I1 / I2 / I3 を確かめる。"""
    seen = set(); frontier = [tuple(X)]
    for _ in range(depth):
        nxt = []
        for S in frontier:
            if S in seen or not S or len(S) > maxlen: continue
            seen.add(S)
            c[f'[{tag}] 訪問'] += 1
            if S[0] == root: c[f'[{tag}] ★ I1 先頭列が根のまま'] += 1
            else:            c[f'[{tag}] ⛔ **I1 破れ**'] += 1
            if lev(S[0]) == lev(root): c[f'[{tag}] ★ I2 lev が段のまま'] += 1
            else:                      c[f'[{tag}] ⛔ **I2 破れ**'] += 1
            if argOK(S[1:]): c[f'[{tag}] ★ I3 尾が argOK'] += 1
            else:            c[f'[{tag}] ⛔ I3 破れ'] += 1
            for n in NS:
                T = tuple(tuple(v) for v in expand([list(v) for v in S], n))
                if T and T not in seen: nxt.append(T)
        frontier = nxt


def run(LM, VS, ZS, TS, BS, CS, depth, NS, maxlen, tag):
    c = Counter(); t0 = time.time()
    COL = [(a, b, cc) for a in range(0, 3) for b in range(3) for cc in (0, 1)]
    for Mt in itertools.product(COL, repeat=LM):
        M = list(Mt)
        ok = argOK(M)
        g = '★argOK' if ok else '⛔argOKなし'
        for v in VS:
            for z in ZS:
                for b in BS:
                    for cc in CS:
                        for t in TS:
                            X = [tuple(x) for x in
                                 Lift1([(0, v, z)] + cap(M, b, cc), t)]
                            descend(X, depth, NS, maxlen, c, g,
                                    (0, v + t, z))
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for g in ('★argOK', '⛔argOKなし'):
        d = c[f'[{g}] 訪問']
        if not d: continue
        def pc(x): return f'{x} ({100*x/max(d,1):8.4f}%)'
        print(f'  **{g}**: 訪問 {d}')
        print(f'      I1 根のまま {pc(c[f"[{g}] ★ I1 先頭列が根のまま"])}   '
              f'⛔ **破れ** {c[f"[{g}] ⛔ **I1 破れ**"]}')
        print(f'      I2 lev が段のまま {pc(c[f"[{g}] ★ I2 lev が段のまま"])}   '
              f'⛔ **破れ** {c[f"[{g}] ⛔ **I2 破れ**"]}')
        print(f'      I3 尾が argOK {pc(c[f"[{g}] ★ I3 尾が argOK"])}   '
              f'⛔ 破れ {c[f"[{g}] ⛔ I3 破れ"]}')
    print()


if __name__ == '__main__':
    run(2, (0, 1), (0, 1), (0, 1), (0, 1, 2), (0, 1), 6, (1, 2, 3), 26,
        '★ |M|=2, v,z,t<=1, b<=2, c<=1, depth=6, n<=3')
    run(3, (0, 1), (0, 1), (0, 1), (0, 2), (0, 1), 5, (1, 2), 26,
        '★★ |M|=3（箱を伸ばす）, depth=5, n<=2')
