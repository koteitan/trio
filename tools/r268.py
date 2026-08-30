# -*- coding: utf-8 -*-
"""**(RSUM3a/b/c/d) ＋ H12 の検算 ＋ (GAP-2)。**

## ⚠ 母集団を 1 行で —— **組み立ての形**

`oper` が実際に作る形をそのまま使う:

    `M` の最終列 `x`、`t = srow M x`、`r = parent M t x`（バッドルート）
    ⟹ **`A = M[:r]`（接頭辞）**、**`T = (oper M n)[r:]`（塔＝悪い部分の n 個のコピー）**
    ⟹ ★ `A ++ T = oper M n` ⟹ **これが `towerClosed_of_hered` の `(A, T)` そのもの**です。

    ★ **正規化あり** ＝ シート由来 `M`（根が `(0,0,0)`）
    ⛔ **正規化なし** ＝ 一様な箱の `M`（根の行 1 が正でもよい）

## 測るもの

    (a) `rsum` の破れ … `A` に `entry A 0 y < entry T 0 0` の列があるか
    (b) `rsum1` の破れ … `A` に `entry A 1 y < entry T 1 0` の列があるか
    (c) **`entry T 1 0 = 0`** か（いちばん単純な鍵）
    (d) 3 条件の相関
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from trio import expand
from collections import Counter
from r126 import srow
from r263 import load, hloc_col
from r267 import boxQ


def split(M, n):
    x = len(M) - 1
    t = srow(M, x)
    r = trio.parent(M, t, x)
    if r is None: return None
    E = [tuple(v) for v in expand([list(v) for v in M], n)]
    if len(E) <= r: return None
    return [tuple(v) for v in M[:r]], E[r:]


def scan(Ms, NS, tag):
    c = Counter(); ex = []; t0 = time.time()
    for M in Ms:
        if len(M) < 3: continue
        for n in NS:
            s = split([tuple(v) for v in M], n)
            if s is None: continue
            A, T = s
            if not T: continue
            c['★ 分母（組み立ての (A,T) の組）'] += 1
            a = any(y[0] < T[0][0] for y in A)          # rsum の破れ
            b = any(y[1] < T[0][1] for y in A)          # rsum1 の破れ
            cc = (T[0][1] == 0)                          # entry T 1 0 = 0
            if a: c['⛔ (a) `rsum` が破れる'] += 1
            if b: c['⛔ (b) `rsum1` が破れる'] += 1
            if cc: c['★★ (c) **entry T 1 0 = 0**'] += 1
            c[f'   (d) (a,b,c)=({int(a)},{int(b)},{int(cc)})'] += 1
            if cc and b: 
                if len(ex) < 3: ex.append(('c真かつb破れ', M, n, A, T))
    def pc(x, y): return f'{x} ({100*x/max(y,1):8.4f}%)'
    d = c['★ 分母（組み立ての (A,T) の組）']
    print(f'### {tag}  [{time.time()-t0:.1f}s]  ★ **分母 {d}**')
    print(f'    ⛔ (a) `rsum` の破れ  {pc(c["⛔ (a) `rsum` が破れる"], d)}')
    print(f'    ⛔ (b) `rsum1` の破れ {pc(c["⛔ (b) `rsum1` が破れる"], d)}')
    print(f'    ★★ (c) **entry T 1 0 = 0** {pc(c["★★ (c) **entry T 1 0 = 0**"], d)}')
    print('    (d) 相関 (a,b,c):')
    for k in sorted(c):
        if k.startswith('   (d)'): print(f'        {k[6:]}: {pc(c[k], d)}')
    for x in ex: print(f'        ⛔ {x[0]}: M={x[1]} n={x[2]} A={x[3]} T={x[4][:3]}...')
    print()


def h12_check():
    """H12 の予測: シートの窓の孤児 353 件で、接頭辞に「窓の根より行 1 が下の列」があるはず。"""
    c = Counter(); ex = []
    for M in load():
        for j in range(2, len(M)):
            B = [tuple(v) for v in M[:j + 1]]
            s = srow(B, j)
            if s == 0: continue
            p = trio.parent(B, s, j)
            if p is None or j - p < 2: continue
            V = [tuple(v) for v in B[p:j]]
            for t in range(1, len(V)):
                if hloc_col(V, t): continue
                c['★ 分母（窓の孤児）'] += 1
                if any(B[y][1] < V[0][1] for y in range(p)):
                    c['★★ 接頭辞に「根より行 1 が下」の列がある'] += 1
                else:
                    c['⛔ **無い（H12 の予測が外れ）**'] += 1
                    if len(ex) < 3: ex.append((B, p, V, t))
                if any(B[y][0] < V[0][0] for y in range(p)):
                    c['   （参考）接頭辞に「根より行 0 が浅い」列がある'] += 1
    d = c['★ 分母（窓の孤児）']
    print(f'### H12 の検算（シートの窓の孤児）  ★ **分母 {d}**')
    print(f'    ★★ **接頭辞に「根より行 1 が下」の列がある** '
          f'{c["★★ 接頭辞に「根より行 1 が下」の列がある"]} '
          f'({100*c["★★ 接頭辞に「根より行 1 が下」の列がある"]/max(d,1):8.4f}%)   '
          f'⛔ 無い {c["⛔ **無い（H12 の予測が外れ）**"]}')
    print(f'    （参考）接頭辞に「根より行 0 が浅い」列 '
          f'{c["   （参考）接頭辞に「根より行 0 が浅い」列がある"]} '
          f'({100*c["   （参考）接頭辞に「根より行 0 が浅い」列がある"]/max(d,1):8.4f}%)')
    for x in ex: print(f'        ⛔ B={x[0]} p={x[1]} V={x[2]} t={x[3]}')
    print()


if __name__ == '__main__':
    h12_check()
    scan(load(), (1, 2, 3), '★ 正規化あり（シート由来 M、n∈{1,2,3}）')
    scan([Q for Q, d, e in boxQ(4, 3, (0, 1, 2), (0, 1), (0, 1, 2))], (1, 2),
         '⛔ 正規化なし（一様な箱の M、n∈{1,2}）')
