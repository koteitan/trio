# -*- coding: utf-8 -*-
"""**(ROW2POS) —— 窓の `row2pos` は `oper` の手で減るか。**

## ⚠ 母集団を 1 行で（(DE-MEAS) と同じ）

シートの全 `drop/take`（`k<=8`）から `|X| >= 3` を取った標本を `oper(·,n)`（`n<=3`）で 4 手。
**手の分類**は `r' < r` ⟹ ⛔ 接頭辞に逃げる手。

## ⚠ 主語（大事）

    `x = |X|-1`、`i1 = srow X x`、`r = parent X i1 x`
    **窓 `V = X[r:x]`**（L3 の `wnd P B j p = B[p:j]` の逐語 ＝ **末尾列を含まない**）
    **`row2pos(Y) = #{ j : entry Y 2 j > 0 }`**

    (a) **窓の `row2pos`**: `row2pos(V)` → `row2pos(V')`   ← ★ **H12 の主張**
    (b) **全体の `row2pos`**: `row2pos(X)` → `row2pos(oper X n)` ← ⚠ **「塔で n 倍」の懸念**
"""
import sys, time, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from trio import expand
from collections import Counter
from r126 import srow
from r263 import load
from r272 import subwins

rng = random.Random(20260830)
r2p = lambda Y: sum(1 for q in Y if q[2] > 0)


def wnd(X):
    x = len(X) - 1
    i1 = srow(X, x)
    r = trio.parent(X, i1, x)
    if r is None: return None
    return r, i1, [tuple(v) for v in X[r:x]]


def run(S, NS, DEPTH, tag):
    c = Counter(); ex = []; t0 = time.time()
    for X0 in S:
        for n in NS:
            X = [tuple(v) for v in X0]
            w = wnd(X)
            if w is None: continue
            r, i1, V = w
            for _ in range(DEPTH):
                Y = [tuple(v) for v in expand([list(v) for v in X], n)]
                if len(Y) < 2: break
                w2 = wnd(Y)
                if w2 is None: break
                r2, i2, V2 = w2
                grp = '⛔ 接頭辞に逃げる手' if r2 < r else '★ ブロックの中の手'
                for lab, a, b in (('(a) 窓の row2pos', r2p(V), r2p(V2)),
                                  ('(b) 全体の row2pos', r2p(X), r2p(Y))):
                    c[f'{grp}|{lab}|分母'] += 1
                    k = '減' if b < a else ('同' if b == a else '増')
                    c[f'{grp}|{lab}|{k}'] += 1
                    if lab.startswith('(a)') and k == '増' and len(ex) < 4:
                        ex.append((X, n, V, V2, a, b, grp))
                # ---------- srow(末尾) = 2 の手だけ ----------
                if i1 == 2:
                    a, b = r2p(V), r2p(V2)
                    c['★ srow=2 の手 分母'] += 1
                    c['★ srow=2 の手|' + ('減' if b < a else
                                          ('同' if b == a else '増'))] += 1
                    c[f'   srow=2 かつ {grp}|' + ('減' if b < a else
                                                  ('同' if b == a else '増'))] += 1
                X, r, i1, V = Y, r2, i2, V2
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for grp in ('⛔ 接頭辞に逃げる手', '★ ブロックの中の手'):
        for lab in ('(a) 窓の row2pos', '(b) 全体の row2pos'):
            d = c[f'{grp}|{lab}|分母']
            dec, sm, inc = (c[f'{grp}|{lab}|減'], c[f'{grp}|{lab}|同'],
                            c[f'{grp}|{lab}|増'])
            m = ' ★★★ **非増加**' if inc == 0 else ''
            print(f'  {grp} {lab:20s} 分母 {d:7d}  減 {100*dec/max(d,1):7.3f}%  '
                  f'同 {100*sm/max(d,1):7.3f}%  増 {100*inc/max(d,1):7.3f}%{m}')
    d = c['★ srow=2 の手 分母']
    print(f'  ★★ **srow(末尾) = 2 の手だけ**（窓の row2pos）分母 {d}  '
          f'減 {100*c["★ srow=2 の手|減"]/max(d,1):7.3f}%  '
          f'同 {100*c["★ srow=2 の手|同"]/max(d,1):7.3f}%  '
          f'増 {100*c["★ srow=2 の手|増"]/max(d,1):7.3f}%')
    for k in sorted(c):
        if k.startswith('   srow=2'): print(f'      {k}: {c[k]}')
    for x in ex:
        print(f'      ⛔ 窓の row2pos が増える例（{x[6]}）: X={x[0]} n={x[1]}')
        print(f'          V={x[2]}（{x[4]}）⟹ V\'={x[3]}（{x[5]}）')
    print()


if __name__ == '__main__':
    Ms = [list(m) for m in load()]
    SW = [list(x) for x in subwins(Ms, 8) if len(x) >= 3]
    S = SW if len(SW) <= 4000 else rng.sample(SW, 4000)
    run(S, (1, 2, 3), 4, f'★ シートの drop/take（標本 {len(S)}）, n<=3, 4 手')
    run([list(m) for m in Ms], (1, 2, 3), 4, '⛔ シート行列そのもの（対照）')
