# -*- coding: utf-8 -*-
"""**(DE-MEAS)(DE-MEAS2) —— `d`・`e` は減るか、辞書式は減るか。**

## ⚠ 母集団を 1 行で

**シートの全 `drop/take`（k<=8）から `|X| >= 3` を取った標本**（`amin != 0` が 81.11% の箱）を
`oper(·,n)`（`n<=3`）で 4 手たどる。**手の分類**は `r' < r` ⟹ ⛔ 接頭辞に逃げる手。
⚠ **`hr0`（根が全列より行 0 が小）の有無も記録**します（H12 の注意）。

## `d` / `e` の定義（`Trio.lean:106-114` 逐語）

    `x = |M|-1`、`i1 = srow M x`、`r = parent M i1 x`
    **`d = if 0 < i1 then entry M 0 x - entry M 0 r else 0`**
    **`e = if 1 < i1 then entry M 1 x - entry M 1 r else 0`**
    **`|V| = x - r`**（悪い部分の長さ）
"""
import sys, time, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from trio import expand
from collections import Counter
from r126 import srow
from r263 import load
from r272 import subwins
from r273 import anc0chain

rng = random.Random(20260830)


def de(M):
    x = len(M) - 1
    i1 = srow(M, x)
    r = trio.parent(M, i1, x)
    if r is None: return None
    d = (M[x][0] - M[r][0]) if i1 > 0 else 0
    e = (M[x][1] - M[r][1]) if i1 > 1 else 0
    am = [min(M[y][1] for y in anc0chain(M, j)) for j in range(len(M))]
    return {'r': r, 'd': d, 'e': e, 'V': x - r,
            'nd': len(set(am)), 'wd': max(am) - min(am), 'L': len(M),
            'hr0': all(M[0][0] < M[l][0] for l in range(1, len(M)))}


def cmp3(a, b):
    return '減' if b < a else ('同' if b == a else '増')


def run(S, NS, DEPTH, tag):
    c = Counter(); ex = []; t0 = time.time()
    LEX = {
        '(d, e, |V|)': lambda f: (f['d'], f['e'], f['V']),
        '(d, e, |M|)': lambda f: (f['d'], f['e'], f['L']),
        '(nd, d, e, |V|)': lambda f: (f['nd'], f['d'], f['e'], f['V']),
        '(wd, d, e, |V|)': lambda f: (f['wd'], f['d'], f['e'], f['V']),
        '(nd, |V|)': lambda f: (f['nd'], f['V']),
        '(e, d, |V|)': lambda f: (f['e'], f['d'], f['V']),
    }
    for X0 in S:
        for n in NS:
            X = [tuple(v) for v in X0]; f = de(X)
            if f is None: continue
            for _ in range(DEPTH):
                Y = [tuple(v) for v in expand([list(v) for v in X], n)]
                if len(Y) < 2: break
                g = de(Y)
                if g is None: break
                grp = '⛔ 接頭辞に逃げる手' if g['r'] < f['r'] else '★ ブロックの中の手'
                c[f'{grp} 分母'] += 1
                c[f'{grp} hr0'] += 1 if f['hr0'] else 0
                for k in ('d', 'e', 'V', 'nd', 'wd'):
                    c[f'{grp}|{k}|{cmp3(f[k], g[k])}'] += 1
                for nm, key in LEX.items():
                    c[f'{grp}|LEX {nm}|{cmp3(key(f), key(g))}'] += 1
                if grp.startswith('⛔') and g['d'] > f['d'] and len(ex) < 3:
                    ex.append((X, n, f, g))
                X, f = Y, g
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for grp in ('⛔ 接頭辞に逃げる手', '★ ブロックの中の手'):
        d = c[f'{grp} 分母']
        print(f'  **{grp}**: 分母 {d}（うち `hr0` {c[f"{grp} hr0"]} '
              f'= {100*c[f"{grp} hr0"]/max(d,1):.2f}%）')
        for k in ('d', 'e', 'V', 'nd', 'wd'):
            dec, sm, inc = (c[f'{grp}|{k}|減'], c[f'{grp}|{k}|同'], c[f'{grp}|{k}|増'])
            m = ' ★★ **非増加**' if inc == 0 else ''
            print(f'      {k:16s} 減 {100*dec/max(d,1):7.3f}%  同 {100*sm/max(d,1):7.3f}%  '
                  f'増 {100*inc/max(d,1):7.3f}%{m}')
        for nm in LEX:
            dec, sm, inc = (c[f'{grp}|LEX {nm}|減'], c[f'{grp}|LEX {nm}|同'],
                            c[f'{grp}|LEX {nm}|増'])
            m = ' ★★★ **非増加**' if inc == 0 else ''
            print(f'      LEX {nm:18s} 減 {100*dec/max(d,1):7.3f}%  '
                  f'同 {100*sm/max(d,1):7.3f}%  増 {100*inc/max(d,1):7.3f}%{m}')
    for x in ex:
        print(f'      ⛔ 接頭辞の手で d が増える例: X={x[0]} n={x[1]} '
              f'd:{x[2]["d"]}→{x[3]["d"]} e:{x[2]["e"]}→{x[3]["e"]} '
              f'|V|:{x[2]["V"]}→{x[3]["V"]}')
    print()


if __name__ == '__main__':
    Ms = [list(m) for m in load()]
    SW = [list(x) for x in subwins(Ms, 8) if len(x) >= 3]
    S = SW if len(SW) <= 4000 else rng.sample(SW, 4000)
    run(S, (1, 2, 3), 4, f'★ シートの drop/take（標本 {len(S)}）, n<=3, 4 手')
    run([list(m) for m in Ms], (1, 2, 3), 4, '⛔ シート行列そのもの（対照）')
