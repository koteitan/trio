# -*- coding: utf-8 -*-
"""**(MEAS) —— `oper` を 1 手進めるたびに何が減るか。**

## ⚠ 母集団を 1 行で

`psiI.json` の DBMS 列 1,637 行列（ground truth）から出発し、`oper(·, n)`（`n ∈ NS`）を
`DEPTH` 手たどる。**各手について候補量を進行前後で記録**する。

## ⚠ 手の分類（L3 の `hbound` に対応）

各手で `r = parent M (srow M x) x`（バッドルートの番地）。次の手の `r'` について

    **`r' >= r`** ⟹ ★ **バッドルートが最後のブロックの中**（`hbound` が立つ手）
    **`r' <  r`** ⟹ ⛔ **接頭辞に逃げる手**（`hbound` が破れる手）← **ここで減る量を探す**

## 候補量

    (1) r（バッドルートの絶対位置）  (2) lev（末尾）  (3) |M|
    (4) 悪い部分の長さ |M|-1-r      (5) 良い部分の長さ r+1
    (6) 行0の最大 / 行1の最大 / 行2>0 の列数   (7) srow=2 の列数
    (8) amin の最大 / 最小          (9) n（ブロック数）
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from trio import expand
from collections import Counter
from r126 import srow
from r263 import load
from r273 import anc0chain


def feats(M):
    x = len(M) - 1
    r = trio.parent(M, srow(M, x), x)
    rr = -1 if r is None else r
    am = [min(M[y][1] for y in anc0chain(M, j)) for j in range(len(M))]
    return {
        '(1) バッドルートの位置 r': rr,
        '(2) lev(末尾)': 2 * M[x][1] + M[x][2],
        '(3) |M|': len(M),
        '(4) 悪い部分の長さ': x - rr,
        '(5) 良い部分の長さ': rr + 1,
        '(6a) 行 0 の最大': max(c[0] for c in M),
        '(6b) 行 1 の最大': max(c[1] for c in M),
        '(6c) 行 2 > 0 の列数': sum(1 for c in M if c[2] > 0),
        '(7) srow = 2 の列数': sum(1 for j in range(len(M)) if srow(M, j) == 2),
        '(8a) amin の最大': max(am),
        '(8b) amin の最小': min(am),
        '(2b) lev の最大': max(2 * c[1] + c[2] for c in M),
        '(2c) lev の総和': sum(2 * c[1] + c[2] for c in M),
    }, rr


def run(NS, DEPTH, LMAX, tag):
    t0 = time.time(); c = Counter(); keys = None
    for M0 in load():
        S = [tuple(v) for v in M0]
        if len(S) > LMAX: continue
        for n in NS:
            X = S; f, r = feats(X)
            if keys is None: keys = list(f)
            for _ in range(DEPTH):
                Y = [tuple(v) for v in expand([list(v) for v in X], n)]
                if len(Y) < 2: break
                g, r2 = feats(Y)
                grp = '⛔ 接頭辞に逃げる手' if r2 < r else '★ ブロックの中の手'
                c[f'{grp} 分母'] += 1
                for k in keys:
                    if g[k] < f[k]: c[f'{grp}|{k}|減'] += 1
                    elif g[k] == f[k]: c[f'{grp}|{k}|同'] += 1
                    else: c[f'{grp}|{k}|増'] += 1
                X, f, r = Y, g, r2
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for grp in ('⛔ 接頭辞に逃げる手', '★ ブロックの中の手'):
        d = c[f'{grp} 分母']
        print(f'  **{grp}**: 分母 {d}')
        for k in keys:
            dec, sam, inc = c[f'{grp}|{k}|減'], c[f'{grp}|{k}|同'], c[f'{grp}|{k}|増']
            mark = ' ★★★ **単調減少**' if inc == 0 and dec > 0 else (
                   ' ★ 非増加' if inc == 0 else '')
            print(f'      {k:26s} 減 {100*dec/max(d,1):7.3f}%  '
                  f'同 {100*sam/max(d,1):7.3f}%  増 {100*inc/max(d,1):7.3f}%{mark}')
    print()


if __name__ == '__main__':
    run((1, 2, 3), 6, 12, '★ シート（|M|<=12）, n∈{1,2,3}, 6 手')
    run((1, 2), 8, 21, '★★ シート全体, n∈{1,2}, 8 手')
