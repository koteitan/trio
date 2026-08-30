# -*- coding: utf-8 -*-
"""**(MEAS-10) —— team-lead の新候補「`argOK` が破れている列の数／根より浅い列の数」。**

## ⚠ 母集団は §R251 と同じ（1 行）

`psiI.json` の 1,637 行列から `oper(·,n)` を数手たどり、各手で候補量を前後で記録。
**手の分類**: `r = parent M (srow M x) x` として **`r' < r` ⟹ ⛔ 接頭辞に逃げる手**、
**`r' >= r` ⟹ ★ ブロックの中の手**。

## 新候補（(10) の 4 変種）

    (10a) **根より深くない列の数** `#{j>=1 : M[j][0] <= M[0][0]}`
    (10b) **`argOK` の破れの数** `#{j>=1 : M[j][0] == 0}`（根の行 0 = 0 のとき）
    (10c) **行 0 の非増加ペアの数** `#{(y,j) : y<j, M[j][0] <= M[y][0]}`
    (10d) **行 0 の「下がり」の回数** `#{i : M[i+1][0] <= M[i][0]}`
    (10e) **行 0 の最小値**（根を含む）
    (11)  **`argOK` を満たす接尾辞の最大長**
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from trio import expand
from collections import Counter
from r126 import srow
from r263 import load


def feats(M):
    x = len(M) - 1
    r = trio.parent(M, srow(M, x), x)
    rr = -1 if r is None else r
    n = len(M)
    suf = 0
    for k in range(n - 1, 0, -1):
        if M[k][0] > 0: suf += 1
        else: break
    return {
        '(10a) 根より深くない列の数': sum(1 for j in range(1, n) if M[j][0] <= M[0][0]),
        '(10b) argOK の破れの数': sum(1 for j in range(1, n) if M[j][0] == 0),
        '(10c) 行 0 の非増加ペアの数': sum(1 for j in range(n) for y in range(j)
                                          if M[j][0] <= M[y][0]),
        '(10d) 行 0 の下がりの回数': sum(1 for i in range(n - 1) if M[i + 1][0] <= M[i][0]),
        '(10e) 行 0 の最小値': min(c[0] for c in M),
        '(11) argOK を満たす接尾辞の最大長': suf,
        '(12) |M| - argOK 接尾辞': n - suf,
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
                    c[f'{grp}|{k}|' + ('減' if g[k] < f[k] else
                                       ('同' if g[k] == f[k] else '増'))] += 1
                X, f, r = Y, g, r2
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for grp in ('⛔ 接頭辞に逃げる手', '★ ブロックの中の手'):
        d = c[f'{grp} 分母']
        print(f'  **{grp}**: 分母 {d}')
        for k in keys:
            dec, sam, inc = (c[f'{grp}|{k}|減'], c[f'{grp}|{k}|同'], c[f'{grp}|{k}|増'])
            mark = ' ★★★ **非増加**' if inc == 0 else (' ★ 非減少' if dec == 0 else '')
            print(f'      {k:30s} 減 {100*dec/max(d,1):7.3f}%  '
                  f'同 {100*sam/max(d,1):7.3f}%  増 {100*inc/max(d,1):7.3f}%{mark}')
    print()


if __name__ == '__main__':
    run((1, 2, 3), 6, 12, '★ シート（|M|<=12）, n∈{1,2,3}, 6 手')
    run((1, 2), 8, 21, '★★ シート全体, n∈{1,2}, 8 手')
