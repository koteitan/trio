# -*- coding: utf-8 -*-
"""**(CONS2)(CONS3) —— `amin` まわりの保存量／単調量を総当たりで探す。**

## ⚠ 母集団・手の分類は §R251 と同じ（1 行）

`psiI.json` の 1,637 行列から `oper(·,n)` を数手たどる。`r = parent M (srow M x) x` として
**`r' < r` ⟹ ⛔ 接頭辞に逃げる手** ／ **`r' >= r` ⟹ ★ ブロックの中の手**。

    `amin M j` ＝ 行 0 祖先鎖（自身を含む）の行 1 値の最小値（H12 の `Cgraft:848`）
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

INF = 10 ** 9


def feats(M):
    n = len(M)
    am = [min(M[y][1] for y in anc0chain(M, j)) for j in range(n)]
    orph = [j for j in range(1, n)
            if M[j][1] > 0 and trio.parent(M[:j + 1], 1, j) is None]
    x = n - 1
    r = trio.parent(M, srow(M, x), x)
    return {
        '(0) amin の最大': max(am),
        '(0) amin の最小': min(am),
        '(1) amin の多重集合': tuple(sorted(am)),
        '(1b) amin の集合': tuple(sorted(set(am))),
        '(2) 相異なる amin 値の個数': len(set(am)),
        '(4) amin M 0 (= entry M 1 0)': am[0],
        '(5) amin の総和': sum(am),
        '(7) amin の最大 - 最小': max(am) - min(am),
        '★(6) 孤児の amin の最小': min((am[j] for j in orph), default=INF),
        '(6b) 孤児の amin の最大': max((am[j] for j in orph), default=-1),
        '(6c) 行 1 の孤児の個数': len(orph),
        '(8) 行 1 の値の多重集合': tuple(sorted(c[1] for c in M)),
        '(9) 行 1 の最小': min(c[1] for c in M),
    }, (-1 if r is None else r)


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
                    a, b = f[k], g[k]
                    if isinstance(a, tuple):
                        c[f'{grp}|{k}|' + ('同' if a == b else '違')] += 1
                    else:
                        c[f'{grp}|{k}|' + ('減' if b < a else
                                           ('同' if b == a else '増'))] += 1
                X, f, r = Y, g, r2
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for grp in ('⛔ 接頭辞に逃げる手', '★ ブロックの中の手'):
        d = c[f'{grp} 分母']
        print(f'  **{grp}**: 分母 {d}')
        for k in keys:
            if c[f'{grp}|{k}|同'] + c[f'{grp}|{k}|違'] == d and c[f'{grp}|{k}|違'] >= 0 \
               and (c[f'{grp}|{k}|違'] or c[f'{grp}|{k}|同']) and \
               not (c[f'{grp}|{k}|減'] or c[f'{grp}|{k}|増']):
                sm, df = c[f'{grp}|{k}|同'], c[f'{grp}|{k}|違']
                mark = ' ★★★ **完全保存**' if df == 0 else ''
                print(f'      {k:30s} 同 {100*sm/max(d,1):7.3f}%  '
                      f'違 {100*df/max(d,1):7.3f}%{mark}')
            else:
                dec, sm, inc = (c[f'{grp}|{k}|減'], c[f'{grp}|{k}|同'], c[f'{grp}|{k}|増'])
                mark = (' ★★★ **完全保存**' if dec == 0 and inc == 0 else
                        (' ★★ **非増加**' if inc == 0 else
                         (' ★ **非減少**' if dec == 0 else '')))
                print(f'      {k:30s} 減 {100*dec/max(d,1):7.3f}%  '
                      f'同 {100*sm/max(d,1):7.3f}%  増 {100*inc/max(d,1):7.3f}%{mark}')
    print()


if __name__ == '__main__':
    run((1, 2, 3), 6, 12, '★ シート（|M|<=12）, n∈{1,2,3}, 6 手')
    run((1, 2), 8, 21, '★★ シート全体, n∈{1,2}, 8 手')
