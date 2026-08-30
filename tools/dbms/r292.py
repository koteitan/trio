# -*- coding: utf-8 -*-
"""**(MEAS-S) ＋ (MEAS-C)。**

## ⚠ 母集団（チェックリスト 5 項目）

1. `entry Q 0 0 > 0`（`u∈{0,1,2}`） 2. **行 1 が全部等しい `Q`** 3. **浅い `A`**
4. **L3 の反例 2 件を直接** 5. **シート由来でも裏を取る**

## (MEAS-S) `rankDE = srow(末尾)`（H12 の (W44)）を使った的絞り

    `towerMeas Q d e = 3|Q| + rankDE d e`、新しい `rankDE d0 e0 = srow(S,last) = i1`
    ⟹ ★ **`|V| = |Q|` の段で `i1 < rankDE d e` か**
    ⟹ ★ **`|V| > |Q|` の段は救えるか**（`|V|` が 1 増えると +3、`srow` は最大 2 しか下がらない）

## (MEAS-C) L3 の 6 個以外の候補（★ 大きさ型・水準型・浅さ型は除外）
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r206 import hr0
from r284 import sheetQ
from r288 import rank, meas
from r291 import lev, AS, step

CE = [([(0, 0, 0)], [(2, 1, 0), (3, 1, 0)], 1, 0, 1, 1),
      ([(0, 0, 0)], [(1, 1, 0), (2, 1, 0)], 0, 0, 1, 1)]


def qsets():
    out = []
    for L in (2, 3, 4):
        for v in (0, 1, 2):
            for s in (0, 1, 2):
                out.append(('★行1が一定', [(a, v, 0) for a in range(s, s + L)]))
    for Q0 in sheetQ(6):
        if hr0(Q0):
            for u in (0, 1, 2):
                out.append(('シート', [(x + u, y, z) for x, y, z in Q0]))
    return out


def cands(A, Q, srw):
    n2 = sum(1 for j in range(len(Q)) if srow(Q, j) == 2)
    sh = sum(1 for q in A if q[0] < Q[0][0])
    return {
        '(1a) |V| - |A|': len(Q) - len(A),
        '(1b) 2|V| + srow': 2 * len(Q) + srw,
        '(2) A の V 根より浅い列数': sh,
        '(3) V の srow=2 の列数': n2,
        '(5) V の行 0 の幅': Q[-1][0] - Q[0][0],
        '(6) V の行 1 の最大 - 根': max(q[1] for q in Q) - Q[0][1],
        '(7) V の相異なる行 1 の値の数': len(set(q[1] for q in Q)),
        '(8) srow(末尾)': srw,
    }


def main():
    t0 = time.time(); c = Counter(); keys = None; ex = []
    print('## ★★★★ (MEAS-S) L3 の反例 2 件')
    for A, Q, d, e, n, j in CE:
        S, last, cc, V, d0, e0 = step(A, Q, d, e, n, j)
        i1 = srow(S, last)
        print(f'   Q={Q} d={d} e={e} j={j} ⟹ |V|={len(V)} vs |Q|={len(Q)}、'
              f'rankDE {rank(d,e)} → **{i1}**、meas {meas(Q,d,e)} → {3*len(V)+i1}')
    print()
    for tag, Q in qsets():
        for A in AS:
            for d in (0, 1, 2):
                for e in (0, 1, 2):
                    f = cands(A, Q, rank(d, e))
                    if keys is None: keys = list(f)
                    m0 = meas(Q, d, e)
                    for n in (1, 2, 3):
                        for j in range(0, len(Q)):
                            r = step(A, Q, d, e, n, j)
                            if r is None: continue
                            S, last, cc, V, d0, e0 = r
                            i1 = srow(S, last)
                            A2 = [tuple(v) for v in S[:cc]]
                            g = cands(A2, V, i1)
                            rel = ('<' if len(V) < len(Q) else
                                   ('=' if len(V) == len(Q) else '>'))
                            c[f'[{tag}] |V| {rel} |Q| 分母'] += 1
                            if i1 < rank(d, e):
                                c[f'[{tag}] |V| {rel} |Q| ★srow 減'] += 1
                            if 3 * len(V) + i1 < m0:
                                c[f'[{tag}] |V| {rel} |Q| ★meas 減'] += 1
                            c[f'[{tag}] 分母'] += 1
                            for k in keys:
                                a, b = f[k], g[k]
                                c[f'[{tag}]|{k}|' + ('減' if b < a else
                                                     ('同' if b == a else '増'))] += 1
    print(f'## ★★ (MEAS-S) `|V|` と `|Q|` の関係別  [{time.time()-t0:.1f}s]')
    for tag in ('★行1が一定', 'シート'):
        for rel in ('<', '=', '>'):
            d = c[f'[{tag}] |V| {rel} |Q| 分母']
            if not d: continue
            print(f'  [{tag}] **|V| {rel} |Q|** 分母 {d:8d}   '
                  f'★ srow が減る {100*c[f"[{tag}] |V| {rel} |Q| ★srow 減"]/d:8.4f}%   '
                  f'★★ **meas が減る** {100*c[f"[{tag}] |V| {rel} |Q| ★meas 減"]/d:8.4f}%')
    print()
    print('## ★★ (MEAS-C) 新しい候補')
    for tag in ('★行1が一定', 'シート'):
        d = c[f'[{tag}] 分母']
        print(f'  **{tag}**: 分母 {d}')
        for k in keys:
            dec, sm, inc = (c[f'[{tag}]|{k}|減'], c[f'[{tag}]|{k}|同'], c[f'[{tag}]|{k}|増'])
            m = ' ★★★ **非増加**' if inc == 0 else ''
            print(f'      {k:30s} 減 {100*dec/max(d,1):7.3f}%  同 {100*sm/max(d,1):7.3f}%  '
                  f'増 {100*inc/max(d,1):7.3f}%{m}')


if __name__ == '__main__':
    main()
