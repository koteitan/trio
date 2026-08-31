# -*- coding: utf-8 -*-
"""**(CHAIN) —— 連鎖を全部走らせて、止まるか／何が減るかを探す。**

## ⚠ 母集団と除外条件（1 行）

シート 1,637 行列、`A = C.take j0`（`1 <= j0 <= 4`）、`Q = C.drop j0`。
**除外**: `|Q| < 2`、`|Q| > 5`、`(P1)`（`∀ q ∈ Q, entry Q 0 0 <= q.1`）を満たさないもの。
**1 手**: `n ∈ NS`・`j` を選び `S = A ++ Q^(n-1) ++ Q[:j+1]`、`c = parent S (srow S last) last`
⟹ 次の状態 **`(A' = S[:c], V = S[c:last])`**。⟹ **良い枝 ＝ `c >= |A|`／残差 ＝ `c < |A|`**。
⚠ **深さ上限 DMAX、状態の重複（循環）を検出**。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r263 import load
from r273 import anc0chain


def stepPC(A, Q, n, j):
    S = list(A) + list(Q) * (n - 1) + list(Q[:j + 1])
    last = len(S) - 1
    c = trio.parent(S, srow(S, last), last)
    if c is None: return None
    return tuple(S[:c]), tuple(S[c:last]), c


def feats(A, Q):
    am = [min(Q[y][1] for y in anc0chain(list(Q), t)) for t in range(len(Q))]
    return {
        '|Q|': len(Q),
        '|A|': len(A),
        '|A|+|Q|': len(A) + len(Q),
        'Q の行 0 の幅': Q[-1][0] - Q[0][0],
        'Q の相異なる行 1 の値の数': len(set(q[1] for q in Q)),
        'Q の行 1 の最大': max(q[1] for q in Q),
        'Q の srow=2 の列数': sum(1 for t in range(len(Q)) if srow(list(Q), t) == 2),
        'Q の孤児の数': sum(1 for t in range(1, len(Q))
                            if (am[t] == Q[t][1] if srow(list(Q), t) == 1 else
                                (trio.parent(list(Q[:t+1]), 2, t) is None
                                 if srow(list(Q), t) == 2 else Q[t][0] == Q[0][0]))),
        'A の最小の行 0': min((q[0] for q in A), default=Q[0][0]),
        'entry Q 0 0': Q[0][0],
    }


def run(NS, DMAX, LQ, J0, tag):
    t0 = time.time(); c = Counter(); keys = None; cyc = []
    seeds = []
    for M in load():
        X = [tuple(v) for v in M]
        for j0 in range(1, min(len(X), J0) + 1):
            A = tuple(X[:j0]); Q = tuple(X[j0:])
            if not (2 <= len(Q) <= LQ): continue
            if not all(Q[0][0] <= q[0] for q in Q): continue
            seeds.append((A, Q))
    seeds = seeds[:120]
    BUDGET = 200000
    for A0, Q0 in seeds:
        stack = [(A0, Q0, 0, (), '')]
        while stack and BUDGET > 0:
            BUDGET -= 1
            A, Q, dep, path, pat = stack.pop()
            if dep >= DMAX:
                c[f'⚠ 深さ上限 {DMAX} に到達'] += 1
                c[f'   到達時の pattern 長 {len(pat)}'] += 1
                continue
            f = feats(A, Q)
            if keys is None: keys = list(f)
            key = (A, Q)
            if key in path:
                c['⛔ **循環（同じ状態に戻る）**'] += 1
                if len(cyc) < 3: cyc.append((A0, Q0, pat))
                continue
            for n in NS:
                for j in range(0, len(Q)):
                    r = stepPC(A, Q, n, j)
                    if r is None: continue
                    A1, V1, cc = r
                    if not V1: continue
                    g = '★良' if cc >= len(A) else '⛔残'
                    c[f'手 {g}'] += 1
                    gf = feats(A1, V1)
                    for k in keys:
                        c[f'{g}|{k}|' + ('減' if gf[k] < f[k] else
                                         ('同' if gf[k] == f[k] else '増'))] += 1
                        c[f'全|{k}|' + ('減' if gf[k] < f[k] else
                                        ('同' if gf[k] == f[k] else '増'))] += 1
                    stack.append((A1, V1, dep + 1, path + (key,),
                                  pat + ('G' if g == '★良' else 'R')))
            c[f'   到達した深さ {dep}'] += 1
            c[f'   pattern: {pat[:6] if pat else "(始)"}'] += 1
    print(f'### (CHAIN) {tag}  種 {len(seeds)}  [{time.time()-t0:.1f}s]')
    print(f'  (a) ⛔ **循環** {c["⛔ **循環（同じ状態に戻る）**"]}   '
          f'⚠ 深さ上限 {DMAX} に到達 {c[f"⚠ 深さ上限 {DMAX} に到達"]}')
    print('      到達した深さ: ' + str({int(k.split()[-1]): v for k, v in c.items()
                                        if k.startswith('   到達した深さ')}))
    print(f'  手: ★良 {c["手 ★良"]}  ⛔残 {c["手 ⛔残"]}')
    print('  ★★★ (c) 連鎖に沿って単調な量')
    for k in keys:
        for g in ('全', '★良', '⛔残'):
            d = sum(c[f'{g}|{k}|{x}'] for x in ('減', '同', '増'))
            if not d: continue
            dec, sm, inc = (c[f'{g}|{k}|減'], c[f'{g}|{k}|同'], c[f'{g}|{k}|増'])
            m = ' ★★★ **非増加**' if inc == 0 else ''
            if g == '全' or m:
                print(f'      [{g}] {k:26s} 減 {100*dec/d:7.3f}%  同 {100*sm/d:7.3f}%  '
                      f'増 {100*inc/d:7.3f}%{m}')
    print('  (d) pattern の分布（先頭 6 手）:')
    ps = sorted(((k[12:], v) for k, v in c.items() if k.startswith('   pattern:')),
                key=lambda t: -t[1])[:8]
    for p, v in ps: print(f'      {p}: {v}')
    for x in cyc: print(f'      ⛔ 循環の種: A={x[0]} Q={x[1]} pattern={x[2]}')
    print()


if __name__ == '__main__':
    run((1, 2), 5, 4, 3, 'n∈{1,2}, DMAX=5, |Q|<=4, j0<=3')
    run((1, 2, 3), 4, 4, 3, 'n∈{1,2,3}, DMAX=4, |Q|<=4, j0<=3')
