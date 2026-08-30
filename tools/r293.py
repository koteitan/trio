# -*- coding: utf-8 -*-
"""**(RES-T1)(RES-T2)(RES-T3) —— 残差の段は連続できるか、2 段で減るか。**

## ⚠ 母集団（チェックリスト 5 項目）

1. `entry Q 0 0 > 0`（`u∈{0,1,2}`） 2. 行 1 が全部等しい `Q` 3. 浅い `A`
4. **L3 の反例 2 件を直接** 5. シート由来でも裏を取る

## 1 段の定義

状態 `(A, Q, d, e)`、`n`・`j` を選ぶ ⟹ `S = A ++ mTower Q d e n ++ block.take (j+1)`、
`c = parent S (srow S (|S|-1)) (|S|-1)` ⟹ **次の状態 `(A' = S[:c], V = S[c:last], d0, e0)`**。
**群**: ★良 ＝ `|V| <= |Q|`（測度が 100% 減る）／ ⛔残差 ＝ `|V| > |Q|`。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r206 import hr0
from r284 import sheetQ
from r288 import rank, meas
from r291 import AS

CE = [([(0, 0, 0)], [(2, 1, 0), (3, 1, 0)], 1, 0),
      ([(0, 0, 0)], [(1, 1, 0), (2, 1, 0)], 0, 0)]


def qsets():
    out = []
    for L in (2, 3, 4):
        for v in (0, 1, 2):
            for s in (0, 1, 2):
                out.append([(a, v, 0) for a in range(s, s + L)])
    for Q0 in sheetQ(5):
        if hr0(Q0):
            for u in (0, 1, 2):
                out.append([(x + u, y, z) for x, y, z in Q0])
    return out


def step1(A, Q, d, e, n, j):
    from r113 import mTower
    from r141 import block
    T = [tuple(x) for x in mTower(Q, d, e, n)]
    B = [tuple(x) for x in block(Q, d, e, n)]
    S = [tuple(x) for x in A] + T + B[:j + 1]
    last = len(S) - 1
    i1 = srow(S, last)
    cc = trio.parent(S, i1, last)
    if cc is None: return None
    V = [tuple(v) for v in S[cc:last]]
    if len(V) < 1: return None
    d0 = (S[last][0] - S[cc][0]) if i1 > 0 else 0
    e0 = (S[last][1] - S[cc][1]) if i1 > 1 else 0
    return [tuple(v) for v in S[:cc]], V, d0, e0, cc, i1, len(S)


def main():
    t0 = time.time(); c = Counter(); ex = []
    NS = (1, 2, 3)
    for Q in qsets():
        for A in AS:
            for d in (0, 1, 2):
                for e in (0, 1, 2):
                    for n in NS:
                        for j in range(0, len(Q)):
                            r = step1(A, Q, d, e, n, j)
                            if r is None: continue
                            A1, V1, d1, e1, c1, s1, T1 = r
                            g1 = '⛔残差' if len(V1) > len(Q) else '★良'
                            c[f'1 段目 {g1}'] += 1
                            if g1 == '⛔残差':
                                # ---------- (RES-T3) 中身 ----------
                                c[f'   (T3) c < |A| ? {c1 < len(A)}'] += 1
                                c[f'   (T3) srow={s1}'] += 1
                                c[f'   (T3) e=0 ? {e == 0}'] += 1
                                c[f'   (T3) d=0 ? {d == 0}'] += 1
                                c[f'   (T3) j=0 ? {j == 0}'] += 1
                                c[f'   (T3) 行1が一定 ? '
                                  f'{len(set(q[1] for q in Q)) == 1}'] += 1
                            # ---------- 2 段目 ----------
                            for n2 in NS:
                                for j2 in range(0, len(V1)):
                                    r2 = step1(A1, V1, d1, e1, n2, j2)
                                    if r2 is None: continue
                                    A2, V2, d2, e2, c2, s2, T2 = r2
                                    g2 = '⛔残差' if len(V2) > len(V1) else '★良'
                                    c[f'(T1) 1段目={g1} → 2段目={g2}'] += 1
                                    # ---------- (RES-T2) 2 段合成 ----------
                                    ok2 = meas(V2, d2, e2) < meas(Q, d, e)
                                    c[f'(T2) 1段目={g1} 2段合成 '
                                      f'{"★減" if ok2 else "⛔増/同"}'] += 1
                                    if g1 == '⛔残差' and g2 == '⛔残差' and len(ex) < 4:
                                        ex.append((A, Q, d, e, n, j, len(V1),
                                                   n2, j2, len(V2)))
    print(f'### (RES-T1)(RES-T2)(RES-T3)  [{time.time()-t0:.1f}s]')
    print(f'  1 段目: ★良 {c["1 段目 ★良"]}  ⛔残差 {c["1 段目 ⛔残差"]}')
    print('  ★★★★ (RES-T1) 1 段目 → 2 段目')
    for g1 in ('⛔残差', '★良'):
        tot = sum(c[f'(T1) 1段目={g1} → 2段目={g2}'] for g2 in ('⛔残差', '★良'))
        if not tot: continue
        for g2 in ('⛔残差', '★良'):
            v = c[f'(T1) 1段目={g1} → 2段目={g2}']
            print(f'      {g1} → {g2}: {v:8d} ({100*v/tot:8.4f}%)')
    print('  ★★★ (RES-T2) 2 段合成で測度が減るか')
    for g1 in ('⛔残差', '★良'):
        a = c[f'(T2) 1段目={g1} 2段合成 ★減']; b = c[f'(T2) 1段目={g1} 2段合成 ⛔増/同']
        if a + b:
            print(f'      1 段目={g1}: 分母 {a+b:8d}  ★減 {a:8d} ({100*a/(a+b):8.4f}%)  '
                  f'⛔ 増/同 {b}')
    print('  ★★ (RES-T3) 残差の中身')
    d = c['1 段目 ⛔残差']
    for k in sorted(c):
        if k.startswith('   (T3)'):
            print(f'      {k[8:]:26s} {c[k]:8d} ({100*c[k]/max(d,1):8.4f}%)')
    for x in ex:
        print(f'      ⛔ 残差→残差: A={x[0]} Q={x[1]} d={x[2]} e={x[3]} n={x[4]} j={x[5]} '
              f'|V1|={x[6]} ⟹ n2={x[7]} j2={x[8]} |V2|={x[9]}')


if __name__ == '__main__':
    main()
