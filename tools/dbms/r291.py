# -*- coding: utf-8 -*-
"""**(LEV-P) —— `lev V 0`（親の水準）を段をまたいで測る。**

## ⚠ 定義（`Wset.lean:57` 逐語）

    **`lev M j = 2 * entry M 1 j + entry M 2 j`**

## ⚠ 母集団（チェックリスト 5 項目を全部当てる）

    1. **`entry Q 0 0 > 0`**（`u ∈ {0,1,2}` で行 0 を持ち上げ）
    2. **行 1 が全部等しい `Q`**（系統的に生成）
    3. **`Q` の根より浅い `A`**
    4. **L3 の反例 2 件を直接**
    5. **シート由来の `Q` でも裏を取る**

## 測るもの

    (a) **段内の検算**: `lev S c < lev S last`（親 < 的）が 100% か
    (b) **段をまたいで**: `lev V 0` vs `lev Q 0`（減 / 同 / 増）
    (c) **辞書式 `(lev V 0, towerMeas)`**
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r206 import hr0
from r284 import sheetQ
from r288 import meas

lev = lambda q: 2 * q[1] + q[2]
AS = [[], [(0, 0, 0)], [(0, 1, 0)], [(1, 0, 0)], [(0, 0, 0), (1, 0, 0)], [(0, 2, 1)]]
CE = [([(0, 0, 0)], [(2, 1, 0), (3, 1, 0)], 1, 0, 1, 1),
      ([(0, 0, 0)], [(1, 1, 0), (2, 1, 0)], 0, 0, 1, 1)]


def qsets():
    out = []
    # 2. 行 1 が全部等しい Q
    for L in (2, 3, 4):
        for v in (0, 1, 2):
            for s in (0, 1, 2):
                out.append(('★行1が一定', [(a, v, 0) for a in range(s, s + L)]))
    # 5. シート由来（1. で持ち上げる）
    for Q0 in sheetQ(6):
        if hr0(Q0):
            for u in (0, 1, 2):
                out.append(('シート', [(x + u, y, z) for x, y, z in Q0]))
    return out


def step(A, Q, d, e, n, j):
    T = [tuple(x) for x in mTower(Q, d, e, n)]
    B = [tuple(x) for x in block(Q, d, e, n)]
    S = [tuple(x) for x in A] + T + B[:j + 1]
    last = len(S) - 1
    i1 = srow(S, last)
    cc = trio.parent(S, i1, last)
    if cc is None: return None
    V = [tuple(v) for v in S[cc:last]]
    if not V: return None
    d0 = (S[last][0] - S[cc][0]) if i1 > 0 else 0
    e0 = (S[last][1] - S[cc][1]) if i1 > 1 else 0
    return S, last, cc, V, d0, e0


def main():
    t0 = time.time(); c = Counter(); ex = []
    print('## ★★★★ (LEV-P-CE) L3 の反例 2 件を直接')
    for A, Q, d, e, n, j in CE:
        r = step(A, Q, d, e, n, j)
        S, last, cc, V, d0, e0 = r
        print(f'   A={A} Q={Q} d={d} e={e} n={n} j={j} ⟹ c={cc} |V|={len(V)}')
        print(f'       段内: lev(親)={lev(S[cc])} < lev(的)={lev(S[last])} ? '
              f'{lev(S[cc]) < lev(S[last])}')
        print(f'       段間: lev V 0 = {lev(V[0])}  vs  lev Q 0 = {lev(Q[0])} ⟹ '
              f'{"★減" if lev(V[0]) < lev(Q[0]) else ("同" if lev(V[0]) == lev(Q[0]) else "⛔増")}')
        print(f'       辞書式 (lev V 0, towerMeas): ({lev(Q[0])},{meas(Q,d,e)}) → '
              f'({lev(V[0])},{meas(V,d0,e0)}) ⟹ '
              f'{"★減" if (lev(V[0]),meas(V,d0,e0)) < (lev(Q[0]),meas(Q,d,e)) else "⛔ **減らない**"}')
    print()
    for tag, Q in qsets():
        for A in AS:
            for d in (0, 1, 2):
                for e in (0, 1, 2):
                    for n in (1, 2, 3):
                        for j in range(0, len(Q)):
                            r = step(A, Q, d, e, n, j)
                            if r is None: continue
                            S, last, cc, V, d0, e0 = r
                            c[f'[{tag}] 分母'] += 1
                            # (a) 段内
                            c[f'[{tag}] ★(a) lev(親) < lev(的)'] += \
                                1 if lev(S[cc]) < lev(S[last]) else 0
                            # (b) 段間
                            a, b = lev(Q[0]), lev(V[0])
                            k = '減' if b < a else ('同' if b == a else '増')
                            c[f'[{tag}] (b) {k}'] += 1
                            # (c) 辞書式
                            lx = (b, meas(V, d0, e0)) < (a, meas(Q, d, e))
                            c[f'[{tag}] ★(c) 辞書式が減る'] += 1 if lx else 0
                            if not lx and len(ex) < 4 and tag == '★行1が一定':
                                ex.append((A, Q, d, e, n, j, cc, a, b,
                                           meas(Q, d, e), meas(V, d0, e0)))
    print(f'## ★★ 全体（チェックリスト適用）  [{time.time()-t0:.1f}s]')
    for tag in ('★行1が一定', 'シート'):
        d = c[f'[{tag}] 分母']
        if not d: continue
        print(f'  **{tag}**: 分母 {d}')
        print(f'      ★ (a) 段内 `lev(親) < lev(的)` '
              f'{c[f"[{tag}] ★(a) lev(親) < lev(的)"]} '
              f'({100*c[f"[{tag}] ★(a) lev(親) < lev(的)"]/d:8.4f}%)')
        print(f'      (b) 段間 `lev V 0`: 減 {100*c[f"[{tag}] (b) 減"]/d:7.3f}%  '
              f'同 {100*c[f"[{tag}] (b) 同"]/d:7.3f}%  増 {100*c[f"[{tag}] (b) 増"]/d:7.3f}%')
        print(f'      ★ (c) 辞書式 `(lev V 0, towerMeas)` が減る '
              f'{c[f"[{tag}] ★(c) 辞書式が減る"]} '
              f'({100*c[f"[{tag}] ★(c) 辞書式が減る"]/d:8.4f}%)')
    for x in ex:
        print(f'      ⛔ 辞書式が減らない例: A={x[0]} Q={x[1]} d={x[2]} e={x[3]} n={x[4]} '
              f'j={x[5]} c={x[6]} lev {x[7]}→{x[8]} meas {x[9]}→{x[10]}')


if __name__ == '__main__':
    main()
