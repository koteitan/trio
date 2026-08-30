# -*- coding: utf-8 -*-
"""**課題 (p3) —— 「根でない証人」は存在するか。**

## 背景（team-lead が `blockRoot_parent_prevBlock` の証明を読んだ結果）

```lean
  have hmin := h.2.2.2.2.2 (k * Q.length) ⟨by omega, hle0⟩    -- 証人 ＝ ブロック k の【根】
```

⟹ 証人に**根**を入れているから `0 < e` が要る。**根でない証人**（行 1 が根より小さい列）
なら `e = 0` でも通る。

## 分母（`Q` 側に課したものを明記）

**`TowerP''(Q)` の 8 本すべて**（`h1out` は訂正後）を満たす消費側の `Q` から出た窓 `V` で
**`d1 = 0` ∧ `entry V 1 0 > 0`**（＝ §R195 の核。全窓の 67.9%）。**重複除去して件数を出す。**

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ (p3a) 高いが 100% とは限らない。見積もり **85〜100%**。
>   （`V[0]` の行 1 が正で、`hr0` は行 1 について何も言わないので、
>    「行 1 が根以上の列しか無い `V`」はありうる。）**
> **⚠ (p3b) ここが勝負。`le0 T x |V|` は `nextrel0` の狭義増加と最小性が要る。
>   見積もり **50〜90%**。**
> **⚠ (p3d) `entry V 1 0 = 1` が多数と予想。**
> **⚠ 反例（(p3c)）が出たらそのまま貼る。**
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r169 import domT
from r171 import step_det
from r201 import dOf, eOf
from r212 import conds, K8, K7


def run(L, R1, VS, ZS, TS, NS, depth, beam, seed, cap=200000):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    core = set()
    # --- 1. 核の窓を集める（重複除去） ---
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        if srow(R, len(R) - 1) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q = M[:-1]
                    if len(Q) < 2: continue
                    d, e = dOf(M), eOf(M)
                    if not all(conds(Q, d, e)[k] for k in K8): continue
                    front = [(tuple(Q), d, e)]
                    for dep in range(1, depth + 1):
                        nxt = set()
                        for (X, dd, ee) in front:
                            for n in NS:
                                for j in range(len(X)):
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    V2, d0, d1 = [tuple(y) for y in r[0]], r[1], r[2]
                                    if all(conds(V2, d0, d1)[k] for k in K7):
                                        nxt.add((tuple(V2), d0, d1))
                                    if d1 == 0 and V2[0][1] > 0:
                                        core.add((tuple(V2), d0))
                        if not nxt: break
                        front = list(nxt)
                        if len(front) > beam:
                            rnd.shuffle(front); front = front[:beam]
    print(f'### |R|={L} 行1<{R1}  ★ 分母（核の窓、重複除去）… {len(core)}  '
          f'[集めるのに {time.time()-t0:.1f}s]')
    if len(core) > cap:
        core = set(list(core)[:cap]); print(f'    （{cap} に打ち切り）')
    # --- 2. 測る ---
    for (Vt, d0) in core:
        V = list(Vt); LV = len(V); r1 = V[0][1]
        c['分母'] += 1
        c[('(p3d) entry V 1 0', min(r1, 3))] += 1
        wit = [x for x in range(1, LV) if V[x][1] < r1]
        if wit:
            c['★ (p3a) 行 1 が根より小さい列がある'] += 1
            c[('(p3a) 本数', min(len(wit), 4))] += 1
            # (p3b) k = 0: `le0 (mTower V d0 0 2) x |V|`
            T = [tuple(x) for x in mTower(V, d0, 0, 2)]
            ok = [x for x in wit if trio.is_ancestor(T, 0, x, LV)]
            if ok:
                c['★★ (p3b) その x が le0 で次のブロック根に繋がる'] += 1
                c[('(p3b) 繋がる本数', min(len(ok), 4))] += 1
            else:
                c['⛔ (p3b) 繋がる x が無い'] += 1
                if len(ex) < 4: ex.append(('p3b', V, d0, wit))
        else:
            c['⛔ (p3a) 証人が 1 つも無い'] += 1
            if len(ex) < 4: ex.append(('p3a', V, d0, []))
    t = c['分母']
    for k in ['★ (p3a) 行 1 が根より小さい列がある', '⛔ (p3a) 証人が 1 つも無い',
              '★★ (p3b) その x が le0 で次のブロック根に繋がる', '⛔ (p3b) 繋がる x が無い']:
        print(f'    {k:44s} {c[k]:8d} ({100*c[k]/max(t,1):8.4f}%)')
    a = c['★ (p3a) 行 1 が根より小さい列がある']
    print(f'    （(p3b) を「証人がある `V`」に絞ると … '
          f'{c["★★ (p3b) その x が le0 で次のブロック根に繋がる"]} / {a} '
          f'({100*c["★★ (p3b) その x が le0 で次のブロック根に繋がる"]/max(a,1):8.4f}%）')
    print('    (p3d) entry V 1 0 の分布（3 は「3 以上」）: ',
          {k[1]: f'{c[k]} ({100*c[k]/max(t,1):.2f}%)' for k in sorted(
              x for x in c if isinstance(x, tuple) and x[0] == '(p3d) entry V 1 0')})
    print('    (p3a) 証人の本数: ', dict(sorted((k[1], c[k]) for k in c
              if isinstance(k, tuple) and k[0] == '(p3a) 本数')))
    print('    (p3b) 繋がる本数: ', dict(sorted((k[1], c[k]) for k in c
              if isinstance(k, tuple) and k[0] == '(p3b) 繋がる本数')))
    for tag, V, d0, w in ex:
        print(f'      ⛔ ({tag}) 反例 V={V} d0={d0} 根の行1={V[0][1]} 証人={w}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 2, 100, 471)
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), 2, 60, 473)
