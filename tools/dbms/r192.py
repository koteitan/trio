# -*- coding: utf-8 -*-
"""**課題 (y1) —— `hz0(V)` が破れるとき、`V` は「錐の中 ∧ 行 2 が正」の列を持つか。**

## 前提の逐語（教訓 2）

`L105Cap:11316`:

```lean
theorem h2_cone {Q : TrioSeq} (hz0 : entry Q 2 0 = 0) :
    ∀ j, 1 ≤ j → j < Q.length → 0 < entry Q 2 j → le1 Q 0 j →
      hasParent (Q.take (j + 1)) 2 j
```

⟹ **`1 ≤ j`。根（`j = 0`）は除外されている。** ここが主語の肝。

`Trio.lean:56` `le1 M j0 j1 = j0 < |M| ∧ j1 < |M| ∧ ReflTransGen (nextrel1 M) j0 j1`
⟹ **反射的**。だから `le1 V 0 0` は常に真だが、`h2_cone` は `j >= 1` しか見ない。

## 測る量

母集団 = **`entry V 2 0 = 1` になった段**（＝ `hz0(V)` が破れた段）。

    **(y1a)** `V` に `1 <= j < |V|` かつ `0 < entry V 2 j` かつ `le1 V 0 j` の列があるか
    **(y1b)** あるとき、その `j` の分布
    **(y1c)** 箱を伸ばす

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ L3 は「0% なら `hz0(V)` は要らない」と言っている。**
> **⚠ 私の見積もり **40〜80%**（`Q` の約半分の列が行 2 = 1、錐は普通に広い）。**
> **⚠ つまり L3 の希望（0%）は**外れる**と予想する。**
> **⚠ 反例（L3 に有利な形）: そういう列が 1 本も無い `V`。**

**箱**: `Q` は `hr0 ∧ hz0` を構成的に満たす（消費側の形）。**`W` 所属は判定しない。**
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r183 import hr0, hz0


def run(E, LS, NS, DE, nsamp, seed):
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    js = Counter()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        a = rnd.randrange(E - 1)
        Q = [(a, rnd.randrange(E), 0)] + \
            [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        assert hr0(Q) and hz0(Q)
        d, e = rnd.choice(DE), rnd.choice(DE)
        for n in NS:
            for j0 in range(L):
                T = [tuple(x) for x in mTower(Q, d, e, n)]
                S = T + block(Q, d, e, n)[:j0 + 1]
                last = len(S) - 1
                par = trio.parent(S, srow(S, last), last)
                if par is None: continue
                V = [tuple(x) for x in S[par:last]]
                if len(V) < 2: continue
                c['全段(|V|>=2)'] += 1
                if V[0][2] == 0:
                    c['hz0(V) 成立'] += 1
                    continue
                c['★ 母集団: hz0(V) が破れた段'] += 1
                hits = [i for i in range(1, len(V))
                        if V[i][2] > 0 and trio.is_ancestor(V, 1, 0, i)]
                if hits:
                    c['⚠ (y1a) 錐の中 ∧ 行 2 が正 の列を持つ'] += 1
                    for i in hits: js[i] += 1
                    c[('その本数', min(len(hits), 5))] += 1
                else:
                    c['★ (y1a) 持たない（hz0(V) は要らない）'] += 1
                    if len(ex) < 3: ex.append((Q, d, e, n, j0, V))
    m = c['★ 母集団: hz0(V) が破れた段']
    print(f'### 値域<{E} |Q|∈{LS} n∈{tuple(NS)} (d,e)∈{tuple(DE)}  '
          f'全段 {c["全段(|V|>=2)"]}  [{time.time()-t0:.1f}s]')
    print(f'    hz0(V) 成立 … {c["hz0(V) 成立"]} '
          f'({100*c["hz0(V) 成立"]/max(c["全段(|V|>=2)"],1):6.2f}%)')
    print(f'    ★ 母集団（hz0(V) が破れた段）… {m}')
    for k in ['⚠ (y1a) 錐の中 ∧ 行 2 が正 の列を持つ', '★ (y1a) 持たない（hz0(V) は要らない）']:
        print(f'      {k:44s} {c[k]:8d} ({100*c[k]/max(m,1):7.3f}%)')
    print('      該当列の本数: ', dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple))))
    print('      (y1b) 該当列の `j` の分布（上位）: ', js.most_common(8))
    for x in ex: print(f'      ★ 持たない例 Q={x[0]} (d,e)=({x[1]},{x[2]}) n={x[3]} j={x[4]} V={x[5]}')
    print()


if __name__ == '__main__':
    run(6,  (3,4,5,6,8), (1,2,3,4,5), range(6),  12000, 211)
    print('#### 教訓 21: 箱を広げる')
    run(9,  (4,6,8,10),  (1,2,3,4,6), range(9),   8000, 213)
    run(12, (5,8,12),    (1,2,3,5,8), range(12),  5000, 215)
