# -*- coding: utf-8 -*-
"""**課題 (w5) —— `h2cone` は遺伝するか。**

## 前提の逐語（教訓 2）

L3 の新しい前提（team-lead が逐語で渡してきた形）:

```lean
h2cone : ∀ j, 0 < j → j < |Q| → le1 Q 0 j → 0 < entry Q 2 j →
           hasParent (Q.take (j + 1)) 2 j
```

`L105Cap:11316` `h2_cone`（緑）が **`hz0 ⟹ h2cone`** を与える。
`Trio.lean:56` `le1 M j0 j1 = j0 < |M| ∧ j1 < |M| ∧ ReflTransGen (nextrel1 M) j0 j1`（反射的）。

**主語**: 「`V` の錐」＝ `V[0]`（＝親の列）からの `le1 V 0 i`。**`Q` の錐ではない。**

## ⚠ 母集団が変わる（教訓 19/20）

前提が `hz0` から `h2cone` に**弱まった**ので、**`Q` の母集団は広がる**。
⟹ **`h2cone(Q)` を課す**（`hz0(Q)` ではない）。`hz0` を課したままだと母集団を狭めすぎる。

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ §R178 で「真の核（錐の中・行 2 正・親なし）＝ `¬h2cone(V)`」を全段の
>   3.390 / 5.222 / 6.231% と測っている（母集団は `hz0(Q)`）。**
> **⚠ 母集団を `h2cone(Q)` に広げると、**破れは増える**と予想。見積もり 4〜12%。**
> **⚠ 非減少の段では 0%（(w4) の恒真）、破れは全部**減る段**に出ると予想。**
> **⚠ 反例の形: `V` の中に「`j>=1`、行 2 正、`le1 V 0 j`、`V.take(j+1)` で行 2 の親なし」の列。**
> **⟹ 100% なら前提が遺伝して帰納が閉じる。破れるならそれが本当の残差。**
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


def h2cone(X):
    """`∀ j, 0<j → j<|X| → le1 X 0 j → 0 < entry X 2 j → hasParent (X.take (j+1)) 2 j`。
    破れる列のリストを返す（空なら成立）。"""
    return [j for j in range(1, len(X))
            if X[j][2] > 0 and trio.is_ancestor(X, 1, 0, j)
            and trio.parent(X[:j + 1], 2, j) is None]


def run(E, LS, NS, DE, nsamp, seed, pop):
    """pop: 'h2cone' = `hr0 ∧ h2cone(Q)` を課す（本命）
            'hz0'    = `hr0 ∧ hz0(Q)`（§R178 と同じ。参考）
            'none'   = `hr0` だけ（陽性対照）"""
    COL = [(x, y, z) for x in range(E) for y in range(E) for z in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []; js = Counter(); t0 = time.time()
    tries = 0
    while c['Q の本数'] < nsamp and tries < nsamp * 200:
        tries += 1
        L = rnd.choice(LS)
        a = rnd.randrange(E - 1)
        Q = [(a, rnd.randrange(E), rnd.randrange(2))] + \
            [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        assert hr0(Q)
        if pop == 'hz0' and not hz0(Q): continue
        if pop == 'h2cone' and h2cone(Q): continue
        c['Q の本数'] += 1
        if not hz0(Q): c['  うち hz0(Q) を満たさない'] += 1
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
                nd = len(V) >= L
                key = '非減少' if nd else '減る'
                c['全段'] += 1; c[(key, '母')] += 1
                bad = h2cone(V)
                if bad:
                    c['⚠ h2cone(V) が破れる'] += 1
                    c[(key, '⚠ 破れ')] += 1
                    for j in bad: js[j] += 1
                    if not hz0(V): c['  破れのうち hz0(V) も破れ'] += 1
                    if len(ex) < 3: ex.append((Q, d, e, n, j0, V, bad))
    t = c['全段']
    print(f'### 母集団={pop}  値域<{E} |Q|∈{LS} n∈{tuple(NS)}  '
          f'Q {c["Q の本数"]}（hz0 不成立 {c["  うち hz0(Q) を満たさない"]}）  全段 {t}  '
          f'[{time.time()-t0:.1f}s]')
    print(f'    **⚠ `h2cone(V)` が破れる … {c["⚠ h2cone(V) が破れる"]} / {t} '
          f'({100*c["⚠ h2cone(V) が破れる"]/max(t,1):7.4f}%)**   '
          f'（うち `hz0(V)` も破れ {c["  破れのうち hz0(V) も破れ"]}）')
    for k in ('減る', '非減少'):
        m = c[(k, '母')]
        print(f'      {k:6s} 母集団 {m:8d}   ⚠ 破れ {c[(k,"⚠ 破れ")]:7d} '
              f'({100*c[(k,"⚠ 破れ")]/max(m,1):7.4f}%)')
    print('      破れる列の `j`（上位）: ', js.most_common(6))
    for x in ex: print(f'      ⚠ 例 Q={x[0]} (d,e)=({x[1]},{x[2]}) n={x[3]} j={x[4]} '
                       f'V={x[5]} 破れる列={x[6]}')
    print()


if __name__ == '__main__':
    print('#### ★ 本命: `h2cone(Q)` を課す（前提が弱まったぶん母集団は広い）')
    run(6,  (3,4,5,6,8), (1,2,3,4,5), range(6),  6000, 241, 'h2cone')
    run(9,  (4,6,8,10),  (1,2,3,4,6), range(9),  4000, 243, 'h2cone')
    run(12, (5,8,12),    (1,2,3,5,8), range(12), 2500, 245, 'h2cone')
    print('#### 参考: `hz0(Q)` を課す（§R178 と同じ母集団）')
    run(9,  (4,6,8,10),  (1,2,3,4,6), range(9),  4000, 243, 'hz0')
    print('#### 陽性対照: `hr0` だけ（鳴るべき）')
    run(9,  (4,6,8,10),  (1,2,3,4,6), range(9),  4000, 243, 'none')


# ---------------- (w5b) 追加: **もっと強い前提なら遺伝するか** ----------------
def h2all(X):
    """`h2`（錐の制限なし、`0 < j` 版）: `∀ j, 0<j → 0 < entry X 2 j →
    hasParent (X.take (j+1)) 2 j`。破れる列を返す。"""
    return [j for j in range(1, len(X))
            if X[j][2] > 0 and trio.parent(X[:j + 1], 2, j) is None]


def run2(E, LS, NS, DE, nsamp, seed, pop):
    """`pop`: 'h2all' = `hr0 ∧ h2all(Q)` を課す。'none' = `hr0` だけ（対照）。
    測る: `h2all(V)` と `h2cone(V)` の破れ。**遺伝すれば L3 は前提を替えられる。**"""
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time(); tries = 0
    while c['Q の本数'] < nsamp and tries < nsamp * 400:
        tries += 1
        L = rnd.choice(LS)
        a = rnd.randrange(E - 1)
        Q = [(a, rnd.randrange(E), rnd.randrange(2))] + \
            [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        if pop == 'h2all' and h2all(Q): continue
        c['Q の本数'] += 1
        if not hz0(Q): c['  うち hz0(Q) 不成立'] += 1
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
                c['全段'] += 1
                if h2all(V): c['⚠ h2all(V) が破れる'] += 1
                b = h2cone(V)
                if b:
                    c['⚠ h2cone(V) が破れる'] += 1
                    if len(ex) < 2: ex.append((Q, d, e, n, j0, V, b))
    t = c['全段']
    print(f'### (w5b) 母集団={pop}  値域<{E} |Q|∈{LS}  Q {c["Q の本数"]}'
          f'（hz0 不成立 {c["  うち hz0(Q) 不成立"]}）  全段 {t}  [{time.time()-t0:.1f}s]')
    for k in ['⚠ h2all(V) が破れる', '⚠ h2cone(V) が破れる']:
        print(f'    {k:26s} {c[k]:8d} ({100*c[k]/max(t,1):7.4f}%)')
    for x in ex: print(f'      ⚠ 例 Q={x[0]} (d,e)=({x[1]},{x[2]}) n={x[3]} j={x[4]} '
                       f'V={x[5]} 破れる列={x[6]}')
    print()
