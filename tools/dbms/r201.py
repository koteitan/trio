# -*- coding: utf-8 -*-
"""**課題 (z3) —— 残差の `V` は、そもそも帰納の中で到達可能か。**

## 前提の逐語（教訓 2）

`H12H2.lean:602-608`:

```lean
def dOf (M : TrioSeq) : ℕ :=
  if 0 < srow M (M.length - 1) then entry M 0 (M.length - 1) - entry M 0 0 else 0
def eOf (M : TrioSeq) : ℕ :=
  if 1 < srow M (M.length - 1) then entry M 1 (M.length - 1) - entry M 1 0 else 0
```

`H12H2.lean:626-630`: 塔は `mTower M.dropLast (dOf M) (eOf M) n ++
  (Lift1 (shiftr01 (dOf M * n) 0 M.dropLast) (eOf M * n)).take j`。

⟹ **★ 消費側では `Q = M.dropLast`、`d = dOf M`、`e = eOf M`。`(d,e)` は深さ 0 でも決まっている。**
（一様な箱の測定では `(d,e)` を振っていた。ここが (z3) の肝。）

`M = Lift1 ((0,v,z) :: R) t`、`Q = M.dropLast = Lift1 ((0,v,z) :: R.dropLast) t`
（`Lift1_dropLast`、`Wset:1007`）。

## ⚠ 母集団は消費側の**上位集合**（(z2) と同じ）

`argOK R`／`R≠[]`／`z<=1`／`∃m, domT R m`／`srow R (|R|-1)=2`／`hasParent ((0,v,z)::R) 2 |R|`。
**`Wstar2` 所属は判定しない。**

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ 一様な箱では `h2cone(V)` の破れが 6.3〜8.5%。**
> **⚠ 消費側から降りると**下がる**と予想。見積もり **0〜3%**。**
> **⚠ 0% なら残差は空虚 ⟹ そのときは箱を伸ばして壊しにいく。**
> **⚠ 反例の形: 深さ 1 で `h2cone(V)` が破れる `(R,v,z,t,n,j)`。**
"""
import sys, itertools, time, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r169 import domT
from r171 import step_det
from r195 import h2cone


def dOf(M):
    j = len(M) - 1
    return (M[j][0] - M[0][0]) if srow(M, j) > 0 else 0


def eOf(M):
    j = len(M) - 1
    return (M[j][1] - M[0][1]) if srow(M, j) > 1 else 0


def run(L, R1, VS, ZS, TS, NS, depth, beam, seed):
    COL = [(a, b, c) for a in range(1, 4) for b in range(R1) for c in (0, 1)]
    c = Counter(); ex = []; t0 = time.time(); rnd = random.Random(seed)
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt); jR = len(R) - 1
        if srow(R, jR) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q = M[:-1]
                    if len(Q) < 2: continue
                    d, e = dOf(M), eOf(M)
                    c['消費側の (R,v,z,t)'] += 1
                    if h2cone(Q): c['⚠ そもそも h2cone(Q) が破れている'] += 1
                    front = [(tuple(Q), d, e)]
                    for dep in range(1, depth + 1):
                        nxt = set()
                        for (X, dd, ee) in front:
                            for n in NS:
                                for j in range(len(X)):
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    V = tuple(r[0])
                                    c[('深さ', dep, '段')] += 1
                                    if h2cone(list(V)):
                                        c[('深さ', dep, '⚠ 破れ')] += 1
                                        if len(ex) < 3:
                                            ex.append((R, v, z, t, d, e, n, j, dep, list(V)))
                                    nxt.add((V, r[1], r[2]))
                        if not nxt: break
                        front = list(nxt)
                        if len(front) > beam:
                            rnd.shuffle(front); front = front[:beam]
    print(f'### |R|={L} 行1<{R1} v∈{tuple(VS)} z∈{tuple(ZS)} t∈{tuple(TS)} n∈{tuple(NS)}  '
          f'消費側 {c["消費側の (R,v,z,t)"]}  [{time.time()-t0:.1f}s]')
    print(f'    ⚠ そもそも `h2cone(Q)` が破れている … {c["⚠ そもそも h2cone(Q) が破れている"]} '
          f'/ {c["消費側の (R,v,z,t)"]} '
          f'({100*c["⚠ そもそも h2cone(Q) が破れている"]/max(c["消費側の (R,v,z,t)"],1):6.2f}%)')
    for dep in range(1, depth + 1):
        s = c[('深さ', dep, '段')]
        if not s: continue
        print(f'    深さ {dep}: 段 {s:9d}   **⚠ `h2cone(V)` の破れ '
              f'{c[("深さ", dep, "⚠ 破れ")]:8d} ({100*c[("深さ",dep,"⚠ 破れ")]/s:7.4f}%)**')
    for x in ex:
        print(f'      ⚠ 破れ例 R={x[0]} v={x[1]} z={x[2]} t={x[3]} (d,e)=({x[4]},{x[5]}) '
              f'n={x[6]} j={x[7]} 深さ={x[8]} V={x[9]}')
    print()


if __name__ == '__main__':
    run(2, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 4, 400, 331)
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 4, 300, 333)
    print('#### 教訓 21: 箱を伸ばす')
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3,4), 4, 300, 335)
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 3, 200, 337)
