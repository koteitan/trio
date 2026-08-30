# -*- coding: utf-8 -*-
"""**R99 —— `Lift1 X 1` と一様シフト `shiftr01 0 1 X` の差分（H12 の (h2) の独立検証）。**

team-lead の指示: 「2 人が独立に出した数字が食い違うかどうかが、いま最も信頼できる検証」。
**H12 の数字は見ずに測る**（見ると独立でなくなる）。

    `Lift1 X d`（`Wset.lean:927`）  行 1 を `d` 上げる。ただし **`le1 X 0 i` の錐の上だけ**
    `shiftr01 0 d X`（`Cnf.lean:626`） 行 1 を `d` 上げる。**全列**

⟹ 食い違う列 ＝ **`le1 X 0 i` が偽の列**。

★ 既に緑の特徴づけがある（`Lcone.lean:36` `le1_zero_iff`）:

    根が真に最浅（`∀l, 0<l<|A| → entry A 0 0 < entry A 0 l`）なら
      **`le1 A 0 j ⟺ ∀ y, y →*₀ j, y ≠ 0 → entry A 1 0 < entry A 1 y`**
    （`→*₀` は行 0 の祖先関係 `nextrel0` の反射推移閉包）

`X = (0,v,z) :: R` で `argOK R`（全列 行 0 >= 1）なら根の行 0 = 0 が真に最浅 ⟹ 前提は自動。
⟹ **食い違う列 `i` ⟺ `i` の行 0 祖先（根以外）に行 1 が `v` 以下のものがある。**

この特徴づけを**実測で照合**し（計器が緑の補題と合うかの検査）、そのうえで差分を数える。

母集団は 2 つ（教訓 11: 母集団で数字が変わるので両方出す）:
  (P-tie)   `LiftTie` / `LiftTieSelf` の場面 … `argOK R` ∧ `z<=1` ∧ **タイあり**（`∃p∈R, p.2.1=v`）
  (P-tower) `TowerOK2` の場面 … R98/R97 と同じ 5 条件
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def anc0(S, j):
    """`j` の行 0 祖先の鎖（`j` 自身を含み、根 0 まで）。"""
    out = [j]
    while True:
        p = trio.parent(S, 0, out[-1])
        if p is None:
            break
        out.append(p)
    return out


def run(DS, BS, CS, VS, ZS, LS, pop, label):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    n = 0
    ndiff = Counter(); chk = Counter(); pos = Counter(); where = Counter()
    ex = {}
    t0 = time.time()
    for L in LS:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            if any(p[0] < 1 for p in R):
                continue                                   # argOK
            for v in VS:
                for z in ZS:
                    if pop == 'tie':
                        if not any(p[1] == v for p in R):
                            continue                       # タイあり
                    else:
                        j = len(R) - 1
                        i1 = srow(R, j)
                        if trio.parent(R, i1, j) is not None:
                            continue                       # domT の ¬hasParent
                        if lev(R[j]) - 1 < 0:
                            continue
                        if trio.parent([(0, v, z)] + R, i1, len(R)) is None:
                            continue                       # 根が復活させる
                    n += 1
                    X = [(0, v, z)] + R
                    A = [(c[0], c[1] + (1 if trio.is_ancestor(X, 1, 0, i) else 0), c[2])
                         for i, c in enumerate(X)]
                    B = [(c[0], c[1] + 1, c[2]) for c in X]
                    d = [i for i in range(len(X)) if A[i] != B[i]]
                    ndiff[len(d)] += 1
                    if not d:
                        where['**一致（Lift1 = 一様シフト）**'] += 1
                    else:
                        where['食い違いあり'] += 1
                        ex.setdefault('差分あり', (R, v, z, d))
                    for i in d:
                        pos[f'位置 i={i} / |X|={len(X)}'] += 1
                    # ---- `le1_zero_iff`（`Lcone.lean:36`、緑）の照合 ----
                    for i in range(len(X)):
                        lhs = trio.is_ancestor(X, 1, 0, i)
                        rhs = all(X[0][1] < X[y][1] for y in anc0(X, i) if y != 0)
                        chk['le1_zero_iff/' + ('ok' if lhs == rhs else '**VIOL**')] += 1
                        if lhs != rhs:
                            ex.setdefault('le1_zero_iff 違反', (R, v, z, i))
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s)  場面 **{n}** 件')
    if n == 0:
        print('  ⚠ 場面 0 件'); return
    print('  -- ★ `le1_zero_iff`（緑）との照合 --')
    for k in sorted(chk):
        print(f'     {k:28s} {chk[k]:11d}')
    print('  -- (h2-1) 一致するか --')
    for k in sorted(where):
        print(f'     {k:32s} {where[k]:10d}  ({100*where[k]/n:5.1f}%)')
    print('  -- (h2-2) 食い違う列の本数 --')
    for k in sorted(ndiff):
        print(f'     {k} 本 : {ndiff[k]:10d}  ({100*ndiff[k]/n:5.1f}%)')
    print('  -- (h2-3) 食い違う列の位置（多い順に 8 件） --')
    for k, c in sorted(pos.items(), key=lambda x: -x[1])[:8]:
        print(f'     {k:26s} {c:10d}')
    for k in sorted(ex):
        print(f'  ex {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=3)
    a = ap.parse_args()
    DS, BS, CS = (1, 2, 3), (0, 1, 2, 3), (0, 1, 2)
    VS, ZS = (0, 1, 2, 3), (0, 1)
    LS = tuple(range(1, a.L + 1))
    run(DS, BS, CS, VS, ZS, LS, 'tie', f'R99 (P-tie) LiftTie の場面 |R|<={a.L}')
    run(DS, BS, CS, VS, ZS, LS, 'tower', f'R99 (P-tower) TowerOK2 の場面 |R|<={a.L}')
