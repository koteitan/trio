# -*- coding: utf-8 -*-
"""**課題 R98（team-lead は「R97」と呼んだが私の §R97（タイの本数）と衝突するので改番）
—— `TowerExp` は実際に呼ばれるのか。**

`Wset.towerOK_of (h2 : TowerGraft2) (he : TowerExp) : TowerOK`（`Wset.lean:4512`）は
`AR : Aop W u0 Wstar R` を `rcases` して分岐する（`Wset.lean:4527-4536` を読んだ）:

    節 1 `|R|<=1 ∧ lev R 0 = 0`                 … `domT` と矛盾（exfalso）
    節 2 `∀ n>=1, R⟦n⟧ ∈ Wstar`                 … **`TowerExp`**
    節 3 `∃ m<u0, domT R m ∧ ∀ y ∈ W m, based y → graft R y ∈ Wstar`
           srow=1 … `tower1_mem`（**証明ずみ**）
           srow=2 … **`TowerGraft2`**

★ **紙の上での予想（測る前に書く。外れたら報告する）**:

    `domT R m` ⟹ `¬ hasParent R (srow ...) (|R|-1)`  かつ  `lev R (|R|-1) = m+1 > 0`
    ⟹ `oper_eq_pred_of_noParent`（`Decrease.lean:37`、`|R|-1 ≠ 0` が要る）より
       **`|R| >= 2` なら `R⟦n⟧ = Pred R = R.dropLast`（全 `n`）**
    一方 `graft_nil`（`Wset.lean:76`、`@[simp]`）より **`graft R [] = R.dropLast`**
    そして `W_nil`（`:259`）と `based_nil`（`:74`）は**どちらも証明ずみ**

    ⟹ **節 3 に `y := []` を入れると節 2 が出る。つまり `|R| >= 2` では 節 3 ⟹ 節 2。**
    ⟹ **`TowerGraft2` が本当に要るのは `|R| = 1` の場合だけ**（そこでは `oper` が恒等で
       節 2 は `R ∈ Wstar` という別物になる）

これを実測で照合する。母集団は**定理が実際に見る形だけ**（教訓 19/20）:

    argOK R / R ≠ [] / z <= 1 / domT R m / hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R|
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def has_parent(S, i, j):
    return trio.parent(S, i, j) is not None


def oper_lean(M, n):
    """**Lean の `oper`（`Trio.lean:98`）**。`trio.expand` は長さ 1 で `[]` を返すが
    Lean は `j1 = 0` で **`M` そのもの（恒等）**。ここが唯一の差（`probe_cap2.py` の
    docstring と同じ）。長さ 1 の場面を数えるので、ここを間違えると偽の違反が出る。"""
    if len(M) - 1 == 0:
        return [tuple(c) for c in M]
    return [tuple(c) for c in trio.expand([list(c) for c in M], n)]


def graft(M, y):
    """`Wset.lean:67` の逐語訳。"""
    d = M[len(M) - 1][0] if M else 0
    return M[:-1] + [(p[0] + d, p[1], p[2]) for p in y]


def scene(R, v, z):
    """`towerOK_of` が実際に見る場面か。満たすなら m を返す。"""
    if not R or any(p[0] < 1 for p in R) or z > 1:
        return None
    j = len(R) - 1
    i1 = srow(R, j)
    if has_parent(R, i1, j):
        return None                                   # domT の ¬hasParent
    m = lev(R[j]) - 1
    if m < 0:
        return None                                   # domT の lev = m+1
    S = [(0, v, z)] + R
    if not has_parent(S, i1, len(S) - 1):
        return None                                   # 根が孤児を復活させる
    return m


def run(DS, BS, CS, VS, ZS, LS, NS, label):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    n = 0
    dist = Counter(); ident = Counter(); branch = Counter(); ex = {}
    t0 = time.time()
    for L in LS:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            for v in VS:
                for z in ZS:
                    m = scene(R, v, z)
                    if m is None:
                        continue
                    n += 1
                    j = len(R) - 1
                    i1 = srow(R, j)
                    dist[(L, i1)] += 1
                    dl = [tuple(c) for c in R[:-1]]
                    # ---- 予想の検算 ----
                    if L >= 2:
                        ok = all(oper_lean(R, nn) == dl for nn in NS)
                        ident['|R|>=2: R⟦n⟧ = R.dropLast/' +
                              ('ok' if ok else '**VIOL**')] += 1
                        if not ok:
                            ex.setdefault('oper≠dropLast', (R, v, z))
                    else:
                        ok = all(oper_lean(R, nn) == [tuple(c) for c in R]
                                 for nn in NS)
                        ident['|R|=1: R⟦n⟧ = R（恒等）/' +
                              ('ok' if ok else '**VIOL**')] += 1
                        if not ok:
                            ex.setdefault('|R|=1 で恒等でない', (R, v, z))
                    g = [tuple(c) for c in graft(R, [])]
                    ident['graft R [] = R.dropLast/' +
                          ('ok' if g == dl else '**VIOL**')] += 1
                    if g != dl:
                        ex.setdefault('graft R []≠dropLast', (R, v, z))
                    # ---- どの核が本当に要るか ----
                    if L >= 2:
                        branch['|R|>=2 ⟹ 節3 から節2 が出る ⟹ **TowerExp だけで足りる**'] += 1
                    elif i1 == 2:
                        branch['**|R|=1 かつ srow=2 ⟹ TowerGraft2 が要る**'] += 1
                        ex.setdefault('|R|=1 srow=2', (R, v, z, m))
                    else:
                        branch['|R|=1 かつ srow=1 ⟹ tower1_mem（証明ずみ）'] += 1
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s)  場面 **{n}** 件')
    if n == 0:
        print('  ⚠ 場面 0 件。母集団を疑うこと（教訓 11）'); return
    print('  -- (x2) (|R|, srow) の分布 --')
    for k in sorted(dist):
        print(f'     |R|={k[0]} srow={k[1]} : {dist[k]:10d}  ({100*dist[k]/n:5.1f}%)')
    print('  -- ★ 予想の検算 --')
    for k in sorted(ident):
        print(f'     {k:44s} {ident[k]:10d}')
    print('  -- ★★ (x1) どの核が本当に要るか --')
    for k in sorted(branch):
        print(f'     {k:52s} {branch[k]:10d}  ({100*branch[k]/n:5.1f}%)')
    for k in sorted(ex):
        print(f'  ex {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    run((1, 2, 3), (0, 1, 2, 3), (0, 1, 2), (0, 1, 2, 3), (0, 1),
        tuple(range(1, a.L + 1)), (1, 2, 3, 4, 5),
        f'R98 `TowerExp` は呼ばれるか |R|<={a.L}（列 36）')
