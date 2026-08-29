# -*- coding: utf-8 -*-
"""**課題 R98 —— 母集団問題の決着 ＋ 「残り何%」の測り直し。**

(WL) `Lift1 ((0,v,z)::R) d ∈ W (m+2d)` を落とす**仮定ゼロの定理 4 本**（全部緑）:

    1 `L53.liftStage_of_strict`（`L53Subst:1871`）  前提 `∀ p ∈ R, v < p.2.1`
    2 `L53.liftStage_of_noTie`（`:1665`）           前提 `∀ p ∈ R, p.2.1 ≠ v`
    3 `L53.liftTie_case_tieFree`（`:2615`）         前提 `1 <= entry X 1 0`（＝ `v>=1`）∧ `TieFree X`
    4 `L105.liftStage_of_zeroRow2`（`L105Cap:2036`）前提 `∀ p ∈ X, p.2.2 = 0`（**今日の新規**）

落ちなかったもの ＝ `L105.LiftTieCoreRow2`（`L105Cap:2056`）:
    タイあり ∧ `¬(v>=1 ∧ TieFree X)` ∧ `∃ p ∈ X, 0 < p.2.2`

定義（`Wtower2.lean:59` / `Cgraft.lean:301`）:
    `coneV A v j := ∀ y, y →*₀ j → v < entry A 1 y`      （`y = j` 自身も含む。`y = 0` も含む）
    `TieFree X  := ∀ j, coneV X (entry X 1 0 - 1) j → le1 X 0 j`

母集団は 2 つ出す（教訓 11）:
  (A) **構成的一様** … `LiftTieCore` の量化子そのもの（`∀ v z R, argOK R → …`）から
      `W` 前提だけを外したもの。**定理が引き受ける集合の上位集合**
  (B) **`TowerOK2` の場面** … `argOK R` ∧ `R≠[]` ∧ `z<=1` ∧ `domT R m` ∧ `srow=2` ∧
      `hasParent ((0,v,z)::R) 2 |R|`。H11 の 70,557 件と比べるため
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
    out = [j]
    while True:
        p = trio.parent(S, 0, out[-1])
        if p is None:
            break
        out.append(p)
    return out


def coneV(X, vv, j):
    """`∀ y →*₀ j, vv < entry X 1 y`（`y = j` も `y = 0` も含む）。"""
    return all(vv < X[y][1] for y in anc0(X, j))


def tiefree(X):
    """`∀ j, coneV X (entry X 1 0 - 1) j → le1 X 0 j`。"""
    v0 = X[0][1]
    thr = v0 - 1 if v0 >= 1 else 0
    for j in range(len(X)):
        if coneV(X, thr, j) and not trio.is_ancestor(X, 1, 0, j):
            return False
    return True


def classify(R, v, z):
    """4 本の仮定ゼロ定理で落ちるか。落ちなければ核。"""
    X = [(0, v, z)] + R
    if all(v < p[1] for p in R):
        return '1 狭義 Strict'
    if all(p[1] != v for p in R):
        return '2 無タイ（狭義でない）'
    if v >= 1 and tiefree(X):
        return '3 タイだが TieFree'
    if all(p[2] == 0 for p in X):
        return '4 行 2 ≡ 0（今日の新規）'
    return '5 **LiftTieCoreRow2 ← 核**'


def run(DS, BS, CS, VS, ZS, LS, pop, label):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    cls = Counter(); byv = Counter(); n = 0
    ex = {}
    t0 = time.time()
    for L in LS:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            if any(p[0] < 1 for p in R):
                continue
            for v in VS:
                for z in ZS:
                    if pop == 'tower':
                        j = len(R) - 1
                        i1 = srow(R, j)
                        if i1 != 2 or trio.parent(R, i1, j) is not None:
                            continue
                        if lev(R[j]) - 1 < 0:
                            continue
                        if trio.parent([(0, v, z)] + R, i1, len(R)) is None:
                            continue
                    n += 1
                    k = classify(R, v, z)
                    cls[k] += 1
                    tie = any(p[1] == v for p in R)
                    byv[(v, 'タイ' if tie else '非タイ')] += 1
                    if k.startswith('5'):
                        ex.setdefault('核の例', (R, v, z))
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s)  母数 **{n}**')
    if n == 0:
        print('  ⚠ 0 件'); return
    for k in sorted(cls):
        print(f'  {k:34s} {cls[k]:10d}  ({100*cls[k]/n:5.2f}%)')
    print('  -- (p2) `v` 別のタイ率 --')
    for vv in sorted({x[0] for x in byv}):
        t = byv[(vv, 'タイ')]; nt = byv[(vv, '非タイ')]
        if t + nt:
            print(f'     v={vv}: タイ {t:9d} / 全 {t+nt:9d} = {100*t/(t+nt):5.1f}%')
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
    run(DS, BS, CS, VS, ZS, LS, 'uniform',
        f'R98 (A) 構成的一様（`LiftTieCore` の量化子）|R|<={a.L}')
    run(DS, BS, CS, VS, ZS, LS, 'tower',
        f'R98 (B) `TowerOK2` の場面 |R|<={a.L}')
