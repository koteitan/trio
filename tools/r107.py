# -*- coding: utf-8 -*-
"""**課題 (r4) ＋ R104 —— 塔の周期構造。`shTower` の形になるか、周期の 1 単位は何か。**

`graft R y = R.dropLast ++ (y を行 0 で `d := entry R 0 (|R|-1)` だけずらしたもの)`（`Wset:67`）
`oper_cons_tower2`（`Wset:3231`、緑）:
    `X⟦k+1⟧ = (0,v,z) :: graft R (Lift1 (X⟦k⟧) D1)`,  `D1 = entry R 1 (|R|-1) - v`
             = **`B ++ shiftr01 d 0 (Lift1 (X⟦k⟧) D1)`**,  `B := (0,v,z) :: R.dropLast`

⟹ **周期の 1 単位は `B = (0,v,z) :: R.dropLast`（長さ `|R|`）**のはず。測って確かめる。

  (r4-a) `X⟦n⟧ = concat_{j<n} shiftr01 (j*d) (j*D1) B`（**一様版**）か
  (r4-b) 一様でないなら `concat_{j<n} Lift1^j (shiftr01 (j*d) 0 B)`（**錐版**）か
  (p1)   周期は `n` を伸ばしても保たれるか
  (p3)   `d0`（`Cnf.lean:1060`）は何で決まるか
  (p4) ★ L3 の「行 2 が `z, (R.dropLast の行 2), z, … と周期的」と、私の (y8) の
        「周期 2 のブロック」は**同じものか**。同じなら周期は `|R|` のはず

⚠ `srow=1` は L3 が `tow v z R n = shTower ((0,v,z)::R.dropLast) e n`（緑）を出している。
   `srow=2` は `Lift1` が入るのでそのままではないはず。**両方測る。**
⚠ `Trio.lean:98` の `oper`。⚠ 教訓 21: 100% は `|R|` / `n` を伸ばして壊す。
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r98 import oper_lean


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def Lift1(X, dd):
    return [(c[0], c[1] + (dd if trio.is_ancestor(X, 1, 0, i) else 0), c[2])
            for i, c in enumerate(X)]


def sh(Q, d0, d1):
    return [(c[0] + d0, c[1] + d1, c[2]) for c in Q]


def run(DS, BS, CS, VS, ZS, LS, NS, label):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    n = 0
    r = Counter(); ex = {}
    t0 = time.time()
    for L in LS:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            if any(p[0] < 1 for p in R):
                continue
            j = len(R) - 1
            i1 = srow(R, j)
            if trio.parent(R, i1, j) is not None or lev(R[j]) - 1 < 0:
                continue
            for v in VS:
                for z in ZS:
                    X = [(0, v, z)] + R
                    if trio.parent(X, i1, len(R)) is None:
                        continue
                    n += 1
                    d = R[j][0]
                    D1 = R[j][1] - v if i1 == 2 else 0
                    B = [(0, v, z)] + R[:-1]
                    for nn in NS:
                        T = oper_lean(X, nn)
                        uni = []
                        for jj in range(nn):
                            uni += sh(B, jj * d, jj * D1)
                        r[f'srow={i1} (r4-a) 一様 shTower/' +
                          ('ok' if T == uni else '**破れる**')] += 1
                        # 錐版: Lift1 を jj 回かける
                        cone = []
                        cur = list(B)
                        for jj in range(nn):
                            cone += sh(cur, jj * d, 0)
                            cur = Lift1(cur, D1)
                        r[f'srow={i1} (r4-b) 錐版 shTower/' +
                          ('ok' if T == cone else '**破れる**')] += 1
                        # (p4) 行 2 の周期性: 周期 |R| か
                        row2 = [c[2] for c in T]
                        per = len(B)
                        r[f'srow={i1} (p4) 行 2 の周期 = |R|/' +
                          ('ok' if all(row2[i] == row2[i % per]
                                       for i in range(len(row2))) else '**破れる**')] += 1
                        # 全体の周期性（行 0 のずれを除いて）
                        okper = (len(T) == nn * per and
                                 all(T[jj * per + q][1:] == T[q][1:]
                                     for jj in range(nn) for q in range(per)))
                        r[f'srow={i1} (p1) 行 1・行 2 が周期 |R|/' +
                          ('ok' if okper else '**破れる**')] += 1
                        if T != uni and f'srow={i1} 一様破れ' not in ex:
                            ex[f'srow={i1} 一様破れ'] = (R, v, z, nn, T, uni)
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s)  場面 **{n}**')
    for k in sorted(r):
        print(f'  {k:44s} {r[k]:10d}')
    for k in sorted(ex):
        print(f'  ★ {k}: R={ex[k][0]} v={ex[k][1]} z={ex[k][2]} n={ex[k][3]}')
        print(f'      実際 = {ex[k][4]}')
        print(f'      一様 = {ex[k][5]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=3)
    a = ap.parse_args()
    run((1, 2, 3), (0, 1, 2, 3), (0, 1), (0, 1, 2, 3), (0, 1),
        tuple(range(1, a.L + 1)), (1, 2, 3, 4, 5),
        f'R104/(r4) 塔の周期構造 |R|<={a.L}（断片 行2<=1）')


def run2(DS, BS, CS, VS, ZS, LS, NS, label):
    """一様版が破れる条件 ＝ `B` にブロッカー（行 1 <= v の列、根以外）があること？"""
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    r = Counter(); ex = {}
    for L in LS:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            if any(p[0] < 1 for p in R):
                continue
            j = len(R) - 1
            i1 = srow(R, j)
            if i1 != 2 or trio.parent(R, i1, j) is not None or lev(R[j]) - 1 < 0:
                continue
            for v in VS:
                for z in ZS:
                    X = [(0, v, z)] + R
                    if trio.parent(X, i1, len(R)) is None:
                        continue
                    d = R[j][0]; D1 = R[j][1] - v
                    B = [(0, v, z)] + R[:-1]
                    blk = any(p[1] <= v for p in R[:-1])     # B のブロッカー
                    for nn in NS:
                        T = oper_lean(X, nn)
                        uni = []
                        for jj in range(nn):
                            uni += sh(B, jj * d, jj * D1)
                        same = (T == uni)
                        r[f'ブロッカー{"あり" if blk else "なし"} × 一様'
                          f'{"一致" if same else "破れる"}'] += 1
                        if blk != (not same) and 'ずれ' not in ex and nn >= 2:
                            ex['ずれ'] = (R, v, z, nn, blk, same, T, uni)
    print(f'### {label}')
    for k in sorted(r):
        print(f'  {k:38s} {r[k]:10d}')
    for k in sorted(ex):
        print(f'  ⚠ {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    run2((1, 2, 3), (0, 1, 2, 3), (0, 1), (0, 1, 2, 3), (0, 1),
         tuple(range(1, 4)), (2, 3, 4, 5),
         '★ 一様版が破れる ⟺ `B` にブロッカー（行 1 <= v）があるか')
