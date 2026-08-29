# -*- coding: utf-8 -*-
"""**課題 R99 —— L3 の反証可能な予測（`le1_root_of_rtg0` / §30）の検証。**

L3 の予測:

> **食い違う列（＝ `Lift1 X d` で行 1 が上がらない列 ＝ 錐の外）は、必ずブロッカー
> （行 1 <= `v` の列）を行 0 祖先に持つ。しかも錐の外の集合は、ブロッカーたちの
> 行 0 部分木の合併に *ちょうど* 等しい。**（`v` = 根の行 1、`X = (0,v,z) :: R`）

  (r1) 錐の外 ⟹ ブロッカーを行 0 祖先に持つ                （片側）
  (r2) ブロッカーの行 0 部分木の合併 ⟹ 錐の外              （もう片側。強い）
  (r3) 一致しない最小の事例

★ 紙の上での予想（測る前に書く）: **両方 100% のはず。** `Lcone.lean:36` `le1_zero_iff`（緑）

    根が真に最浅なら `le1 A 0 j ⟺ ∀ y, y →*₀ j, y ≠ 0 → entry A 1 0 < entry A 1 y`

の**否定を取っただけ**だから:

    `¬ le1 X 0 j ⟺ ∃ y ∈ anc0(j), y ≠ 0, entry X 1 y <= v`
                ⟺ **`j` はブロッカー `y` の行 0 部分木に入る**

⟹ (r1)(r2) は `le1_zero_iff` の言い換え。**外れたら私か L3 のどちらかが定義を読み違えている。**

⚠ `le1_zero_iff` の前提は「根が真に最浅」。`X = (0,v,z)::R` で `argOK R` なら自動。
   **`argOK` を外した対照**も置く（外すと壊れるはず ⟹ 前提が本質という証拠）。
⚠ 教訓 21: 100% が出たら 1 段長い `|R|` で壊してみる。
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


def run(DS, BS, CS, VS, ZS, LS, pop, label, argok=True):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    n = 0
    r = Counter(); ex = {}
    t0 = time.time()
    for L in LS:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            if argok and any(p[0] < 1 for p in R):
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
                    X = [(0, v, z)] + R
                    # 錐の外
                    out = {j for j in range(len(X))
                           if not trio.is_ancestor(X, 1, 0, j)}
                    # ブロッカー（根以外で行 1 <= v）とその行 0 部分木の合併
                    blk = {y for y in range(1, len(X)) if X[y][1] <= v}
                    sub = {j for j in range(len(X))
                           if any(y in anc0(X, j) for y in blk)}
                    r['(r1) 錐の外 ⊆ 部分木/' + ('ok' if out <= sub else '**VIOL**')] += 1
                    r['(r2) 部分木 ⊆ 錐の外/' + ('ok' if sub <= out else '**VIOL**')] += 1
                    r['(r1∧r2) 一致/' + ('ok' if out == sub else '**VIOL**')] += 1
                    if out != sub:
                        key = ('r1 破れ' if not (out <= sub) else 'r2 破れ')
                        if key not in ex or len(X) < len(ex[key][0]):
                            ex[key] = (X, v, z, sorted(out), sorted(sub), sorted(blk))
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s)  母数 **{n}**')
    for k in sorted(r):
        print(f'  {k:34s} {r[k]:10d}')
    for k in sorted(ex):
        print(f'  ★ 最小の {k}: X={ex[k][0]} v={ex[k][1]} z={ex[k][2]}')
        print(f'      錐の外={ex[k][3]}  部分木={ex[k][4]}  ブロッカー={ex[k][5]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    DS, BS, CS = (1, 2, 3), (0, 1, 2, 3), (0, 1, 2)
    VS, ZS = (0, 1, 2, 3), (0, 1)
    LS = tuple(range(1, a.L + 1))
    run(DS, BS, CS, VS, ZS, LS, 'tower', f'R99 (P-tower) |R|<={a.L}')
    run(DS, BS, CS, VS, ZS, LS, 'uniform', f'R99 (P-uniform, argOK あり) |R|<={a.L}')
    run((0, 1, 2, 3), BS, CS, VS, ZS, LS, 'uniform',
        f'R99 **対照: argOK を外す（行 0 = 0 を許す）** |R|<={a.L}', argok=False)
