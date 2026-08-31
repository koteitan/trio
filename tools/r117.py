# -*- coding: utf-8 -*-
"""**課題 R114 —— `v = 0` の残核 (δ) の構造。所属の判定はしない（H12 の警告）。**

⚠ **測る前に書く（教訓 45）。反例の形と予想:**

  (r2) 錐の形 … `v=0` では `le1_zero_iff`（緑、`y ≠ 0` の除外つき）より
       **`j` が錐 ⟺ `j` の行 0 祖先のうち根以外が全部 行 1 >= 1**。
       **予想: 接尾辞ではない**（H12 の §184 と同じ）。
       **反例の形**「錐に入る列の前に錐に入らない列がある」が母集団にあるかを数える。
  (r3) 葉の形 … **§R94 の定理より `oper` は第 1 列を落とさない** ⟹
       **到達する単元は `[(0,0,z)]` だけ**（`lev = z`）。
       ⟹ **葉の形は測るまでもなく決まっている。** ここは検算だけ。
       **本当に測る価値があるのは「木が底に着くか」だが、それは有限では判定できない（R94）。**
       ⟹ **代わりに `n = 1` の 1 本道**（`oper` が長さを増やさない枝）を追う。

**箱**（2 つ。教訓 27 で行 2 の軸を振る）:
  (a) 列 行0∈[1,2]×行1∈[0,2]×**行2∈[0,1]**、`v = 0`、`z∈[0,1]`
  (b) 列 行0∈[1,3]×行1∈[0,3]×**行2∈[0,2]**、`v = 0`、`z∈[0,1]`
**単位**: 明記する（事例／列／ステップ）。**分母**: 明記。**全数**（サンプリングなし）。
**除外条件**: `le1_zero_iff` の `y ≠ 0`（塔の根）を必ず除外する。
**母集団**: `TowerExpBigRow2` の前提を全部 ＋ `srow=2` ＋ `v=0` ＋ **(δ)（ブロッカーあり）**。
⚠ `R.dropLast ∈ Wstar` は有限で判定できない（R94）ので落とした**上位集合**。
"""
import sys, itertools, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r98 import oper_lean


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


def scene(COL, ZS, Ls):
    """`TowerExpBigRow2` の前提 ＋ `srow=2` ＋ `v=0` ＋ (δ)。"""
    for L in Ls:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            if any(p[0] < 1 for p in R):
                continue
            j = len(R) - 1
            i1 = srow(R, j)
            if i1 != 2 or trio.parent(R, i1, j) is not None or lev(R[j]) - 1 < 0:
                continue
            v = 0
            for z in ZS:
                if trio.parent([(0, v, z)] + R, i1, len(R)) is None:
                    continue
                if not any(p[2] != z for p in R[:-1]):
                    continue
                if not any(p[1] <= v for p in R[:-1]):
                    continue                      # (δ): ブロッカーあり（v=0 ⟹ タイ）
                yield R, v, z


def run(COL, ZS, Ls, label):
    c = Counter(); ex = {}
    for R, v, z in scene(COL, ZS, Ls):
        X = [(0, v, z)] + R
        L = len(X)
        c[('分母(事例)', z)] += 1
        # ---- (r1) ブロッカーの位置（単位: 列） ----
        blk = [i for i in range(1, L) if X[i][1] <= v]
        for i in blk:
            c[('r1 ブロッカーの相対位置', f'{int(10*(i-1)/max(L-2,1))//3}/3')] += 1
            c[('r1 ブロッカーの行 0',
               'd と同じ' if X[i][0] == X[L-1][0] else
               'd より浅い' if X[i][0] < X[L-1][0] else 'd より深い')] += 1
        c[('r1 ブロッカーの本数', min(len(blk), 4))] += 1
        # ---- (r2) 錐の形（単位: 事例） ----
        cone = [j for j in range(L) if trio.is_ancestor(X, 1, 0, j)]
        # 検算: le1_zero_iff（y ≠ 0 を除外）
        for j in range(L):
            lhs = j in cone
            rhs = all(X[y][1] > v for y in anc0(X, j) if y != 0)
            c[('r2 le1_zero_iff 検算', 'ok' if lhs == rhs else '**不一致**')] += 1
        iv = 0
        for a in range(L):
            if a in cone and (a == 0 or (a - 1) not in cone):
                iv += 1
        c[('r2 錐の極大区間の本数', min(iv, 4))] += 1
        c[('r2 錐は接尾辞か',
           'はい' if cone and cone == list(range(cone[0], L)) else '**いいえ**')] += 1
        if cone and cone != list(range(cone[0], L)):
            ex.setdefault('錐が接尾辞でない', (R, z, cone, L))
        # ---- (r3) 葉の形 ＋ n=1 の 1 本道 ----
        cur = list(X); steps = 0
        while len(cur) > 1 and steps < 60:
            cur = oper_lean(cur, 1)
            steps += 1
        c[('r3 n=1 で単元に到達', 'した' if len(cur) <= 1 else '**60 歩で未到達**')] += 1
        if len(cur) == 1:
            c[('r3 葉の形', 'X[0] と同じ' if tuple(cur[0]) == tuple(X[0])
               else f'**別の列 {cur[0]}**')] += 1
            c[('r3 葉の lev', lev(cur[0]))] += 1
            c[('r3 n=1 の歩数', min(steps, 8))] += 1
    print(f'### {label}')
    for key in ('分母(事例)', 'r1 ブロッカーの相対位置', 'r1 ブロッカーの行 0',
                'r1 ブロッカーの本数', 'r2 le1_zero_iff 検算', 'r2 錐の極大区間の本数',
                'r2 錐は接尾辞か', 'r3 n=1 で単元に到達', 'r3 葉の形', 'r3 葉の lev',
                'r3 n=1 の歩数'):
        sub = {k[1]: n for k, n in c.items() if k[0] == key}
        if not sub:
            continue
        s = sum(sub.values())
        print(f'  -- {key}（分母 {s}） --')
        for k in sorted(sub, key=str):
            print(f'     {str(k):24s} {sub[k]:9d}  ({100*sub[k]/s:5.2f}%)')
    for k in sorted(ex):
        print(f'  ★ {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    Ls = tuple(range(2, a.L + 1))
    run([(d, b, c) for d in (1, 2) for b in (0, 1, 2) for c in (0, 1)],
        (0, 1), Ls, f'R114 (a) 箱 行2<=1／`v=0`／(δ)／|R|<={a.L}／全数')
    run([(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2, 3) for c in (0, 1, 2)],
        (0, 1), (2, 3), 'R114 (b) 箱 **行2<=2**／`v=0`／(δ)／|R|<=3／全数')
