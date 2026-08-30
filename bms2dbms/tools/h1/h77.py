# -*- coding: utf-8 -*-
"""**課題 H66 (o1) ＋ H64 (n3c): 節 3 は本当に死んでいるか／塔の繋ぎ目に何が要るか。**

⚠ **教訓 24 を先に当てた**（候補を測る前に `grep`）:

    `Wset.le1_take`（`Wset.lean:908`）… 私の §185 は**既に緑だった**。測定は不要だった
    `Wset.W_add`（`:1682`）… `rsum A B` が要る
    `Wset.W_flatMap_copies`（`:2552`）… **同一の**写しの連結（シフト無し）。塔はシフトつきなので直接は当たらない
    `L53.rsum_graft_iff`（`:2916`）… `graft` の連結が `rsum` になる条件の**厳密な iff**（既に緑）
    `L53.not_rsum_cons_root`（`:2900`）… 根つきでは `rsum` が破れる（既に緑）
    `Wset.W_drop`（`Wtower2:2870`）/ `W_segment`（`:2981`）… 部分列は無料（向きが逆）

⟹ **`rsum` が成り立つ条件そのものは測らない**（`rsum_graft_iff` が既に iff を与えている）。
**測るのは「塔のブロックの繋ぎ目で `rsum` を破る列が何本あるか」**。
1 本（＝ 根だけ）なら、要る道具は「根 1 本だけ例外を許す `W_add`」に絞れる。

## 測るもの

    (o1) `TowerExpBigRow2` の前提を満たす事例で、`domT ((0,v,z)::R) m` を満たす `m` はあるか
         （`lev = m+1` の連言まで込みで実測。無ければ**節 3 は死んでいる**）
    (o2) その事例で `R.dropLast` の `Aop` の節はどれか（節 1 / 節 2 / 節 3 の比率）
    (n3c) 塔 `S⟦n⟧ = B_0 ++ … ++ B_{n-1}` の繋ぎ目で **`rsum` を破る列は何本か**

⚠ 分母を必ず出す（教訓 23）。⚠ 100% は `|R|` を伸ばして壊す（教訓 21）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, levM, argOK
from h75 import oper
from collections import Counter


def domT_any(M):
    """`∃ m, domT M m`。`lev = m+1 >= 1` かつ末尾が自分の行で親なし。"""
    if not M:
        return False
    j = len(M) - 1
    return levM(M, j) >= 1 and not has_parent(M, srow(M, j), j)


def main(lens=(2, 3), vmax=3, dmax=4, bmax=3, nmax=3, tag=''):
    cols = [(d, b, c) for d in range(1, dmax) for b in range(bmax)
            for c in range(2)]
    print('### 母集団%s（列 = 行0∈[1,%d]・行1<%d・行2<2、`|R|` = %s、`v < %d`）'
          % (tag, dmax - 1, bmax, list(lens), vmax))
    print()
    den = Counter()
    o1 = Counter()
    n3c = Counter()
    ex = []
    checked = 0
    for L in lens:
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            m = dom_m(R)
            for v in range(vmax):
                for z in range(2):
                    checked += 1
                    if m is None:
                        continue
                    S = [(0, v, z)] + R
                    if not has_parent(S, srow(R, len(R) - 1), len(R)):
                        continue
                    # `TowerExpBigRow2`: 行 2 に非零がある
                    if not any(q[2] > 0 for q in S):
                        den['行 2 が全部 0（`…Row2` の前提を満たさない）'] += 1
                        continue
                    den['**前提を満たした（分母）**'] += 1
                    # ---- (o1) `domT ((0,v,z)::R) m` は成り立つか
                    o1['`domT ((0,v,z)::R) m` を満たす `m` が %s'
                       % ('**ある**' if domT_any(S) else 'ない')] += 1
                    o1['　うち `lev ((0,v,z)::R) (|R|) >= 1`: %s'
                       % ('はい' if levM(S, len(R)) >= 1 else 'いいえ')] += 1
                    # ---- (n3c) 塔の繋ぎ目で `rsum` を破る列
                    for n in (2, 3):
                        T = oper(S, n)
                        k = len(R)
                        if len(T) != n * k:
                            n3c['塔がブロック分割にならない'] += 1
                            continue
                        for b in range(1, n):
                            pre = T[:b * k]
                            blk = T[b * k:(b + 1) * k]
                            r0 = blk[0][0]
                            bad = [j for j, p in enumerate(pre + blk)
                                   if p[0] < r0]
                            n3c['繋ぎ目 %d/%d: `rsum` を破る列 = %d 本'
                                % (b, n, len(bad))] += 1
                            n3c['　破る列は**根だけ**か: %s'
                                % ('**はい**' if bad == [0] else
                                   'いいえ（%d 本）' % len(bad))] += 1
                            if bad != [0] and bad and len(ex) < 5:
                                ex.append((R, v, z, n, b, T, bad))
    print('検査した `(R,v,z)`: **%d**' % checked)
    print()
    wref.tally(den, '前提の充足（教訓 23）')
    wref.tally(o1, '(o1) 節 3（`domT`）は生きているか')
    wref.tally(n3c, '(n3c) 塔の繋ぎ目で `rsum` を破る列の本数')
    for R, v, z, n, b, T, bad in ex:
        print('    根だけでない例: R=`%s` v=%d z=%d n=%d 繋ぎ目=%d 破る列=%s'
              % (fmt(R), v, z, n, b, bad))
        print('        T=`%s`' % fmt(T))
    print()


if __name__ == '__main__':
    print('## H66 (o1) ＋ H64 (n3c)')
    print()
    main(lens=(2,), tag='（`|R|` = 2）')
    main(lens=(3,), tag='（`|R|` = 3）')
    print('## ⚠ 教訓 21: `|R| = 4` で壊れないか')
    print()
    main(lens=(4,), vmax=2, dmax=3, bmax=2, tag='（`|R|` = 4、列は狭め）')
