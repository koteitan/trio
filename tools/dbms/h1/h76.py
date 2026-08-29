# -*- coding: utf-8 -*-
"""**課題 H64 (n2): 孤児でなくなったとき `oper` は何になるか。**

`|R| = 1` の証明の鎖は「孤児 ⟹ `oper` は `Pred` ⟹ 根まで剥ける」だった。
§192 で **`|R| >= 2` では `srow = 2` の非孤児が 27〜33% 現れる**と分かったので、
その枝で `oper`（`Trio.lean:98`）が何になるかを見る:

    `j1 = |M|-1`；`j1 = 0` → `M` そのもの
    末尾が全零 → `Pred M`
    `¬hasParent M (srow M j1) j1` → `Pred M`      ← **`|R|=1` はここしか通らない**
    それ以外 → **`M.take j0 ++ (range n).flatMap …`**（コピー枝）

**測るもの:**

    (n2a) コピー枝に入ったとき、**バッドルート `j0` はどこか**
          とくに **`j0 = 0`（根そのもの）か `j0 >= 1` か**
          （L3: **`j0 >= 1` は `oper_cons_nat` で「尾が展開された同じ目標」に落ちる**
          　 ⟹ **`j0 = 0` が本当の新しさ**）
    (n2b) `oper` を繰り返すと何歩で長さ <= 1 に落ちるか（`Pred` の鎖は復活するか）
    (n2c) 途中で `Pred` 枝に戻るか、コピー枝が続くか

⚠ 母集団は `TowerExpBig` の構文の前提を満たすものだけ。**分母を出す**（教訓 23）。
⚠ `oper` は長さ 1 で恒等（`trio.expand` の罠）。⚠ 教訓 21: 100% は 1 段長い母集団で壊す。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m
from h75 import oper
from collections import Counter

MAXSTEP = 40
MAXLEN = 60


def badroot(M):
    """`oper` がコピー枝に入るときのバッドルート `j0`（`Pred` 枝なら None）。"""
    if len(M) <= 1:
        return None
    j1 = len(M) - 1
    if all(x == 0 for x in M[j1]):
        return None
    i1 = srow(M, j1)
    return trio.parent(list(M), i1, j1)


def main(lens=(2, 3), vmax=3, dmax=4, bmax=3, nmax=3, tag=''):
    cols = [(d, b, c) for d in range(1, dmax) for b in range(bmax)
            for c in range(2)]
    print('### 母集団%s（列 = 行0∈[1,%d]・行1<%d・行2<2、`|R|` = %s、`v < %d`）'
          % (tag, dmax - 1, bmax, list(lens), vmax))
    print()
    den = Counter()
    a = Counter()
    b = Counter()
    ex = []
    for L in lens:
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            m = dom_m(R)
            if m is None:
                continue
            for v in range(vmax):
                for z in range(2):
                    S = [(0, v, z)] + R
                    if not has_parent(S, srow(R, len(R) - 1), len(R)):
                        continue
                    den['**前提を満たした `(R,v,z)`（分母）**'] += 1
                    for n in range(1, nmax + 1):
                        T = oper(S, n)
                        j0 = badroot(T)
                        if j0 is None:
                            a['`|R|`=%d / `S⟦n⟧` は `Pred` 枝（孤児 or 全零）' % L] += 1
                            continue
                        a['`|R|`=%d / コピー枝 / **`j0` = %s**'
                          % (L, '**0（根）**' if j0 == 0 else '>= 1')] += 1
                        a['`|R|`=%d / コピー枝 / `srow` = %d'
                          % (L, srow(T, len(T) - 1))] += 1
                        if j0 == 0 and len(ex) < 6:
                            ex.append((R, v, z, n, T))
                        # ---- (n2b) 繰り返して何歩で落ちるか
                        U = list(T)
                        steps = 0
                        pred_again = False
                        while len(U) > 1 and steps < MAXSTEP and len(U) <= MAXLEN:
                            if badroot(U) is None:
                                pred_again = True
                            U = oper(U, n)
                            steps += 1
                        b['`|R|`=%d / %s' % (L, ('長さ <= 1 に落ちた（%d 歩以内）' % MAXSTEP)
                                             if len(U) <= 1
                                             else '**予算内に落ちない**')] += 1
                        b['`|R|`=%d / 途中で `Pred` 枝に戻る: %s'
                          % (L, 'はい' if pred_again else '**いいえ**')] += 1
    wref.tally(den, '前提の充足（教訓 23）')
    wref.tally(a, '(n2a) `oper` の枝と バッドルート `j0`')
    wref.tally(b, '(n2b)(n2c) 繰り返したときの挙動')
    for R, v, z, n, T in ex:
        print('    `j0 = 0` の例: R=`%s` v=%d z=%d n=%d' % (fmt(R), v, z, n))
        print('        S⟦n⟧=`%s`' % fmt(T))
    print()


if __name__ == '__main__':
    print('## (n2) 孤児でなくなったとき `oper` は何になるか')
    print()
    main(lens=(1,), tag='（`|R|` = 1 —— 対照）')
    main(lens=(2,), tag='（`|R|` = 2）')
    main(lens=(3,), tag='（`|R|` = 3）')
    print('## ⚠ 教訓 21: `|R| = 4` で壊れないか')
    print()
    main(lens=(4,), vmax=2, dmax=3, bmax=2, tag='（`|R|` = 4、列の範囲は狭め）')
