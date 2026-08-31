# -*- coding: utf-8 -*-
"""課題 R80: **`PrefixCopies`（`j0 ≠ 0`）が残核に落ちるか。**

`expfam`（`oper_unfold`）より `M⟦n⟧ = A0 ++ concat_k (Q0 + k*D)`、
`A0 = M.take j0`、**`Q0 = M[j0 : j1]`（`j1 = |M|-1`）**。

    **`|Q0| = 1`（＝ `j0 = j1 - 1`）** のとき
      `S := M⟦1⟧ = M.dropLast = A0 ++ [q]`、`p := j0 = |S|-1`、
      `C := [q, q+D, …, q+(n-1)D]`
    ⟹ `M⟦n⟧ = S.take p ++ C ++ S.drop (p+1)` ＝ **残核 `Subst1gRevive` の形そのもの**

`|Q0| >= 2` は 1 列の差し替えにならないので残核は直に当たらない。
"""
import sys
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from r79 import badroot


def audit(P, name):
    c = Counter(); N = 0
    for M in P:
        M = tuple(map(tuple, M))
        j0 = badroot(M)
        if j0 is None or j0 == 0:
            continue                       # `j0 = 0` は無料（R79）
        N += 1
        j1 = len(M) - 1
        q = j1 - j0                        # |Q0|
        c['**|Q0| = 1（＝ j0 = j1-1）⟹ 残核の形**' if q == 1 else
          ('|Q0| = 2' if q == 2 else '|Q0| >= 3')] += 1
        if q == 1:
            A0 = M[:j0]
            # 残核の 4 条件（S = M.dropLast, p = j0, C = [q, q+D, ...]）
            c['   (1) entry C 0 0 = entry S 0 p  **自動**'] += 1
            c['   (2) 全 c in C, entry S 0 p <= c.1  **自動**（D >= 0）'] += 1
            c['   (3) lev C 0 <= lev S p  **自動**（等号）'] += 1
            c['   (4) **S.take p に行 2 > 0 の列がある**' if any(p2[2] > 0 for p2 in A0)
              else '   (4) **S.take p に行 2 > 0 の列が無い ⟹ 前提が偽**'] += 1
    print('== %s（`j0 != 0` が %d 件）' % (name, N), flush=True)
    for k in sorted(c, key=str):
        print('   %-52s %d (%.1f%%)' % (k, c[k], 100.0 * c[k] / N), flush=True)


if __name__ == '__main__':
    from rows3 import gen3
    from book import load_book
    audit([b for *_, b, _ in load_book()], 'ブックのラダー（最大 44 列）')
    for L in (6, 8):
        audit(gen3('BMS', L, zcap=1), '`ST_TS` 標準形 len<=%d' % L)
