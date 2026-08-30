# -*- coding: utf-8 -*-
"""**課題 R139 —— `PrefixCopiesOpen` の展開（列の等式。番人が付く的）。**

**主語（`L53Subst:3599` / `:3803` から逐語）:**

    `PrefixCopies : ∀ u n A Q, A ++ Q ∈ W u → **(∀ q ∈ Q, entry Q 0 0 <= q.1)**
                    → A ++ (range n).flatMap (fun _ => Q) ∈ W u`
    `PrefixCopiesOpen` … 上に **`(∃ q ∈ A, q.1 < entry Q 0 0)`** を足した版

**場面**（§R149 で 4 条件とも 100% と確認済み）:
`T = shTower Q e n`、`j0 >= 1`、**`A = T.take j0`**、**`D = T.drop j0`**。
⚠ **`PrefixCopies` の側条件 `∀ q ∈ D, entry D 0 0 <= q.1`（`D` の根が `D` の中で行 0 最小）
も課す。これは §R149 では測っていない。まず分母を数える（教訓 23）。**

**L3 の見立て（§125、証明はしていない）:**
> `D` が段内に親を持てば `comm_of_hasParentInBlock` で
> **`(A ++ D^m)⟦m'⟧ = (A ++ D^(m-1)) ++ D⟦m'⟧`**
> ⟹ 底は **`A ++ D^(m-1) ++ [D の先頭列]`**

## ★ 反例の形を先に書く（教訓 45）＋ 充足率の見積もり（L3 の §105.2）

> **L3 の見立ての前提は「`A ++ D^m` の末尾列の親が**最後のコピーの中**にある」。**
>
> **⚠ 反例の形: 「末尾列の親が、最後の `D` のコピーの外（前のコピー、または `A`）にある」。**
> **⚠ 私の見積もり: `D^m` は**平坦なコピー**（ずらし無し）なので、
> 前のコピーの同じ列は行 0 が**等しく**、`nextrel0` の狭義増加を満たさない。
> ⟹ 前のコピーに逃げるのは難しいはず。**破れは 5 〜 20%** と見積もる。**
> **⚠ ただし `A` に逃げる可能性はある（`A` は行 0 が浅い列を含む）。そこが主な破れ元と予想。**

**箱と単位**: 単位 `(Q, e, n, j0, m, m')`。箱 = 行0 ∈ 1..3、行1 < 3、行2 = 0、
`|Q| = 2..4`、`e ∈ 1..3`、`n ∈ 1..3`、`m ∈ 1..5`、`m' ∈ 1..3`。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r98 import oper_lean


def shTower(Q, e, n):
    return [(c[0] + k * e, c[1], c[2]) for k in range(n) for c in Q]


def run(L, ES, NS, MS, MPS, R1):
    COL = [(a, b, 0) for a in range(1, 4) for b in range(R1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for v in range(R1):
        for t in itertools.product(COL, repeat=L - 1):
            Q = [(0, v, 0)] + list(t)
            for e in ES:
                for n in NS:
                    T = shTower(Q, e, n)
                    for j0 in range(1, len(T)):
                        A = T[:j0]; D = T[j0:]
                        if not D:
                            continue
                        c['(前提を課す前の) 分母'] += 1
                        # `PrefixCopies` の側条件
                        if not all(D[0][0] <= p[0] for p in D):
                            c['⚠ 側条件で落ちた'] += 1
                            continue
                        c['★ 母集団（側条件つき）'] += 1
                        for m in MS:
                            S = list(A)
                            for _ in range(m):
                                S += D
                            last = len(S) - 1
                            sr = srow(S, last)
                            par = trio.parent(S, sr, last)
                            base = len(A) + (m - 1) * len(D)   # 最後のコピーの先頭
                            if par is None:
                                c[('末尾列', m, '孤児')] += 1
                            elif par >= base:
                                c[('末尾列', m, '★ 親は最後のコピーの中')] += 1
                            elif par >= len(A):
                                c[('末尾列', m, '⚠ 親は前のコピー')] += 1
                            else:
                                c[('末尾列', m, '⚠ 親は A の中')] += 1
                                ex.setdefault('親が A', (Q, e, n, j0, m, par))
                            for mp in MPS:
                                lhs = oper_lean(S, mp)
                                pre = list(A)
                                for _ in range(m - 1):
                                    pre += D
                                rhs = pre + oper_lean(D, mp)
                                c[('★ L3 の見立て', m, lhs == rhs)] += 1
                                if lhs != rhs:
                                    ex.setdefault(('破れ', m), (Q, e, n, j0, m, mp, par, base))
    tot = c['★ 母集団（側条件つき）']
    print(f'### |Q|={L} 行1<{R1}  前提前 {c["(前提を課す前の) 分母"]:8d} → '
          f'**側条件を通った {tot:8d}**（{100*tot/max(c["(前提を課す前の) 分母"],1):5.1f}%）  [{time.time()-t0:.1f}s]')
    if not tot:
        print('  （0 件）\n'); return
    for m in MS:
        row = {k[2]: c[k] for k in c if isinstance(k, tuple) and len(k) == 3 and k[0] == '末尾列' and k[1] == m}
        y = c[('★ L3 の見立て', m, True)]; nn = c[('★ L3 の見立て', m, False)]
        if y + nn:
            print(f'  m={m}: **見立て成立 {y:8d} / {y+nn} ({100*y/(y+nn):6.2f}%)**  '
                  f'破れ {nn:7d}   末尾列の親: {row}')
    for k in sorted(ex, key=str):
        print(f'      例 {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for R1 in (3,):
        for L in range(2, a.L + 1):
            run(L, (1, 2, 3), (1, 2, 3), (1, 2, 3, 4, 5), (1, 2, 3), R1)
