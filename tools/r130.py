# -*- coding: utf-8 -*-
"""**課題 R130（L3 の依頼）—— 復活したとき、親はどのブロックにいるか。**

**主語**: `T = mTower Q d e n`、`j = |T|-1`（塔の末尾列）。
`Q` が**ブロック内で孤児**（`¬ HasParentInBlock Q`）なのに
**`hasParent T (srow T j) j`** が成り立つ場合（＝ §R132 の (z5) の破れ、F2b のみ）に、
**親 `p = parent T (srow T j) j` がどのブロックにいるか。**

    `k_parent = p // |Q|`   `q_parent = p % |Q|`   `戻り = (n-1) - k_parent`

**(d5) 反例の形を先に書く（教訓 45）:**

⚠ **私の §R132 の箱は `n ∈ {2,3,4}` だったが、`n = 2` では
「第 0 ブロック」と「1 つ前のブロック（`n-2`）」が同じものになる。**
**⟹ 私の最小反例（`n=2` で親が index 1）は、どちらの仮説とも矛盾しない。**
**`n >= 3` で初めて分かれる。** ⟹ **(d3) がこの課題の心臓。**

    **仮説 H0「常に第 0 ブロック」**   … `k_parent = 0` が 100%
    **仮説 H1「常に 1 つ前のブロック」** … `戻り = 1` が 100%
    **仮説 H2「その中間もある」**      … `k_parent` が散らばる

**もし H1 なら L3 の「`Q` と最後のブロックの 2 つだけで書ける」は成り立たない**
（`Q` ではなく「1 つ前のブロック」が要る。ただし形は同じ `Q` のリフトなので直せる）。

**箱と単位**: 単位 = `(Q, d, e, n)` で破れたもの。
箱 = 行0<4, 行1<3, 行2<=cm（**3 段**）、`|Q| = 2..5`、`d,e ∈ 0..3`、**`n ∈ {2,3,4,5}`**。
母集団 = `2<=|Q|` ∧ **根が狭義最浅** ∧ **ブロック内で孤児**。**`W` 所属は判定しない。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r126 import srow, hasP, classify
from r113 import mTower


def run(cm, L, DE, NS):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            if hasP(Q):
                continue                                   # ブロック内で孤児だけ
            i, fs = classify(Q)
            tag = '+'.join(f.split()[0] for f in fs)
            for d in DE:
                for e in DE:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        j = len(T) - 1
                        p = trio.parent(T, srow(T, j), j)
                        c[('分母', n)] += 1
                        if p is None:
                            continue
                        kp, qp = divmod(p, L)
                        back = (n - 1) - kp
                        c[('破れ', n)] += 1
                        c[('k_parent', kp)] += 1
                        c[('戻り', back)] += 1
                        c[('q_parent', qp)] += 1
                        c[('形', tag)] += 1
                        c[('n 別 k_parent', n, kp)] += 1
                        ex.setdefault((n, kp), (Q, d, e, n, p))
    tot = sum(c[('分母', n)] for n in NS); br = sum(c[('破れ', n)] for n in NS)
    print(f'### 行2<={cm} |Q|={L}  分母 {tot:9d}  **破れ {br:7d}** '
          f'({100*br/max(tot,1):5.3f}%)  [{time.time()-t0:.1f}s]')
    if br == 0:
        return
    print('  **(d1) 親のブロック `k_parent`**: ', end='')
    print('  '.join(f'k={k}: {c[("k_parent", k)]}' for k in sorted(
        kk[1] for kk in c if isinstance(kk, tuple) and len(kk) == 2 and kk[0] == 'k_parent')))
    print('  **戻り (n-1)-k_parent**: ', end='')
    print('  '.join(f'{b} つ前: {c[("戻り", b)]}' for b in sorted(
        kk[1] for kk in c if isinstance(kk, tuple) and len(kk) == 2 and kk[0] == '戻り')))
    print('  **(d2) 親の列番号 `q_parent`（`Q` の何列目）**: ', end='')
    print('  '.join(f'q={q}: {c[("q_parent", q)]}' for q in sorted(
        kk[1] for kk in c if isinstance(kk, tuple) and len(kk) == 2 and kk[0] == 'q_parent')))
    print('  破れた `Q` の形: ', dict((k[1], c[k]) for k in c
                                   if isinstance(k, tuple) and len(k) == 2 and k[0] == '形'))
    print('  **(d3) `n` 別の `k_parent`**:')
    for n in NS:
        row = [(kk[2], c[kk]) for kk in c
               if isinstance(kk, tuple) and len(kk) == 3 and kk[0] == 'n 別 k_parent' and kk[1] == n]
        if row:
            print(f'      n={n}: 破れ {c[("破れ", n)]:7d}  ' +
                  '  '.join(f'k_parent={k}: {v}' for k, v in sorted(row)))
    for k in sorted(ex)[:6]:
        Q, d, e, n, p = ex[k]
        print(f'      例 n={k[0]} k_parent={k[1]}: Q={Q} d={d} e={e} → 親の絶対位置 {p}')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--big', action='store_true')
    a = ap.parse_args()
    if not a.big:
        for cm in (1, 2):
            for L in (2, 3):
                run(cm, L, range(4), (2, 3, 4, 5))
    else:
        run(1, 4, range(4), (2, 3, 4, 5))
        run(1, 5, range(4), (2, 3))
