# -*- coding: utf-8 -*-
"""**課題 (f1a) —— F2a の反例の形の分母を数える（教訓 23）。**

**L3 の反例の形（そのまま写す）:**
> 「`srow=2` ∧ `last` が錐の外 ∧ `M` の末尾列が行 2 の孤児」の場面で、
> **`le1` の鎖が境界を G2 の列で越え、その先に `entry M 2 < entry M 2 q_last` の列がある。**

**⟹ 部品に分けて数える（`T = mTower Q d e n`, `last = |T|-1`）:**

    **(N0)** F2a の場面そのもの（`¬hasP(Q)` ∧ `srow=2` ∧ 末尾列が `Q` の錐の外）
    **(N1)** `last` の **`le1` 鎖が最終ブロックを出る**（境界を越える）
    **(N2)** 越えた先（＝ 最終ブロックの外）の鎖上に **`entry T 2 a < entry T 2 last`** の列がある
             ← **これが `nextrel2` の候補。0 件なら (z5) の F2a は空虚**
    **(N3)** さらに、越える先の列 `b` が **G2**（錐の外なのに行 1 が根より上）

**⚠ `nextrel2 T a last` は `le1 T a last` を要求する。`le1 T a last` ⟺ `a` が `last` の
行 1 の親鎖の上にある。⟹ 候補は鎖の上だけを見ればよい。**（`nextrel2` の定義から。`Trio.lean:59`）

**箱と単位**: 単位 `(Q,d,e,n)`。箱 = 行0<R0, 行1<3, 行2<=cm、`|Q| = 3..6`（＝ `|M| = 4..7`）、
`d,e ∈ 0..3`、`n ∈ {2,3}`。**`W` 所属は判定しない。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow, hasP, le1_root, classify
from r113 import mTower


def chain1(T, x):
    """`x` の行 1 の親鎖（`x` 自身を含む）。`le1 T a x` ⟺ `a` がこの鎖の上。"""
    out = []
    while x is not None:
        out.append(x)
        x = trio.parent(T, 1, x)
    return out


def run(R0, cm, L, DE, NS):
    COL = [(a, b, c) for a in range(R0) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            if hasP(Q):
                continue
            i, fs = classify(Q)
            tag = '+'.join(f.split()[0] for f in fs)
            if 'F2a' not in tag:
                continue
            for d in DE:
                for e in DE:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        last = len(T) - 1
                        kb = (n - 1) * L                    # 最終ブロックの先頭
                        c['N0 F2a の場面'] += 1
                        ch = chain1(T, last)
                        out = [a for a in ch if a < kb]     # 最終ブロックの外
                        if not out:
                            continue
                        c['N1 鎖が最終ブロックを出る'] += 1
                        cand = [a for a in out if T[a][2] < T[last][2]]
                        if cand:
                            c['★ N2 その先に行 2 の候補がある'] += 1
                            ex.setdefault('N2', (Q, d, e, n, cand[:3], T[last]))
                        # 越える 1 歩 (c_, b_) を探す
                        g2cross = False
                        for idx in range(len(ch) - 1):
                            b_, c_ = ch[idx], ch[idx + 1]
                            if b_ // L != c_ // L:
                                qb = b_ % L
                                if (not le1_root(Q, qb)) and Q[qb][1] > Q[0][1]:
                                    g2cross = True
                                break
                        if g2cross:
                            c['N3 越える先が G2'] += 1
                            if cand:
                                c['★★ 完全な形（N2 ∧ N3）'] += 1
                                ex.setdefault('完全', (Q, d, e, n, cand[:3]))
    n0 = c['N0 F2a の場面']
    print(f'  行0<{R0} 行2<={cm} |Q|={L}（|M|={L+1}）: '
          f'N0 {n0:9d}  N1 {c["N1 鎖が最終ブロックを出る"]:8d}  '
          f'**N2 {c["★ N2 その先に行 2 の候補がある"]:8d}**  N3 {c["N3 越える先が G2"]:8d}  '
          f'**完全 {c["★★ 完全な形（N2 ∧ N3）"]:8d}**  [{time.time()-t0:.1f}s]')
    for k in sorted(ex):
        print(f'      例 {k}: Q={ex[k][0]} d={ex[k][1]} e={ex[k][2]} n={ex[k][3]} 候補={ex[k][4]}')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--stage', type=int, default=1)
    a = ap.parse_args()
    print('### (f1a) F2a の反例の形の分母（|M| = |Q|+1）')
    if a.stage == 1:
        for L in (3, 4, 5):
            run(4, 1, L, range(4), (2, 3))
    else:
        run(3, 1, 6, range(4), (2, 3))
