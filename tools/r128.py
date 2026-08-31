# -*- coding: utf-8 -*-
"""**課題 R128 —— §R131 を `n = 3,4,5` まで伸ばして測り直す（L3 の反証、教訓 21/27/45）。**

**L3 の §88.2（そのまま写す）:**

> `nextrel1 T a (ブロック n の末尾列)` の極小性は `j := ブロック n の根` で
>   **`entry T 1 last <= entry T 1 (root n) = entry Q 1 0 + n*d1`** を要求する。
> 末尾列が **`Q` の錐の外**なら `entry T 1 last = entry Q 1 last`（リフト無し）
> ⟹ **`entry Q 1 last <= entry Q 1 0 + n*d1`** ⟹ **`n` が小さいと満たせない。**
>
> **⟹ 反例の形 = 「`srow ∈ {1,2}` ∧ 末尾列が `Q` の錐の外 ∧
> `n*d1 >= entry Q 1 last − entry Q 1 0`」。`n <= 2` の箱にはほとんど入っていない疑い。**

**(b2) ⟹ この形が箱に何件入っているかを `n` 別に数える（教訓 23）。0 件なら私の「破れ 0」は空虚。**

**(b3) `m` について（私の判断と理由）:**
`m` は `oper` の複製回数。**等式の両辺とも同じ `m` で展開する**ので、`m` は
「悪根がどこか」を変えない（悪根は `m` に依らず `T` だけで決まる）。
⟹ **反例の形は `m` を含まない。`m` を伸ばす必要は無い。**
ただし **`m` が小さいと右辺の `⟦m⟧` が短くなって差が出にくい可能性**はあるので、
**`m ∈ {1,2,3}` の 3 段**は振る（伸ばすコストが小さいため）。

**(b4)** `d1 = 0`（＝ `e = 0`）は除く（(D) の前提 `0 < d1`。錐が動かないと形が成立しない）。

**箱と単位**: §R131 と同じ決め打ち。`X = (0,v,z) :: R`、
`d = entry R 0 (|R|-1)`、`e = entry R 1 (|R|-1) - v`、`Q = X.dropLast`。
単位 `(R,v,z,n,m)`。**`hj0`（`parent X = 0`）は課したまま**（`oper_eq_mTower` の前提）。
**`hblk`（`HasParentInBlock Q`）は落とす。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r113 import Lift1, sh, mTower
from r98 import oper_lean
from r126 import srow, hasP, le1_root


def run(COL, Ls, VS, ZS, NS, MS, label):
    c = Counter(); ex = {}
    t0 = time.time()
    for L in Ls:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            jR = len(R) - 1
            for v in VS:
                for z in ZS:
                    X = [(0, v, z)] + R
                    jX = len(X) - 1
                    iX = srow(X, jX)
                    if trio.parent(X, iX, jX) != 0:
                        continue                       # hj0（外せない）
                    # ⚠ Lean は `Nat` の切り捨て減算。負にはならず 0 になる（`Trio.lean:98`）
                    d = max(0, X[jX][0] - X[0][0]) if iX > 0 else 0
                    e = max(0, X[jX][1] - X[0][1]) if iX > 1 else 0
                    if e == 0:
                        continue                       # (b4) d1 = 0 は除く
                    Q = X[:-1]
                    if len(Q) < 2 or hasP(Q):
                        continue                       # hblk を落とした側だけ
                    jQ = len(Q) - 1
                    iQ = srow(Q, jQ)
                    # L3 の反例の形の部品
                    outcone = not le1_root(Q, jQ)
                    need = Q[jQ][1] - Q[0][1]          # entry Q 1 last - entry Q 1 0
                    for n in NS:
                        shape = (iQ in (1, 2)) and outcone and (n * e >= need)
                        for m in MS:
                            c[('分母', n)] += 1
                            if shape:
                                c[('★ L3 の反例の形', n)] += 1
                            lhs = oper_lean(mTower(Q, d, e, n + 1), m)
                            rhs = ([tuple(x) for x in mTower(Q, d, e, n)]
                                   + oper_lean(Lift1(sh(Q, d * n), e * n), m))
                            if lhs != rhs:
                                c[('**破れ**', n)] += 1
                                ex.setdefault(n, (R, v, z, d, e, n, m))
                                if shape:
                                    c[('破れかつ形', n)] += 1
    print(f'### {label}  [{time.time()-t0:.1f}s]')
    for n in NS:
        dn = c[('分ームー', n)] if False else c[('分母', n)]
        if not dn:
            continue
        sh_ = c[('★ L3 の反例の形', n)]; br = c[('**破れ**', n)]
        print(f'  n={n}: 分母 {dn:9d}  **L3 の形 {sh_:8d} ({100*sh_/dn:6.2f}%)**  '
              f'**破れ {br:6d}**' + (f'   例 {ex[n]}' if n in ex else ''))
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=3)
    ap.add_argument('--b', type=int, default=2)      # 行 1 の上限
    ap.add_argument('--d', type=int, default=2)      # 行 0 の上限
    a = ap.parse_args()
    for cm in (1, 2, 3):
        run([(dd, b, cc) for dd in range(a.d + 1) for b in range(a.b + 1)
             for cc in range(cm + 1)],
            tuple(range(2, a.L + 1)), tuple(range(a.b + 1)), (0, 1),
            (1, 2, 3, 4, 5), (1, 2, 3),
            f'R128 箱 行0<={a.d} 行1<={a.b} 行2<={cm} |R|<={a.L}')
