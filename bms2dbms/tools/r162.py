# -*- coding: utf-8 -*-
"""**課題 (y4a)-(y4c)（L3 / team-lead の依頼）—— `Mono` は展開で保たれるか。**

**`Mono`** ＝ `Q` の**行 0 が狭義単調** ∧ **行 1 が狭義単調** ∧ **`entry Q 2 0 = 0`**
（`d, e >= 1` は外から与える条件なので、ここでは列の性質だけを見る）。

## ★ 反例の形を先に書く（教訓 45）＋ 見積もり（L3 の §105.2）

**導出**: `Q⟦n⟧ = Q.take j0 ++ (写しを n 個)`。写し `k` の行 1 は
`entry Q 1 j + k*d1`（`j ∈ [j0, j1)`、`A` 行列が 1 のとき）。
**写し `k` の最後と写し `k+1` の最初の境目**で単調性が要求するのは

    `entry Q 1 (j1−1) + k*d1 < entry Q 1 j0 + (k+1)*d1`
    ⟺ **`entry Q 1 (j1−1) − entry Q 1 j0 < d1`**

`Q` が行 1 で狭義単調なら左辺 `>= j1−1−j0 >= 1` ⟹ **`d1` が窓の幅以上でないと壊れる。**

> **★ 反例の形: 写しの境目で行 1 が下がる（`d1 <= entry Q 1 (j1−1) − entry Q 1 j0`）。**
> **⚠ 見積もり: `n >= 2`（写しが 2 個以上）で **60 〜 95% 破れる**。**
> **`n = 1` は写しが 1 個で `Q⟦1⟧ = Q.dropLast` ⟹ **部分列なので単調性は保たれる**（破れ 0%）。**

**(y4c)** 生成元 `D_v = (0,0,0)(1,1,1)…(v,v,1)` から実際に展開して現れる行列の `Mono` 率。
⚠ **`D_v` の根は `(0,0,0)` なので `entry Q 2 0 = 0` ✓。行 0・行 1 とも `0,1,…,v` で狭義単調 ✓。**
⟹ **`D_v` 自身は `Mono`。問題は展開後。**

**箱と単位**: (y4a) 単位 `(Q, n)`。箱 = 行0<5, 行1<5, 行2<=1、`|Q| = 3..5`、`n ∈ 1..6`。
(y4c) `v = 1..5`、深さ 1..4、各段の `n ∈ {1,2,3}`。**`W` 所属は判定しない。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r98 import oper_lean


def mono(Q):
    if len(Q) == 0:
        return False
    r0 = all(Q[i][0] < Q[i + 1][0] for i in range(len(Q) - 1))
    r1 = all(Q[i][1] < Q[i + 1][1] for i in range(len(Q) - 1))
    return r0 and r1 and Q[0][2] == 0


def which(Q):
    """どの条件が破れるか。"""
    out = []
    if not all(Q[i][0] < Q[i + 1][0] for i in range(len(Q) - 1)):
        out.append('行0')
    if not all(Q[i][1] < Q[i + 1][1] for i in range(len(Q) - 1)):
        out.append('行1')
    if len(Q) and Q[0][2] != 0:
        out.append('根の行2')
    return '+'.join(out) if out else 'なし'


def y4ab(L, R0, R1, NS):
    COL = [(a, b, c) for a in range(R0) for b in range(R1) for c in (0, 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for Qt in itertools.product(COL, repeat=L):
        Q = list(Qt)
        if not mono(Q):
            continue
        c['Mono な Q'] += 1
        for n in NS:
            R = oper_lean(Q, n)
            if len(R) < 1:
                continue
            c[('分母', n)] += 1
            ok = mono(R)
            c[('★ 展開も Mono', n, ok)] += 1
            if not ok:
                c[('(y4b) 破れた条件', n, which(R))] += 1
                ex.setdefault(n, (Q, n, R[:6], which(R)))
    print(f'### (y4a)(y4b) |Q|={L} 行0<{R0} 行1<{R1}  `Mono` な `Q` {c["Mono な Q"]:7d} 本  '
          f'[{time.time()-t0:.1f}s]')
    for n in NS:
        tot = c[('分母', n)]
        if not tot:
            continue
        y = c[('★ 展開も Mono', n, True)]
        row = {kk[2]: c[kk] for kk in c if isinstance(kk, tuple) and len(kk) == 3
               and kk[0] == '(y4b) 破れた条件' and kk[1] == n}
        print(f'  n={n}: 分母 {tot:7d}  **展開も Mono {y:7d} ({100*y/tot:6.2f}%)**  '
              f'破れた条件 {row}')
    for n in sorted(ex):
        if n <= 2:
            print(f'      例 n={n}: Q={ex[n][0]} → {ex[n][2]}… 破れ={ex[n][3]}')
    print()


def y4c(VS, depth, NS):
    print(f'### (y4c) 生成元 `D_v` から実際に展開（深さ {depth}、各段 n ∈ {NS}）')
    for v in VS:
        D = [tuple(x) for x in trio.diag(3, v, 1)]
        cur = {tuple(D)}
        print(f'  v={v}: D_v={D}  Mono={mono(D)}')
        for dep in range(1, depth + 1):
            nxt = set()
            for M in cur:
                for n in NS:
                    R = oper_lean(list(M), n)
                    if len(R) >= 1:
                        nxt.add(tuple(tuple(x) for x in R))
            if not nxt:
                break
            cur = nxt
            ok = sum(1 for M in cur if mono(list(M)))
            bad = Counter(which(list(M)) for M in cur if not mono(list(M)))
            print(f'      深さ {dep}: {len(cur):6d} 個  **Mono {ok:6d} ({100*ok/len(cur):6.2f}%)**  '
                  f'破れ {dict(bad)}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--part', default='ab')
    a = ap.parse_args()
    if 'a' in a.part:
        for L in (3, 4, 5):
            y4ab(L, 5, 5, (1, 2, 3, 4, 5, 6))
    if 'c' in a.part:
        y4c((1, 2, 3, 4, 5), 4, (1, 2, 3))
