# -*- coding: utf-8 -*-
"""**L3 の §103.5 への回答 —— F2a の「破れ 0」は箱の産物か。`|Q|` を 6 まで伸ばす。**

**L3 の指摘（そのまま写す）:**
> F2a の反例は **G2 の列**（行 1 は根より上なのに錐の外）を通らなければ作れない。
> `|M|` が小さい箱には G2 がほとんど無い。⟹ `|M|` を 6, 7 まで伸ばして測り直す必要がある。
> **その形が母集団に何件入っているかを先に数えてください。0 件なら「破れ 0」は空虚です。**

**先に数えた結果（`r137count`）—— 0 件ではなかった:**

    行0<3: |Q|=3 **2.22%** / 4 **6.07%** / 5 **10.29%** / 6 **14.34%**
    行0<4: |Q|=3 **3.17%** / 4 **8.31%** / 5 **13.73%** / 6 **18.83%**

⟹ **私の §R132 の箱（|Q| <= 4）にも G2 を持つ `Q` は 236 〜 1,292 本入っていた。**
**空虚ではない。だが割合は小さいので、伸ばして測り直す価値はある。**

**測るもの**: F2a の場面（`srow=2` ∧ 末尾列が錐の外 ∧ ブロック内で孤児）で
**「ブロック内で孤児 ⟹ 塔全体でも孤児」が破れるか**（＝ §R132 の (z5) の F2a 版）。

**`|Q| = 6` は G2 を持つ `Q` に絞る。これは L3 自身の §103.4 の議論から健全**
（鎖がブロック境界を越えるには G2 の列が要る ⟹ G2 が無ければ越えられない）。
⚠ ただし L3 の議論は `le1_mTower_block`（前提 `0 < e`）を経由するので、
**`e = 0` については絞りが正当化されない。⟹ `|Q| <= 5` は全数で測り、`e=0` も含める。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r126 import srow, hasP, le1_root, classify
from r113 import mTower


def run(R0, cm, L, DE, NS, only_g2):
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
            g2 = [q for q in range(1, L) if (not le1_root(Q, q)) and Q[q][1] > Q[0][1]]
            if only_g2 and not g2:
                continue
            key = 'G2 あり' if g2 else 'G2 なし'
            for d in DE:
                for e in DE:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        j = len(T) - 1
                        orp = trio.parent(T, srow(T, j), j) is None
                        c[(key, tag, 'ok' if orp else '**破れ**')] += 1
                        if not orp:
                            ex.setdefault((key, tag), (Q, d, e, n,
                                                       trio.parent(T, srow(T, j), j)))
    print(f'### 行0<{R0} 行2<={cm} |Q|={L} {"G2 あり限定" if only_g2 else "全数"}  '
          f'[{time.time()-t0:.1f}s]')
    for key in ('G2 あり', 'G2 なし'):
        for tag in ('F2a', 'F2a+F2b'):
            o = c[(key, tag, 'ok')]; b = c[(key, tag, '**破れ**')]
            if o + b:
                print(f'  {key:8s} {tag:9s}: 分母 {o+b:9d}  塔でも孤児 {o:9d}  '
                      f'**破れ {b:7d}** ({100*b/(o+b):6.3f}%)')
    for k in sorted(ex, key=str):
        Q, d, e, n, p = ex[k]
        print(f'    ★ 反例 {k}: Q={Q} d={d} e={e} n={n} → 親 {p}')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--stage', type=int, default=1)
    a = ap.parse_args()
    if a.stage == 1:
        for L in (3, 4, 5):
            run(4, 1, L, range(4), (2, 3), False)
    else:
        run(3, 1, 6, range(4), (2, 3), True)
        run(4, 1, 6, range(4), (2,), True)
