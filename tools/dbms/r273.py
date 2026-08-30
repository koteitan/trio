# -*- coding: utf-8 -*-
"""**(H2P-W) ＋ (AMIN)。**

## ⚠ 母集団を 1 行で

`W` は `oper` / `dropLast` / **`(M.drop p).take k`（`window_mem_W`）**に閉じているので、
`W` の元の代表 ＝ **シート 1,637 行列＋その全 `drop/take`（k<=8）** と
**`Reach`＋その全 `drop/take`**。**`Reach ⊆ W` なので `Reach` の破れは `W` の破れ**。

    **(H2P)(X) :⟺ ∀ t, 0 < t < |X|, 0 < entry X 2 t → ∃ y, nextrel1 X y t**
    ⚠ (H2P) は **行 0 を使わない**ので、`R1<=R0` のときの「正規化が恒等」の罠は無い。
    ⟹ ★ ですが **`drop/take` で何が変わるか**は必ず見る。

    **`amin X j` ＝ 行 0 祖先鎖（自身を含む）の行 1 値の最小値**
    ⟹ ★ H12: **`¬ hasParent X 1 j ⟺ amin X j = entry X 1 j`**（前提なし）⟹ **検算する**
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from trio import diag
from collections import Counter
from r263 import load
from r260 import reach
from r270 import H2P
from r272 import subwins


def anc0chain(X, j):
    return [j] + [y for y in range(j) if trio.is_ancestor(X, 0, y, j)]


def report_h2p(S, tag):
    c = Counter(); ex = []
    for X in S:
        Y = [tuple(v) for v in X]
        c['分母'] += 1
        if any(v[2] > 0 for v in Y[1:]): c['   （行 2 > 0 の列を持つ）'] += 1
        if H2P(Y): c['★ (H2P) 真'] += 1
        else:
            c['⛔ **(H2P) 偽**'] += 1
            if len(ex) < 4 and len(Y) <= 5: ex.append(Y)
    d = c['分母']
    def pc(x): return f'{x} ({100*x/max(d,1):8.4f}%)'
    print(f'  {tag}: 分母 {d}   ★ **(H2P) 真** {pc(c["★ (H2P) 真"])}   '
          f'⛔ **偽** {pc(c["⛔ **(H2P) 偽**"])}   '
          f'（行 2 > 0 の列を持つ {pc(c["   （行 2 > 0 の列を持つ）"])}）')
    for x in ex: print(f'        ⛔ (H2P) が偽の例: {x}')


def report_amin(S, tag):
    c = Counter()
    for X in S:
        Y = [tuple(v) for v in X]
        for j in range(1, len(Y)):
            if Y[j][1] == 0: continue
            ch = anc0chain(Y, j)
            am = min(Y[y][1] for y in ch)
            orph = trio.parent(Y[:j + 1], 1, j) is None
            c['★ 分母（行 1 > 0 の列）'] += 1
            if orph == (am == Y[j][1]): c['★★ (AMIN) H12 の同値が成立'] += 1
            else: c['⛔ **(AMIN) 同値が破れる**'] += 1
            if orph: continue
            mins = [y for y in ch if Y[y][1] == am]
            c['（非孤児）分母'] += 1
            if 0 in mins: c['   ★ 最小を実現する祖先に**根**が居る'] += 1
            else:         c['   ★★ **根では実現しない（非根のみ）**'] += 1
    d = c['★ 分母（行 1 > 0 の列）']; d2 = c['（非孤児）分母']
    def pc(x, y=None): return f'{x} ({100*x/max(y or d,1):8.4f}%)'
    print(f'  {tag}: 分母 {d}   ★★ **H12 の同値が成立** '
          f'{pc(c["★★ (AMIN) H12 の同値が成立"])}   '
          f'⛔ **破れ** {c["⛔ **(AMIN) 同値が破れる**"]}')
    print(f'      （非孤児）{d2}  ★ 根で実現 {pc(c["   ★ 最小を実現する祖先に**根**が居る"], d2)}  '
          f'★★ **非根のみ** {pc(c["   ★★ **根では実現しない（非根のみ）**"], d2)}')


if __name__ == '__main__':
    t0 = time.time()
    print('## ★★★ (H2P-W)')
    print('   中核 D_v: ' + '  '.join(
        f'D_{v}={"★真" if H2P([tuple(x) for x in diag(3,v,1)]) else "⛔偽"}'
        for v in range(1, 8)))
    Ms = [list(m) for m in load()]
    report_h2p({tuple(tuple(v) for v in M) for M in Ms}, 'シート行列そのもの')
    SW = subwins(Ms, 8)
    report_h2p(SW, '★★ **シートの全 drop/take（k<=8）** ＝ `W` の元')
    for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4), (1, 2, 3), 6),
                          ((1, 2, 3, 4, 5, 6), (1, 2, 3), 5)):
        R = reach(vs, ns, depth)
        RW = subwins([list(x) for x in R], 8)
        report_h2p(R, f'Reach(depth={depth}, D_{vs}) そのもの')
        report_h2p(RW, f'★★ **その全 drop/take**（depth={depth}）')
    print()
    print('## ★★ (AMIN)')
    report_amin(SW, '★ シートの全 drop/take')
    report_amin(reach((1, 2, 3, 4), (1, 2, 3), 6), 'Reach(depth=6)')
    print(f'[{time.time()-t0:.1f}s]')
