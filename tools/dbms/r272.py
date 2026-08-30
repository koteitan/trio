# -*- coding: utf-8 -*-
"""**(R1R0-W) —— 正規化版 `R1<=R0` は `W` の元で成り立つか。**

## ⚠ 母集団を 1 行で

`W` は **`oper`**（`oper_closed`）、**`dropLast`**（`W_dropLast`）、
そして **`(M.drop p).take k`**（H12 の `window_mem_W`）に閉じています。
⟹ ★ ですから **`W` の元の代表**として次を取ります:

    ★ **シート** … `psiI.json` の 1,637 行列 ＋ **その全 `drop p / take k`**
    ★ **`Reach`** … 中核 `D_v` から `oper` で到達 ＋ 接頭辞 ＋ **全 `drop p / take k`**
    ★ **中核 `D_v`**（v = 1..7）

**正規化版 `R1<=R0`**: `∀ i, entry X 1 i <= entry X 0 i - entry X 0 0`。
⚠ 根が `(0,*,*)` なら正規化は恒等なので、**`drop` を入れないと自明に 100% になります**（教訓 21）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from trio import diag
from collections import Counter
from r263 import load
from r269 import R1R0, norm
from r260 import reach

R1R0N = lambda X: R1R0(norm(X))


def subwins(Ms, KMAX):
    """`(M.drop p).take k`（`k >= 2`）を全部。"""
    seen = set()
    for M in Ms:
        X = tuple(tuple(v) for v in M)
        for p in range(len(X)):
            for k in range(2, min(len(X) - p, KMAX) + 1):
                seen.add(X[p:p + k])
    return seen


def report(S, tag, drop_only=False):
    c = Counter(); ex = []
    for X in S:
        Y = [tuple(v) for v in X]
        c['分母'] += 1
        if Y[0][0] == 0: c['   （根の行 0 = 0 ＝ 正規化が恒等）'] += 1
        if R1R0N(Y): c['★ 正規化版 R1<=R0 が真'] += 1
        else:
            c['⛔ **偽**'] += 1
            if len(ex) < 4 and len(Y) <= 5: ex.append(Y)
        if R1R0(Y): c['（参考）正規化なし版が真'] += 1
    d = c['分母']
    def pc(x): return f'{x} ({100*x/max(d,1):8.4f}%)'
    print(f'  {tag}: 分母 {d}   ★ **正規化版が真** {pc(c["★ 正規化版 R1<=R0 が真"])}   '
          f'⛔ **偽** {pc(c["⛔ **偽**"])}')
    print(f'      （参考）正規化なし版が真 {pc(c["（参考）正規化なし版が真"])}   '
          f'根の行 0 = 0 が {pc(c["   （根の行 0 = 0 ＝ 正規化が恒等）"])}')
    for x in ex: print(f'        ⛔ 偽の例: {x}')


if __name__ == '__main__':
    t0 = time.time()
    print('## ★ 中核 `D_v`')
    for v in range(1, 8):
        D = [tuple(x) for x in diag(3, v, 1)]
        print(f'   D_{v}: 正規化版 R1<=R0 = {"★真" if R1R0N(D) else "⛔偽"}')
    print()
    Ms = [list(m) for m in load()]
    print('## ★ シート')
    report({tuple(tuple(v) for v in M) for M in Ms}, '行列そのもの（1,637）')
    report(subwins(Ms, 8), '★★ **全 drop p / take k（k<=8）** ＝ `window_mem_W` で `W` の元')
    print()
    print('## ★ `Reach`（中核から `oper` で到達 ＋ 接頭辞 ＋ drop/take）')
    for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5),
                          ((1, 2, 3, 4), (1, 2, 3), 6),
                          ((1, 2, 3, 4, 5, 6), (1, 2, 3), 5)):
        R = reach(vs, ns, depth)
        report(R, f'Reach(D_{vs}, n<=%d, depth={depth}) そのもの' % max(ns))
        report(subwins([list(x) for x in R], 8),
               f'★★ **その全 drop/take**（depth={depth}）')
    print(f'[{time.time()-t0:.1f}s]')
