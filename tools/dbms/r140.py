# -*- coding: utf-8 -*-
"""**課題 (i1)-(i4) —— `hlp` を課して「内部の列」を測り直す。**

⚠ **まず主語の確認（教訓 2）。ここに食い違いがある:**

    `gexp M 0 Lb d0 d1 n` の **`Lb = |M| - 1`**、ブロックは **`M.dropLast`**（長さ `Lb`）
    `hlp : le1 M 0 (0 + Lb)` ＝ **`M` の末尾列（index `Lb`）が `M` の根の錐の中**
    ⟹ **`hlp` が言及する列は `M` の末尾列であって、塔には入らない。**

⚠ **§R138 の私の測定は `Q` を直接生成して `mTower Q d e n` を作っていた**（ブロック長 = `|Q|`）。
**⟹ そこには `M` が存在せず、`hlp` は定義されない。**
**L3 は私の `Q` を `M` と読んで「`hlp` を満たさない」と分析している**（算術は正しいが、
**その読みではブロック長が `|Q|-1` になり、私が測った対象と別物**）。
**⟹ ここでは `M` を生成し、`Q := M.dropLast` として測り直す。それが正しい突き合わせ。**

**母集団**: `|M| = Lb + 1`、**根が狭義最浅**（`hr0`）、`Q = M.dropLast`、`T = mTower Q d e n`。
**単位**: `(M, d, e, n, k, q)`。`k >= 1`、`1 <= q < Lb`、**`q` は `Q` の錐の外**（§107/§115 の場面）。
**`W` 所属は判定しない。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import le1_root
from r113 import mTower
from r138 import chain1


def run(cm, Lb, DE, NS):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product(COL, repeat=Lb):
            M = [root] + list(t)
            if not all(M[0][0] < M[l][0] for l in range(1, Lb + 1)):
                continue                                   # hr0（根が狭義最浅）
            c['(i2) hr0 を通った M'] += 1
            hlp = le1_root(M, Lb)                          # `M` の末尾列が錐の中
            if hlp:
                c['(i2) ★ hlp も通った M'] += 1
            Q = M[:-1]
            dpin = M[Lb][0] - M[0][0]                      # hd0e で決まる d
            for d in DE:
                for e in DE:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        for k in range(1, n):
                            for q in range(1, Lb):
                                if le1_root(Q, q):
                                    continue               # 錐の外だけ
                                b = k * Lb + q
                                leaves = any(a // Lb != k for a in chain1(T, b))
                                key = ('★ hlp あり' if hlp else 'hlp なし（陰性対照）')
                                c[(key, '出る' if leaves else '閉じる')] += 1
                                if leaves:
                                    ex.setdefault(key, (M, d, e, n, k, q, chain1(T, b)))
                                if hlp and d == dpin:
                                    c[('hlp ∧ d 固定', '出る' if leaves else '閉じる')] += 1
    print(f'### 行2<={cm} |M|={Lb+1}（ブロック長 {Lb}）  [{time.time()-t0:.1f}s]')
    print(f'  **(i2) 分母**: hr0 を通った `M` {c["(i2) hr0 を通った M"]:8d} 本 → '
          f'**hlp も通った {c["(i2) ★ hlp も通った M"]:8d} 本 '
          f'({100*c["(i2) ★ hlp も通った M"]/max(c["(i2) hr0 を通った M"],1):5.1f}%)**')
    for key in ('★ hlp あり', 'hlp なし（陰性対照）', 'hlp ∧ d 固定'):
        cl = c[(key, '閉じる')]; lv = c[(key, '出る')]
        if cl + lv:
            print(f'  {key:22s}: 分母 {cl+lv:9d}  閉じる {cl:9d} ({100*cl/(cl+lv):6.2f}%)  '
                  f'**出る {lv:8d} ({100*lv/(cl+lv):5.2f}%)**')
        if key in ex:
            M, d, e, n, k, q, ch = ex[key]
            print(f'      例 M={M} d={d} e={e} n={n} k={k} q={q} 鎖={ch}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--Lb', type=int, default=4)
    a = ap.parse_args()
    for cm in (1, 2):
        for Lb in range(3, a.Lb + 1):
            run(cm, Lb, range(4), (2, 3))
