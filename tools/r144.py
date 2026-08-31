# -*- coding: utf-8 -*-
"""**課題 R135 —— F2b で復活したあと `oper` が何を作るか（列の等式。番人が付く的）。**

**主語（`Trio.lean:98` の `oper` を逐語）:**

    `M⟦n⟧ = M.take j0 ++ (range n).flatMap fun k => (range' j0 (j1-j0)).map fun j =>
              (entry M 0 j + k*d0*A_{j,0}, entry M 1 j + k*d1*A_{j,1}, entry M 2 j)`
    **`A_{j,y} = 1` ⟺ 悪根 `j0` が行 `y` の木で `j` の祖先**

**§68（`j0 = 0`）が `mTower` になったのは、根が狭義最浅なので `A_{j,0} ≡ 1` だったから。**

## ★ 反例の形を先に書く（教訓 45）＋ 充足率の見積もり（L3 の §105.2）

> **予想: `T⟦m⟧ = T.take j0 ++ mTower B d0 d1 m`（`B = T[j0 : j0+Lb]`）は
> **破れる**。なぜなら `j0 > 0` では `A_{j,0} ≡ 1` が保証されないから。**
>
> **反例の形: 「塊 `B` の中に、悪根 `j0` の行 0 の子孫でない列がある」。**
>
> **⚠ 充足率の私の見積もり: 塊はブロック境界をまたぐ（§R143 (k1)）。**
> **`j0` はブロック `n-2` の内部の列（`q >= 1`）なので、同じブロックの後ろの列で
> `j0` より行 0 が低いものがあれば子孫にならない。⟹ **かなり高いはず（5 割超）**と見積もる。**

**測るもの**: (k1) `j0, Lb, d0, d1` ／ (k2) 上の等式の成立率と、破れるときの形 ／
(k3) `n` 依存 ／ (k4) 予想した形の充足率。

**箱と単位**: 単位 `(Q,d,e,n,m)`。母集団 = **F2b かつ塔で復活**。
箱 = 行0<4, 行1<3, 行2<=cm（**3 段**）、`|Q| = 3..4`、`d,e ∈ 0..3`、`n ∈ {2,3,4}`、`m ∈ {1,2,3}`。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow, hasP, le1_root, classify
from r113 import mTower
from r98 import oper_lean


def run(cm, L, DE, NS, MS):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            if hasP(Q):
                continue
            i, fs = classify(Q)
            if '+'.join(f.split()[0] for f in fs) != 'F2b':
                continue
            for d in DE:
                for e in DE:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        last = len(T) - 1
                        sr = srow(T, last)
                        j0 = trio.parent(T, sr, last)
                        if j0 is None:
                            continue
                        Lb = last - j0
                        B = T[j0:j0 + Lb]
                        d0 = T[last][0] - T[j0][0]
                        d1 = (T[last][1] - T[j0][1]) if sr > 1 else 0
                        # (k4) 予想した形: `B` の中に `j0` の行 0 の子孫でない列があるか
                        notdesc = [x for x in range(j0, last)
                                   if not trio.is_ancestor(T, 0, j0, x)]
                        c['分母'] += 1
                        c[('★ 予想の形（行0の非子孫あり）', bool(notdesc))] += 1
                        for m in MS:
                            lhs = oper_lean(T, m)
                            rhs = T[:j0] + [tuple(x) for x in mTower(B, d0, d1, m)]
                            c[('等式', m, lhs == rhs)] += 1
                            if lhs != rhs:
                                ex.setdefault(('破れ', m), (Q, d, e, n, m, j0, Lb, d0, d1,
                                                          len(notdesc)))
                            else:
                                ex.setdefault(('成立', m), (Q, d, e, n, m, j0, Lb, d0, d1,
                                                          len(notdesc)))
                        c[('n 別 j0-（n-2）|Q|', (n, j0 - (n - 2) * L))] += 1
                        c[('Lb - |Q|', Lb - L)] += 1
    tot = c['分母']
    print(f'### 行2<={cm} |Q|={L}  復活 {tot:8d} 件  [{time.time()-t0:.1f}s]')
    if not tot:
        print('  （0 件）\n'); return
    y = c[('★ 予想の形（行0の非子孫あり）', True)]
    print(f'  **(k4) 予想の形の充足率: {y:8d} / {tot} ({100*y/tot:6.2f}%)**'
          f'   （私の見積もりは「5 割超」）')
    for m in MS:
        ok = c[('等式', m, True)]; ng = c[('等式', m, False)]
        if ok + ng:
            print(f'  **(k2) m={m}: `T⟦m⟧ = T.take j0 ++ mTower B d0 d1 m` … '
                  f'成立 {ok:8d} ({100*ok/(ok+ng):6.2f}%)  **破れ {ng:8d}**')
    print('  **(k1) `Lb - |Q|`**: ', dict(sorted((k[1], c[k]) for k in c
                                            if isinstance(k, tuple) and k[0] == 'Lb - |Q|')))
    print('  **(k3) `n` 別の `j0 - (n-2)*|Q|`**: ',
          dict(sorted((k[1], c[k]) for k in c
                      if isinstance(k, tuple) and k[0] == 'n 別 j0-（n-2）|Q|')))
    for k in sorted(ex, key=str):
        Q, d, e, n, m, j0, Lb, d0, d1, nd = ex[k]
        print(f'      {k}: Q={Q} d={d} e={e} n={n} m={m} j0={j0} Lb={Lb} '
              f'd0={d0} d1={d1} 非子孫 {nd} 本')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(3, a.L + 1):
            run(cm, L, range(4), (2, 3, 4), (1, 2, 3))
