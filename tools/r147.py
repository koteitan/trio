# -*- coding: utf-8 -*-
"""**課題 (n1') —— `z = 0 ∧ v >= 1`（ブロッカーの枝）で `(D ++ [r])⟦m⟧` は何になるか。**

**場面**: `S = shTower Q e n ++ [r]`、`r = (n*e, v, 0)`、`v = entry Q 1 0 >= 1`。
`j0` ＝ `S` の中での `r` の親（§R145 より **行 0 祖先であるブロッカーの像のうち最も右**）。
`A = (shTower Q e n).take j0`、**`D = (shTower Q e n).drop j0`**、測るのは **`(D ++ [r])⟦m⟧`**。

## ★ 先に導出できる部分（測るまでもない）

    `srow r = 1`（`z=0`, `v>=1`）⟹ `oper` の **`d1 = if 1 < i1 then … else 0` = 0**
    `mTower Q' d0 0 m = shTower Q' d0 m`（`Lift1 X 0 = X` かつ `shTower` の定義と一致）

⟹ **team-lead の予想「`shTower` の形になるのでは」は、`d1 = 0` の部分は定義から出る。**

## ★ 反例の形を先に書く（教訓 45）＋ 充足率の見積もり（L3 の §105.2）

> **本当に非自明なのは「接頭辞が消えるか」＝ `D ++ [r]` の中での `r` の親が index 0 か。**
>
> **私の予想: `j0'' = 0` が 100%。**
> 理由: `j0` は `S` の中での親で、`D` はちょうど `j0` から始まる。`nextrel1` の極小性条項は
> `y > j0` だけを見るので、前半 `A` を捨てても関係は変わらない（`le1_append_right` は無条件）。
>
> **⚠ 反例の形: 「`D` の中に、`r` の親としてより右の候補が現れる」。**
> **⚠ 充足率の見積もり: **0 〜 5%**（`le1_append_right` が無条件なので、ほぼ起きないはず）。**

**測るもの**: `j0''` の分布 ／ `d0`, `d1` ／ `Lb''` ／ **`(D ++ [r])⟦m⟧ = shTower B d0 m` か**。

**箱と単位**: 単位 `(Q,e,n,m)`。`Q` の根 `= (0,v,0)`、**`v >= 1`**、他の列は行0 >= 1。
箱 = 行0 ∈ 1..3、行1 < R1、`|Q| = 2..5`、`e ∈ 1..3`、`n ∈ 1..3`、`m ∈ 1..3`。
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


def shT(Q, e, n):
    """`shTower Q e n` を任意の列 `Q` に対して（塊のコピー塔）。"""
    return [(c[0] + k * e, c[1], c[2]) for k in range(n) for c in Q]


def run(L, ES, NS, MS, R1):
    COL = [(a, b, 0) for a in range(1, 4) for b in range(R1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for v in range(1, R1):
        for t in itertools.product(COL, repeat=L - 1):
            Q = [(0, v, 0)] + list(t)
            for e in ES:
                for n in NS:
                    S = shTower(Q, e, n) + [(n * e, v, 0)]
                    j = len(S) - 1
                    if srow(S, j) != 1:
                        continue
                    j0 = trio.parent(S, 1, j)
                    if j0 is None:
                        continue                      # 孤児は無料（§R145）
                    D = S[j0:j]                       # (shTower).drop j0
                    Sp = D + [S[j]]                   # D ++ [r]
                    jp = len(Sp) - 1
                    ip = srow(Sp, jp)
                    j0p = trio.parent(Sp, ip, jp)
                    c['分母'] += 1
                    c[('srow(r) in D++[r]', ip)] += 1
                    if j0p is None:
                        c['⚠ D ++ [r] では孤児'] += 1
                        ex.setdefault('孤児', (Q, e, n, j0))
                        continue
                    c[('★ j0が0か', j0p == 0)] += 1
                    if j0p != 0:
                        ex.setdefault('j0!=0', (Q, e, n, j0, j0p, len(Sp)))
                    d0 = Sp[jp][0] - Sp[j0p][0]
                    d1 = (Sp[jp][1] - Sp[j0p][1]) if ip > 1 else 0
                    Lb = jp - j0p
                    c[('d1 == 0', d1 == 0)] += 1
                    c[('Lb', min(Lb, L + 2))] += 1
                    c[('d0 == e', d0 == e)] += 1
                    for m in MS:
                        lhs = oper_lean(Sp, m)
                        B = Sp[j0p:j0p + Lb]
                        rhs = list(Sp[:j0p]) + shT(B, d0, m)
                        c[('★ 展開 = take ++ shTower', m, lhs == rhs)] += 1
                        if lhs != rhs:
                            ex.setdefault(('等式破れ', m), (Q, e, n, m, j0p, Lb, d0))
    tot = c['分母']
    print(f'### |Q|={L} 行1<{R1}  分母 {tot:9d}  [{time.time()-t0:.1f}s]')
    if not tot:
        print('  （0 件）\n'); return
    print(f'  `D ++ [r]` での `srow(r)`: ' + str({k[1]: c[k] for k in c
                                              if isinstance(k, tuple) and k[0] == 'srow(r) in D++[r]'})
          + f'   ⚠ そこで孤児 {c["⚠ D ++ [r] では孤児"]}')
    ok = c[('★ j0が0か', True)]; ng = c[('★ j0が0か', False)]
    print(f'  **★ `j0`（`D ++ [r]` の中の親）= 0: {ok:9d} / {ok+ng} '
          f'({100*ok/max(ok+ng,1):6.2f}%)**   （私の予想は 100%、反例の見積もりは 0〜5%）')
    print(f'  `d1 == 0`: {c[("d1 == 0", True)]}/{ok+ng}   '
          f'`d0 == e`: {c[("d0 == e", True)]}/{ok+ng}   '
          f'`Lb` ' + str(dict(sorted((k[1], c[k]) for k in c
                                 if isinstance(k, tuple) and k[0] == 'Lb'))))
    for m in MS:
        y = c[('★ 展開 = take ++ shTower', m, True)]; nn = c[('★ 展開 = take ++ shTower', m, False)]
        if y + nn:
            print(f'  **m={m}: `(D ++ [r])⟦m⟧ = take ++ shTower B d0 m` … '
                  f'成立 {y:9d} ({100*y/(y+nn):6.2f}%)  破れ {nn:8d}**')
    for k in sorted(ex, key=str):
        print(f'      例 {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=5)
    a = ap.parse_args()
    for R1 in (3, 4):
        for L in range(2, a.L + 1):
            run(L, (1, 2, 3), (1, 2, 3), (1, 2, 3), R1)
