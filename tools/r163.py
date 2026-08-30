# -*- coding: utf-8 -*-
"""**課題 (z2)(z3)（L3 の直接依頼）—— `h2` の成立率と、錐の外の列の割合。**

## `h2` の逐語（`L105Cap:11472` `mTowerClosed_of_snocStepCone`）

    **`(h2 : ∀ j, j < Q.length → 0 < entry Q 2 j → hasParent (Q.take (j + 1)) 2 j)`**

⟹ **`Q` の位置 `j` で行 2 が正なら、`Q.take (j+1)` の中で**行 2 の**親を持つ**（行は 2 に固定）。
`hr0` も一緒に写した: `∀ l, 0 < l → l < |Q| → entry Q 0 0 < entry Q 0 l`。

**消費側が渡す `Q` の形**（team-lead の指定）: **`Q = Lift1 ((0, v, z) :: R.dropLast) t`**。
`Lift1 X d = (range |X|).map fun i => (entry X 0 i, entry X 1 i + (if le1 X 0 i then d else 0), entry X 2 i)`
（`Wset:927`）⟹ **`Lift1` は行 2 を変えない。**

## ★ 反例の形を先に書く（教訓 45）＋ 見積もり（L3 の §105.2）

> **反例 ＝ 「行 2 が正の列 `j` で、`Q.take (j+1)` の中に行 2 の親がない」＝ `j` が行 2 の孤児。**
> `nextrel2` は「行 1 の祖先 ∧ 行 2 が狭義に小さい」を要求する。
> `z < 2` の断片では行 2 ∈ {0,1} なので、行 2 の親には **行 2 = 0 の列**が要る。
> **根の行 2 が `z`。`z = 1` なら根は候補にならない ⟹ `z=1` で破れやすいはず。**
>
> **⚠ 見積もり: `h2` は全体で 50 〜 80%。`z = 0` では高く、`z = 1` では低い。**

**箱と単位**: 単位 `Q`（＝ `(v, z, R, t)`）。箱 = `R` の列は 行0<4, 行1<3, 行2<=1、
`|R| = 3..5`（⟹ `|Q| = |R|`）、`v ∈ 0..2`、`z ∈ {0,1}`、`t ∈ 0..2`。
母集団 = **`hr0`（根が狭義最浅）を満たすもの**。**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import le1_root


def Lift1(X, d):
    return [(X[i][0], X[i][1] + (d if le1_root(X, i) else 0), X[i][2])
            for i in range(len(X))]


def run(L, VS, ZS, TS, R0, R1, cm):
    """`|R| = L` ⟹ `X = (0,v,z) :: R.dropLast` は長さ `L`、`Q = Lift1 X t`。"""
    COL = [(a, b, c) for a in range(R0) for b in range(R1) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for v in VS:
        for z in ZS:
            for Rd in itertools.product(COL, repeat=L - 1):   # R.dropLast
                X = [(0, v, z)] + list(Rd)
                if not all(X[0][0] < X[l][0] for l in range(1, len(X))):
                    continue                                   # hr0
                for t in TS:
                    Q = Lift1(X, t)
                    c['分母'] += 1
                    c[('z 別分母', z)] += 1
                    ok = True
                    for j in range(len(Q)):
                        if Q[j][2] > 0:
                            c[('行 2 が正の列', z)] += 1
                            P = Q[:j + 1]
                            if trio.parent(P, 2, j) is None:
                                ok = False
                                c[('★ 行 2 の孤児', z)] += 1
                                ex.setdefault(('h2 破れ', z), (v, z, list(Rd), t, j, Q))
                    c[('★ (z2) h2 成立', z, ok)] += 1
                    # (z3) 錐の外の列の割合
                    out = sum(1 for j in range(1, len(Q)) if not le1_root(Q, j))
                    c[('(z3) 錐の外の列', out)] += 1
                    c['(z3) 列の分母'] += len(Q) - 1
                    c['(z3) 錐の外の合計'] += out
    tot = c['分母']
    print(f'### |Q|={L} 行0<{R0} 行1<{R1} 行2<={cm}  `hr0` を通った `Q` {tot:8d} 本  '
          f'[{time.time()-t0:.1f}s]')
    for z in ZS:
        n_ = c[('z 別分母', z)]
        if not n_:
            continue
        y = c[('★ (z2) h2 成立', z, True)]
        print(f'  **z={z}: (z2) `h2` 成立 {y:8d} / {n_} ({100*y/n_:6.2f}%)**   '
              f'行 2 が正の列 {c[("行 2 が正の列", z)]:8d} 本中 **行 2 の孤児 {c[("★ 行 2 の孤児", z)]:8d}**')
    ally = sum(c[('★ (z2) h2 成立', z, True)] for z in ZS)
    print(f'  **★ (z2) 全体の `h2` 成立: {ally} / {tot} ({100*ally/tot:6.2f}%)**')
    print(f'  **(z3) 錐の外の列: {c["(z3) 錐の外の合計"]} / {c["(z3) 列の分母"]} '
          f'({100*c["(z3) 錐の外の合計"]/max(c["(z3) 列の分母"],1):6.2f}%)**   '
          f'`Q` あたりの本数: ' + str(dict(sorted((k[1], c[k]) for k in c
                                          if isinstance(k, tuple) and k[0] == '(z3) 錐の外の列'))))
    for k in sorted(ex, key=str):
        print(f'      {k}: v={ex[k][0]} z={ex[k][1]} R.dropLast={ex[k][2]} t={ex[k][3]} '
              f'j={ex[k][4]} Q={ex[k][5]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=5)
    a = ap.parse_args()
    for L in range(3, a.L + 1):
        run(L, (0, 1, 2), (0, 1), (0, 1, 2), 4, 3, 1)
