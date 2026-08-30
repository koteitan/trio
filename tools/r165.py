# -*- coding: utf-8 -*-
"""**課題 (H3'')（L3 / team-lead の依頼）—— 消費側が「鎖に沿った行 1 の単調性」を供給するか。**

**消費側の `Q`**: `Q = Lift1 ((0, v, z) :: R.dropLast) t`。

**「鎖に沿った行 1 の狭義単調性」の定義**（`nextrel0` の親鎖に沿って）:

    **`∀ j, 0 < j < |Q| → entry Q 1 (parent0 j) < entry Q 1 j`**
    （`parent0 j` ＝ `Q` の行 0 の親。根が狭義最浅なので必ず存在する）

**比較する「ブロッカーなし」**（`L105Cap:10813` の `hnb`）:

    **`∀ l, 0 < l < |Q| → entry Q 1 0 < entry Q 1 l`**（**根とだけ**比べる）

⟹ **鎖に沿った単調性 ⟹ ブロッカーなし**（鎖をたどれば根に着くので推移的）。**前者のほうが強い。**

## ★ 予想を先に書く（教訓 45）＋ 見積もり（L3 の §105.2）

> **team-lead の懸念（消費側の `Q` は普通ブロッカーを持つ）が正しければ、
> 鎖に沿った単調性はもっと成り立たない。**
> **⚠ 見積もり: 鎖に沿った単調性 5 〜 20%、ブロッカーなしより低い。**
> **⚠ 反例の形: `R.dropLast` に行 1 が `v + t` 以下の列がある ⟹ その列で鎖が下がる。**

**箱と単位**: 単位 `Q`（＝ `(v, z, R.dropLast, t)`）。箱 = `R` の列は 行0<4, 行1<3, 行2<=1、
`|Q| = 3..5`、`v ∈ 0..2`、`z ∈ {0,1}`、`t ∈ 0..2`。母集団 = **`hr0` を満たすもの**。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r163 import Lift1
from r126 import le1_root


def chainmono(Q):
    """鎖に沿った行 1 の狭義単調性。破れた `j` のリストを返す。"""
    bad = []
    for j in range(1, len(Q)):
        p = trio.parent(Q, 0, j)
        if p is None:
            bad.append((j, None))
        elif not (Q[p][1] < Q[j][1]):
            bad.append((j, p))
    return bad


def nb(Q):
    return all(Q[0][1] < Q[l][1] for l in range(1, len(Q)))


def run(L, VS, ZS, TS, R0, R1, cm):
    COL = [(a, b, c) for a in range(R0) for b in range(R1) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for v in VS:
        for z in ZS:
            for Rd in itertools.product(COL, repeat=L - 1):
                X = [(0, v, z)] + list(Rd)
                if not all(X[0][0] < X[l][0] for l in range(1, len(X))):
                    continue
                for t in TS:
                    Q = Lift1(X, t)
                    c['分母'] += 1
                    bad = chainmono(Q)
                    cm_ok = not bad
                    nb_ok = nb(Q)
                    c[('★ (a) 鎖に沿った単調', cm_ok)] += 1
                    c[('(c) ブロッカーなし', nb_ok)] += 1
                    c[('両者', cm_ok, nb_ok)] += 1
                    c[('錐の外の列がある', any(not le1_root(Q, j) for j in range(1, len(Q))))] += 1
                    if bad:
                        c[('(b) 破れた位置 j', bad[0][0])] += 1
                        c[('(b) 破れの型', '親と等しい' if bad[0][1] is not None
                           and Q[bad[0][1]][1] == Q[bad[0][0]][1] else '親より小さい')] += 1
                        ex.setdefault('破れ', (v, z, list(Rd), t, Q, bad[:2]))
                    else:
                        ex.setdefault('成立', (v, z, list(Rd), t, Q))
    tot = c['分母']
    a = c[('★ (a) 鎖に沿った単調', True)]; b = c[('(c) ブロッカーなし', True)]
    print(f'### |Q|={L} 行0<{R0} 行1<{R1} 行2<={cm}  `hr0` を通った `Q` {tot:9d} 本  '
          f'[{time.time()-t0:.1f}s]')
    print(f'  **★ (a) 鎖に沿った行 1 の狭義単調 … {a:9d} ({100*a/tot:6.2f}%)**')
    print(f'  **(c) ブロッカーなし（根とだけ比較）… {b:9d} ({100*b/tot:6.2f}%)**')
    print(f'      両者の関係: 鎖○∧ブロ○ {c[("両者", True, True)]}  '
          f'鎖○∧ブロ× **{c[("両者", True, False)]}**（0 のはず）  '
          f'鎖×∧ブロ○ {c[("両者", False, True)]}  鎖×∧ブロ× {c[("両者", False, False)]}')
    print(f'      錐の外の列がある `Q` … {c[("錐の外の列がある", True)]} '
          f'({100*c[("錐の外の列がある", True)]/tot:6.2f}%)')
    print('  **(b) 破れた位置 `j`**: ', dict(sorted((k[1], c[k]) for k in c
                                          if isinstance(k, tuple) and k[0] == '(b) 破れた位置 j')),
          '   型: ', dict(sorted((k[1], c[k]) for k in c
                             if isinstance(k, tuple) and k[0] == '(b) 破れの型')))
    for k in sorted(ex):
        print(f'      {k}: v={ex[k][0]} z={ex[k][1]} R.dropLast={ex[k][2]} t={ex[k][3]} Q={ex[k][4]}'
              + (f' 破れ={ex[k][5]}' if k == '破れ' else ''))
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=5)
    a = ap.parse_args()
    for L in range(3, a.L + 1):
        run(L, (0, 1, 2), (0, 1), (0, 1, 2), 4, 3, 1)
