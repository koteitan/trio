# -*- coding: utf-8 -*-
"""**R140 の続き（自発）—— 写す塊 `B` の形と、接頭辞が縮むか。**

**§R151 で出た形**: `S⟦m'⟧ = S.take j0 ++ mTower B d0 d1 m'`、`B = S[j0 : last]`。
`S = A ++ D^m` で `j0 < |A|` なので:

    **`B = A[j0:] ++ D^(m-1) ++ D.dropLast`**（`A` の末尾 `|A|−j0` 列 ＋ 写し ＋ 切った写し）
    **接頭辞は `S.take j0 = A.take j0`、長さ `j0 < |A|`**

## ★ 予想を先に書く（教訓 45）＋ 充足率の見積もり（L3 の §105.2）

> **★ 本命の予想: `j0 < |A|` なので、展開のたびに**接頭辞が真に縮む**。**
> **⟹ 何段かで `j0 = 0` に着き、そこは接頭辞なしの `mTower` ＝ `MTowerClosedS` の形。**
> **⟹ `PrefixCopiesOpen` は「接頭辞の長さ」に関する整礎帰納で `MTowerClosedS` に落ちる。**
>
> **⚠ ただし縮むのは「その段の `A`」に対してであって、次の段の悪根が
> 前の接頭辞のさらに手前に行く保証は無い。⟹ そこが反例の形。**
> **⚠ 反例の形: 「次の段の `j0'` が、その段の接頭辞の長さ以上（＝ 縮まない）」。**
> **⚠ 充足率の見積もり: 縮まない事例は **0 〜 10%**。**
>
> **⚠ §R151 の (s3) より `|A| − j0 <= |Q| − 1` なので、1 段で縮む幅は最大 `|Q| − 1`。**
> **⟹ `j0 = 0` に着くまで約 `|A| / (|Q|−1)` 段。有限。**

**箱と単位**: 単位 = 鎖の各段。母集団 = §R151 と同じ（親が `A` の中、側条件つき）。
箱 = 行0 ∈ 1..3、行1 < 3、行2 = 0、`|Q| = 2..4`、`e ∈ 1..3`、`n ∈ 1..3`、`m ∈ 1..3`、`m' ∈ 1..3`。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r98 import oper_lean


def shTower(Q, e, n):
    return [(c[0] + k * e, c[1], c[2]) for k in range(n) for c in Q]


def badroot(S):
    if len(S) < 2:
        return None
    last = len(S) - 1
    return trio.parent(S, srow(S, last), last)


def run(L, ES, NS, MS, MPS, R1, cap=15):
    COL = [(a, b, 0) for a in range(1, 4) for b in range(R1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for v in range(R1):
        for t in itertools.product(COL, repeat=L - 1):
            Q = [(0, v, 0)] + list(t)
            for e in ES:
                for n in NS:
                    T = shTower(Q, e, n)
                    for j0p in range(1, len(T)):
                        A = T[:j0p]; D = T[j0p:]
                        if not D or not all(D[0][0] <= p[0] for p in D):
                            continue
                        for m in MS:
                            S0 = list(A) + D * m
                            j0 = badroot(S0)
                            if j0 is None or j0 >= len(A):
                                continue          # 親が `A` の中の枝だけ
                            c[('出発点の悪根', '0（接頭辞なし）' if j0 == 0 else '>=1')] += 1
                            if j0 == 0:
                                continue          # 既に到達点。鎖をたどる意味が無い
                            for mp in MPS:
                                # 鎖をたどって接頭辞（悪根の位置）が縮むか
                                S = S0; prev = j0; steps = 0
                                shrink_ok = True
                                while steps < cap:
                                    S = oper_lean(S, mp)
                                    if len(S) < 2:
                                        break
                                    nj = badroot(S)
                                    if nj is None:
                                        c['鎖: 孤児に着いた'] += 1
                                        break
                                    c['段の分母'] += 1
                                    # ⚠ 悪根が既に 0 なら「接頭辞が消えている」＝ 到達点。
                                    #    そこを「縮まない」と数えていたのがバグだった。
                                    if nj == 0:
                                        c[('★★ 接頭辞が消えるまでの段数', min(steps + 1, 6))] += 1
                                        c[('★ 悪根が真に縮む（0 到達を除く）', True)] += 1
                                        break
                                    c[('★ 悪根が真に縮む（0 到達を除く）', nj < prev)] += 1
                                    if nj >= prev:
                                        shrink_ok = False
                                        ex.setdefault('縮まない', (Q, e, n, j0p, m, mp,
                                                                prev, nj, steps))
                                        break
                                    prev = nj; steps += 1
                                else:
                                    c['⛔ 打ち切り（cap 段で終わらない）'] += 1
                                c[('鎖が縮み続けた', shrink_ok)] += 1
    tot = c['段の分母']
    print(f'### |Q|={L} 行1<{R1}  段の分母 {tot:9d}  [{time.time()-t0:.1f}s]')
    if not tot:
        print('  （0 件）\n'); return
    y = c[('★ 悪根が真に縮む（0 到達を除く）', True)]
    nn = c[('★ 悪根が真に縮む（0 到達を除く）', False)]
    print(f'  **★ 各段で悪根が真に縮む: {y:9d} / {y+nn} ({100*y/(y+nn):6.2f}%)**  '
          f'縮まない {nn}')
    print(f'  鎖が最後まで縮み続けた: {c[("鎖が縮み続けた", True)]} / '
          f'{c[("鎖が縮み続けた", True)]+c[("鎖が縮み続けた", False)]}   '
          f'孤児に着いた {c["鎖: 孤児に着いた"]}   ⛔ 打ち切り {c["⛔ 打ち切り（cap 段で終わらない）"]}')
    print('  **★★ 接頭辞が消える（悪根 = 0）までの段数**: ',
          dict(sorted((k[1], c[k]) for k in c
                      if isinstance(k, tuple) and k[0] == '★★ 接頭辞が消えるまでの段数')))
    print('  出発点の悪根: ', dict(sorted((k[1], c[k]) for k in c
                                      if isinstance(k, tuple) and k[0] == '出発点の悪根')))
    for k in sorted(ex):
        print(f'      {k} の例: Q={ex[k][0]} e={ex[k][1]} n={ex[k][2]} j0\'={ex[k][3]} '
              f'm={ex[k][4]} m\'={ex[k][5]} 前の悪根={ex[k][6]} 次の悪根={ex[k][7]} 段={ex[k][8]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for R1 in (3,):
        for L in range(2, a.L + 1):
            run(L, (1, 2, 3), (1, 2, 3), (1, 2, 3), (1, 2, 3), R1)
