# -*- coding: utf-8 -*-
"""**課題 (s1)-(s3)（L3 の直接依頼）—— `hstep` の場面での「復活」。**

**場面**（§94/§138/§140）: `T = mTower Q d e n`、`Bn = Lift1 (shiftr01 (d*n) 0 Q) (e*n)`、
**`S_j = T ++ Bn.take (j+1)`**。足した列 `Bn[j]` の親を `par`。

    `par is None` … **(i) 孤児**（§139 で場合分けにより消える）
    `par >= n*|Q|` … **(ii) 同じブロック**（`p = par − n*|Q|`。窓 `j − p <= |Q|−1` ⟹ **測度が減る**）
    `par <  n*|Q|` … **(iii) 手前のブロック ＝ 復活**（**核**）

## ★ 予想を先に書く（教訓 45）＋ 充足率の見積もり（L3 の §105.2）

**(s1)** §R153 で既に部分的に出ている: `j >= 1` で **1.97 〜 2.95%**、`j = 0` で **29.8 〜 41.3%**。
⚠ **`j = 0` はブロックが 1 列なので自分の中に親を持てない**（§104）⟹ 必ず (ii) に入れない。
**⟹ 全 `j` を込みにした復活率は `(1/|Q|)*35% + ((|Q|-1)/|Q|)*2.5%` くらい。
`|Q|=4` なら約 10.6%。⚠ 見積もり: 8 〜 14%。**

⚠ **team-lead の読み「§R152 の 6.44% ＝ (iii) の割合かもしれない」について:**
**⟹ 場面が違う**（あちらは `S = A ++ D^m` の展開、こちらは `hstep`）。
**⟹ 一致するとは限らない。数字を並べて確かめる。**

**(s2) 予想**: **末尾 `j = |Q|−1` に集中するが、末尾だけではない。**
根拠: §R153 の `j >= 1` の最小例は `j = 3 = |Q|−1` だったが、`p = 0` は `j` の全域で起きていた。
**⚠ 見積もり: 末尾が 60 〜 90%。**

**(s3) 予想**: **1 つ前のブロックだけ、100%。** 根拠: §R134（F2b）で「復活先は常に 1 つ前、100%」。
⚠ **ただし場面が違う**（あちらは塔の末尾列、こちらはブロックの途中の列）。
**⚠ 見積もり: 1 つ前が 90 〜 100%。**

**箱と単位**: 単位 `(Q, d, e, n, j)`。箱 = 行0<4, 行1<3, 行2<=cm（**3 段**）、
`|Q| = 2..4`、`d,e ∈ 0..3`、**`n ∈ 2..4`**（`n >= 2` でないと「手前のブロック」が無い）。
母集団 = **根が狭義最浅**。**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow, le1_root
from r113 import mTower
from r141 import block


def run(cm, L, DE, NS):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            for d in DE:
                for e in DE:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bn = block(Q, d, e, n)
                        for j in range(L):
                            S = T + Bn[:j + 1]
                            last = len(S) - 1
                            par = trio.parent(S, srow(S, last), last)
                            c['分母'] += 1
                            c[('j 別分母', j)] += 1
                            if par is None:
                                c['(i) 孤児'] += 1
                                continue
                            if par >= n * L:
                                c['(ii) 同じブロック'] += 1
                                p = par - n * L
                                c[('(ii) 窓 j-p', j - p)] += 1
                                c[('(ii) 窓 < |Q|', (j - p) < L)] += 1
                                continue
                            # (iii) 復活
                            c['★ (iii) 復活'] += 1
                            c[('(s2) 復活の j', j)] += 1
                            c[('(s2) 末尾か', j == L - 1)] += 1
                            kp = par // L
                            c[('★ (s3) 戻り', n - kp)] += 1
                            c[('(s3) 親の列 q', par % L)] += 1
                            ex.setdefault(('復活', 'j=末尾' if j == L - 1 else 'j=途中'),
                                          (Q, d, e, n, j, par, kp, n - kp))
    tot = c['分母']; rev = c['★ (iii) 復活']
    print(f'### 行2<={cm} |Q|={L}  分母 {tot:9d}  [{time.time()-t0:.1f}s]')
    print(f'  **(i) 孤児 {c["(i) 孤児"]:9d} ({100*c["(i) 孤児"]/tot:6.2f}%)**  '
          f'**(ii) 同じブロック {c["(ii) 同じブロック"]:9d} ({100*c["(ii) 同じブロック"]/tot:6.2f}%)**  '
          f'**★ (iii) 復活 {rev:9d} ({100*rev/tot:6.2f}%)**')
    ok = c[('(ii) 窓 < |Q|', True)]; ng = c[('(ii) 窓 < |Q|', False)]
    print(f'  **(ii) の窓 `j−p < |Q|`: {ok} / {ok+ng} ({100*ok/max(ok+ng,1):6.2f}%)**   '
          f'窓の長さ: ' + str(dict(sorted((k[1], c[k]) for k in c
                                    if isinstance(k, tuple) and k[0] == '(ii) 窓 j-p'))))
    if rev:
        print('  **(s2) 復活の `j`**: ', dict(sorted((k[1], c[k]) for k in c
                                            if isinstance(k, tuple) and k[0] == '(s2) 復活の j')),
              f'   **末尾 `j={L-1}` の割合: {c[("(s2) 末尾か", True)]} / {rev} '
              f'({100*c[("(s2) 末尾か", True)]/rev:6.2f}%)**')
        print('  **★ (s3) 親のブロック戻り**: ', dict(sorted((k[1], c[k]) for k in c
                                               if isinstance(k, tuple) and k[0] == '★ (s3) 戻り')),
              '   親の列 q: ', dict(sorted((k[1], c[k]) for k in c
                                     if isinstance(k, tuple) and k[0] == '(s3) 親の列 q')))
    print('  `j` 別の分母: ', dict(sorted((k[1], c[k]) for k in c
                                   if isinstance(k, tuple) and k[0] == 'j 別分母')))
    for k in sorted(ex, key=str):
        print(f'      例 {k}: Q={ex[k][0]} d={ex[k][1]} e={ex[k][2]} n={ex[k][3]} '
              f'j={ex[k][4]} 親={ex[k][5]}（ブロック {ex[k][6]}、戻り {ex[k][7]}）')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(2, a.L + 1):
            run(cm, L, range(4), (2, 3, 4))
