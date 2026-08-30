# -*- coding: utf-8 -*-
"""**課題 (u1)-(u3) ＋ (t1)(t2)（L3 / team-lead の依頼）—— 帯の幅と飛び先。**

**場面**: `S_j = mTower Q d e n ++ Bn.take (j+1)`。復活 ＝ 親が `n*|Q|` 未満。

## ★ 予想を先に書く（教訓 45）＋ 見積もり（L3 の §105.2）

**(u1)** 「親のブロック戻りは常に 1」が `n` を伸ばしても保つか。
  §R154（`n ∈ 2..4`）・§R155（`n ∈ 2..5`）で **100%**。⟹ **保つと予想。見積もり: 戻り >= 2 は 0 〜 2%。**
  ⚠ **反例の形: 「戻りが 2 以上」＝ 親が 2 つ以上前のブロック。**
  ⚠ team-lead の懸念「`n` が小さいと自明」は当たらない（`n = 5` でも 4 通りの戻りがありえた）。

**(u2)** ⚠ **§R155 で `k == L3 の式` は 1.05 / 1.96% だった。**
  ⟹ **`k*`（`entry Q 1 0 + e*k < entry Q 1 j` を満たす最大の `k`）は実際の親ブロック `n-1` より小さい。**
  ⟹ **team-lead の「`k* = n-1`」は外れるはず。見積もり: `k* = n-1` は 1 〜 5%。**
  （L3 の §144-145 は `k*` を**下界**と言っているだけで、下界が tight とは言っていない。）

**(u3)** ⚠ **§R155 の (t2)「`entry Q 1 0 < entry Q 1 j`」は 19.17 / 18.35% しか成り立たない。**
  ⟹ **復活の 80.8% は帯の**下限すら**満たさない。⟹ 帯に入るのは 0 〜 20% と見積もる。**

**(t1)(t2)** L3 の予測 100%。§R155 で既に 80.83 / 19.17% と出ている。**`n` を伸ばして再確認する。**

**箱と単位**: 単位 `(Q,d,e,n,j)`。箱 = 行0<4, 行1<4, 行2<=1、`|Q| = 3..4`、
`d,e ∈ 0..3`、**`n ∈ 2..7`**（team-lead の指定）。母集団 = 根が狭義最浅 ∧ **復活**。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow, le1_root
from r113 import mTower
from r141 import block


def run(cm, L, DE, NS, R1):
    COL = [(a, b, c) for a in range(4) for b in range(R1) for c in range(cm + 1)]
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
                            if par is None or par >= n * L:
                                continue
                            k, q = divmod(par, L)
                            back = n - k
                            jk = 'j=0' if j == 0 else '★ j>=1'
                            c[(jk, '復活')] += 1
                            c[(jk, 'n 別', n, '戻り', min(back, 3))] += 1
                            c[('★ (u1) 戻り', back)] += 1
                            # (u2) `k*`
                            ks = [kk for kk in range(n + 1) if Q[0][1] + e * kk < Q[j][1]]
                            kst = max(ks) if ks else None
                            c[('(u2) k* == n-1', kst == n - 1)] += 1
                            c[('(u2) k* <= 実際の k（下界として正しいか）',
                               kst is None or kst <= k)] += 1
                            if kst is not None and kst > k:
                                ex.setdefault('u2 下界が破れる', (Q, d, e, n, j, k, kst))
                            # (u3) 帯の幅
                            lo = Q[0][1] + e * (n - 1); hi = Q[0][1] + e * n
                            c[('(u3) 1 ブロック帯に入る', lo < Q[j][1] <= hi)] += 1
                            c[('(u3) L3 の広い帯に入る', Q[0][1] < Q[j][1] <= hi)] += 1
                            # (t1)(t2)
                            c[(jk, '(t1) 錐の外', not le1_root(Q, j))] += 1
                            c[(jk, '(t2) 行1 が根より上', Q[0][1] < Q[j][1])] += 1
                            if back >= 2:
                                ex.setdefault('★ 戻り >= 2', (Q, d, e, n, j, par, k, back))
    print(f'### 行2<={cm} |Q|={L} 行1<{R1}  [{time.time()-t0:.1f}s]')
    tot = sum(c[(jk, '復活')] for jk in ('j=0', '★ j>=1'))
    print(f'  復活 {tot:9d}（j=0 {c[("j=0", "復活")]:9d} ／ j>=1 {c[("★ j>=1", "復活")]:8d}）')
    print('  **★ (u1) 親のブロック戻り**: ', dict(sorted((k[1], c[k]) for k in c
                                            if isinstance(k, tuple) and len(k) == 2 and k[0] == '★ (u1) 戻り')))
    for n in NS:
        row = {kk[4]: c[kk] for kk in c if isinstance(kk, tuple) and len(kk) == 5
               and kk[2] == n and kk[3] == '戻り'}
        if row:
            print(f'      n={n} の戻り分布: {dict(sorted(row.items()))}')
    for lab in ('(u2) k* == n-1', '(u2) k* <= 実際の k（下界として正しいか）',
                '(u3) 1 ブロック帯に入る', '(u3) L3 の広い帯に入る'):
        y = c[(lab, True)]; nn = c[(lab, False)]
        if y + nn:
            print(f'  **{lab}: {y:9d} / {y+nn} ({100*y/(y+nn):6.2f}%)**')
    for jk in ('★ j>=1', 'j=0'):
        t_ = c[(jk, '復活')]
        if t_:
            print(f'  {jk}: **(t1) 錐の外 {100*c[(jk, "(t1) 錐の外", True)]/t_:6.2f}%**  '
                  f'**(t2) 行1 が根より上 {100*c[(jk, "(t2) 行1 が根より上", True)]/t_:6.2f}%**')
    for k in sorted(ex):
        print(f'      {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1,):
        for R1 in (3, 4):
            for L in range(3, a.L + 1):
                run(cm, L, range(4), (2, 3, 4, 5, 6, 7), R1)
