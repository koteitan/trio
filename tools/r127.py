# -*- coding: utf-8 -*-
"""**課題 R127（SESSION §293）—— 「錐の外の `b`」がどれだけ出るか。**

**主語（教訓 2: 前提と除外条件を写す）** `L105Cap:6658` `nextrel1_gexp_no_enter`:

    前提 `hq : q < Lb`  `hq1 : 0 < q`  **`hcone : le1 M 0 (0 + q)`**
         `hup : ∀ l, 0 < l → l <= 0 + Lb → entry M 0 0 < entry M 0 l`（根が狭義最浅）
    結論 `nextrel1 (gexp M 0 Lb d0 d1 n) a (0 + (k*Lb+q))` ⟹ `k*Lb <= a`

⟹ **分岐条件は `Q` 側の `le1 Q 0 q`**（`q < Lb = |Q|` なので `le1 M 0 q` と同値）。
⟹ **`q = 0`（根）は除外**（`hq1`）。根は反射で必ず錐の中。

**⚠ 「錐の外」は `¬ le1 Q 0 q` であって、塔の `k` には依らない**（`q` だけで決まる）。
⟹ **(a3)「`k` が大きいほど増えるか」は定義から「増えも減りもしない」。**
   それでも塔側 `¬ le1 T 0 (k*Lb+q)` を直接測って、`k` 依存と
   `le1_mTower_block`（`:6574`、前提 `0 < e`）を検算する。**`e = 0` を陰性対照にする。**

**(a2) 形を先に書く（教訓 45）**: `le1` の 1 歩は行 1 の**狭義増加**を要求するので、
`q != 0` が錐の中なら `entry Q 1 0 < entry Q 1 q` が**必要**。⟹ 錐の外は少なくとも 2 種:

    **(G1) `entry Q 1 q <= entry Q 1 0`** … 行 1 が根以下。**算術だけの理由**
    **(G2) `entry Q 1 0 < entry Q 1 q` なのに錐の外** … **ブロッカーの向こう側**（§59.1）
                                                        ← **こちらが本当の残差**

**箱と単位**: 単位 = 列 `Q` の位置 `q`（`1 <= q < |Q|`）。
箱 = 行0 ∈ {0..3}, 行1 ∈ {0..2}, 行2 ∈ {0..cm}（**3 段**）、`|Q| = 2..5`（**3 段以上**）。
母集団 = `2 <= |Q|` ∧ **根が狭義最浅**。**`W` 所属は判定しない**（明記）。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r126 import srow, le1_root
from r113 import mTower


def runQ(cm, L):
    """(a1)(a2) `Q` 側: 位置 `q`（1 <= q < |Q|）が錐の外になる割合。"""
    COL = [(d, b, c) for d in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            z = root[2]
            for q in range(1, L):
                inc = le1_root(Q, q)
                i = srow(Q, q)
                c['全体'] += 1
                c[('srow', i)] += 1
                c[('z', z)] += 1
                if inc:
                    continue
                c['錐の外'] += 1
                c[('外srow', i)] += 1
                c[('外z', z)] += 1
                if Q[q][1] <= Q[0][1]:
                    c['G1 行1が根以下'] += 1
                    ex.setdefault('G1', (Q, q))
                else:
                    c['★ G2 行1は根より上なのに錐の外（ブロッカー）'] += 1
                    ex.setdefault('G2', (Q, q))
    tot = c['全体']; out = c['錐の外']
    print(f'  行2<={cm} |Q|={L}: 分母 {tot:9d}  **錐の外 {out:8d} ({100*out/max(tot,1):6.2f}%)**')
    for i in (0, 1, 2):
        n = c[('srow', i)]; o = c[('外srow', i)]
        if n:
            print(f'      srow(q)={i}: 分母 {n:9d}  錐の外 {o:8d} ({100*o/n:6.2f}%)')
    for z in range(cm + 1):
        n = c[('z', z)]; o = c[('外z', z)]
        if n:
            print(f'      根の行2 z={z}: 分母 {n:9d}  錐の外 {o:8d} ({100*o/n:6.2f}%)')
    g1 = c['G1 行1が根以下']; g2 = c['★ G2 行1は根より上なのに錐の外（ブロッカー）']
    print(f'      **G1 行1が根以下          {g1:8d} ({100*g1/max(out,1):6.2f}% of 錐の外)**')
    print(f'      **★ G2 ブロッカーの向こう {g2:8d} ({100*g2/max(out,1):6.2f}% of 錐の外)**')
    for k in sorted(ex):
        print(f'      最小例 {k}: Q={ex[k][0]} q={ex[k][1]}')


def runT(cm, L, DS, ES, NS):
    """(a3) 塔側: `¬ le1 T 0 (k*Lb+q)` を `k` 別に。`le1_mTower_block` の検算も。"""
    COL = [(d, b, c) for d in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            base = [le1_root(Q, q) for q in range(L)]
            for d in DS:
                for e in ES:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        for k in range(n):
                            for q in range(1, L):
                                b = k * L + q
                                inT = le1_root(T, b)
                                c[(('e=0' if e == 0 else 'e>=1'), 'k=%d' % k,
                                   '錐の中' if inT else '錐の外')] += 1
                                key = ('e=0' if e == 0 else 'e>=1')
                                if inT == base[q]:
                                    c[(key, '一致')] += 1
                                else:
                                    c[(key, '**le1_mTower_block が破れる**')] += 1
                                    ex.setdefault(key, (Q, d, e, n, k, q, base[q], inT))
    print(f'  行2<={cm} |Q|={L}  塔側:')
    for key in ('e=0', 'e>=1'):
        ok = c[(key, '一致')]; bad = c[(key, '**le1_mTower_block が破れる**')]
        if ok + bad:
            print(f'      {key}: 分母 {ok+bad:9d}  `le1 T 0 (k*Lb+q)` = `le1 Q 0 q` '
                  f'**{ok:9d}（{100*ok/(ok+bad):6.2f}%）**  破れ **{bad:8d}**')
    for k in range(max(NS)):
        row = []
        for key in ('e=0', 'e>=1'):
            i = c[(key, 'k=%d' % k, '錐の中')]; o = c[(key, 'k=%d' % k, '錐の外')]
            if i + o:
                row.append(f'{key} 錐の外 {o:8d}/{i+o:8d} ({100*o/(i+o):6.2f}%)')
        if row:
            print(f'      k={k}: ' + '   '.join(row))
    for key in sorted(ex):
        Q, d, e, n, k, q, bq, bt = ex[key]
        print(f'      ★ 破れの例 {key}: Q={Q} d={d} e={e} n={n} k={k} q={q} '
              f'（Q 側 {bq} / 塔側 {bt}）')


if __name__ == '__main__':
    print('### R127 (a1)(a2) `Q` 側: 位置が根の行 1 錐の外になる割合')
    for cm in (1, 2, 3):
        for L in (2, 3, 4, 5):
            runQ(cm, L)
        print()
    print('### R127 (a3) 塔側: `k` 依存 ＋ `le1_mTower_block`（前提 `0 < e`）の検算')
    for cm in (1, 2):
        for L in (2, 3):
            runT(cm, L, (0, 1, 2), (0, 1, 2), (3,))
