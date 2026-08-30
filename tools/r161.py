# -*- coding: utf-8 -*-
"""**課題 (z1)（L3 の反証テスト）—— ブロッカーなしで `j >= 1` の復活は起きるか。**

## 前提を `file:line` から逐語で写した（教訓 2）

    `L105Cap:10813` **`le1_zero_of_no_blocker`**
      `(hr0 : ∀ l, 0 < l → l < |Q| → entry Q 0 0 < entry Q 0 l)`   ← 根が行 0 で狭義最浅
      **`(hnb : ∀ l, 0 < l → l < |Q| → entry Q 1 0 < entry Q 1 l)`** ← **ブロッカーなし**
      `⟹ le1 Q 0 j`
    `L105Cap:10824` `block_blockParent_of_no_blocker` … 前提に **`hj1 : 0 < j`**
    §154.1 … **ブロッカーなし ∧ `entry Q 2 0 = 0` ⟹ 非根の列はすべてブロック内に親**
    §155 … **`j = 0` は必ず復活**（ブロッカーがなくても）

## ★ 反例の形を先に書く（教訓 45）＋ 見積もり

> **反例 ＝ 「ブロッカーなし ∧ `entry Q 2 0 = 0` ∧ `j >= 1` なのに復活」1 件。**
> **L3 の予測は 0 件。私の見積もりも 0 〜 2%**（§R159 の 555,201 件の復活は
> §155 より全部 `j = 0` のはず。そこを確かめる）。
> ⚠ **`entry Q 2 0` の条件を落とした版も測る**（`z >= 1` で破れるなら §154 の前提が効いている）。

**箱と単位**: 単位 `(Q,d,e,n,j)`。箱 = 行0<4, 行1<4, 行2<=cm（**3 段**）、`|Q| = 3..4`、
`d ∈ 0..3`、`e ∈ 0..4`、`n ∈ 2..5`。母集団 = 根が狭義最浅 ∧ **ブロッカーなし**。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block


def nb(Q):
    """`hnb`: ブロッカーなし。"""
    return all(Q[0][1] < Q[l][1] for l in range(1, len(Q)))


def run(cm, L, DS, ES, NS):
    COL = [(a, b, c) for a in range(4) for b in range(4) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            if not nb(Q):
                continue
            zk = 'z=0' if Q[0][2] == 0 else 'z>=1'
            for d in DS:
                for e in ES:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bn = block(Q, d, e, n)
                        for j in range(L):
                            S = T + Bn[:j + 1]
                            last = len(S) - 1
                            par = trio.parent(S, srow(S, last), last)
                            jk = 'j=0' if j == 0 else '★ j>=1'
                            key = (zk, jk)
                            c[(key, '分母')] += 1
                            if par is None:
                                c[(key, '(i) 孤児')] += 1
                            elif par >= n * L:
                                c[(key, '(ii) 同ブロック')] += 1
                            else:
                                c[(key, '★ (iii) 復活')] += 1
                                if jk == '★ j>=1':
                                    ex.setdefault(('⛔ 反例', zk),
                                                  (Q, d, e, n, j, par, srow(S, last)))
    print(f'### 行2<={cm} |Q|={L}  ブロッカーなしの `Q` のみ  [{time.time()-t0:.1f}s]')
    for zk in ('z=0', 'z>=1'):
        for jk in ('★ j>=1', 'j=0'):
            key = (zk, jk); tot = c[(key, '分母')]
            if not tot:
                continue
            rv = c[(key, '★ (iii) 復活')]
            mark = '  ★★★ §154 の射程' if (zk == 'z=0' and jk == '★ j>=1') else ''
            print(f'  {zk} {jk}: 分母 {tot:9d}  (i) 孤児 {c[(key,"(i) 孤児")]:9d}  '
                  f'(ii) 同ブロック {c[(key,"(ii) 同ブロック")]:9d}  '
                  f'**(iii) 復活 {rv:9d} ({100*rv/tot:6.3f}%)**{mark}')
    for k in sorted(ex, key=str):
        print(f'      {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(3, a.L + 1):
            run(cm, L, range(4), range(5), (2, 3, 4, 5))
