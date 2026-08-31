# -*- coding: utf-8 -*-
"""**課題 R123 —— 新しい核 `MTowerClosedS` を壊しにいく。**

⚠ 定義を `file:line` から写した（教訓 1・2・25）:

    `L105.MTowerClosedS`（`L105Cap.lean:5618`）
      ∀ (u d e n : ℕ) (Q : TrioSeq), **`Q ∈ W u`** →
        **`∀ j, 1 <= j → j < |Q| → entry Q 0 0 < entry Q 0 j`**（根が行 0 で狭義最浅）→
        **`mTower Q d e n ∈ W u`**
    `L105.mTower`（`:4177`）＝ `flatMap k => Lift1 (shiftr01 (d0*k) 0 Q) (d1*k)`

★ **測る前に書く（教訓 45）: そもそも私の計器で反証できるか。**

    ブロック 0（`k=0`）＝ `Lift1 (shiftr01 0 0 Q) 0` ＝ **`Q` そのもの**
    ⟹ **`mTower Q d e n` の根は `Q[0]`** ⟹ `lev (mTower …) 0 = lev Q 0`
    前提 `Q ∈ W u` ＋ `Wset.lev_root_le_of_mem_W`（`:2161`、緑）⟹ **`lev Q 0 <= u`**
    ⟹ **結論の根の `lev` は `u` 以下が自動**
    ⟹ **§R94 の定理より、健全な反証器は絶対に鳴らない。§R95 の表の「鳴りえない」に入る。**

**⟹ (w1)「反例を探す」は、私の計器では原理的に不可能。** そう報告する。
**代わりに測れるもの**: 前提の充足率・空虚性（w3）、対照（w4）、
そして**証明の障害**（`W_add` の `rsum` が接ぎ目で破れるか）。

**`Q ∈ W u` の扱い**: **健全な判定器 `inW` が `True` を返した `Q` だけを使う**（構成的。
`True` は健全＝本当に `W u` の元）。⟹ **上位集合ではなく、確実に前提を満たす母集団。**
"""
import sys, itertools, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r89 import inW, lev
from r113 import Lift1, sh


def mTower(Q, d, e, n):
    out = []
    for k in range(n):
        out += Lift1(sh(Q, d * k), e * k)
    return out


def shallowest(Q):
    return all(Q[0][0] < Q[j][0] for j in range(1, len(Q)))


def run(COL, Lq, US, DS, ES, NS, label, depth=9, maxlen=30):
    memo = {}
    c = Counter(); ex = {}
    for lq in Lq:
        for Qt in itertools.product(COL, repeat=lq):
            Q = list(Qt)
            for u in US:
                # ★ 前提 `Q ∈ W u` を**健全な判定器で確認**（True だけ採用）
                if inW(Q, u, depth, memo, maxlen) is not True:
                    c['前提 `Q ∈ W u` が確認できない（除外）'] += 1
                    continue
                sh_ok = shallowest(Q)
                c['(w3) 根が狭義最浅' if sh_ok else '(w3) 根が狭義最浅でない'] += 1
                for d in DS:
                    for e in ES:
                        for n in NS:
                            T = mTower(Q, d, e, n)
                            # 根の検算（反証可能性の判定の根拠）
                            if T:
                                c['根 = Q[0]' if tuple(T[0]) == tuple(Q[0])
                                  else '**根が変わる**'] += 1
                                c['lev(根) <= u' if lev(T[0]) <= u
                                  else '**lev(根) > u（反証器が鳴りうる）**'] += 1
                            r = inW(T, u, depth, memo, maxlen)
                            key = ('VIOL' if r is False else 'ok' if r is True
                                   else 'unknown')
                            tag = '前提 OK' if sh_ok else '**対照: 最浅でない**'
                            c[f'{tag} / {key}'] += 1
                            if r is False:
                                ex.setdefault(f'{tag} VIOL', (Q, u, d, e, n, T))
                            # 接ぎ目の rsum（W_add が使えるか）
                            if n >= 2 and T:
                                B = Lift1(sh(Q, d * (n - 1)), e * (n - 1))
                                A = mTower(Q, d, e, n - 1)
                                if B and A:
                                    ok = all(B[0][0] <= p[0] for p in A + B)
                                    c['接ぎ目の rsum が成立' if ok
                                      else '**接ぎ目の rsum が破れる（W_add 不可）**'] += 1
    print(f'### {label}')
    for k in sorted(c, key=str):
        print(f'  {k:48s} {c[k]:9d}')
    for k in sorted(ex):
        print(f'  ★ {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    a = ap.parse_args()
    # 箱 1: 行 2 <= 1、d と e を 0 込みで振る（L3 の指定: `e > 0` と `d = 0` を含む）
    run([(dd, b, cc) for dd in (0, 1, 2) for b in (0, 1) for cc in (0, 1)],
        (1, 2, 3), (0, 1, 2), (0, 1, 2), (0, 1, 2), (1, 2, 3),
        'R123 (a) 箱 行2<=1、d,e ∈[0,2]（`d=0` と `e>0` を含む）')
