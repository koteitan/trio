# -*- coding: utf-8 -*-
"""**課題 (w1)（team-lead の疑問）—— 鎖の各段で `(d, e)` は本当に自由か。**

## ⚠ team-lead の疑問（正しい可能性が高い）

L3 の §165: **`T_{j+1}⟦m⟧ = T_p ++ mTower V d0' d1' m`**。
`Trio.lean:98` の `oper`:

    `let d0 := if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0`
    `let d1 := if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0`

⟹ **次の塔の `(d0, d1)` は**展開が決める**。自由ではない。**
⟹ **§R164-4 / §R167 の鎖は `(d,e)` を毎段自由に選んでいた ⟹ 過大評価だった可能性。**

## ★ 予想を先に書く（教訓 45）＋ 見積もり

> **`(d,e)` を決め打ちにすると選択肢が減るので、鎖は短くなるはず。**
> **⚠ 見積もり: 30 段続く鎖が **20 〜 60%** 残る（完全には消えない）。**
> **⚠ 反例の形: 決め打ちの `(d,e)` でも `|V| >= |Q|` にできる `(n,j)` がある場合。**

**鎖の作り方（正しい形）:**

    段 0: `Q_0`, `(d_0, e_0)` は外から（全探索）
    各段: `(n, j)` だけ自由に選ぶ（`hstep` が `∀ n, ∀ j` を要求するので）
          `M = mTower Q d e n ++ Bn.take (j+1)`、`par` を悪根、`V = M[par:last]`
          **`d' = entry M 0 last − entry M 0 par`（`srow > 0` のとき）**
          **`e' = entry M 1 last − entry M 1 par`（`srow > 1` のとき、他は 0）**
          次段: `Q := V`, `d := d'`, `e := e'`

**箱と単位**: 鎖 1 本。`|Q0| = 3..4`、初期 `(d,e) ∈ 0..3`、`n ∈ 2..3`、`j ∈ 0..|Q|-1`。
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


def step_det(Q, d, e, n, j):
    """1 段。`V` と、`oper` が決める `(d', e')` を返す。"""
    L = len(Q)
    T = [tuple(x) for x in mTower(Q, d, e, n)]
    Bn = block(Q, d, e, n)
    S = T + Bn[:j + 1]
    last = len(S) - 1
    i1 = srow(S, last)
    par = trio.parent(S, i1, last)
    if par is None:
        return None
    d2 = (S[last][0] - S[par][0]) if i1 > 0 else 0
    e2 = (S[last][1] - S[par][1]) if i1 > 1 else 0
    return S[par:last], d2, e2


def run(L, cap, DE, NS, nmax):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in (0, 1)]
    c = Counter(); ex = []
    t0 = time.time(); done = 0
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q0 = [root] + list(t)
            for d0 in DE:
                for e0 in DE:
                    cur, d, e = list(Q0), d0, e0
                    seq = [len(cur)]; s = 0
                    while s < cap:
                        nxt = None
                        for n in NS:
                            for j in range(len(cur)):
                                r = step_det(cur, d, e, n, j)
                                if r and len(r[0]) >= len(cur):
                                    nxt = r; break
                            if nxt: break
                        if nxt is None:
                            break
                        cur, d, e = list(nxt[0]), nxt[1], nxt[2]
                        seq.append(len(cur)); s += 1
                    c['鎖の本数'] += 1
                    if s >= cap:
                        c['★ 最後まで続いた'] += 1
                        if len(ex) < 3:
                            ex.append((Q0, d0, e0, seq[:13]))
                    else:
                        c[('止まった段', min(s, 8))] += 1
                    done += 1
                    if done >= nmax:
                        break
                if done >= nmax: break
            if done >= nmax: break
        if done >= nmax: break
    tot = c['鎖の本数']
    print(f'### |Q0|={L}  `(d,e)` を `oper` が決める版  鎖 {tot} 本、{cap} 段まで  '
          f'[{time.time()-t0:.1f}s]')
    print(f'  **★ 最後まで（{cap} 段）続いた … {c["★ 最後まで続いた"]} / {tot} '
          f'({100*c["★ 最後まで続いた"]/max(tot,1):6.2f}%)**')
    print('  止まった段の分布: ', dict(sorted((k[1], c[k]) for k in c
                                      if isinstance(k, tuple) and k[0] == '止まった段')))
    for Q0, d0, e0, seq in ex:
        print(f'      続いた例 Q0={Q0} (d,e)=({d0},{e0}) ⟹ `|V|` の列 {seq}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--cap', type=int, default=30)
    ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for L in range(3, a.L + 1):
        run(L, a.cap, range(4), (2, 3), 400)
