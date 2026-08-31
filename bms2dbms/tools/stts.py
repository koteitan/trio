# -*- coding: utf-8 -*-
"""**`ST_TS` の正しい母集団**（課題 R26 / 2026-08-29）。

`bms2dbms/tools/r7.py` の `stts_pool(vmax, maxlen, ns=(1,2,3))` は
**既定引数が 2 つとも `ST_TS` の定義を狭めていた**。ここはその修正版である。

## Lean の定義（`lean/Trio.lean:121,127`）

    def diagSeqT (a b : ℕ) : TrioSeq :=
      (List.range' a (b + 1 - a)).map fun j => (j, j, min j 1)

    inductive ST_TS : TrioSeq → Prop where
      | diag (v : ℕ) : ST_TS (diagSeqT 0 v)
      | oper {M : TrioSeq} {n : ℕ} : ST_TS M → **1 ≤ n** → ST_TS (M⟦n⟧)

## 有限打ち切りが完全になる条件（証明つき）

* **`ns = 1 .. maxlen` で完全。**
  `|S⟦n⟧| = r + n*bp` で `bp >= 1` なので **`|S⟦n⟧| >= n`**。
  ⟹ `n > maxlen` の展開は必ず `maxlen` を超えて捨てられる。
* **`vmax = maxlen - 1` で完全。**
  `diagSeqT 0 v` は **`v+1` 列**なので、`len <= maxlen` に入る対角は `v <= maxlen - 1`。

⚠ **これだけでは完全ではない**（課題 R28 / R1 が発見。2026-08-29）。
`M⟦n⟧` は `M` より**短くなれる**（`M⟦1⟧ = M.dropLast`）ので、
**長さ `maxlen` 以下の `ST_TS` 行列が、長さ `maxlen` を超える中間状態を
経由してしか到達できない**ことがありうる。下の `len(T) <= maxlen` の枝刈りは
**その経路を切ってしまう**。

⟹ **`stts(maxlen)` は `ST_TS ∩ {len <= maxlen}` の部分集合にとどまる。**
上の 2 つ（`ns` / `vmax`）は必要条件であって十分条件ではない。
`stts(L)` を `L > maxlen` で作って長さで絞る（`stts_upto(maxlen, L)`）ほうが広い。

**`isstd(b, 'BMS')`（`core.py:172`）は「対角から展開で到達可能」そのもの**
（`reach(s, b)` が基本列を降りる）なので、**`gen3('BMS', L, zcap=1)` が
`ST_TS ∩ {len <= L}` と一致する可能性がある**。一致するなら `gen3` を使うのが正しい。
**未確認（課題 R28）。**

## 古い既定が何を落としていたか（実測、R1）

    v<=5 len<=8   ns=1..3 **19721** -> ns=1..6 **25211（+28%）**
    v<=5 len<=9   ns=1..3 **44064** -> ns=1..6 **61875（+40%）**

    落ちていた例（9 列、BMS 標準形、`ns=1..6` で入る）
      (0,0,0)(1,1,1)(2,2,1)(2,1,1)(3,2,1)(3,1,1)(4,2,1)(4,1,1)(5,2,1)

⚠ **「逆像が見つからない」系の測定は、母集団が狭いほど水増しされる。**
`ImgCofinalT` の破れの数は、古い母集団では**すべて上界**である。


## ★ 結論（課題 R28 / R1、2026-08-29）—— **この計器は使わなくてよい**

    **gen3('BMS', L, zcap=1)  =  ST_TS ∩ {len <= L}**

    標準形 ∧ z<2 ⟹ ST_TS   len<=5 1018 / len<=6 8387 / **len<=7 77282**  違反 **0**
    ST_TS ⟹ 標準形 ∧ z<2   stts(8) 25236                                違反 **0**

測り方は **BFS を使わない**: `core._isstd_raw` は `reach(s, b)`（基本列を降りて `b` に
届くか）で判定していて、`s` 自身も標準形なので**再帰すれば完全な対角から `b` までの
経路が構成できる**。その経路が z 頭打ち対角 `diagSeqT 0 v` を通れば `b ∈ ST_TS`
（`CLAUDE.md`: z 頭打ち対角は完全な対角の展開）。**枝刈りが要らないので 11-c を回避する。**
計器は `bms2dbms/tools/r46.py`（21 秒）。

⟹ **`ST_TS` の母集団が要るときは `rows3.gen3('BMS', L, zcap=1)` を使うこと。**
この `stts` は **枝刈りで大きく取りこぼす**（`stts(7)` は 3002 で、正しくは **77282**。
96% を落としていた）。**比較実験用にだけ残す。**

使い方: `from stts import stts`  /  `python3 bms2dbms/tools/stts.py 9`
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import trio


def stts(maxlen, vmax=None, ns=None):
    """`ST_TS ∩ {len <= maxlen}` を**完全に**返す（`seqlex` 昇順）。

    `vmax` / `ns` は既定で完全になる値が入る。狭めたいときだけ明示する
    （比較実験用。狭めると `ST_TS` の真部分集合になることに注意）。
    """
    if vmax is None:
        vmax = max(0, maxlen - 1)
    if ns is None:
        ns = range(1, maxlen + 1)
    seen, frontier = set(), []
    for v in range(vmax + 1):
        S = tuple(tuple(c) for c in trio.diag(3, v, zcap=1))
        if len(S) <= maxlen and S not in seen:
            seen.add(S); frontier.append(S)
    while frontier:
        S = frontier.pop()
        for n in ns:
            T = tuple(tuple(c) for c in trio.expand(list(S), n))
            if T and len(T) <= maxlen and T not in seen:
                seen.add(T); frontier.append(T)
    return sorted(seen)


if __name__ == '__main__':
    import time
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    for lab, kw in (('**正しい既定**', {}),
                    ('古い既定 (vmax=5, ns=1..3)', dict(vmax=5, ns=(1, 2, 3)))):
        t = time.time(); P = stts(L, **kw)
        print('len<=%-2d %-28s **%d 個**  (%.0fs)' % (L, lab, len(P), time.time() - t),
              flush=True)


def stts_upto(maxlen, depth):
    """`stts(depth)` を作ってから `len <= maxlen` で絞る。

    `stts(maxlen)` の枝刈りが切ってしまう経路（長い中間状態を経由するもの）を
    `depth > maxlen` にすることで拾う。`depth` を上げて数が飽和すれば、
    `ST_TS ∩ {len <= maxlen}` に達したと見てよい。
    """
    return [M for M in stts(depth) if len(M) <= maxlen]
