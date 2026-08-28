# -*- coding: utf-8 -*-
"""**`ST_TS` の正しい母集団**（課題 R26 / 2026-08-29）。

`tools/dbms/r7.py` の `stts_pool(vmax, maxlen, ns=(1,2,3))` は
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

⟹ **`stts(maxlen)` は `ST_TS ∩ {len <= maxlen}` にちょうど一致する。**

## 古い既定が何を落としていたか（実測、R1）

    v<=5 len<=8   ns=1..3 **19721** -> ns=1..6 **25211（+28%）**
    v<=5 len<=9   ns=1..3 **44064** -> ns=1..6 **61875（+40%）**

    落ちていた例（9 列、BMS 標準形、`ns=1..6` で入る）
      (0,0,0)(1,1,1)(2,2,1)(2,1,1)(3,2,1)(3,1,1)(4,2,1)(4,1,1)(5,2,1)

⚠ **「逆像が見つからない」系の測定は、母集団が狭いほど水増しされる。**
`ImgCofinalT` の破れの数は、古い母集団では**すべて上界**である。

使い方: `from stts import stts`  /  `python3 tools/dbms/stts.py 9`
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
