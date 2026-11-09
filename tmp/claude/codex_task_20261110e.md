# codex 作業 5（2026-11-10、trio-claude から）

## 先に連絡
作業 4 の V3DecPTopWire.lean はまだコミットしません。そのまま置いておいてください。

測定で `DecPShape` に反例が 1 件見つかりました。r の子が [c0, u, q] で、u も「上げ先で topped」の場合です。このとき q − 1 は u の部分木にあり、c0 の部分木にはありません。

そこで、形を「c0 から q までの隣り合う兄弟 w < w' ごとに、w の bump の子 b の子が w' − 1」に直します（いま 86 集合で測り直しています）。値は右から左へ 1 段ずつ伝えます。その 1 段の補題が今回の作業です。

## ファイル
- 新規: /home/koteitan/proofs/trio/Ytosk/lean/Ytosk/V3DecPStep.lean
- import は `Ytosk.V3DecPTop` にしてください。namespace と open は V3DecPTop.lean と同じです。
- lakefile.toml の roots の最後に "Ytosk.V3DecPStep" を足してよいです。

## 証明してほしい文

```lean
/-- **One step of `decP`**: if a child `k` of the bump child `b` of `w` has `qnS ≤ v(k)`, then `qnS < v(w)`. -/
theorem decP_step {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {τ : Valn} (hτ : Cons (M.take (r + L)) τ)
    {w b k : Nat} (hwx : w < r + L) (hp1 : par M 1 w = some r) (he1 : entry M 1 w ≠ 0)
    (he2 : entry M 2 w ≠ 0) (hb : b ∈ children M w) (hbx : b < r + L) (hbb : col M b = bump M w)
    (hk : k ∈ children M b) (hkx : k < r + L) (hvk : qnS M ρ r L q ≤ τ.v k) :
    qnS M ρ r L q < τ.v w := by
  sorry
```

## ヒント
- 作業 3 の `decP_of_shape` の証明の写しです。違うのは次の 2 点だけです。
  - `q - 1` を `k` に替えます。
  - `τ.v (q-1) = qnS` を使っていた所は、仮定 `hvk : qnS ≤ τ.v k` を使います。
- `decp_term` には `y := z` を渡します。`psi qnS z z ≤ psi (τ.v k) y' z` は次のように出します。
  - `le_psi_sub hvk : psi qnS z z ≤ psi (τ.v k) z z`
  - `le_psi_arg : psi (τ.v k) z z ≤ psi (τ.v k) y' z`
  - この 2 つを le_trans でつなぎます。
- `hun`（upg(x−1) = none）と `hupq` は使わないので、仮定から外しました。
- `τ.v r = ρ.v r` は前と同じく `v_take_of_untopped I hlen (by omega) (topP_C hM hS I hlen hr hq hqr) hτ` で出ます。

## 確認
- 単体 check と全体ビルドを、どちらも exit 0 にしてください。sorry は残さないでください。
- 終わったら chm で次の 3 つを送ってください。
  - ファイル名
  - 2 つの exit
  - 公理
- git は使わないでください。
