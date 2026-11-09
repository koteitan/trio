# codex 作業 3（2026-11-10、trio-claude から）

## 目的
残りの欄 decP（C1 の場合: r の最後の数える子 c0 で qnS < v_T(c0)）のうち、c0 が topped の場合（全体の 97%）の値の部分を示します。
形はこうです: c0 の最後の子 b は c0 の bump の子で、q − 1 は b の子です。
- q − 1 は q を上げる列なので、v(q − 1) = v(q) = qnS です。
- v(c0) = V + ω^Y で、Y の中に ω^{(… + o(q − 1))} があります。
- o(q − 1) = ψ_{qnS}(…) ≥ Ω_{qnS} > qnS ≥ ω^{X₀} ≥ X₀ です（qnS = V + ω^{X₀}、X₀ = 1 + Σ_q）。
- よって X₀ < Y となり、qnS < v(c0) です。

構造の部分（c0 が topped なら b と q − 1 がこの形になること）は trio-claude が別に示します。ここでは形を仮定に取ってください。

## ファイル
- 新規: /home/koteitan/proofs/trio/Ytosk/lean/Ytosk/V3DecPTop.lean
- 書き出しは次のとおりです。
  ```lean
  import Ytosk.V3C1Strict
  namespace Ytosk.V3Main.SeedPF
  open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
  ```
- V3ShStrict は import しないでください（名前がぶつかります）。
- lakefile.toml の roots の最後に "Ytosk.V3DecPTop" を足してよいです。既存のファイルは変えないでください。

## 証明してほしい文（名前と形はこのとおりに）

```lean
/-- The term part: `V + ω^{X₀} < V + ω^Y` when `Y` contains `ω^G` and `G` contains `ψ_{V+ω^{X₀}}(y)`. -/
theorem decp_term {V X0 Y G y : T} (hV : isOT V = true) (hX0 : isOT X0 = true) (hY : isOT Y = true)
    (hG : isOT G = true)
    (hGY : omega G ≤ Y) (hpG : psi (add V (omega X0)) y z ≤ G) :
    add V (omega X0) < add V (omega Y) := by
  sorry

/-- **decP when `c₀` ends with its bump child `b` and `q − 1` is a child of `b`** (C1). -/
theorem decP_of_shape {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hun : upg M (r + L - 1) = none)
    {τ : Valn} (hτ : Cons (M.take (r + L)) τ)
    {c0 b : Nat} (hc0x : c0 < r + L) (hp1 : par M 1 c0 = some r) (he1 : entry M 1 c0 ≠ 0)
    (he2 : entry M 2 c0 ≠ 0) (hb : b ∈ children M c0) (hbx : b < r + L) (hbb : col M b = bump M c0)
    (hqb : q - 1 ∈ children M b) (hupq : upg M (q - 1) = some q) :
    qnS M ρ r L q < τ.v c0 := by
  sorry
```

## ヒント
- `decp_term` の鎖は次のとおりです。
  - `X0 ≤ omega X0`（`self_le_omega`）
  - `omega X0 ≤ add V (omega X0)`（`le_add_left_self`）
  - `add V (omega X0) < psi (add V (omega X0)) z z`（`lt_Om_self`）
  - `psi _ z z ≤ psi _ y z`（`le_psi_arg`、`z ≤ y` は `T.z_le` 系）
  - `≤ G ≤ omega G ≤ Y`（`self_le_omega`）
  - これで X0 < Y です。そのあと `omega_lt_omega`（Omega.lean:402）と `add_lt_add_left`（Arith:89）を使います。
  - isOT の側条件は `isOT_omega`・`isOT_add` です。
- `decP_of_shape` の材料は次のとおりです。
  - 準備（c1_strict_holds（V3C1Strict.lean）の冒頭と同じ）:
    - `hG : Good3 (M.take (r+L)) τ` は `good3_take_anyV3U I (Ctx.drop (by omega)) (by omega) hτ'` で作り、`M.length - 1 = r + L` で書き換えます。
    - `hRk` は `rk_take_all` で作ります。
    - `hvr : τ.v r = ρ.v r` は `v_take_of_untopped I hlen (by omega) (topP_C hM hS I hlen hr hq hqr) hτ` で出ます。
  - v(c0) の式: `(hτ c0 _).2` で `τ.v c0 = vRhs …` が出ます。`unfold vRhs` して、`entry_take`・`par_take` で M に戻します（e1 ≠ 0、e2 ≠ 0 の枝）。結果は `sf (add (τ.v r) (omega (sumN (one :: (children (M.take (r+L)) c0).map (bumpTerm (M.take (r+L)) τ c0)))))` です。sf は `sf_ot` で外します。
  - qnS の定義は `qnS M ρ r L q = add (ρ.v r) (omega (sumN (one :: …)))`（V3T2SeedQNL.lean:23）です。`decp_term` の X0 にそのまま合わせてください。
  - Y ≥ ω^G: `bumpTerm (M.take x) τ c0 b = omega (sumN ((children (M.take x) b).map τ.o))` です（`unfold bumpTerm`、`col_take`・`bump_take`）。b は `children (M.take x) c0` に入るので、`mem_le_sumN` で ≤ Y が出ます。
  - G ≥ ψ_{qnS}(y):
    - q − 1 は `children (M.take x) b` に入ります。
    - `o_cl_eq hτ hG _` で `τ.o (q-1) = psi (τ.v (q-1)) _ z` です。
    - `τ.v (q-1) = τ.v q` は `v_upg_takeG I hx hτ hG hux hupq (q < r+L)` で出ます（hux は hun から）。
    - `τ.v q = qnS` は `c_vqP_of_un hM hS I hlen hr hq hqr hun τ hτ` で出ます。
    - 最後に `mem_le_sumN` を使います。
  - children (M.take x) の要素の判定は `children_take` と `List.mem_filter` でします（V3SVFlowV.lean の `sv_ruleB` に同じ書き方があります）。

## 確認
```
LEANMAN_TIMEOUT=900 leanman check --backend lean -C /home/koteitan/proofs/trio/Ytosk/lean /home/koteitan/proofs/trio/Ytosk/lean/Ytosk/V3DecPTop.lean
```
- exit 0 だけが緑です。sorry を残さないでください。
- 文の形を変える必要があれば、変えた点と理由を報告に書いてください。
- 終わったら chm（`chm send --to trio-claude -`）で次の 4 つを送ってください。
  - ファイル名
  - check の exit
  - 全体ビルドの exit
  - `#print axioms` の結果
- git は使わないでください。
