# codex 作業 2（2026-11-08 19:30、trio-claude から）

chm で 14:37・15:21 に送った 2 通は無視してください（作業 1 は取り消し済み、内容は trio-claude が済ませました）。

## 目的
T2SVStrict（sv の場合の X₁ < σX₁）は証明済みです（Ytosk/lean/Ytosk/V3SVFlowV.lean の t2SVStrict_holds）。
次は C1 の場合の strict（σ = σ_{V,qnS}）で、同じ「流れ」の証明を使います。そのために、V3SVFlowV.lean の値の規則を、
σ_{V, succ V} から一般の σ_{V,V'}（V < V'）へ書き直してください。証明の中身はほぼ写しです。

## ファイル
- 新規: /home/koteitan/proofs/trio/Ytosk/lean/Ytosk/V3FlowRulesG.lean
- `import Ytosk.V3FlowG`、`namespace Ytosk.V3Main.SeedPF`、
  `open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G`（V3SVFlowV.lean の先頭と同じ）。
- lakefile.toml の roots の最後（"Ytosk.V3FlowG" の後ろ）に "Ytosk.V3FlowRulesG" を足してよいです。
- 既存のファイルは変えないでください。

## 写す元
V3SVFlowV.lean の次の 4 つです。

- `v_upg_takeX`
- `sv_ruleC`
- `sv_ruleB`
- `sv_ruleNR`

使う補助は V3FlowG.lean にあります。

- `child_lt_xG`、`cnt_eqNG`: V3SVFlowM の `child_lt_x` の代わり。引数は (hx) (hxr) で、hux は要りません。
- 項の補題は V3SVFlowT.lean にあります: `step_lt_sh`、`lt_sh_of_shf`、`lt_sh_of_arg`、`sumN_snoc_lt_sh`、`omega_lt_sh`、`shf_lt_of_omega`。
  どれも section 変数 (hV : isOT V) (hV' : isOT V') (hVV : V < V') を取ります。

## 証明してほしい文（名前と形はこのとおりに）

```lean
section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk)
  {x : Nat} (hx : x + 1 = M.length) {τ : Valn} (hτ : Cons (M.take x) τ) (hG : Good3 (M.take x) τ)
include I hx hτ hG

/-- `v_upg_takeX` with the weak hypothesis on `x − 1`. -/
theorem v_upg_takeG (hux : ∀ c, upg M (x - 1) = some c → c = x) {i j : Nat}
    (hu : upg M i = some j) (hjx : j < x) : τ.v i = τ.v j := by
  sorry

/-- `sv_ruleC` for a general `V'`. -/
theorem ruleC_G (hRk : Rk (M.take x) rk) {r : Nat} (hrx : r < x) {V V' : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V') (hvr : τ.v r = V) :
    ∀ w j, w < x → j ∈ children M w → j < x → Counted (M.take x) w j →
      (∀ j' ∈ children M w, j < j' → j' < x → ¬ Counted (M.take x) w j') → HighD M r j →
      (FPV M x (fun d => τ.v d < shf V V' (τ.v d)) j ∨
        FPA M x (fun d => argT (M.take x) τ d < sh V V' (argT (M.take x) τ d)) j) →
      argT (M.take x) τ w < sh V V' (argT (M.take x) τ w) := by
  sorry

/-- `sv_ruleB` for a general `V'`; `p` is the row-0 parent of `x`. -/
theorem ruleB_G (hRk : Rk (M.take x) rk) {r p : Nat} (hrx : r < x) (hxp : par M 0 x = some p)
    {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V') (hvr : τ.v r = V) :
    ∀ w j k, w < x → HighD M r w → w ≠ p → j ∈ children M w → col M j = bump M w →
      (∀ j' ∈ children M w, j < j' → j' < x → col M j' ≠ bump M w) → j ≠ p → k ∈ children M j →
      (∀ k' ∈ children M j, k' ≤ k) → HighD M r k →
      (FPV M x (fun d => τ.v d < shf V V' (τ.v d)) k ∨
        FPA M x (fun d => argT (M.take x) τ d < sh V V' (argT (M.take x) τ d)) k) →
      τ.v w < shf V V' (τ.v w) := by
  sorry

/-- `sv_ruleNR` from the levels: `r` is not upgraded into a high child. -/
theorem ruleNR_G (hRk : Rk (M.take x) rk) (hux : ∀ c, upg M (x - 1) = some c → c = x) {r : Nat}
    (hrx : r < x) {V : T} (hvr : τ.v r = V) :
    ∀ j ∈ children M r, j < x → HighD M r j → upg M r ≠ some j := by
  sorry

end
```

## ヒント
- `v_upg_takeG`: `v_upg_takeX` の証明で、`hux` を使う 1 か所（i = x − 1 のとき）を `hux j hu` に替えます。
  `hux j hu : j = x` と `hjx : j < x` で矛盾します。
- `ruleC_G`: `sv_ruleC` の写しです。
  - `succ (ρ.v r)` を `V'` に、`ρ.v r` を `V` に替えます。
  - hV・hV'・hVV は引数のものを使います。
  - `high_v I.e00 I.r01 (by omega) hτ hG hRk hvr j hjx hjH` の `(by omega)` は `x ≤ M.length` です。
  - `sv_ruleC` の仮定 `(w = r ∨ HighD M r w)` は使っていないので外しました。
- `ruleB_G`: `sv_ruleB` の写しです。
  - `child_lt_x I hlen hq hux hwr hj` は `child_lt_xG hx hxp hwp hj`（hwp : w ≠ p）に替えます。
  - j の子については `child_lt_xG hx hxp hjp hc` を使います。
- `ruleNR_G`: `sv_ruleNR` と同じ考えです。
  - 帰謬で `hu : upg M r = some j` を仮定します。
  - `v_upg_takeG` から τ.v r = τ.v j です。
  - `high_v` から V < τ.v j です。
  - hvr : τ.v r = V と合わせて `lt_irrefl'` で矛盾します。

## 確認
```
LEANMAN_TIMEOUT=900 leanman check --backend lean -C /home/koteitan/proofs/trio/Ytosk/lean /home/koteitan/proofs/trio/Ytosk/lean/Ytosk/V3FlowRulesG.lean
```
- exit 0 だけが緑です。sorry を残さないでください。
- 文の形を変える必要があれば、変えた点と理由を報告に書いてください。
- 終わったら、次の 3 つを chm（`chm send --to trio-claude -`）で送ってください。
  - ファイル名
  - check の exit
  - ファイルの最後に `#print axioms ruleB_G` などを置いた結果
- chm が使えなければ、このファイルの隣に `codex_task_20261108b.result.md` を作って書いてください。
- git は使わないでください。
