/-
**HUACB2 の値の部分を外す（2026-10-31, WfH7W2）。**

HUACB2（Bad2 の x − 1 = n が祖先 k < n へ上げるとき、v(P₁ n) の成分は v(n) の成分か 0 以下）の値の部分は
証明済みの補題で済む。m = P₀ k、j = k の最後の bump 子、c = j の最初の子、a = m の行 1 の鎖で行 1 が c と同じ列。
- k の bump 子の子がすべて行 1 = 0 なら bumpW(k) の段は 0（`lev_bumpW_zero`）で `HUACZero.dom_of_zero`。
- そうでなければ v(c) = v(a)（`WfHUACDeep.deep_return`）で、鎖の a より上の段の増分が `StepDom` なら
  `WfHUACDeep.dom_of_deep`（構造は `WfHUAC2Canon.canon_struct`、生き残りは `first_kid_survives`）。
- 鎖の a より上に上げる列がなければ `StepDom` は空（`b2Step_of_noU`）。

残り（どちらか一方で HUACB2 が出る）:
- `B2Step`（Bad2 の下の StepDom、値）: `huacB2_of_step : B2Step → HUACB2`
- `B2NoUB`（Bad2 の下の構造の結論: 鎖の a より上に上げる列がない）: `huacB2_of_noU : B2NoUB → HUACB2`。
  Bad2 を外すと偽（P₀ n が bump 子でも、cbadext の 27 列の標準形で m が上げる）。

偽だった案: 「行 1 = 0 か、最後の bump 子の最後の子が m の行に戻る（i = 0 の ReturnWitness）」は Bad2 の枠でも偽
（接ぎ木の標準形 28 列 …(8,3,0)(8,3,0)(8,0,0)、n = 26・k = 19・m = 15、c = 21 = (6,1,0) は m の 1 段上 8 に戻る）。
-/
import Ytosk.WfH7WB2
import Ytosk.V3HUACZero
import Ytosk.WfHUAC2Canon

namespace Ytosk.WfH7W2

open T

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- A left fold of standard sums of level-`0` standard terms has level `0`. -/
theorem lev_foldl_z : ∀ (l : List T) (a : T), isOT a = true → lev a = z →
    (∀ t ∈ l, isOT t = true ∧ lev t = z) →
    isOT (l.foldl (fun a b => sf (add a b)) a) = true ∧ lev (l.foldl (fun a b => sf (add a b)) a) = z
  | [], a, ha, hl, _ => ⟨ha, hl⟩
  | t :: l, a, ha, hl, h => by
    simp only [List.foldl_cons]
    obtain ⟨ht, htl⟩ := h t (by simp)
    have hot := isOT_add ha ht
    apply lev_foldl_z l _ (by rw [sf_ot hot]; exact hot)
    · rw [sf_ot hot]
      rcases lev_add_cases a t with e | e <;> rw [e] <;> assumption
    · intro s hs; exact h s (by simp [hs])

theorem lev_sumN_z {l : List T} (h : ∀ t ∈ l, isOT t = true ∧ lev t = z) : lev (sumN l) = z :=
  (lev_foldl_z l z rfl rfl h).2

/-- **`bumpW` has level `0` when every grandchild through a bump child has row 1 equal to `0`.** -/
theorem lev_bumpW_zero {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {k : Nat}
    (h0 : ∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j, entry M 1 c = 0) :
    lev (bumpW M ρ k) = z := by
  unfold bumpW
  rw [OmegaComps.lev_omega_eq]
  apply lev_sumN_z
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact ⟨isOT_one, rfl⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  refine ⟨isOT_bumpTerm hG k j, ?_⟩
  unfold bumpTerm
  split
  · rename_i hjb
    rw [OmegaComps.lev_omega_eq]
    apply lev_sumN_z
    intro s hs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    have hcN := (mem_children hc).2
    refine ⟨hG.ot_o c hcN, ?_⟩
    obtain ⟨y, hy⟩ := o_psi_sub hC hcN
    rw [hy, v_z_of_e1 hC hcN (h0 j hj hjb c hc)]
    rfl
  · rfl

/-- **Residual (`StepDom` under `Bad2`)**: at the second-to-last column `n` of a `Bad2` matrix, upgrading to an
ancestor `k` (`m = P₀ k`), either `bumpW(k)` has level `0`, or the last bump child `j` of `k` has a first child `c`
and the `U`-increments of the row-1 chain of `m` above the level of `c` are dominated by `v` at that level
(`StepDom`). The same statement for every upgrade (`WfHUAC2Canon.HUACStep`) is false (`WfStepHUACStepFalse`,
where `k = P₀ n`, so that matrix is not `Bad2`). -/
def B2Step : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ n, n + 2 = M.length → ∀ k m, upg M n = some k →
    k < n → par M 0 k = some m →
    lev (bumpW M ρ k) = z ∨
    ∃ L j R c C, children M k = L ++ j :: R ∧ col M j = bump M k ∧ (∀ d ∈ R, col M d ≠ bump M k) ∧
      children M j = c :: C ∧
      ∀ a, WfHUACDeep.Up1 M a m → entry M 1 a = entry M 1 c → WfHUACDeep.StepDom M ρ a m

/-- **`HUACB2` from `B2Step`** (the structure of the deep witness is `WfHUAC2Canon.canon_struct`, survival is
`first_kid_survives`, the components are carried by `WfHUACDeep.dom_of_deep`). -/
theorem huacB2_of_step (h : B2Step) : WfH7W.HUACB2 := by
  intro M ρ rk hM hS hB I n hn k hu hk u
  have S := sInv_std hM hS
  obtain ⟨m, _, hkm⟩ := upg_target_par0 S.r0p hu
  have hnN : n < M.length := by omega
  rcases h M ρ rk hM hS hB I n hn k m hu hk hkm with h0 | ⟨L, j, R, c, C, hL, hjb, hR, hCc, hst⟩
  · exact HUACZero.dom_of_zero S I.cons I.good hnN hu h0 u
  · have hj : j ∈ children M k := by rw [hL]; simp
    obtain ⟨hcn, hc2, a, ha, hae⟩ := WfHUAC2Canon.canon_struct hM hS hu hk hkm hL hjb hCc
    exact WfHUACDeep.dom_of_deep S I.cons I.good hnN hu hk hkm
      ⟨L, j, R, c, a, hL, hjb, hR, by rw [hCc]; simp,
        WfHUAC2Canon.first_kid_survives hM hS I.cons I.good hj hjb hCc, hcn, ha, hae.symm, hc2,
        hst a ha hae⟩ u

/-- **Alternative residual (structural conclusion under `Bad2`)**: in the `B2Step` frame, either every child of a
bump child of `k` has row 1 equal to `0`, or the last bump child `j` of `k` has a first child `c` and no column of
the row-1 chain of `m` strictly above the level of `c` has an upgrade. Measured: in every `Bad2` frame the level
of `c` is `m` or `P₁ m` and there is no such upgrade. Without `Bad2` it is false, also with the bump parent
`P₀ n = bump(P₀ P₀ n)` (cbadext, 27 columns, `n = 25`, `k = 19`, `m = 15`, `c = 21`: `15` upgrades to `12`;
`StepDom` holds there). -/
def B2NoUB : Prop :=
  ∀ M, Std M → M ≠ SRO → Bad2 M → ∀ n, n + 2 = M.length → ∀ k m, upg M n = some k → k < n →
    par M 0 k = some m →
    (∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j, entry M 1 c = 0) ∨
    ∃ L j R c C, children M k = L ++ j :: R ∧ col M j = bump M k ∧ (∀ d ∈ R, col M d ≠ bump M k) ∧
      children M j = c :: C ∧
      ∀ a, WfHUACDeep.Up1 M a m → entry M 1 a = entry M 1 c →
        ∀ y, WfHUACDeep.Up1 M a y → WfHUACDeep.Up1 M y m → y ≠ a → upg M y = none

theorem b2Step_of_noU (h : B2NoUB) : B2Step := by
  intro M ρ rk hM hS hB I n hn k m hu hk hkm
  rcases h M hM hS hB n hn k m hu hk hkm with h0 | ⟨L, j, R, c, C, hL, hjb, hR, hCc, hno⟩
  · exact Or.inl (lev_bumpW_zero I.cons I.good h0)
  · refine Or.inr ⟨L, j, R, c, C, hL, hjb, hR, hCc, fun a ha hae y h1 h2 hne t ht => ?_⟩
    rw [hno a ha hae y h1 h2 hne] at ht
    cases ht

/-- **`HUACB2` from the structural-conclusion `B2NoUB`.** -/
theorem huacB2_of_noU (h : B2NoUB) : WfH7W.HUACB2 := huacB2_of_step (b2Step_of_noU h)

end Ytosk.WfH7W2
