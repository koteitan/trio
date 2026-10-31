/-
**B2StepAb を値の B2UpgVG と Bad2 の B2NoInner に分ける（2026-10-31, WfB2L）。**

`WfB2S2` の分け方（構造の B2LevS と値の B2UpgV）は B2LevS が偽で使えない（`WfB2LFalse.not_B2LevS`、
40 列の標準形、b = e1 k = 4 で c の段が m の 2 段下）。b ≥ 4 の枠（tmp/wf/WfB2L/lift.py の lift1・lift2）で:
- c の段 a より上、m より下の鎖の列 y（e1 c < e1 y < e1 m）は Bad2 の枠では上げを持たない（Bad2 でない枠では持つ）。
- m が t へ上げるなら、段の差 i = e1 m − e1 c ≥ 1 のどれでも bumpW(k) ≤ last v(t)（B2UpgV の i = 1 を外した形）。
この 2 つで StepDom は空に成り立つ: y = m は吸収と矛盾（`WfB2S.summands_add_ge`）、y ≠ m は上げがない。
c の存在: bump 子の子の行 1 がすべて 0 なら段 0（`lev_bumpW_zero`）、そうでなければ子を持つ bump 子があり、
その最後のものを j にとる（`exists_last`）。

`b2StepAb_of_inner : B2UpgVG → B2NoInner → WfB2S.B2StepAb`。
-/
import Ytosk.WfB2S2

namespace Ytosk.WfB2L

open T Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **Value residual** (`WfB2S.B2UpgV` for every level gap): when `c` sits below `m` on the row-1 chain and `m`
upgrades to `t`, the bump term of `k` is at most `last v(t)`. Measured without `Bad2` at every position with a bump
parent (lift1, lift2, graft2..5, cbadext): 0 exceptions, level gaps 1 to 4. -/
def B2UpgVG : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ n, n + 2 = M.length → ∀ k m, upg M n = some k →
    k < n → par M 0 k = some m →
    ∀ L j R c C, children M k = L ++ j :: R → col M j = bump M k →
      (∀ d ∈ R, col M d = bump M k → children M d = []) → children M j = c :: C →
      entry M 1 c < entry M 1 m → ∀ t, upg M m = some t → bumpW M ρ k ≤ last (ρ.v t)

/-- **`Bad2` residual**: in the `B2StepAb` frame (with absorption), no column strictly between the level of `c` and
`m` on the row-1 chain of `m` upgrades. Measured at `x − 1` of every prefix of lift1 / lift2 (Bad2 frames: 0
exceptions, level gaps up to 4); false without `Bad2` (absorption and an inner upgrade, StepDom false: lift1). -/
def B2NoInner : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ n, n + 2 = M.length → ∀ k m, upg M n = some k →
    k < n → par M 0 k = some m → (∃ r ∈ summands (ρ.v m), r < bumpW M ρ k) →
    ∀ L j R c C, children M k = L ++ j :: R → col M j = bump M k →
      (∀ d ∈ R, col M d = bump M k → children M d = []) → children M j = c :: C →
      ∀ y, WfHUACDeep.Up1 M y m → y ≠ m → entry M 1 c < entry M 1 y → upg M y = none

/-- The last element of a list with a property. -/
theorem exists_last {α : Type} (P : α → Prop) :
    ∀ l : List α, (∃ x ∈ l, P x) → ∃ L x R, l = L ++ x :: R ∧ P x ∧ ∀ d ∈ R, ¬ P d
  | [], ⟨_, h, _⟩ => by simp at h
  | a :: l, h => by
    by_cases h' : ∃ x ∈ l, P x
    · obtain ⟨L, x, R, hl, hx, hR⟩ := exists_last P l h'
      exact ⟨a :: L, x, R, by rw [hl]; rfl, hx, hR⟩
    · obtain ⟨x, hx, hPx⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨[], x, l, rfl, hPx, fun d hd hPd => h' ⟨d, hd, hPd⟩⟩
      · exact absurd ⟨x, hx, hPx⟩ h'

/-- Either every child of a bump child of `k` has row 1 equal to `0`, or there is a last bump child with children. -/
theorem zero_or_lastK (M : Mat) (k : Nat) :
    (∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j, entry M 1 c = 0) ∨
    ∃ L j R c C, children M k = L ++ j :: R ∧ col M j = bump M k ∧
      (∀ d ∈ R, col M d = bump M k → children M d = []) ∧ children M j = c :: C := by
  by_cases h0 : ∀ j ∈ children M k, col M j = bump M k → ∀ c ∈ children M j, entry M 1 c = 0
  · exact Or.inl h0
  right
  push Not at h0
  obtain ⟨j0, hj0, hb0, c0, hc0, _⟩ := h0
  obtain ⟨L, j, R, hl, ⟨hjb, hjc⟩, hR⟩ := exists_last (fun d => col M d = bump M k ∧ children M d ≠ [])
    (children M k) ⟨j0, hj0, hb0, by intro h; rw [h] at hc0; simp at hc0⟩
  obtain ⟨c, C, hCc⟩ : ∃ c C, children M j = c :: C := by
    cases hch : children M j with
    | nil => exact absurd hch hjc
    | cons c C => exact ⟨c, C, rfl⟩
  refine ⟨L, j, R, c, C, hl, hjb, fun d hd hb => ?_, hCc⟩
  by_contra hne
  exact hR d hd ⟨hb, hne⟩

theorem b2StepAb_of_inner (hV : B2UpgVG) (hI : B2NoInner) : WfB2S.B2StepAb := by
  intro M ρ rk hM hS' hB I n hn k m hu hk hkm hab
  have S := sInv_std hM hS'
  have hnN : n < M.length := by omega
  rcases zero_or_lastK M k with h0 | ⟨L, j, R, c, C, hL, hjb, hR, hCc⟩
  · exact Or.inl (WfH7W2.lev_bumpW_zero I.cons I.good h0)
  refine Or.inr ⟨L, j, R, c, C, hL, hjb, hR, hCc, ?_⟩
  intro a ha hae y h1 h2 hne t ht
  exfalso
  have hya : entry M 1 a < entry M 1 y :=
    WfHUACDeep.up1_hi h1 y (WfHUACDeep.up1_anc0 h1) (Anc0.refl y) hne
  have hcy : entry M 1 c < entry M 1 y := by omega
  by_cases hym : y = m
  swap
  · have := hI M ρ rk hM hS' hB I n hn k m hu hk hkm hab L j R c C hL hjb hR hCc y h2 hym hcy
    rw [this] at ht; cases ht
  subst hym
  have hWL := hV M ρ rk hM hS' hB I n hn k y hu hk hkm L j R c C hL hjb hR hCc hcy t ht
  obtain ⟨r, hr, hrW⟩ := hab
  have hkN := upg_lt hnN hu
  have hyN : y < M.length := by have := par_lt M 0 k y hkm; omega
  obtain ⟨h1y, h2y'⟩ := upg_e12 ht
  have h2y : entry M 2 y = 0 := by have := S.z2 y; omega
  have htN := upg_lt hyN ht
  have hVot := vOpt_ot I.good hyN
  obtain ⟨s, b, hW⟩ := omega_psi_form (sumN (one :: (children M k).map (bumpTerm M ρ k)))
  have hbW : bumpW M ρ k = psi s b z := hW
  rw [hbW] at hWL hrW
  rcases WfB2S.last_form (ρ.v t) with hl | ⟨a', b', hl⟩
  · rw [hl] at hWL
    rcases hWL with h | h
    · exact not_lt_z _ h
    · cases h
  rw [hl] at hWL
  have hvy : ρ.v y = add (vOpt ρ (par M 1 y)) (psi a' b' z) := by
    rw [(I.cons y hyN).2]
    unfold vRhs
    rw [if_neg h1y, if_pos h2y, ht]
    simp only
    rw [hl]
    exact sf_ot (isOT_add hVot (by rw [← hl]; exact isOT_last (I.good.ot_v t htN)))
  rw [hvy] at hr
  have hge := WfB2S.summands_add_ge _ r hr
  rcases hWL with h | h
  · exact hge (lt_trans' hrW h)
  · rw [h] at hrW; exact hge hrW

/-- The old value residual is the level-gap-1 case of `B2UpgVG`. -/
theorem b2UpgV_of_G (h : B2UpgVG) : WfB2S.B2UpgV := by
  intro M ρ rk hM hS hB I n hn k m hu hk hkm L j R c C hL hjb hR hCc hcm t ht
  exact h M ρ rk hM hS hB I n hn k m hu hk hkm L j R c C hL hjb hR hCc (by omega) t ht

#print axioms b2StepAb_of_inner

end Ytosk.WfB2L
