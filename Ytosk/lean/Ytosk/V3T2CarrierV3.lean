/-
The t=2 engine assembled over Inv3V3 and the repaired PO/PV2 drop.
The remaining inputs are the actual below-boundary/seed-frame obligations and
VSmallF, FrameClosed, VSmallRAll at expansions. Rank, Good3, all other carried
fields, root order, and root descent are proved, not assumed as ExpCoreV3.
-/
import Ytosk.V3T2FieldsV3

namespace Ytosk.V3Main
open T Classical WfExQ1 WfExQ2
set_option linter.unusedVariables false

theorem t2_carrierV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hF : WfExQ2.HFrameV3) (hB : T2BelowAtV3 M ρ)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3V3 M ρ rk)
    (D : DropV3 M ρ rk)
    (I1 : Inv3V3 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hFO : T2SeedFrames QFO M)
    (hSF : T2SeedFrames G.QT2F M) (hSP : T2SeedFrames G.QT2P M)
    (hN : ∀ n, 2 ≤ n → ∀ σ rkN, Cons (expand M n) σ → Rk (expand M n) rkN → Good3 (expand M n) σ →
      PH3cG (expand M n) σ → VSmallF (expand M n) σ ∧
      FrameClosed (expand M n) σ ∧ VSmallRAll (expand M n) σ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V3 (expand M n) ρN rkN ∧
      isOT (root (expand M n) ρN) = true ∧ root (expand M n) ρN < root M ρ := by
  intro n hn
  have S := sInv_std hM hS
  have IW : Inv3W M ρ rk := coreW S I
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨rkN, hRN⟩ := rk_expand_t2 hX hJ hz h2 I.rank n (by omega)
  have hCN := cons_of_rk hRN
  set σ := rhsIt (expand M n) (rkBound (expand M n) rkN) with hσ
  have hGN := good3_expand_t2V3 hM hS IW D hz h2 (t2BelowXE_V3 hB hM hS IW D hz h2)
    (t2CopyResV3 hM hS IW hz h2) n (by omega) σ hCN
  -- the prefix `M.take x`
  have hAg : ∀ τ', Cons (M.take (M.length - 1)) τ' →
      Agree (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) τ' :=
    fun τ' h => agree_of_cons I1.cons h I1.rank
  have hfo := frameOT_expand_t2V3 hB hM hS IW D hz h2
    (fun τ' h => clField_congr (Q := QFO) I1.fo (hAg τ' h)) hFO n (by omega) σ hCN
  have hbd := bumpFields_expand_t2V3 hB hM hS IW D hz h2
    (fun τ' h => ⟨bumpKidsDec_congr I1.kd (hAg τ' h), bumpTermDec_congr I1.td (hAg τ' h)⟩)
    (t2SeedBump_holds hM hS IW hz h2) n (by omega) σ hCN
  have hrp := rootP_expand_t2V3 hB hM hS IW D hz h2 n hn σ hCN
  have hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      FrameOT (M.take (M.length - 1)) τ ∧ PH3cG (M.take (M.length - 1)) τ ∧ FC3 (M.take (M.length - 1)) τ :=
    fun τ h => ⟨clField_congr (Q := QFO) I1.fo (hAg τ h), G.ph3c_congr I1.ph (hAg τ h),
      G.fc3_congr I1.fc3 (hAg τ h)⟩
  have hph := ph3c_expand_t2V3 hB hM hS IW D I.ph hz h2
    (fun τ hτ => ⟨(hT τ hτ).1, (hT τ hτ).2.1⟩) hSP n (by omega) σ hCN
  have hfc3 := fc3_expand_t2V3 hB hM hS IW D I.fc3 hz h2
    (fun τ hτ => ⟨(hT τ hτ).1, (hT τ hτ).2.2⟩) hSF n (by omega) σ hCN
  have NR := hN n hn σ rkN hCN hRN hGN hph
  have hl : 2 ≤ M.length := by
    obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
    rw [h2] at hr
    have := par_lt M 2 _ r hr
    omega
  obtain ⟨F, hTP, hTPW⟩ := hF _ σ rkN (Std.exp n hM) (ne_SRO_of_rk hRN)
    (expand_nonempty hl (by omega)) hCN hRN hGN
  have K : CarryV3 (expand M n) σ :=
    ⟨NR.1, NR.2.1, hfo, hbd.1, hbd.2, hph, hfc3, NR.2.2⟩
  refine ⟨σ, rkN, inv3V3_of_parts hCN hGN hRN (rootS_of_good hCN hGN) hrp K F hTP hTPW, ?_⟩
  -- the drop of the value
  have hGall := good3_expand_t2V3 hM hS IW D hz h2 (t2BelowXE_V3 hB hM hS IW D hz h2)
    (t2CopyResV3 hM hS IW hz h2)
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  rw [hL] at hr
  have hexp : ∀ m, expand M m = TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have key := t2_rootV3 hB hM hS IW D hz h2 hlen hr n hn
    (fun m hm1 _ τ hτ => by rw [← hexp m] at hτ ⊢; exact hGall m hm1 τ hτ) σ
    (by rw [← hexp n]; exact hCN)
    (fun j _ hj => by rw [← hexp n] at hj; exact ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩)
    (by rw [← hexp n]; exact hGN)
  rw [hexp n]; exact key


end Ytosk.V3Main
