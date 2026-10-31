/-
**WfT2R6: `ExpT2V2` from `T2BelowXResV2X` (2026-11-01, t = 2 Bad2 route).**

`hExp_t2_inv3V2XR`: `hExp_t2_inv3V2` (V3ExpT2Inv2) on `T2BelowXResAtX`; the value drop of `M[n]` comes from
`WfT2X.t2_root_ofX` (WfT2R5) in place of `t2_drops_ge2` with `Res3T2` (whose field `absN` is the false `AbsWN`).
`expT2V2_ofXR`: `expT2V2_of` (V3ExpT2V2) on `T2BelowXResV2X`.
-/
import Ytosk.WfT2R5
import Ytosk.V3ExpT2Inv2
import Ytosk.V3ExpT2V2

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The `t = 2` expansion with `Inv3V2`**: from `Inv3V2` of `M` and of `M.take x`, the drop residual, and
the named residuals, every `M[n]` (`n ≥ 2`) has `Inv3V2`, a standard value, and a smaller value. -/
theorem hExp_t2_inv3V2XR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3V2 M ρ rk)
    (RW : Res3W M ρ rk)
    (I1 : Inv3V2 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hFO : T2SeedFrames QFO M) (hPR : G.T2SeedPRes M ρ)
    (hN : ∀ n, 2 ≤ n → ∀ σ rkN, Cons (expand M n) σ → Rk (expand M n) rkN → Good3 (expand M n) σ →
      PH3cG (expand M n) σ → T2NRes (expand M n) σ rkN) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (expand M n) ρN rkN ∧
      isOT (root (expand M n) ρN) = true ∧ root (expand M n) ρN < root M ρ := by
  intro n hn
  have S := sInv_std hM hS
  have IW : Inv3W M ρ rk := Inv3W.ofV2 S I
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨rkN, hRN⟩ := rk_expand_t2 hX hJ hz h2 I.rank n (by omega)
  have hCN := cons_of_rk hRN
  set σ := rhsIt (expand M n) (rkBound (expand M n) rkN) with hσ
  have hGN := good3_expand_t2 hM hS IW RW hz h2 (WfT2X.t2BelowXE_ofX hB hM hS IW RW hz h2)
    (t2CopyResAll_holds M ρ rk hM hS IW RW hz h2) n (by omega) σ hCN
  -- the prefix `M.take x`
  have hAg : ∀ τ', Cons (M.take (M.length - 1)) τ' →
      Agree (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) τ' :=
    fun τ' h => agree_of_cons I1.cons h I1.rank
  have hfo := frameOT_expand_t2XR hB hM hS IW RW hz h2
    (fun τ' h => clField_congr (Q := QFO) I1.fo (hAg τ' h)) hFO n (by omega) σ hCN
  have hbd := bumpFields_expand_t2XR hB hM hS IW RW hz h2
    (fun τ' h => ⟨bumpKidsDec_congr I1.kd (hAg τ' h), bumpTermDec_congr I1.td (hAg τ' h)⟩)
    (t2SeedBump_holds hM hS IW hz h2) n (by omega) σ hCN
  have hrp := rootP_expand_t2XR hB hM hS IW RW hz h2 n hn σ hCN
  have hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      FrameOT (M.take (M.length - 1)) τ ∧ PH3cG (M.take (M.length - 1)) τ ∧ FC3 (M.take (M.length - 1)) τ :=
    fun τ h => ⟨clField_congr (Q := QFO) I1.fo (hAg τ h), G.ph3c_congr I1.ph (hAg τ h),
      G.fc3_congr I1.fc3 (hAg τ h)⟩
  have hph := G.ph3c_expand_t2SXR hB hM hS IW RW I.ph I.fc3 hz h2 hT hFO hPR n (by omega) σ hCN
  have hfc3 := G.fc3_expand_t2SXR hB hM hS IW RW I.ph I.fc3 hz h2 hT hFO hPR n (by omega) σ hCN
  have NR := hN n hn σ rkN hCN hRN hGN hph
  refine ⟨σ, rkN, ⟨hCN, hGN, hRN, NR.vs, NR.fc, hfo, hbd.1, hbd.2, hph, hfc3, NR.vra,
    NR.frame.ads, NR.frame.aus, tp1C_of_ph3cG hCN hGN.toOT hph NR.tp1, NR.frame.tplos,
    tp1WC_of_ph3cG hCN hGN.toOT hph NR.tp1w, NR.frame.tplow, NR.frame.auwl, NR.frame.auw0,
    NR.frame.adw, NR.frame.trigs, NR.frame.tplon, NR.frame.adn, rootS_of_good hCN hGN, hrp⟩, ?_⟩
  -- the drop of the value
  have hGall := good3_expand_t2 hM hS IW RW hz h2 (WfT2X.t2BelowXE_ofX hB hM hS IW RW hz h2)
    (t2CopyResAll_holds M ρ rk hM hS IW RW hz h2)
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
  have key := WfT2X.t2_root_ofX hB hM hS IW RW hz h2 hlen hr n hn
    (fun m hm1 _ τ hτ => by rw [← hexp m] at hτ ⊢; exact hGall m hm1 τ hτ) σ
    (by rw [← hexp n]; exact hCN)
    (fun j _ hj => by rw [← hexp n] at hj; exact ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩)
    (by rw [← hexp n]; exact hGN)
  rw [hexp n]; exact key

end Ytosk

namespace Ytosk
open T
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **ExpT2V2 from the named residuals.** -/
theorem expT2V2_ofXR (hB : WfT2X.T2BelowXResV2X) (hFO : T2FOSeedV2) (hPR : T2SeedPResV2) (hVF : T2VSFCV2)
    (hVA : T2VRAV2) (hF : HFrameV2) (hL : HLeafV2) : ExpT2V2 := by
  intro M ρ rk C hz h2 n hn
  obtain ⟨hX, _⟩ := sInvXJ_std C.std C.ne
  have hl2 : 2 ≤ M.length := by
    obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
    rw [h2] at hr
    have := par_lt M 2 _ r hr; omega
  obtain ⟨I1, _⟩ := C.pre (M.length - 1) (by omega) (by omega)
  have hE := expand_ne_nil_t2 hX hz h2 (n := n) (by omega)
  have hStd : Std (expand M n) := Std.exp n C.std
  obtain ⟨ρN, rkN, IN, _⟩ := hExp_t2_inv3V2XR (hB M ρ rk C) C.std C.ne C.I C.toW I1 hz h2
    (hFO M ρ rk C hz h2) (hPR M ρ rk C hz h2)
    (fun m hm σ rkN hCN hRN hGN hPN => by
      have hEm := expand_ne_nil_t2 hX hz h2 (n := m) (by omega)
      have hSm : Std (expand M m) := Std.exp m C.std
      obtain ⟨hvs, hfc⟩ := hVF M ρ rk C hz h2 m hm σ rkN hCN hRN hGN hPN
      obtain ⟨hl1, hl2⟩ := hL _ σ rkN hSm (ne_SRO_of_rk hRN) hEm hCN hRN hGN
      exact ⟨hvs, hfc, hVA M ρ rk C hz h2 m hm σ rkN hCN hRN hGN hPN,
        hF _ σ rkN hSm (ne_SRO_of_rk hRN) hEm hCN hRN hGN, hl1, hl2⟩) n hn
  exact ⟨ρN, rkN, IN⟩

end Ytosk
