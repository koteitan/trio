/-
Induction and descent on Inv3V3, with explicit unfinished engine outputs.
This is a conditional assembly theorem, not a proof of the engine residuals.
There is no conversion from Inv3V3 to Inv3V2 and no use of hInvV2_all.
The old unconditional hBaseR is used only for the direct expansions of SRO.
-/
import Ytosk.V3TakeV3
import Ytosk.WfCof

namespace Ytosk.V3Main
open T WfExQ1 WfExQ2

/-- Context supplied by the new induction, including Bad2 and T2CBad matrices.
The prefix valuations and rankings are the actual canonical drop valuations. -/
structure StepCtx3 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  std : Std M
  ne : M ≠ SRO
  nonempty : M ≠ []
  S : SInv M
  I : Inv3V3 M ρ rk
  drop : 2 ≤ M.length → DropV3 M ρ rk
  pre : ∀ j, 1 ≤ j → j < M.length → Inv3V3 (M.take j) (drop1 M j rk) rk

/-- Unfinished engine output for one srow. The input is Inv3V3, not StepCtxT2/V2.
Bad2 and C-bad cases are included; neither is assumed away. -/
def ExpOutV3 (t : Nat) : Prop :=
  ∀ M ρ rk, StepCtx3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = t → ∀ n, 2 ≤ n →
      ∃ σ rkN, Inv3V3 (expand M n) σ rkN ∧ root (expand M n) σ < root M ρ

/-- The context can be built without any old invariant existence assumption. -/
theorem ctx3 (hD : HDropV3) (hF : HFrameV3) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (hE : M ≠ [])
    (I : Inv3V3 M ρ rk) : StepCtx3 M ρ rk :=
  ⟨hM, hS, hE, sInv_std hM hS, I, fun hl => hD M ρ rk hM hS hl I,
    prefix_inv hD hF hM hS I⟩

theorem exp_out (h0 : ExpOutV3 0) (h1 : ExpOutV3 1) (h2 : ExpOutV3 2)
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) {n : Nat} (hn : 2 ≤ n) :
    ∃ σ rkN, Inv3V3 (expand M n) σ rkN ∧ root (expand M n) σ < root M ρ := by
  have hs : TRIO.srow M (M.length - 1) = 0 ∨ TRIO.srow M (M.length - 1) = 1 ∨
      TRIO.srow M (M.length - 1) = 2 := by
    unfold TRIO.srow; split_ifs <;> simp
  rcases hs with hs | hs | hs
  · exact h0 M ρ rk C hz hs n hn
  · exact h1 M ρ rk C hz hs n hn
  · exact h2 M ρ rk C hz hs n hn

/-- Actual induction on Std.exp, retaining only the repaired invariant.
The three ExpOutV3 assumptions remain separate obligations. -/
theorem inv3V3_all (hD : HDropV3) (hF : HFrameV3)
    (h0 : ExpOutV3 0) (h1 : ExpOutV3 1) (h2 : ExpOutV3 2) :
    ∀ M, Std M → M ≠ SRO → M ≠ [] → ∃ ρ rk, Inv3V3 M ρ rk := by
  intro M hM
  induction hM with
  | sro => intro h; exact absurd rfl h
  | @exp M n hM ih =>
    intro hNS hNE
    by_cases hMS : M = SRO
    · subst hMS
      obtain ⟨ρ, rk, I, _⟩ := hBaseR n
      exact ⟨ρ, rk, WfExQ1.Inv3V2.toV3 I⟩
    by_cases hME : M = []
    · subst hME; exact absurd rfl hNE
    obtain ⟨ρ, rk, I⟩ := ih hMS hME
    have hp := prefix_inv hD hF hM hMS I
    have hlen : 0 < M.length := List.length_pos_of_ne_nil hME
    have pref : ∀ j, j < M.length → M.take j ≠ [] → ∃ σ rkN, Inv3V3 (M.take j) σ rkN := by
      intro j hj he
      have hj1 : 1 ≤ j := by
        by_contra h
        have : j = 0 := by omega
        subst j; exact he List.take_zero
      exact ⟨_, rk, hp j hj1 hj⟩
    by_cases hz : col M (M.length - 1) = (0, 0, 0)
    · rw [expand_zero_last hME hz n] at hNE ⊢
      exact pref _ (by omega) hNE
    by_cases hn : 2 ≤ n
    · obtain ⟨σ, rkN, IN, _⟩ := exp_out h0 h1 h2 (ctx3 hD hF hM hMS hME I) hz hn
      exact ⟨σ, rkN, IN⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · obtain ⟨j, hj, he⟩ := expand_zero_take hME
      rw [he] at hNE ⊢
      exact pref j hj hNE
    · obtain rfl : n = 1 := by omega
      rw [expand_one] at hNE ⊢
      exact pref _ (by omega) hNE

/-- The root values of the proper prefixes are monotone. -/
theorem prefix_root_chain (hD : HDropV3) {M : Mat} {rk : Bool → Nat → Nat}
    (hM : Std M)
    (hp : ∀ j, 1 ≤ j → j < M.length → Inv3V3 (M.take j) (drop1 M j rk) rk) :
    ∀ j k, j ≤ k → k < M.length →
      root (M.take j) (drop1 M j rk) ≤ root (M.take k) (drop1 M k rk) := by
  have step : ∀ k, 1 ≤ k → k + 1 < M.length →
      root (M.take k) (drop1 M k rk) ≤ root (M.take (k + 1)) (drop1 M (k + 1) rk) := by
    intro k hk hkl
    have IP := hp (k + 1) (by omega) hkl
    have hSP := std_take hM (k + 1) (by omega)
    have hNP := ne_SRO_of_rk IP.rank
    have hlen : (M.take (k + 1)).length = k + 1 := by rw [List.length_take]; omega
    have h := take_root_lt (sInv_std hSP hNP) IP (by omega)
      (hD _ _ rk hSP hNP (by omega) IP)
    rw [hlen, show k + 1 - 1 = k from by omega, take_take_succ, drop1_take_succ] at h
    exact h.le
  have key : ∀ d j, j + d < M.length →
      root (M.take j) (drop1 M j rk) ≤ root (M.take (j + d)) (drop1 M (j + d) rk) := by
    intro d
    induction d with
    | zero => intro j _; exact le_refl _
    | succ d ih =>
      intro j hjd
      refine le_trans (ih j (by omega)) ?_
      rw [show j + (d + 1) = (j + d) + 1 from by omega]
      rcases Nat.eq_zero_or_pos (j + d) with h | h
      · rw [h, root_take_zero]; exact z_le _
      · exact step (j + d) h (by omega)
  intro j k hjk hk
  have h := key (k - j) j (by omega)
  simpa only [Nat.add_sub_of_le hjk] using h

/-- Desc3 for the translation, without the inconsistent V2 hypotheses.
This remains conditional on HDropV3, HFrameV3 and the three engine outputs. -/
theorem desc3_V3 (hD : HDropV3) (hF : HFrameV3)
    (h0 : ExpOutV3 0) (h1 : ExpOutV3 1) (h2 : ExpOutV3 2) : Desc3 := by
  intro M n hM hS hE
  obtain ⟨ρ, rk, I⟩ := inv3V3_all hD hF h0 h1 h2 M hM hS hE
  have hv : Val M (root M ρ) := ⟨ρ, rk, I.cons, I.rank, rfl⟩
  by_cases hz : col M (M.length - 1) = (0, 0, 0)
  · obtain ⟨t, ht, _, hlt⟩ := zero_last_desc hE I.cons I.good I.rank hz n
    exact ⟨_, t, hv, ht, root_ot I.good, hlt⟩
  have hl : 2 ≤ M.length := by
    have hpos := List.length_pos_of_ne_nil hE
    by_contra h
    have he : M.length - 1 = 0 := by omega
    have S := sInv_std hM hS
    apply hz
    exact (col_zero_iff M _).mpr ⟨by simpa only [he] using S.e00,
      S.r01 _ (by simpa only [he] using S.e00),
      S.r12 _ (S.r01 _ (by simpa only [he] using S.e00))⟩
  by_cases hn : 2 ≤ n
  · obtain ⟨σ, rkN, IN, hlt⟩ := exp_out h0 h1 h2 (ctx3 hD hF hM hS hE I) hz hn
    exact ⟨_, _, hv, ⟨σ, rkN, IN.cons, IN.rank, rfl⟩, root_ot I.good, hlt⟩
  have hp := prefix_inv hD hF hM hS I
  have hlast := take_root_lt (sInv_std hM hS) I hl (hD M ρ rk hM hS hl I)
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · obtain ⟨j, hj, he⟩ := expand_zero_take hE
    have ht : Val (M.take j) (root (M.take j) (drop1 M j rk)) := by
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · simpa only [List.take_zero, root_take_zero] using val_nil
      · have IP := hp j hj1 hj
        exact ⟨_, rk, IP.cons, IP.rank, rfl⟩
    refine ⟨_, _, hv, ?_, root_ot I.good, lt_of_le_of_lt
      (prefix_root_chain hD hM hp j (M.length - 1) (by omega) (by omega)) hlast⟩
    rw [he]; exact ht
  · obtain rfl : n = 1 := by omega
    have IP := hp (M.length - 1) (by omega) (by omega)
    refine ⟨_, _, hv, ?_, root_ot I.good, hlast⟩
    rw [expand_one]; exact ⟨_, rk, IP.cons, IP.rank, rfl⟩

/-- The actual target: order preservation, using the repaired conditional assembly. -/
theorem order_pres_V3 (hD : HDropV3) (hF : HFrameV3)
    (h0 : ExpOutV3 0) (h1 : ExpOutV3 1) (h2 : ExpOutV3 2)
    {A B : Mat} (hA : Std A) (hB : Std B) (hAS : A ≠ SRO)
    (hBE : B ≠ []) (hlt : TRIO.seqlex B A) :
    ∃ tA tB, Val A tA ∧ Val B tB ∧ isOT tA = true ∧ isOT tB = true ∧ tB < tA :=
  order_pres (desc3_V3 hD hF h0 h1 h2) hA hB hAS hBE hlt

/-- Surjectivity below each SRO expansion remains conditional on evaluation cofinality. -/
theorem surj_V3 (hD : HDropV3) (hF : HFrameV3)
    (h0 : ExpOutV3 0) (h1 : ExpOutV3 1) (h2 : ExpOutV3 2) (hC : EvalCof)
    {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj (desc3_V3 hD hF h0 h1 h2) hC hot hvN hlt

end Ytosk.V3Main
