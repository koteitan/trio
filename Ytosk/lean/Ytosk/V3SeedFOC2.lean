/- C2 QFO from source-state equality or Lhd. No prefix valuation is used. -/
import Ytosk.V3SeedFO2

namespace Ytosk.V3Main.SeedFO
open T Classical WfExQ1 WfExQ2 G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- OT transfers to a standard argument which is equal or Lhd below the old one. -/
theorem qFO_of_state_lhd {a AN AM : T} (ha : isOT a = true) (hAN : isOT AN = true)
    (hrel : AN = AM ∨ Lhd z AN AM) (hAM : isOT (psi a AM z) = true) :
    isOT (psi a AN z) = true := by
  rcases hrel with rfl | hrel
  · exact hAM
  · apply psi_ot_of_lhd ha hAN hrel (isOT_psi_iff.mp hAM).2.2.2.2
    intro _ g hg
    simp [comps] at hg

/-- Finite-state relation at a C2 root. All n >= 2 and Cons/Good3 targets are
quantified. The residual concerns arguments, not QFO itself. The childwise
Lhd-to-spArg transport is not assumed implicitly. -/
structure T2C2RootRel (M : Mat) (ρ : Valn) (r L q : Nat) : Prop where
  source_children : CL M r = CL (M.take (r + L)) r
  target : ∀ n, 2 ≤ n → ∀ σ,
    Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n) σ →
    Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n) σ →
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) n) r = CL M r ++ [q] ∧
    σ.v r = ρ.v r ∧
    ∀ j, j ≤ (CL M r).length →
      spArg (ρ.v r) z (sumN (((CL M r).take j).map σ.o)) =
        spArg (ρ.v r) z (sumN (((CL M r).take j).map ρ.o)) ∨
      Lhd z (spArg (ρ.v r) z (sumN (((CL M r).take j).map σ.o)))
        (spArg (ρ.v r) z (sumN (((CL M r).take j).map ρ.o)))

/-- QFO at the C2 root follows from source FrameOT and the state relation. -/
theorem seedFO_C2_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtx3 M ρ rk) {r L q : Nat} (hlen : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hrel : T2C2RootRel M ρ r L q) :
    SeedFr QFO M r L r := by
  have I := coreW C.S C.I
  have hrx := par_lt M 2 _ r hr
  have hrM : r < M.length := by omega
  intro n hn hGlow σ hCN hGN Lc c R hsplit
  obtain ⟨hCLN, hvr, hstate⟩ := hrel.target n hn σ hCN hGN
  have hj : Lc.length ≤ (CL M r).length := by
    have hlength := congrArg List.length (hsplit.symm.trans hCLN)
    simp only [List.length_append, List.length_cons, List.length_nil] at hlength
    omega
  have htake : Lc = (CL M r).take Lc.length := by
    have heq := congrArg (List.take Lc.length) (hsplit.symm.trans hCLN)
    simpa only [List.take_append_of_le_length (by omega : Lc.length ≤ Lc.length),
      List.take_length, List.take_append_of_le_length hj] using heq
  have hAM : isOT (psi (ρ.v r)
      (spArg (ρ.v r) z (sumN (((CL M r).take Lc.length).map ρ.o))) z) = true := by
    by_cases he : Lc.length = (CL M r).length
    · rw [he, List.take_length, ← o_cl_eq I.cons I.good hrM]
      exact I.good.ot_o r hrM
    · have hjlt : Lc.length < (CL M r).length := by omega
      cases hd : (CL M r).drop Lc.length with
      | nil =>
        have hlength := congrArg List.length hd
        simp only [List.length_drop, List.length_nil] at hlength
        omega
      | cons d ds =>
        have hs : CL M r = (CL M r).take Lc.length ++ d :: ds := by
          rw [← hd]
          exact (List.take_append_drop _ _).symm
        exact I.fo r hrM _ d ds hs
  have hAN : isOT (spArg (ρ.v r) z (sumN (((CL M r).take Lc.length).map σ.o))) = true := by
    apply isOT_spArg _ _ z rfl
    apply isOT_sumN
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    have hdCL : d ∈ CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n) r := by
      rw [hCLN]
      exact List.mem_append_left _ (List.mem_of_mem_take hd)
    exact hGN.ot_o d (mem_children (cl_mem_children hdCL)).2
  show isOT (psi (σ.v r) (spArg (σ.v r) z (sumN (Lc.map σ.o))) z) = true
  rw [hvr, htake]
  exact qFO_of_state_lhd (I.good.ot_v r hrM) hAN (hstate _ hj) hAM

/-- Global QFO assembly with only the C2 argument relation as a residual. -/
theorem hFO_of_C2rel (hC2 : T2AtV3 (fun M ρ => ∀ r L q k,
    r + L + 1 = M.length → par M 2 (r + L) = some r →
    par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k →
    T2C2RootRel M ρ r L q)) : T2AtV3 (fun M _ => T2SeedFrames QFO M) := by
  apply hFO_of_C2
  intro M ρ rk C hz h2 r L q k hlen hr hq hqr hncl hu
  exact seedFO_C2_of C hlen hr (hC2 M ρ rk C hz h2 r L q k hlen hr hq hqr hncl hu)

end Ytosk.V3Main.SeedFO
