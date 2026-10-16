/-
**t = 2・q ≠ r の種の残り `T2SeedQNRes.σB`（2026-10-17、t2）。**

σ = σ_{V, s′}（V = v(r)、s′ = V + ω^S = v_{M.take x}(q)）で、q より前の状態 B = spArg V 0 (Σ o(Lc)) は動かない。
一般の V′ の closure の補題 `tg_sigmaB`（V3T2TameG）を x := q で使う。仮定の確かめ:
- 吸収: s′ < V + ω^W なら s′ + ω^W = V + ω^W（`add_omega_absorb`）。
- r の q より前の子 d で s′ < v(d): 数える子は兄弟の減少 o(d) ≥ o(q) から v(d) ≥ v(q) > s′（`qn_vqlt`）。
  数えない子（上げの的で topped）は名前つきの残り `hU`（実測で例外 0）。
- q への上げはない: q の最後の子 x は bump 子なので q は topped、q は r で数えられるので上げの的でない。
-/
import Ytosk.V3T2TameG
import Ytosk.V3T2SeedRes

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`T2SeedQNRes.σB`**, with the uncounted children of `r` before `q` as the named residual. -/
theorem qn_sigmaB {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCL : CL M r = Lc ++ [q])
    (hU : ∀ d ∈ children M r, d < q → ¬ Counted M r d → qnS M ρ r L q < ρ.v d) :
    sh (ρ.v r) (qnS M ρ r L q) (t2B (ρ.v r) ρ Lc) = t2B (ρ.v r) ρ Lc := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 q r hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hqM : q < M.length := by omega
  have hrM : r < M.length := by omega
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, _, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he2q : entry M 2 q = 1 := I.be q (r + L) hxq Txb
  have he1q : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (show r + L < M.length by omega) hr
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  -- `s′ = V + ω^S`
  set S := sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q)) with hSdef
  have hSot : isOT S = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm I.good q d
  have hqnS : qnS M ρ r L q = add (ρ.v r) (omega S) := rfl
  have hV' : isOT (qnS M ρ r L q) = true := by rw [hqnS]; exact isOT_add hVot (isOT_omega hSot)
  have hVV : ρ.v r < qnS M ρ r L q := by
    rw [hqnS]; obtain ⟨s, y, h⟩ := omega_psi_form S; rw [h]; exact lt_add_principal s y _
  have habs : ∀ W, isOT W = true → qnS M ρ r L q < add (ρ.v r) (omega W) →
      add (qnS M ρ r L q) (omega W) = add (ρ.v r) (omega W) := by
    intro W _ h; rw [hqnS] at h ⊢; exact add_omega_absorb h
  have hvq := qn_vqlt hM hS I hlen hr hq hqr
  -- `q` is counted at `r`
  have hqCL : q ∈ CL M r := by rw [hCL]; simp
  have hqcnt : Counted M r q := by
    have := hqCL; unfold CL at this; simpa using (List.mem_filter.mp this).2
  have hdir : ∀ d ∈ children M r, d < q → entry M 2 d ≠ 0 → qnS M ρ r L q < ρ.v d := by
    intro d hd hdq _
    by_cases hcnt : Counted M r d
    · have hdCL : d ∈ CL M r := List.mem_filter.mpr ⟨hd, decide_eq_true hcnt⟩
      rw [hCL] at hdCL
      have hdL : d ∈ Lc := by
        rcases List.mem_append.mp hdCL with h | h
        · exact h
        · simp at h; omega
      obtain ⟨_, hpM⟩ := cl_vals I.cons I.good hrM
      rw [hCL, List.map_append, List.map_singleton] at hpM
      have hoq : ρ.o q ≤ ρ.o d := (List.pairwise_append.mp hpM).2.2 _ (List.mem_map_of_mem hdL) _ (by simp)
      have hdM : d < M.length := (mem_children hd).2
      obtain ⟨y, hy⟩ := o_psi_sub I.cons hdM
      obtain ⟨y', hy'⟩ := o_psi_sub I.cons hqM
      rw [hy, hy', sf_ot (I.good.ot_v d hdM), sf_ot (I.good.ot_v q hqM)] at hoq
      have := lev_le_of_le hoq
      simp only [lev_psi] at this
      exact lt_of_lt_of_le hvq this
    · exact hU d hd hdq hcnt
  -- nothing upgrades into `q`
  have hux : ∀ i, upg M i = some q → ρ.v r < ρ.v q →
      shf (ρ.v r) (qnS M ρ r L q) (ρ.v q) = ρ.v q := by
    intro i hu _
    exfalso
    apply hqcnt.2
    refine ⟨?_, ?_⟩
    · unfold isUpg
      exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr (by have := upg_lt_len hu; omega), decide_eq_true hu⟩
    · have hsplit := split_last_max _ _ (children_sorted M q) hxq
        (fun d hd => by have := (mem_children hd).2; omega)
      unfold topped
      rw [hsplit, List.getLast?_append]
      simp [Txb]
  have hrx : par M 0 q = some r := hpq
  exact tg_sigmaB hX hJ I.cons I.good I.rank hrx hqM he2q (by omega) he2r hV' hVV habs hdir hux hCL

/-- **The residual of `qn_sigmaB`**: the uncounted children of `r` before `q` have `v > s′`. -/
def QNUncRes (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ d ∈ children M r, d < q → ¬ Counted M r d → qnS M ρ r L q < ρ.v d

/-- **`T2SeedQNResR` with `σB` replaced by `QNUncRes`.** -/
structure T2SeedQNResR2 (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop where
  unc : QNUncRes M ρ r L q
  base : ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ∧
    ∀ k, ρ.v r < tqN (ρ.v r) (qnS M ρ r L q) t1 k ∧
      ¬ shf (ρ.v r) (qnS M ρ r L q) (tqN (ρ.v r) (qnS M ρ r L q) t1 k) < succ (qnS M ρ r L q) ∧
      (1 ≤ k → tqN (ρ.v r) (qnS M ρ r L q) t1 k < ρ.v q ∧
        (tqN (ρ.v r) (qnS M ρ r L q) t1 k = ρ.v q ∨ Lhd z (tqN (ρ.v r) (qnS M ρ r L q) t1 k) (ρ.v q)))

theorem t2SeedQNResR_of2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCL : CL M r = Lc ++ [q])
    (h : T2SeedQNResR2 M ρ r L q Lc) : T2SeedQNResR M ρ r L q Lc :=
  ⟨qn_sigmaB hM hS I hlen hr hq hqr hCL h.unc, h.base⟩

/-- **`T2SeedPResR` with the qn residual `T2SeedQNResR2`.** -/
structure T2SeedPResR2 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQRResR M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → T2SeedSVResR M ρ r L
  qn : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNResR2 M ρ r L q Lc
  C : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCRes M ρ r L q ∧ G.T2SeedCBig M ρ r L q

theorem t2SeedPResR_of2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (h : T2SeedPResR2 M ρ) : T2SeedPResR M ρ where
  qr := h.qr
  sv := h.sv
  qn := fun r L q hlen hr hq hqr Lc hCL => t2SeedQNResR_of2 hM hS I hlen hr hq hqr hCL (h.qn r L q hlen hr hq hqr Lc hCL)
  C := h.C

end Ytosk
