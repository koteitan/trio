/-
A return grandchild under an ancestor-upgrade target has the same row-1
parent and upgrade search as the column being copied.
-/
import Ytosk.V3HUACPath
import Ytosk.V3OmegaComps
import Ytosk.V3SumComps

namespace Ytosk.HUACCopy
open T

/-- The three inserted ancestors are skipped by the row-1 parent search. -/
theorem par1_return {M : Mat} {m k j c : Nat}
    (hkm : par M 0 k = some m) (hjk : par M 0 j = some k)
    (hcj : par M 0 c = some j)
    (hmk : entry M 1 m < entry M 1 k)
    (hjk1 : entry M 1 j = entry M 1 k)
    (hc1 : entry M 1 c = entry M 1 m) :
    par M 1 c = par M 1 m := by
  rw [par1_find M c, ancL_eq hcj, ancL_eq hjk, ancL_eq hkm, hc1]
  simp only [List.find?_cons]
  have hj : ¬ entry M 1 j < entry M 1 m := by omega
  have hk : ¬ entry M 1 k < entry M 1 m := by omega
  simp only [decide_eq_false hj, decide_eq_false hk, Nat.lt_irrefl, decide_false]
  exact (par1_find M m).symm

/-- Once both next columns stay below the copied ancestor, the ancestor searches agree. -/
theorem upg_return {M : Mat} {m k j c : Nat}
    (hkm : par M 0 k = some m) (hjk : par M 0 j = some k)
    (hcj : par M 0 c = some j)
    (hmk : entry M 1 m < entry M 1 k)
    (hjk1 : entry M 1 j = entry M 1 k)
    (hc1 : entry M 1 c = entry M 1 m)
    (hm2 : entry M 2 m = 0) (hc2 : entry M 2 c = 0)
    (hmN : m + 1 < M.length) (hcN : c + 1 < M.length)
    (hmd : entry M 0 m < entry M 0 (m + 1))
    (hcd : entry M 0 m < entry M 0 (c + 1)) : upg M c = upg M m := by
  have hp := par1_return hkm hjk hcj hmk hjk1 hc1
  by_cases h10 : entry M 1 m = 0
  · simp [upg, hc1, h10]
  unfold upg
  rw [hc1, hc2, hm2, if_neg (by omega), if_neg (by omega), hp]
  cases hm : par M 1 m with
  | none => rfl
  | some p =>
    have hpm : entry M 0 p < entry M 0 m :=
      anc0_e0_lt (anc0_of_par M 1 p m hm) (by have := par_lt M 1 m p hm; omega)
    have hnotc : ¬ (par M 1 (c + 1) = some p ∧
        col M (c + 1) = (entry M 0 p + 1, entry M 1 m, entry M 2 p + 1)) := by
      rintro ⟨_, h⟩
      have := e0_of_col h
      omega
    have hnotm : ¬ (par M 1 (m + 1) = some p ∧
        col M (m + 1) = (entry M 0 p + 1, entry M 1 m, entry M 2 p + 1)) := by
      rintro ⟨_, h⟩
      have := e0_of_col h
      omega
    simp only
    rw [if_neg hnotc, if_neg hnotm, upgClimb_find, upgClimb_find,
      ancL_eq hcj, ancL_eq hjk, ancL_eq hkm]
    have hfj : decide (par M 1 j = some p ∧
        col M j = (entry M 0 p + 1, entry M 1 m, entry M 2 p + 1) ∧
        entry M 0 j < entry M 0 (c + 1)) = false := by
      apply decide_eq_false
      rintro ⟨_, h, _⟩
      have := e1_of_col h
      omega
    have hfk : decide (par M 1 k = some p ∧
        col M k = (entry M 0 p + 1, entry M 1 m, entry M 2 p + 1) ∧
        entry M 0 k < entry M 0 (c + 1)) = false := by
      apply decide_eq_false
      rintro ⟨_, h, _⟩
      have := e1_of_col h
      omega
    have hfm : decide (par M 1 m = some p ∧
        col M m = (entry M 0 p + 1, entry M 1 m, entry M 2 p + 1) ∧
        entry M 0 m < entry M 0 (c + 1)) = false := by
      apply decide_eq_false
      rintro ⟨_, h, _⟩
      have := e2_of_col h
      omega
    simp only [List.find?_cons, hfj, hfk, hfm]
    apply find?_congr'
    intro q hq
    have hqm : entry M 0 q < entry M 0 m :=
      anc0_e0_lt (anc0_of_mem_ancL hq) (by have := mem_ancL_lt hq; omega)
    simp only [show entry M 0 q < entry M 0 (c + 1) from by omega,
      show entry M 0 q < entry M 0 (m + 1) from by omega, and_true]

/-- The structural return-copy certificate, derived from an actual ancestor upgrade. -/
theorem return_copy {M : Mat} (S : SInv M) {n k m j c : Nat}
    (hn : n < M.length) (hu : upg M n = some k) (hkn : k < n)
    (hkm : par M 0 k = some m)
    (hj : j ∈ children M k) (hjb : col M j = bump M k)
    (hc : c ∈ children M j) (hcn : c < n)
    (hc1 : entry M 1 c = entry M 1 m) (hc2 : entry M 2 c = 0) :
    par M 1 c = par M 1 m ∧ upg M c = upg M m := by
  obtain ⟨m', hm', hkm'⟩ := upg_target_par0 S.r0p hu
  rw [hkm] at hkm'; cases hkm'
  obtain ⟨m'', hm'', hk1, hcol, hcase⟩ := upg_spec hu
  rw [hm'] at hm''; cases hm''
  have hmk := par1_entry_lt hk1
  have hjk1 : entry M 1 j = entry M 1 k := e1_of_col hjb
  have hjk := (mem_children_iff.mp hj).2
  have hcj := (mem_children_iff.mp hc).2
  have hkj := (mem_children hj).1
  have hjc := (mem_children hc).1
  have hmkN := par_lt M 0 k m hkm
  have hm2 : entry M 2 m = 0 := by
    have h2 := e2_of_col hcol
    have hZ := S.z2 k
    omega
  have hA : Anc0 M k n := by rcases hcase with h | h; omega; exact h.1
  have hmnext : par M 0 (m + 1) = some m :=
    child_succ (Anc0.step hkm (Anc0.refl m)) (by omega)
  have hmd : entry M 0 m < entry M 0 (m + 1) := by
    have := S.r0p (m + 1) m hmnext
    omega
  have hAcnext : Anc0 M k (c + 1) := anc_between hA (c + 1) (by omega) (by omega)
  have hcd : entry M 0 m < entry M 0 (c + 1) := by
    have := anc0_e0_lt hAcnext (by omega)
    have := S.r0p k m hkm
    omega
  exact ⟨par1_return hkm hjk hcj hmk hjk1 hc1,
    upg_return hkm hjk hcj hmk hjk1 hc1 hm2 hc2 (by omega) (by omega) hmd hcd⟩

/-- Cons turns the structural return certificate into equality of values. -/
theorem value_return_copy {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ)
    {n k m j c : Nat} (hn : n < M.length) (hu : upg M n = some k) (hkn : k < n)
    (hkm : par M 0 k = some m)
    (hj : j ∈ children M k) (hjb : col M j = bump M k)
    (hc : c ∈ children M j) (hcn : c < n)
    (hc1 : entry M 1 c = entry M 1 m) (hc2 : entry M 2 c = 0) : ρ.v c = ρ.v m := by
  obtain ⟨hp, hup⟩ := return_copy S hn hu hkn hkm hj hjb hc hcn hc1 hc2
  have hcN := (mem_children hc).2
  have hmk := par_lt M 0 k m hkm
  obtain ⟨m', hm', hk0⟩ := upg_target_par0 S.r0p hu
  rw [hkm] at hk0; cases hk0
  obtain ⟨m'', hm'', _, hcol, _⟩ := upg_spec hu
  rw [hm'] at hm''; cases hm''
  have hm2 : entry M 2 m = 0 := by have := e2_of_col hcol; have := S.z2 k; omega
  rw [(hC c hcN).2, (hC m (by omega)).2]
  unfold vRhs
  rw [hc1, hc2, hm2, hp, hup]
  simp only [ite_true]

/-- A final bump child with a final grandchild returning to the copied row. -/
def ReturnWitness (M : Mat) (n k m : Nat) : Prop :=
  ∃ L j R K c, children M k = L ++ j :: R ∧ col M j = bump M k ∧
    (∀ d ∈ R, col M d ≠ bump M k) ∧ children M j = K ++ [c] ∧
    c < n ∧ entry M 1 c = entry M 1 m ∧ entry M 2 c = 0

/-- A return witness transports components through the two omega stages and sums. -/
theorem dom_of_return {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {n k m : Nat} (hn : n < M.length) (hu : upg M n = some k) (hkn : k < n)
    (hkm : par M 0 k = some m) (hw : ReturnWitness M n k m) :
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z]) := by
  obtain ⟨L, j, R, K, c, hL, hjb, hR, hK, hcn, hc1, hc2⟩ := hw
  have hj : j ∈ children M k := by rw [hL]; simp
  have hc : c ∈ children M j := by rw [hK]; simp
  have hcN := (mem_children hc).2
  have hvc := value_return_copy S hC hn hu hkn hkm hj hjb hc hcn hc1 hc2
  obtain ⟨m', hm', hk0⟩ := upg_target_par0 S.r0p hu
  rw [hkm] at hk0; cases hk0
  rw [hm']
  simp only [vOpt]
  obtain ⟨y, hy⟩ := o_psi_sub hC hcN
  rw [sf_ot (hG.ot_v c hcN)] at hy
  have hv_o : ∀ u, Dom (comps u (ρ.v m)) (comps u (ρ.o c) ++ [z]) := by
    rw [← hvc, hy]
    exact HUACPath.index_comp_dom (hG.ot_v c hcN)
  have ho_G : ∀ u, Dom (comps u (ρ.o c))
      (comps u (sumN ((children M j).map ρ.o)) ++ [z]) := by
    intro u a ha
    refine ⟨a, List.mem_append_left _ ?_, le_refl _⟩
    rw [hK, List.map_append, List.map_singleton]
    apply SumComps.mem_sumN_snoc ?_ (hG.ot_o c hcN) ha
    intro q hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
    have hdM : d ∈ children M j := by rw [hK]; simp [hd]
    exact hG.ot_o d (mem_children hdM).2
  have hGot : isOT (sumN ((children M j).map ρ.o)) = true :=
    isOT_sumN _ (by intro q hq; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq; exact hG.ot_o d (mem_children hd).2)
  have hG_B : ∀ u, Dom (comps u (sumN ((children M j).map ρ.o)))
      (comps u (bumpTerm M ρ k j) ++ [z]) := by
    unfold bumpTerm
    rw [if_pos hjb]
    exact OmegaComps.dom_comps_omega hGot
  let P := sumN (one :: (children M k).map (bumpTerm M ρ k))
  have hB_P : ∀ u, Dom (comps u (bumpTerm M ρ k j)) (comps u P ++ [z]) := by
    intro u a ha
    refine ⟨a, List.mem_append_left _ ?_, le_refl _⟩
    dsimp only [P]
    rw [hL, List.map_append, List.map_cons]
    change a ∈ comps u (sumN ((one :: L.map (bumpTerm M ρ k)) ++
      bumpTerm M ρ k j :: R.map (bumpTerm M ρ k)))
    apply SumComps.mem_sumN_last_nonzero ?_ (isOT_bumpTerm hG k j) ?_ ha
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
        exact isOT_bumpTerm hG k d
    · intro q hq
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      unfold bumpTerm
      rw [if_neg (hR d hd)]
  have hP_W : ∀ u, Dom (comps u P) (comps u (omega P) ++ [z]) :=
    OmegaComps.dom_comps_omega (isOT_bumpP hG k)
  have hW_v : ∀ u, Dom (comps u (omega P)) (comps u (ρ.v n) ++ [z]) := by
    obtain ⟨hn1, hn2'⟩ := upg_e12 hu
    have hn2 : entry M 2 n = 0 := by have := S.z2 n; omega
    have hnv := v_upg_eq hC hn hn1 hn2 hu (vOpt_ot hG (by omega))
      (fun _ _ _ d hd => hG.ot_o d (mem_children hd).2)
    obtain ⟨m'', hm'', hk1, hcol, _⟩ := upg_spec hu
    rw [hm'] at hm''; cases hm''
    have hkN : k < M.length := by omega
    have hk2 : entry M 2 k ≠ 0 := by have := e2_of_col hcol; omega
    have hk1nz : entry M 1 k ≠ 0 := by have := e1_of_col hcol; omega
    have hkv : ρ.v k = add (ρ.v m) (omega P) := by
      rw [(hC k hkN).2]
      unfold vRhs
      rw [if_neg hk1nz, if_neg hk2, hk1]
      simp only [vOpt]
      exact sf_ot (isOT_add (hG.ot_v m (by have := par_lt M 0 k m hkm; omega))
        (isOT_omega (isOT_bumpP hG k)))
    intro u a ha
    refine ⟨a, List.mem_append_left _ ?_, le_refl _⟩
    rw [hnv, hkv]
    exact SumComps.mem_add_right ha
  exact HUACPath.comp_dom_trans hv_o (HUACPath.comp_dom_trans ho_G
    (HUACPath.comp_dom_trans hG_B (HUACPath.comp_dom_trans hB_P (HUACPath.comp_dom_trans hP_W hW_v))))

/-- HUAC only when the final bump-child / return-grandchild certificate is absent.
The measured critical occurrences split into 220,937 with this certificate and
7,320 without it: 1,108 have a childless final bump child and zero head index;
6,212 have a positive unequal head index, with a finite summand-support bound
as a candidate replacement certificate. These finite measurements are not a
proof of the remaining residual. Noncritical cases are not excluded here. -/
def HUAC' : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ →
    ∀ n k m, upg N n = some k → k < n → par N 0 k = some m →
      ¬ ReturnWitness N n k m →
      ∀ u, Dom (comps u (vOpt σ (par N 1 n))) (comps u (σ.v n) ++ [z])

/-- The return-copy cases are theorems; only the absent-certificate cases remain. -/
theorem hUAC_of (hU : HUAC') : HUAC := by
  intro N σ rk hN hS hC hR hG n k hu hkn
  have S := sInv_std hN hS
  obtain ⟨m, _, hkm⟩ := upg_target_par0 S.r0p hu
  by_cases hw : ReturnWitness N n k m
  · exact dom_of_return S hC hG (by have := upg_succ_lt hu; omega) hu hkn hkm hw
  · exact hU N σ rk hN hS hC hR hG n k m hu hkn hkm hw

end Ytosk.HUACCopy
