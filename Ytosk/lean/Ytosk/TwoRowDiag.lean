/-
**2 行の対角列 (0,0,0)(1,1,0)…(k,k,0) は Inv2 を満たす。**

値は o(k) = Ω_k = ψ_k(0)、i < k では o(i) = ψ_i(Ω_k)（親と子が 1 本の鎖で、k−2 から下は吸収）。
-/
import Ytosk.TwoRowFin2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The two-row diagonal `(0,0,0)(1,1,0)…(k,k,0)`. -/
def diag2 (k : Nat) : Mat := (List.range (k + 1)).map (fun i => (i, i, 0))

theorem diag2_length (k : Nat) : (diag2 k).length = k + 1 := by simp [diag2]

theorem diag2_getD {k i : Nat} (hi : i ≤ k) : (diag2 k).getD i (0, 0, 0) = (i, i, 0) := by
  unfold diag2
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem diag2_entry0 {k i : Nat} (hi : i ≤ k) : entry (diag2 k) 0 i = i := by
  unfold entry; rw [diag2_getD hi]; rfl
theorem diag2_entry1 {k i : Nat} (hi : i ≤ k) : entry (diag2 k) 1 i = i := by
  unfold entry; rw [diag2_getD hi]; rfl
theorem diag2_entry2 (k i : Nat) : entry (diag2 k) 2 i = 0 := by
  by_cases hi : i ≤ k
  · unfold entry; rw [diag2_getD hi]; rfl
  · unfold entry; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [diag2_length]; omega)]
    rfl

theorem diag2_par0 {k i : Nat} (hi : i ≤ k) (h1 : 1 ≤ i) : par (diag2 k) 0 i = some (i - 1) := by
  rw [par0_spec]
  refine ⟨by omega, by rw [diag2_entry0 (by omega), diag2_entry0 hi]; omega, fun j h2 h3 => by omega⟩

theorem diag2_par0_zero (k : Nat) : par (diag2 k) 0 0 = none := by
  cases h : par (diag2 k) 0 0 with
  | none => rfl
  | some a => have := par_lt _ 0 0 a h; omega

theorem diag2_par1 {k i : Nat} (hi : i ≤ k) (h1 : 1 ≤ i) : par (diag2 k) 1 i = some (i - 1) := by
  show climb (par (diag2 k) 0) (fun q => decide (entry (diag2 k) 1 q < entry (diag2 k) 1 i)) (i + 1)
    (par (diag2 k) 0 i) = some (i - 1)
  rw [diag2_par0 hi h1]
  simp only [climb]
  rw [if_pos (by rw [diag2_entry1 (by omega), diag2_entry1 hi]; simp; omega)]

theorem diag2_F1 (k : Nat) : F1 (diag2 k) := by
  intro j hj
  by_cases hjk : j ≤ k
  · rw [diag2_entry1 hjk] at hj ⊢
    refine ⟨j - 1, diag2_par1 hjk (by omega), ?_⟩
    rw [diag2_entry1 (by omega)]; omega
  · exfalso
    have : entry (diag2 k) 1 j = 0 := by
      unfold entry; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [diag2_length]; omega)]
      rfl
    omega

theorem diag2_vr {k i : Nat} (hi : i ≤ k) : vr (diag2 k) i = nT i := by
  rw [vr_eq_nT (diag2_F1 k), diag2_entry1 hi]

theorem diag2_children {k i : Nat} (hi : i < k) : children (diag2 k) i = [i + 1] := by
  apply eq_of_sorted_mem _ _ (children_sorted _ _) (List.pairwise_singleton _ _)
  intro c
  rw [mem_children_iff, List.mem_singleton, diag2_length]
  constructor
  · rintro ⟨hc, hp⟩
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · subst h0; rw [diag2_par0_zero] at hp; cases hp
    · rw [diag2_par0 (by omega) hpos] at hp
      have := Option.some.inj hp; omega
  · rintro rfl
    exact ⟨by omega, by rw [diag2_par0 (by omega) (by omega)]; rfl⟩

theorem diag2_children_last (k : Nat) : children (diag2 k) k = [] :=
  children_last (by rw [diag2_length])

theorem isOT_om_nT (k : Nat) : isOT (psi (nT k) z z) = true := isOT_psi_zz (isOT_nT k)

theorem isOT_diag_val (i k : Nat) : isOT (psi (nT i) (psi (nT k) z z) z) = true := by
  rw [isOT_psi_iff]
  refine ⟨isOT_nT i, isOT_om_nT k, rfl, z_le _, ?_⟩
  intro g hg
  have hz : g = z := by
    simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · split at hg
      · simp at hg
      · simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · rfl
        · simp [comps] at hg
        · exact comps_nT k _ g hg
    · simp [comps] at hg
  subst hz; exact T.z_lt_psi _ _ _

/-- **The values of the diagonal.** -/
theorem diag2_o2r (k : Nat) : ∀ i, i ≤ k →
    o2r (diag2 k) i = if i = k then psi (nT k) z z else psi (nT i) (psi (nT k) z z) z := by
  have key : ∀ m i, k - i ≤ m → i ≤ k →
      o2r (diag2 k) i = if i = k then psi (nT k) z z else psi (nT i) (psi (nT k) z z) z := by
    intro m
    induction m with
    | zero =>
      intro i h1 h2
      have hik : i = k := by omega
      subst hik
      rw [if_pos rfl, o2r_leaf (by rw [diag2_length]) (by rw [diag2_vr (le_refl _)]; exact isOT_nT _),
        diag2_vr (le_refl _)]
    | succ m ih =>
      intro i hm hik
      rcases Nat.eq_or_lt_of_le hik with h | h
      · subst h
        rw [if_pos rfl, o2r_leaf (by rw [diag2_length]) (by rw [diag2_vr (le_refl _)]; exact isOT_nT _),
          diag2_vr (le_refl _)]
      · rw [if_neg (by omega)]
        have hch := diag2_children h
        have hc := ih (i + 1) (by omega) (by omega)
        have hcot : isOT (o2r (diag2 k) (i + 1)) = true := by
          rw [hc]; split_ifs
          · exact isOT_om_nT k
          · exact isOT_diag_val _ _
        rw [o2r_spArg (by rw [diag2_vr (by omega)]; exact isOT_nT i) (by
            rw [hch]; simp [sumN, sf_ot hcot]; exact hcot)]
        rw [hch, diag2_vr (by omega)]
        simp only [List.map_cons, List.map_nil]
        have hs : sumN [o2r (diag2 k) (i + 1)] = o2r (diag2 k) (i + 1) := by
          simp [sumN, sf_ot hcot]
        rw [hs, hc]
        by_cases hk : i + 1 = k
        · rw [if_pos hk, spArg_single]
          subst hk
          unfold step
          rw [if_neg (by simp [lt])]
          simp
        · rw [if_neg hk, spArg_single]
          have hlt : lt (nT i) (nT (i + 1)) = true := lt_nT (by omega)
          unfold step
          rw [if_pos ⟨T.z_lt_psi _ _ _, by rw [show lt (psi (nT i) z z) (psi (nT (i + 1)) (psi (nT k) z z) z) =
              true from psi_lt_psi_z_iff.mpr (Or.inl hlt)]⟩]
          rw [H_eq (isOT_diag_val _ _)]
          have hhigh : (split (psi (nT k) z z) (psi (succ (nT (i + 1))) z z)).2 = z := by
            have : ¬ lt (psi (nT k) z z) (psi (succ (nT (i + 1))) z z) = true := by
              intro hc'
              have := psi_lt_om_succ.mp hc'
              rw [← nT_succ] at this
              rcases Nat.lt_or_ge k (i + 2) with h3 | h3
              · omega
              · rcases Nat.eq_or_lt_of_le h3 with h4 | h4
                · rw [h4] at this; exact lt_irrefl' _ this
                · exact lt_irrefl' _ (lt_trans (a := nT (i + 2)) (lt_nT h4) this)
            simp [split, this]
          rw [if_pos hhigh]
          have hfst : (split (psi (nT k) z z) (psi (succ (nT (i + 1))) z z)).1 = psi (nT k) z z := by
            have := split_app (psi (succ (nT (i + 1))) z z) (psi (nT k) z z)
            rw [hhigh, app_z_right] at this; exact this
          rw [hfst, app_z_right]
  exact fun i hi => key _ i (Nat.le_refl _) hi

theorem diag2_o2r_sub {k p : Nat} (hp : p ≤ k) : ∃ y, o2r (diag2 k) p = psi (nT p) y z := by
  rw [diag2_o2r k p hp]
  split_ifs with h
  · subst h; exact ⟨z, rfl⟩
  · exact ⟨_, rfl⟩

theorem diag2_par_in {k h p : Nat} (hp : par (diag2 k) 0 p = some h) : 1 ≤ p ∧ p ≤ k ∧ h = p - 1 := by
  have hlt := ((par0_spec _).mp hp).2.1
  have hpk : p ≤ k := by
    by_contra hc
    have : entry (diag2 k) 0 p = 0 := by
      unfold entry; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [diag2_length]; omega)]
      rfl
    omega
  have hp1 : 1 ≤ p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0; rw [diag2_par0_zero] at hp; cases hp
    · exact h0
  rw [diag2_par0 hpk hp1] at hp
  exact ⟨hp1, hpk, (Option.some.inj hp).symm⟩

theorem diag2_bst {k h p : Nat} (hp : par (diag2 k) 0 p = some h) : bst (diag2 k) h p = z := by
  obtain ⟨hp1, hpk, rfl⟩ := diag2_par_in hp
  unfold bst
  rw [diag2_children (show p - 1 < k by omega)]
  simp [show ¬ p - 1 + 1 < p by omega, sumN, spArg]

/-- **The diagonal satisfies the invariant.** -/
theorem inv2_diag2 (k : Nat) : Inv2 (diag2 k) where
  g2 := by
    refine ⟨diag2_F1 k, ?_, ?_⟩
    · intro i
      by_cases hi : i ≤ k
      · rw [diag2_o2r k i hi]; split_ifs
        · exact isOT_om_nT k
        · exact isOT_diag_val _ _
      · rw [o2r_out (by rw [diag2_length]; omega)]; rfl
    · intro h
      by_cases hh : h < k
      · rw [diag2_children hh]; exact List.pairwise_singleton _ _
      · have : children (diag2 k) h = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro c hc
          have hcm := mem_children_iff.mp hc
          obtain ⟨_, hck, hh'⟩ := diag2_par_in hcm.2
          omega
        rw [this]; exact List.Pairwise.nil
  hi := by
    intro h p s y _ hp _ hB
    exact absurd (diag2_bst hp) hB
  fc := by
    intro h p s y _ hp hc _ _ _ hv
    obtain ⟨hp1, hpk, rfl⟩ := diag2_par_in hp
    obtain ⟨y', hy'⟩ := diag2_o2r_sub hpk
    rw [hy'] at hc
    obtain ⟨rfl, _, _⟩ := psi.inj hc
    rw [diag2_vr (by omega)] at hv
    have := lt_nT (show p - 1 < p by omega)
    rw [hv] at this
    exact absurd this (lt_irrefl' _)
  rd := by
    unfold RootsDec
    have hroots : roots (diag2 k) = [0] := by
      apply eq_of_sorted_mem _ _ (roots_sorted _) (List.pairwise_singleton _ _)
      intro c
      rw [mem_roots, List.mem_singleton, diag2_length]
      constructor
      · rintro ⟨hc, hc0⟩
        have h1 := congrArg Prod.fst hc0
        have h2 : (col (diag2 k) c).1 = entry (diag2 k) 0 c := rfl
        rw [h2, diag2_entry0 (by omega)] at h1
        exact h1
      · rintro rfl
        refine ⟨by omega, ?_⟩
        unfold col; rw [diag2_getD (by omega)]
    rw [hroots]; exact List.pairwise_singleton _ _
  z0 := by
    intro j hj h0
    rw [diag2_length] at hj
    rw [diag2_getD (by omega)] at h0 ⊢
    simp at h0 ⊢; exact h0
  r1 := by
    intro j hj hpos
    rw [diag2_length] at hj
    rw [diag2_getD (by omega)] at hpos ⊢
    simp only at hpos ⊢
    refine ⟨j - 1, by omega, ?_, fun l h1 h2 => by omega, ?_⟩
    · rw [diag2_getD (by omega)]; simp; omega
    · rw [diag2_getD (by omega)]; simp; omega
  e00 := by rw [diag2_entry0 (by omega)]
  row2 := diag2_entry2 k

/-- **The two-row standard matrices**: the diagonals and their expansions. -/
inductive Std2 : Mat → Prop
  | diag (k : Nat) : Std2 (diag2 k)
  | exp {M : Mat} (n : Nat) : Std2 M → Std2 (expand M n)

theorem std2_inv2 {M : Mat} (h : Std2 M) : Inv2 M := by
  induction h with
  | diag k => exact inv2_diag2 k
  | exp n _ ih => exact inv2_expand_all ih n

/-- **Two-row termination via the Ytosk translation**: no infinite expansion sequence from a standard
two-row matrix. -/
theorem twoRow_terminates :
    WellFounded (fun N M : Mat => Std2 M ∧ 1 ≤ M.length ∧ ∃ n, N = expand M n) := by
  apply Subrelation.wf _ twoRow_wf
  intro N M ⟨hS, hM, hn⟩
  exact ⟨std2_inv2 hS, hM, hn⟩

end Ytosk
