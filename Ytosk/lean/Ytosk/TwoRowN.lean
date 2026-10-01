/-
**2 行: 最後の列を落とすと行列の値（根の和 `ev2r`）は真に下がる。**

最後の列が (0,0,0) なら最後の根（値 ψ_0(0) = 1）が消え、そうでなければ一番上の祖先の値が (T) で下がる。
これを繰り返して、先頭部分 M.take k（k < |M|）の値は M の値より小さい。展開の n = 0, 1 と最後の列が (0,0,0) の場合はこれ。
-/
import Ytosk.TwoRowZ4

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Dropping the last column lowers the matrix value.** -/
theorem ev2r_drop_last {M : Mat} (hM : 1 ≤ M.length) (hG : Good2 M)
    (hG' : Good2 (M.take (M.length - 1))) (hRD : RootsDec M) (hz0 : TRIO.z0ok M)
    (h00 : entry M 0 0 = 0) :
    isOT (ev2r (M.take (M.length - 1))) = true ∧ ev2r (M.take (M.length - 1)) < ev2r M := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hlt : (M.take (M.length - 1)).length = M.length - 1 := by rw [List.length_take]; omega
  by_cases hcol : col M (M.length - 1) = (0, 0, 0)
  · -- the last root disappears
    have hsplit := roots_split hx (Anc0.refl _) hcol
    set R := (roots M).filter (fun c => decide (c < M.length - 1)) with hRd
    have hex : entry M 0 (M.length - 1) = 0 := by unfold entry; unfold col at hcol; rw [hcol]; rfl
    have hroots : roots (M.take (M.length - 1)) = R := by
      apply eq_of_sorted_mem _ _ (roots_sorted _) (List.Pairwise.filter _ (roots_sorted M))
      intro c
      rw [mem_roots, List.mem_filter, mem_roots, hlt]
      constructor
      · rintro ⟨hc, hc0⟩
        rw [col_take M hc] at hc0; exact ⟨⟨by omega, hc0⟩, by simpa using hc⟩
      · rintro ⟨⟨_, hc0⟩, hc⟩
        have hc' : c < M.length - 1 := by simpa using hc
        exact ⟨hc', by rw [col_take M hc']; exact hc0⟩
    have hRv : R.map (o2r (M.take (M.length - 1))) = R.map (o2r M) := by
      apply List.map_congr_left
      intro c hc
      rw [hRd, List.mem_filter] at hc
      exact o2r_take_low hex c (by simpa using hc.2)
    have hdM : (R.map (o2r M) ++ [o2r M (M.length - 1)]).Pairwise (fun a b => b ≤ a) := by
      have := hRD; unfold RootsDec at this
      rw [hsplit, List.map_append] at this; exact this
    have hsM : ∀ t ∈ R.map (o2r M) ++ [o2r M (M.length - 1)], Single t := by
      intro t ht; obtain ⟨i, _, rfl⟩ := List.mem_map.mp (by
        rcases List.mem_append.mp ht with h | h
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h; exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by
            rw [hRd, List.mem_filter] at hi; exact (mem_roots.mp hi.1).1), rfl⟩
        · rw [List.mem_singleton] at h; subst h
          exact List.mem_map.mpr ⟨M.length - 1, List.mem_range.mpr (by omega), rfl⟩ :
        t ∈ (List.range M.length).map (o2r M))
      exact single_o2r hG i
    have eN : ev2r (M.take (M.length - 1)) = sumN (R.map (o2r M)) := by
      rw [ev2r_roots, hroots, hRv]
    have eM : ev2r M = app (sumN (R.map (o2r M))) (o2r M (M.length - 1)) := by
      rw [ev2r_roots, hsplit, List.map_append]
      exact sumN_snoc_dec hsM hdM
    refine ⟨?_, ?_⟩
    · rw [eN]
      exact (sumN_dec _ (fun t ht => hsM t (List.mem_append_left _ ht))
        (List.pairwise_append.mp hdM).1).1
    · rw [eN, eM]
      obtain ⟨w, w', hw⟩ := o2r_psi_form M (M.length - 1)
      exact lt_app_of (by rw [hw]; simp)
  · -- the top of the path drops
    obtain ⟨ρ, hρ, hρn⟩ := top_anc M (M.length - 1)
    have hρ0 := col_zero_of_top hz0 h00 (by have := hρ.le; omega) hρn
    have hρx : ρ < M.length - 1 := by
      rcases Nat.eq_or_lt_of_le hρ.le with h | h
      · rw [h] at hρ0; exact absurd hρ0 hcol
      · exact h
    have hroots : roots (M.take (M.length - 1)) = roots M := by
      apply roots_eq hx (by omega) (fun c hc => col_take M hc) hcol
      intro c h1 h2; rw [hlt] at h2; omega
    apply ev2r_lt_of_top hx hG hRD hρ hρ0 hroots
    · intro c hc hcρ
      apply o2r_take_off hx c (by omega)
      intro hcA
      rcases anc0_total hcA hρ with h' | h'
      · cases h' with
        | refl => omega
        | step hp _ => rw [hp] at hρn; cases hρn
      · have := h'.le; omega
    · exact hG'.ot ρ
    · exact o2r_take_anc hx hG hG' ρ hρ hρx

/-- **Every proper prefix has a smaller matrix value** (given the invariants on all prefixes). -/
theorem ev2r_take_lt {M : Mat}
    (hI : ∀ j, j ≤ M.length → Good2 (M.take j) ∧ RootsDec (M.take j) ∧ TRIO.z0ok (M.take j))
    (h00 : entry M 0 0 = 0) :
    ∀ k, k < M.length → isOT (ev2r (M.take k)) = true ∧ ev2r (M.take k) < ev2r M := by
  have hstep : ∀ j, 1 ≤ j → j ≤ M.length →
      isOT (ev2r (M.take (j - 1))) = true ∧ ev2r (M.take (j - 1)) < ev2r (M.take j) := by
    intro j hj1 hj2
    have hl : (M.take j).length = j := by simp; omega
    have h := ev2r_drop_last (M := M.take j) (by omega) (hI j hj2).1
      (by rw [hl, List.take_take, Nat.min_eq_left (by omega)]; exact (hI (j - 1) (by omega)).1)
      (hI j hj2).2.1 (hI j hj2).2.2 (by rw [entry_take M 0 (show 0 < j by omega)]; exact h00)
    rw [hl, List.take_take, Nat.min_eq_left (by omega)] at h
    exact h
  have key : ∀ m k, k + 1 + m ≤ M.length →
      isOT (ev2r (M.take k)) = true ∧ ev2r (M.take k) < ev2r (M.take (k + 1 + m)) := by
    intro m
    induction m with
    | zero => intro k hk; have := hstep (k + 1) (by omega) hk; simpa using this
    | succ m ih =>
      intro k hk
      obtain ⟨h1, h2⟩ := ih k (by omega)
      have h3 := (hstep (k + 1 + m + 1) (by omega) hk).2
      simp only [Nat.add_sub_cancel] at h3
      exact ⟨h1, lt_trans h2 (by rw [show k + 1 + (m + 1) = k + 1 + m + 1 by omega]; exact h3)⟩
  intro k hk
  have := key (M.length - k - 1) k (by omega)
  rw [show k + 1 + (M.length - k - 1) = M.length by omega, List.take_length] at this
  exact this

/-- With last column `(0,0,0)`, the expansion drops it. -/
theorem expand_zero_col {M : Mat} (hM : 1 ≤ M.length) (hcol : col M (M.length - 1) = (0, 0, 0))
    (n : Nat) : expand M n = M.take (M.length - 1) := by
  cases M with
  | nil => simp at hM
  | cons c M' =>
    unfold expand
    simp only
    rw [if_pos hcol]

/-- `M[0] = M.take r`. -/
theorem expand_n0 {M : Mat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    {r : Nat} (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r) :
    expand M 0 = M.take r := by
  have hrx := par_lt M _ _ _ hr
  rw [expand_eq_gexp M 0 hM hz hr]
  unfold TRIO.gexp
  conv => rhs; rw [← List.append_nil (M.take r)]
  congr 1

/-- `M[1] = M.take x`. -/
theorem expand_n1 {M : Mat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    {r : Nat} (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r) :
    expand M 1 = M.take (M.length - 1) := by
  have hrx := par_lt M _ _ _ hr
  have hlen : (expand M 1).length = M.length - 1 := by
    rw [expand_eq_gexp M 1 hM hz hr, TRIO.gexp_length (by omega)]; omega
  rw [← expand_take_prefix M hM (Nat.le_refl 1), List.take_of_length_le (by omega)]

end Ytosk
