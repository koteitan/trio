/-
**2 行: 行列全体の値（根の和 `ev2r`）の段。**

経路の一番上の祖先 ρ（根）は最後の根で、ev2r = （前の根の値の和）+ o(ρ)。展開で根の並びが変わらなければ、
ρ の値が小さく標準形になれば ev2r も小さく標準形になる。
-/
import Ytosk.TwoRowZ2

namespace Ytosk

open T

/-- The root columns. -/
def roots (M : Mat) : List Nat := (List.range M.length).filter (fun i => decide (col M i = (0, 0, 0)))

theorem ev2r_roots (M : Mat) : ev2r M = sumN ((roots M).map (o2r M)) := rfl

theorem roots_sorted (M : Mat) : (roots M).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem mem_roots {M : Mat} {c : Nat} : c ∈ roots M ↔ c < M.length ∧ col M c = (0, 0, 0) := by
  unfold roots; rw [List.mem_filter, List.mem_range]; simp

/-- Root values, left to right, do not increase. -/
def RootsDec (M : Mat) : Prop := ((roots M).map (o2r M)).Pairwise (fun a b => b ≤ a)

/-- **The top of the path is the last root.** -/
theorem roots_split {M : Mat} {x ρ : Nat} (hx : x + 1 = M.length) (hρ : Anc0 M ρ x)
    (hρ0 : col M ρ = (0, 0, 0)) :
    roots M = (roots M).filter (fun c => decide (c < ρ)) ++ [ρ] := by
  apply split_last_max _ ρ (roots_sorted M) (mem_roots.mpr ⟨by have := hρ.le; omega, hρ0⟩)
  intro c hc
  obtain ⟨hcl, hc0⟩ := mem_roots.mp hc
  by_contra hcon
  have h1 := anc0_interval hρ c (by omega) (by omega)
  have e1 : entry M 0 c = 0 := by unfold entry; unfold col at hc0; rw [hc0]; rfl
  omega

/-- **Roots unchanged** when the columns before `x` agree and no later column is a root. -/
theorem roots_eq {M N : Mat} {x : Nat} (hx : x + 1 = M.length) (hNl : x ≤ N.length)
    (hpre : ∀ c, c < x → col N c = col M c) (hxr : col M x ≠ (0, 0, 0))
    (hcopy : ∀ c, x ≤ c → c < N.length → col N c ≠ (0, 0, 0)) : roots N = roots M := by
  apply eq_of_sorted_mem _ _ (roots_sorted N) (roots_sorted M)
  intro c
  rw [mem_roots, mem_roots]
  constructor
  · rintro ⟨hcl, hc0⟩
    rcases Nat.lt_or_ge c x with h | h
    · rw [hpre c h] at hc0; exact ⟨by omega, hc0⟩
    · exact absurd hc0 (hcopy c h hcl)
  · rintro ⟨hcl, hc0⟩
    rcases Nat.lt_or_ge c x with h | h
    · rw [← hpre c h] at hc0; exact ⟨by omega, hc0⟩
    · have : c = x := by omega
      subst this; exact absurd hc0 hxr

/-- **The matrix value drops with the top of the path.** -/
theorem ev2r_lt_of_top {M N : Mat} {x ρ : Nat} (hx : x + 1 = M.length) (hG : Good2 M)
    (hRD : RootsDec M) (hρ : Anc0 M ρ x) (hρ0 : col M ρ = (0, 0, 0)) (hroots : roots N = roots M)
    (hoff : ∀ c ∈ roots M, c < ρ → o2r N c = o2r M c)
    (hot : isOT (o2r N ρ) = true) (hlt : o2r N ρ < o2r M ρ) :
    isOT (ev2r N) = true ∧ ev2r N < ev2r M := by
  have hsplit := roots_split hx hρ hρ0
  set R := (roots M).filter (fun c => decide (c < ρ)) with hRdef
  have hRv : R.map (o2r N) = R.map (o2r M) := by
    apply List.map_congr_left
    intro c hc
    rw [hRdef, List.mem_filter] at hc
    exact hoff c hc.1 (by simpa using hc.2)
  have hdM : (R.map (o2r M) ++ [o2r M ρ]).Pairwise (fun a b => b ≤ a) := by
    have := hRD; unfold RootsDec at this
    rw [hsplit, List.map_append] at this; exact this
  have hdM' := List.pairwise_append.mp hdM
  have hsing : ∀ t ∈ R.map (o2r M), Single t := by
    intro t ht; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hG i
  have hdN : (R.map (o2r M) ++ [o2r N ρ]).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_append]
    refine ⟨hdM'.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    exact le_trans (le_of_lt hlt) (hdM'.2.2 a ha _ (List.mem_singleton_self _))
  have hsN : ∀ t ∈ R.map (o2r M) ++ [o2r N ρ], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsing t ht
    · rw [List.mem_singleton] at ht; subst ht; exact ⟨hot, o2r_psi_form _ _⟩
  have hsM : ∀ t ∈ R.map (o2r M) ++ [o2r M ρ], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsing t ht
    · rw [List.mem_singleton] at ht; subst ht; exact single_o2r hG ρ
  have eN : ev2r N = app (sumN (R.map (o2r M))) (o2r N ρ) := by
    rw [ev2r_roots, hroots, hsplit, List.map_append, hRv]
    exact sumN_snoc_dec hsN hdN
  have eM : ev2r M = app (sumN (R.map (o2r M))) (o2r M ρ) := by
    rw [ev2r_roots, hsplit, List.map_append]
    exact sumN_snoc_dec hsM hdM
  refine ⟨?_, ?_⟩
  · have := (sumN_dec _ hsN hdN).1
    rw [eN, ← sumN_snoc_dec hsN hdN]; exact this
  · rw [eN, eM]; exact (app_lt_app_left_iff _).mpr hlt

/-- Every column has a top row-0 ancestor. -/
theorem top_anc (M : Mat) : ∀ x, ∃ ρ, Anc0 M ρ x ∧ par M 0 ρ = none := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    cases hp : par M 0 x with
    | none => exact ⟨x, Anc0.refl x, hp⟩
    | some p =>
      obtain ⟨ρ, hρ, hρn⟩ := ih p (par_lt M 0 x p hp)
      exact ⟨ρ, hρ.trans (Anc0.step hp (Anc0.refl p)), hρn⟩

/-- A top column is a root `(0,0,0)` (first column zero, `z0ok`). -/
theorem col_zero_of_top {M : Mat} (hz0 : TRIO.z0ok M) (h00 : entry M 0 0 = 0) {ρ : Nat}
    (hl : ρ < M.length) (hρ : par M 0 ρ = none) : col M ρ = (0, 0, 0) := by
  have he : entry M 0 ρ = 0 := by
    rcases Nat.eq_zero_or_pos ρ with h | h
    · subst h; exact h00
    · by_contra hne
      obtain ⟨p, hp⟩ := par0_some_of (M := M) (show 0 < ρ from h) (by omega)
      rw [hp] at hρ; cases hρ
  have := hz0 ρ hl he
  unfold col
  change (M.getD ρ (0, 0, 0)).1 = 0 at he
  obtain ⟨h1, h2⟩ := this
  rcases hc : M.getD ρ (0, 0, 0) with ⟨a, b, c⟩
  rw [hc] at he h1 h2
  simp at he h1 h2
  rw [he, h1, h2]

theorem col_ne_zero_of_entry {M : Mat} {c : Nat} (h : 0 < entry M 0 c) : col M c ≠ (0, 0, 0) := by
  intro hc; unfold entry col at *; rw [hc] at h; simp at h

/-- **With `t ≥ 1` (row 0 ascends), the expansion keeps the roots.** -/
theorem roots_expand_t1 {M : Mat} {r n : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht : 0 < TRIO.srow M (M.length - 1)) (hn : 1 ≤ n)
    (hxr : col M (M.length - 1) ≠ (0, 0, 0)) : roots (expand M n) = roots M := by
  obtain ⟨d1, heq, hlen, hLb, hA, hd0e⟩ := expand_gexp_data M n hM hz hr ht
  have hrx := par_lt M _ _ _ hr
  have hdpos : 0 < entry M 0 (M.length - 1) - entry M 0 r := by
    have := anc0_interval (anc0_of_par M _ _ _ hr) (M.length - 1) hrx (Nat.le_refl _); omega
  have hlen' : (expand M n).length = r + n * (M.length - 1 - r) := by
    rw [heq]; exact TRIO.gexp_length hlen
  apply roots_eq (x := M.length - 1) (by omega)
  · rw [hlen']; have := Nat.mul_le_mul_right (M.length - 1 - r) hn; simp at this; omega
  · intro c hc
    have h1 := expand_take_prefix M hM hn
    rw [← col_take (expand M n) hc, h1, col_take M hc]
  · exact hxr
  · intro c hc1 hc2
    apply col_ne_zero_of_entry
    rw [hlen'] at hc2
    obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (n := n) (p := c) hLb (by omega) hc2
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simp at hc1; omega
      · exact h0
    rw [heq, entry0_gexp_mir hlen hk hq]
    have : 1 * (entry M 0 (M.length - 1) - entry M 0 r) ≤ k * (entry M 0 (M.length - 1) - entry M 0 r) :=
      Nat.mul_le_mul_right _ hk1
    omega

/-- **From the path to the matrix value** (`t ≥ 1`, `n ≥ 2`). -/
theorem ev2r_expand_t1 {M : Mat} {r n : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht : 0 < TRIO.srow M (M.length - 1)) (hn : 2 ≤ n) (hG : Good2 M) (hRD : RootsDec M)
    (hz0 : TRIO.z0ok M) (h00 : entry M 0 0 = 0)
    (hpath : ∀ h, Anc0 M h (M.length - 1) →
      isOT (o2r (expand M n) h) = true ∧ o2r (expand M n) h < o2r M h) :
    isOT (ev2r (expand M n)) = true ∧ ev2r (expand M n) < ev2r M := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hxr : col M (M.length - 1) ≠ (0, 0, 0) := by
    intro h; apply hz; unfold col at h
    rw [← entry_eq, ← entry_eq, ← entry_eq]; unfold entry; rw [h]; simp
  obtain ⟨ρ, hρ, hρn⟩ := top_anc M (M.length - 1)
  have hρ0 := col_zero_of_top hz0 h00 (by have := hρ.le; omega) hρn
  apply ev2r_lt_of_top hx hG hRD hρ hρ0 (roots_expand_t1 hM hz hr ht (by omega) hxr)
  · intro c hc hcρ
    have hcl := (mem_roots.mp hc).1
    apply o2r_expand_off hM hz hr ht hn c (by have := hρ.le; omega)
    intro hcA
    rcases anc0_total hcA hρ with h' | h'
    · rcases Nat.eq_or_lt_of_le h'.le with h2 | h2
      · omega
      · cases h' with
        | refl => omega
        | step hp _ => rw [hp] at hρn; cases hρn
    · have := h'.le; omega
  · exact (hpath ρ hρ).1
  · exact (hpath ρ hρ).2

/-- **Two rows, `t = 1`, `q = r`: the matrix value drops and stays standard.** Remaining hypothesis: PRE. -/
theorem twoRow_desc_qr {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hG : Good2 M) (hb1 : 0 < entry M 1 (M.length - 1))
    (hr1 : TRIO.r1ok M) (hz0 : TRIO.z0ok M) (hRD : RootsDec M) (h00 : entry M 0 0 = 0)
    (hqr : par M 0 (M.length - 1) = some r)
    (hPRE : ∀ h p s y, Anc0 M p (M.length - 1) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
      bst M h p ≠ z → ∃ rest, y = app (bst M h p) rest ∧ rest ≠ z) {n : Nat} (hn : 2 ≤ n) :
    isOT (ev2r (expand M n)) = true ∧ ev2r (expand M n) < ev2r M := by
  apply ev2r_expand_t1 hM hz hr (by omega) hn hG hRD hz0 h00
  intro h hh
  obtain ⟨j, hj, hjot, hjlt⟩ := twoRow_qr_PRE hM hz hr ht1 hG hb1 hr1 hz0 hqr hPRE n hn h hh
  rw [hj]; exact ⟨hjot, hjlt⟩

end Ytosk
