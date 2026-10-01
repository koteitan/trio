/-
**3 行・t = 1: 写しの根と、写しの列の topped・上げられる。**

- `par1_root`: 写しの根 x の P_1 は M の r の P_1。
- `upg_root`: 写しの根の上げは P の r の上げ（行 2 ≤ 1 のとき）。どちらも行き先は r より前。
- `topped_copy`・`isUpg_copy`: 写しの列（0 < a）の topped・上げられるは P の r + a のもの。
-/
import Ytosk.V3Copy3
import Ytosk.TwoRowI3

namespace Ytosk

/-- An upgrade target is at most the next column. -/
theorem upg_le {M : Mat} {k t : Nat} (h : upg M k = some t) : t ≤ k + 1 := by
  unfold upg at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only at h
      split at h
      · cases h; exact Nat.le_refl _
      · rename_i m _ _
        rw [upgClimb_find] at h
        have := mem_ancL_lt (List.mem_of_find?_eq_some h)
        omega

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

theorem e1_root : entry (TRIO.gexp M r L d0 0 n) 1 (r + L) = entry M 1 r := by
  have h0 : 0 < (n - 1) * L := Nat.mul_pos (by omega) hL
  have := e1_gexp_shift (M := M) (r := r) (L := L) (d0 := d0) (n := n) (a := 0) hlen hL hn h0
  rw [show r + L + 0 = r + L by omega, show r + 0 = r by omega] at this
  rw [this, e1_gexp_pre (m := n - 1) hlen (by omega) (by omega)]

/-- **P_1 of the copy root.** -/
theorem par1_root (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) :
    par (TRIO.gexp M r L d0 0 n) 1 (r + L) = par M 1 r := by
  obtain ⟨S0, hS0, hS0p⟩ := ancL_through hA (by omega)
  rw [par1_find, par1_find M r, ancL_N_pre hlen hL hA hd0e hn (Nat.le_refl _), hS0,
    e1_root hlen hL hA hd0e hn]
  simp only [List.find?_append, List.find?_cons]
  have h1 : S0.find? (fun q => decide (entry (TRIO.gexp M r L d0 0 n) 1 q < entry M 1 r)) = none := by
    rw [List.find?_eq_none]
    intro s hs
    obtain ⟨h1, h2, h3, h4⟩ := hS0p s hs
    have := hpath s h3 h4 (by omega) (by omega)
    rw [e1_gexp_pre (m := n) hlen (by omega) (by omega)]; simp; omega
  have h2 : entry (TRIO.gexp M r L d0 0 n) 1 r = entry M 1 r := e1_gexp_pre (m := n) hlen (by omega) (by omega)
  have h3 : (ancL M r).find? (fun q => decide (entry (TRIO.gexp M r L d0 0 n) 1 q < entry M 1 r)) =
      (ancL M r).find? (fun q => decide (entry M 1 q < entry M 1 r)) := by
    apply find?_congr'
    intro q hq
    have := mem_ancL_lt hq
    rw [e1_gexp_pre (m := n) hlen (by omega) (by omega)]
  rw [h1, h2, h3]
  simp

/-- **Topped is preserved by the shift.** -/
theorem topped_copy {a : Nat} (ha : a < (n - 1) * L) :
    topped (TRIO.gexp M r L d0 0 n) (r + L + a) = topped (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by
  have hlP := len_P (d0 := d0) (n := n) hlen
  unfold topped
  rw [children_shift hlen hL hA hd0e hn ha, List.getLast?_map]
  cases hc : (children (TRIO.gexp M r L d0 0 (n - 1)) (r + a)).getLast? with
  | none => rfl
  | some c =>
    simp only [Option.map_some]
    have hcm := List.mem_of_getLast? hc
    have hcc := mem_children hcm
    rw [hlP] at hcc
    have hca : c - r < (n - 1) * L := by omega
    rw [show c + L = r + L + (c - r) by omega, col_copy (d0 := d0) hlen hL hn hca,
      show r + (c - r) = c by omega]
    unfold bump
    rw [e0_copy (d0 := d0) hlen hL hn ha, e1_gexp_shift hlen hL hn ha, col_eq_entries]
    simp only [Prod.mk.injEq, decide_eq_decide]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩

/-- **Upgrade of the copy root** (row 2 at `r` is at most `1`). -/
theorem upg_root (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hz2 : entry M 2 r ≤ 1) :
    upg (TRIO.gexp M r L d0 0 n) (r + L) = upg (TRIO.gexp M r L d0 0 (n - 1)) r := by
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have h0 : 0 < (n - 1) * L := Nat.mul_pos (by omega) hL
  have he1 : entry (TRIO.gexp M r L d0 0 n) 1 (r + L) = entry (TRIO.gexp M r L d0 0 (n - 1)) 1 r := by
    rw [e1_root hlen hL hA hd0e hn, e1_gexp_pre (m := n - 1) hlen (by omega) (by omega)]
  have he2 : entry (TRIO.gexp M r L d0 0 n) 2 (r + L) = entry (TRIO.gexp M r L d0 0 (n - 1)) 2 r := by
    have := e2_copy (d0 := d0) (a := 0) hlen hL hn h0
    simpa using this
  have hp1 : par (TRIO.gexp M r L d0 0 n) 1 (r + L) = par (TRIO.gexp M r L d0 0 (n - 1)) 1 r := by
    rw [par1_root hlen hL hA hd0e hn hpath, par_gexp_pre hlen (by omega) 1 (by omega)]
  unfold upg
  rw [he1, he2, hp1]
  by_cases hc : entry (TRIO.gexp M r L d0 0 (n - 1)) 1 r = 0 ∨
      entry (TRIO.gexp M r L d0 0 (n - 1)) 2 r = 1 ∨ r + 1 = (TRIO.gexp M r L d0 0 (n - 1)).length
  · have hc' : entry (TRIO.gexp M r L d0 0 (n - 1)) 1 r = 0 ∨
        entry (TRIO.gexp M r L d0 0 (n - 1)) 2 r = 1 ∨
        r + L + 1 = (TRIO.gexp M r L d0 0 n).length := by
      rcases hc with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by omega))
    rw [if_pos hc', if_pos hc]
  · have hc' : ¬ (entry (TRIO.gexp M r L d0 0 (n - 1)) 1 r = 0 ∨
        entry (TRIO.gexp M r L d0 0 (n - 1)) 2 r = 1 ∨
        r + L + 1 = (TRIO.gexp M r L d0 0 n).length) := by
      intro h; apply hc
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by omega))
    rw [if_neg hc', if_neg hc]
    have h1L : 1 < (n - 1) * L := by
      have : r + 1 ≠ r + (n - 1) * L := fun h => hc (Or.inr (Or.inr (by omega)))
      omega
    cases hm : par (TRIO.gexp M r L d0 0 (n - 1)) 1 r with
    | none => rfl
    | some m =>
      simp only
      have hmr : m < r := par_lt _ 1 r m hm
      have hem : ∀ y, entry (TRIO.gexp M r L d0 0 n) y m = entry (TRIO.gexp M r L d0 0 (n - 1)) y m := by
        intro y
        rw [entry_gexp_pre hlen (by omega) y (by omega), entry_gexp_pre hlen (by omega) y (by omega)]
      rw [hem 0, hem 2]
      have hno : ∀ (G : Mat) (c : Nat) (Lc : Nat × Nat × Nat), Lc.1 = entry G 0 m + 1 →
          par G 0 c ≠ some m → ¬ (par G 1 c = some m ∧ col G c = Lc) := by
        intro G c Lc hLc hc ⟨h1, h2⟩
        apply hc
        apply par0_of_upgshape h1
        have : entry G 0 c = (col G c).1 := rfl
        rw [this, h2, hLc]
      rw [if_neg (hno (TRIO.gexp M r L d0 0 n) (r + L + 1) _ (by simp [hem 0])
          (copyN_not_child hlen hL hA hd0e hn (by omega) (by omega) hmr)),
        if_neg (hno (TRIO.gexp M r L d0 0 (n - 1)) (r + 1) _ rfl
          (copyP_not_child hlen hL hA hd0e hn (by omega) (by omega) hmr)),
        upgClimb_find, upgClimb_find, upgFind_child _ _ m _ (by simp [hem 0]),
        upgFind_child _ _ m _ rfl, ancL_N_pre hlen hL hA hd0e hn (Nat.le_refl _),
        ancL_P_pre hlen hL hd0e hn (by omega)]
      obtain ⟨S0, hS0, hS0p⟩ := ancL_through hA (by omega)
      rw [hS0]
      have hS0f : S0.find? (fun q => decide (par (TRIO.gexp M r L d0 0 n) 0 q = some m)) = none := by
        rw [List.find?_eq_none]
        intro s hs
        obtain ⟨hs1, hs2, hs3, hs4⟩ := hS0p s hs
        simp only [decide_eq_true_eq]
        rw [par_gexp_pre hlen (by omega) 0 (by omega)]
        intro h
        have := par0_ge_of_anc hA hs1 (by omega) h
        omega
      have hlow : (ancL M r).find? (fun q => decide (par (TRIO.gexp M r L d0 0 n) 0 q = some m)) =
          (ancL M r).find? (fun q => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 q = some m)) := by
        apply find?_congr'
        intro q hq
        have := mem_ancL_lt hq
        rw [par_gexp_pre hlen (by omega) 0 (by omega), par_gexp_pre hlen (by omega) 0 (by omega)]
      simp only [List.find?_append, List.find?_cons, hS0f, Option.none_or]
      by_cases hrm : par (TRIO.gexp M r L d0 0 n) 0 r = some m
      · -- the child of `m` is `r`, whose row 2 is not `e2 m + 1`
        rw [show decide (par (TRIO.gexp M r L d0 0 n) 0 r = some m) = true from decide_eq_true hrm]
        dsimp only
        have hr2 : entry (TRIO.gexp M r L d0 0 (n - 1)) 2 r = 0 := by
          have h1 : entry (TRIO.gexp M r L d0 0 (n - 1)) 2 r ≠ 1 := fun h => hc (Or.inr (Or.inl h))
          rw [entry_gexp_pre hlen (by omega) 2 (by omega)] at h1 ⊢
          omega
        have hnone : (ancL M r).find? (fun q => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 q = some m)) = none := by
          rw [List.find?_eq_none]
          intro q hq
          have hqr := mem_ancL_lt hq
          simp only [decide_eq_true_eq]
          rw [par_gexp_pre hlen (by omega) 0 (by omega)]
          rw [par_gexp_pre hlen (by omega) 0 (by omega)] at hrm
          intro h
          have hAq := anc0_of_mem_ancL hq
          -- `m` is the parent of `r`, and `q` is a proper ancestor of `r`, so `q ≤ m`
          have := anc0_par hAq (by omega) hrm
          have := this.le
          have := par_lt M 0 q m h
          omega
        rw [hnone]
        simp only [Option.filter_some]
        rw [if_neg]
        · rfl
        · simp only [decide_eq_true_eq, not_and]
          intro _ hcol
          have : (col (TRIO.gexp M r L d0 0 n) r).2.2 = entry (TRIO.gexp M r L d0 0 (n - 1)) 2 m + 1 := by
            rw [hcol]
          rw [col_gexp_pre hlen (by omega) (by omega)] at this
          rw [entry_gexp_pre hlen (by omega) 2 (by omega)] at hr2
          have h2 : (col M r).2.2 = entry M 2 r := rfl
          omega
      · rw [show decide (par (TRIO.gexp M r L d0 0 n) 0 r = some m) = false from decide_eq_false hrm]
        dsimp only
        rw [hlow]
        cases hco : (ancL M r).find? (fun q => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 q = some m)) with
        | none => rfl
        | some c =>
          have hcr := mem_ancL_lt (List.mem_of_find?_eq_some hco)
          have hAc := anc0_of_mem_ancL (List.mem_of_find?_eq_some hco)
          obtain ⟨S1, hSP1, -, -⟩ := ancL_copy hlen hL hA hd0e hn 1 (by omega) h1L
          have hrA : Anc0 (TRIO.gexp M r L d0 0 (n - 1)) r (r + 1) := anc0_of_mem_ancL (by rw [hSP1]; simp)
          have hrlt := anc0_interval hrA (r + 1) (by omega) (Nat.le_refl _)
          have hclt := anc0_interval hAc r hcr (Nat.le_refl _)
          have he0b : entry (TRIO.gexp M r L d0 0 n) 0 (r + L + 1) =
              entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + 1) + d0 := e0_copy (d0 := d0) hlen hL hn h1L
          have hP0 : entry (TRIO.gexp M r L d0 0 (n - 1)) 0 r = entry M 0 r :=
            entry_gexp_pre hlen (by omega) 0 (by omega)
          simp only [Option.filter_some]
          rw [par_gexp_pre (m := n) hlen (by omega) 1 (by omega),
            par_gexp_pre (m := n - 1) hlen (by omega) 1 (by omega),
            col_gexp_pre (m := n) hlen (by omega) (by omega), col_gexp_pre (m := n - 1) hlen (by omega) (by omega),
            entry_gexp_pre (m := n) hlen (by omega) 0 (by omega),
            entry_gexp_pre (m := n - 1) hlen (by omega) 0 (by omega), he0b]
          have hlt1 : entry M 0 c < entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + 1) := by omega
          have hlt2 : entry M 0 c < entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + 1) + d0 := by omega
          rw [entry_gexp_pre (m := n - 1) (i := c) hlen (by omega) 0 (by omega)]
          simp only [hlt1, hlt2, and_true]

/-- The upgrade of `r` in `P` is before `r`. -/
theorem upgP_root_lt {t : Nat} (h : upg (TRIO.gexp M r L d0 0 (n - 1)) r = some t) : t < r := by
  have hlP := len_P (d0 := d0) (n := n) hlen
  unfold upg at h
  split at h
  · cases h
  · rename_i hc
    split at h
    · cases h
    · rename_i m hm
      simp only at h
      have hmr : m < r := par_lt _ 1 r m hm
      have hr1 : r + 1 < r + (n - 1) * L := by
        have : r + 1 ≠ (TRIO.gexp M r L d0 0 (n - 1)).length := fun h' => hc (Or.inr (Or.inr h'))
        have h0 : 0 < (n - 1) * L := Nat.mul_pos (by omega) hL
        omega
      split at h
      · rename_i hcl
        exfalso
        apply copyP_not_child hlen hL hA hd0e hn (c := r + 1) (by omega) hr1 hmr
        apply par0_of_upgshape hcl.1
        have : entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + 1) =
            (col (TRIO.gexp M r L d0 0 (n - 1)) (r + 1)).1 := rfl
        rw [this, hcl.2]
      · rw [upgClimb_find] at h
        exact mem_ancL_lt (List.mem_of_find?_eq_some h)

/-- **Being an upgrade target is preserved by the shift** (copy columns after the root). -/
theorem isUpg_copy (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hz2 : entry M 2 r ≤ 1) {a : Nat} (ha0 : 0 < a)
    (ha : a < (n - 1) * L) :
    isUpg (TRIO.gexp M r L d0 0 n) (r + L + a) = isUpg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  unfold isUpg
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨k, hk, hkk⟩
    have hk' := List.mem_range.mp hk
    have hu : upg (TRIO.gexp M r L d0 0 n) k = some (r + L + a) := of_decide_eq_true hkk
    have hle := upg_le hu
    rcases Nat.lt_or_ge k (r + L) with hlt | hge
    · omega
    rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · subst heq
      rw [upg_root hlen hL hA hd0e hn hpath hz2] at hu
      have := upgP_root_lt hlen hL hA hd0e hn hu
      omega
    · rw [show k = r + L + (k - (r + L)) by omega,
        upg_copy hlen hL hA hd0e hn hpath (by omega) (by omega)] at hu
      cases hup : upg (TRIO.gexp M r L d0 0 (n - 1)) (r + (k - (r + L))) with
      | none => rw [hup] at hu; cases hu
      | some t =>
        rw [hup] at hu
        simp only [Option.map_some, Option.some.injEq] at hu
        split at hu
        · refine ⟨r + (k - (r + L)), List.mem_range.mpr (by omega), ?_⟩
          rw [hup]; simp; omega
        · omega
  · rintro ⟨k, hk, hkk⟩
    have hk' := List.mem_range.mp hk
    have hu : upg (TRIO.gexp M r L d0 0 (n - 1)) k = some (r + a) := of_decide_eq_true hkk
    have hle := upg_le hu
    rcases Nat.lt_or_ge k r with hlt | hge
    · omega
    rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · subst heq
      have := upgP_root_lt hlen hL hA hd0e hn hu
      omega
    · refine ⟨r + L + (k - r), List.mem_range.mpr (by omega), ?_⟩
      rw [upg_copy hlen hL hA hd0e hn hpath (by omega) (by omega), show r + (k - r) = k by omega, hu]
      simp only [Option.map_some, decide_eq_true_eq, Option.some.injEq]
      rw [if_pos (by omega)]; omega

end

end Ytosk
