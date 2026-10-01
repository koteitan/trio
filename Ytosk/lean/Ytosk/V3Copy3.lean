/-
**3 行・t = 1: 写しの列の値のずれと上げの対応。**

写しの列 x + a の列は P の r + a の列の行 0 を d0 上げたもの（`col_copy`）。上げは
`upg_copy`: upg_N(x + j) = upg_P(r + j) を「r より後ろなら L ずらす」もの（0 < j）。
-/
import Ytosk.V3Copy2

namespace Ytosk

theorem map_phi1_eq {m L r : Nat} (hmr : r ≤ m) :
    ∀ o : Option Nat, o.map (fun p => if r ≤ p then p + L else p) = some (m + L) ↔ o = some m
  | none => by simp
  | some p => by
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · intro h
      split at h
      · omega
      · omega
    · intro h; subst h; simp [hmr]

theorem map_phi1_eq_lt {m L r : Nat} (hmr : m < r) :
    ∀ o : Option Nat, o.map (fun p => if r ≤ p then p + L else p) = some m ↔ o = some m
  | none => by simp
  | some p => by
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · intro h
      split at h
      · omega
      · exact h
    · intro h; subst h; simp; omega

theorem col_eq_entries (M : Mat) (i : Nat) : col M i = (entry M 0 i, entry M 1 i, entry M 2 i) := rfl

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

omit hA hd0e in
/-- **A copy column is the shifted column of `P`.** -/
theorem col_copy {a : Nat} (ha : a < (n - 1) * L) :
    col (TRIO.gexp M r L d0 0 n) (r + L + a) =
      (entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + a) + d0,
       entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a),
       entry (TRIO.gexp M r L d0 0 (n - 1)) 2 (r + a)) := by
  obtain ⟨k, qb, hk, hqb, hak⟩ := TRIO.gexp_pos_decomp (j0 := 0) (n := n - 1) (p := a) hL
    (Nat.zero_le _) (by simpa using ha)
  simp only [Nat.zero_add] at hak
  subst hak
  have hN := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := 0) (n := n)
    (k := k + 1) (q := qb) hlen (by omega) hqb
  have hP := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := 0) (n := n - 1)
    (k := k) (q := qb) hlen hk hqb
  unfold col entry
  rw [show r + L + (k * L + qb) = r + ((k + 1) * L + qb) by rw [Nat.succ_mul]; omega, hN, hP]
  simp [TRIO.entry, Nat.succ_mul]
  omega

omit hA hd0e in
theorem e0_copy {a : Nat} (ha : a < (n - 1) * L) :
    entry (TRIO.gexp M r L d0 0 n) 0 (r + L + a) = entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + a) + d0 := by
  have := col_copy (d0 := d0) hlen hL hn ha
  have h : entry (TRIO.gexp M r L d0 0 n) 0 (r + L + a) = (col (TRIO.gexp M r L d0 0 n) (r + L + a)).1 := rfl
  rw [h, this]

omit hA hd0e in
theorem e2_copy {a : Nat} (ha : a < (n - 1) * L) :
    entry (TRIO.gexp M r L d0 0 n) 2 (r + L + a) = entry (TRIO.gexp M r L d0 0 (n - 1)) 2 (r + a) := by
  have := col_copy (d0 := d0) hlen hL hn ha
  have h : entry (TRIO.gexp M r L d0 0 n) 2 (r + L + a) = (col (TRIO.gexp M r L d0 0 n) (r + L + a)).2.2 := by
    unfold entry col; rfl
  rw [h, this]

omit hL hA hd0e in
theorem len_N : (TRIO.gexp M r L d0 0 n).length = r + L + (n - 1) * L := by
  rw [TRIO.gexp_length hlen]
  have : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
  omega

omit hL hA hd0e hn in
theorem len_P : (TRIO.gexp M r L d0 0 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen

/-- A copy column of `P` (after `r`) is not a row-0 child of a column before `r`. -/
theorem copyP_not_child {c m : Nat} (hc0 : r < c) (hc : c < r + (n - 1) * L) (hm : m < r) :
    par (TRIO.gexp M r L d0 0 (n - 1)) 0 c ≠ some m := by
  obtain ⟨p, hp, hrp⟩ := parP_ge hlen hL hA hd0e hn (j := c - r) (by omega) (by omega)
  rw [show r + (c - r) = c by omega] at hp
  rw [hp]; intro h; cases h; omega

/-- A copy column of `N` (at or after `x`) is not a row-0 child of a column before `r`. -/
theorem copyN_not_child {c m : Nat} (hc0 : r + L ≤ c) (hc : c < r + L + (n - 1) * L) (hm : m < r) :
    par (TRIO.gexp M r L d0 0 n) 0 c ≠ some m := by
  rcases Nat.eq_or_lt_of_le hc0 with heq | hlt
  · subst heq
    obtain ⟨q, hq⟩ := par0_some_of (show r < r + L by omega)
      (anc0_interval hA (r + L) (by omega) (Nat.le_refl _))
    have hrq : r ≤ q := par0_ge_of_anc hA (by omega) (Nat.le_refl _) hq
    have hqx := par_lt M 0 _ _ hq
    have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [hq]; congr 1; omega
    have hroot := par0_gexp_root (d1 := 0) (n := n) hlen (k := 1) (by omega) (Nat.le_refl _)
      (by omega) hd0e hq'
    rw [show r + (1 * L + 0) = r + L by omega] at hroot
    rw [hroot]; intro h; cases h; omega
  · obtain ⟨p, hp, hpx⟩ := par0_gexp_ge (d1 := 0) (n := n) hlen hL hA hd0e (c := c) hlt
      (by rw [show r + n * L = r + L + (n - 1) * L by
            have : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
            omega]; exact hc)
    rw [hp]; intro h; cases h; omega

/-- The child of a copy column `m` (`r ≤ m`) on the path, shifted. -/
theorem childOn_shift {j m : Nat} (hj0 : 0 < j) (hj : j < (n - 1) * L) (hmr : r ≤ m) :
    (ancL (TRIO.gexp M r L d0 0 n) (r + L + j)).find?
        (fun q => decide (par (TRIO.gexp M r L d0 0 n) 0 q = some (m + L))) =
      ((ancL (TRIO.gexp M r L d0 0 (n - 1)) (r + j)).find?
        (fun q => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 q = some m))).map (· + L) := by
  obtain ⟨S, hSP, hSN, hS⟩ := ancL_copy hlen hL hA hd0e hn j hj0 hj
  rw [hSP, hSN]
  simp only [List.find?_append, List.find?_map]
  have hfS : S.find? ((fun q => decide (par (TRIO.gexp M r L d0 0 n) 0 q = some (m + L))) ∘ (· + L)) =
      S.find? (fun q => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 q = some m)) := by
    apply find?_congr'
    intro s hs
    have := hS s hs
    have hps : par (TRIO.gexp M r L d0 0 n) 0 (s + L) =
        (par (TRIO.gexp M r L d0 0 (n - 1)) 0 s).map (· + L) := by
      rw [show s + L = r + L + (s - r) by omega, par0_gexp_shift hlen hL hA hd0e hn (by omega) (by omega),
        show r + (s - r) = s by omega]
    simp only [Function.comp]
    rw [decide_eq_decide, hps]
    cases par (TRIO.gexp M r L d0 0 (n - 1)) 0 s with
    | none => simp
    | some p => simp
  rw [hfS]
  -- both tails fail
  have htN : ((r + L) :: ancL M (r + L)).find?
      (fun q => decide (par (TRIO.gexp M r L d0 0 n) 0 q = some (m + L))) = none := by
    rw [List.find?_eq_none]
    intro y hy
    have hyx : y ≤ r + L := by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (mem_ancL_lt hy)
    simp only [decide_eq_true_eq]
    intro h
    have := par_lt _ 0 _ _ h
    omega
  have htP : (r :: ancL M r).find?
      (fun q => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 q = some m)) = none := by
    rw [List.find?_eq_none]
    intro y hy
    have hyr : y ≤ r := by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (mem_ancL_lt hy)
    simp only [decide_eq_true_eq]
    intro h
    have := par_lt _ 0 _ _ h
    omega
  rw [htN, htP]
  cases S.find? (fun q => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 q = some m)) <;> rfl

/-- The child of a column `m < r` on the path is the same column in `N` and `P`. -/
theorem childOn_same {j m : Nat} (hj0 : 0 < j) (hj : j < (n - 1) * L) (hmr : m < r) :
    (ancL (TRIO.gexp M r L d0 0 n) (r + L + j)).find?
        (fun q => decide (par (TRIO.gexp M r L d0 0 n) 0 q = some m)) =
      (ancL (TRIO.gexp M r L d0 0 (n - 1)) (r + j)).find?
        (fun q => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 q = some m)) := by
  have hlN := len_N (d0 := d0) hlen hn
  obtain ⟨S, hSP, hSN, hS⟩ := ancL_copy hlen hL hA hd0e hn j hj0 hj
  obtain ⟨S0, hS0, hS0p⟩ := ancL_through hA (by omega)
  rw [hSP, hSN, hS0]
  simp only [List.find?_append, List.find?_map]
  have h1 : S.find? ((fun q => decide (par (TRIO.gexp M r L d0 0 n) 0 q = some m)) ∘ (· + L)) = none := by
    rw [List.find?_eq_none]
    intro s hs
    have := hS s hs
    simp only [Function.comp, decide_eq_true_eq]
    exact copyN_not_child hlen hL hA hd0e hn (c := s + L) (by omega) (by omega) hmr
  have h2 : S.find? (fun q => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 q = some m)) = none := by
    rw [List.find?_eq_none]
    intro s hs
    have := hS s hs
    simp only [decide_eq_true_eq]
    exact copyP_not_child hlen hL hA hd0e hn (by omega) (by omega) hmr
  have h3 : ¬ (par (TRIO.gexp M r L d0 0 n) 0 (r + L) = some m) :=
    copyN_not_child hlen hL hA hd0e hn (c := r + L) (Nat.le_refl _) (by omega) hmr
  have h4 : S0.find? (fun q => decide (par (TRIO.gexp M r L d0 0 n) 0 q = some m)) = none := by
    rw [List.find?_eq_none]
    intro s hs
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hS0p s hs
    simp only [decide_eq_true_eq]
    rw [par_gexp_pre hlen (by omega) 0 (by omega)]
    intro h
    have := par0_ge_of_anc hA hs1 (by omega) h
    omega
  have h5 : (r :: ancL M r).find? (fun q => decide (par (TRIO.gexp M r L d0 0 n) 0 q = some m)) =
      (r :: ancL M r).find? (fun q => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 q = some m)) := by
    apply find?_congr'
    intro y hy
    have hyr : y ≤ r := by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (mem_ancL_lt hy)
    rw [par_gexp_pre hlen (by omega) 0 (by omega), par_gexp_pre hlen (by omega) 0 (by omega)]
  rw [h1, h2]
  simp only [Option.map_none, Option.none_or, List.find?_cons, h3, decide_false,
    List.find?_append, h4]
  simp only [List.find?_cons] at h5
  exact h5

/-- **Upgrades of copy columns.** -/
theorem upg_copy (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s)
    {j : Nat} (hj0 : 0 < j) (hj : j < (n - 1) * L) :
    upg (TRIO.gexp M r L d0 0 n) (r + L + j) =
      (upg (TRIO.gexp M r L d0 0 (n - 1)) (r + j)).map (fun t => if r < t then t + L else t) := by
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have he1 : entry (TRIO.gexp M r L d0 0 n) 1 (r + L + j) =
      entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j) := e1_gexp_shift hlen hL hn (by omega)
  have he2 := e2_copy (d0 := d0) hlen hL hn (show j < (n - 1) * L from hj)
  unfold upg
  rw [he1, he2]
  by_cases hc : entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j) = 0 ∨
      entry (TRIO.gexp M r L d0 0 (n - 1)) 2 (r + j) = 1 ∨
      r + j + 1 = (TRIO.gexp M r L d0 0 (n - 1)).length
  · have hc' : entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j) = 0 ∨
        entry (TRIO.gexp M r L d0 0 (n - 1)) 2 (r + j) = 1 ∨
        r + L + j + 1 = (TRIO.gexp M r L d0 0 n).length := by
      rcases hc with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by omega))
    rw [if_pos hc', if_pos hc]; rfl
  · have hc' : ¬ (entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j) = 0 ∨
        entry (TRIO.gexp M r L d0 0 (n - 1)) 2 (r + j) = 1 ∨
        r + L + j + 1 = (TRIO.gexp M r L d0 0 n).length) := by
      intro h; apply hc
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by omega))
    rw [if_neg hc', if_neg hc]
    have hj1 : j + 1 < (n - 1) * L := by
      have : r + j + 1 ≠ r + (n - 1) * L := fun h => hc (Or.inr (Or.inr (by omega)))
      omega
    rw [par1_copy hlen hL hA hd0e hn hpath hj0 hj]
    cases hm : par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j) with
    | none => rfl
    | some m =>
      simp only [Option.map_some]
      have hmlt : m < r + j := par_lt _ 1 _ _ hm
      have hp1 := par1_copy hlen hL hA hd0e hn hpath (j := j + 1) (by omega) hj1
      have hcol1 := col_copy (d0 := d0) hlen hL hn (a := j + 1) hj1
      rw [upgClimb_find, upgClimb_find,
        show r + L + j + 1 = r + L + (j + 1) by omega, show r + j + 1 = r + (j + 1) by omega]
      by_cases hmr : r ≤ m
      · rw [if_pos hmr]
        have hma : m - r < (n - 1) * L := by omega
        have hem0 : entry (TRIO.gexp M r L d0 0 n) 0 (m + L) =
            entry (TRIO.gexp M r L d0 0 (n - 1)) 0 m + d0 := by
          rw [show m + L = r + L + (m - r) by omega, e0_copy (d0 := d0) hlen hL hn hma,
            show r + (m - r) = m by omega]
        have hem2 : entry (TRIO.gexp M r L d0 0 n) 2 (m + L) =
            entry (TRIO.gexp M r L d0 0 (n - 1)) 2 m := by
          rw [show m + L = r + L + (m - r) by omega, e2_copy (d0 := d0) hlen hL hn hma,
            show r + (m - r) = m by omega]
        have he0b : entry (TRIO.gexp M r L d0 0 n) 0 (r + L + (j + 1)) =
            entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + (j + 1)) + d0 := e0_copy (d0 := d0) hlen hL hn hj1
        have hcond : (par (TRIO.gexp M r L d0 0 n) 1 (r + L + (j + 1)) = some (m + L) ∧
              col (TRIO.gexp M r L d0 0 n) (r + L + (j + 1)) =
                (entry (TRIO.gexp M r L d0 0 n) 0 (m + L) + 1, entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j),
                  entry (TRIO.gexp M r L d0 0 n) 2 (m + L) + 1)) ↔
            (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + (j + 1)) = some m ∧
              col (TRIO.gexp M r L d0 0 (n - 1)) (r + (j + 1)) =
                (entry (TRIO.gexp M r L d0 0 (n - 1)) 0 m + 1, entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j),
                  entry (TRIO.gexp M r L d0 0 (n - 1)) 2 m + 1)) := by
          rw [hp1, hcol1, hem0, hem2, map_phi1_eq hmr, col_eq_entries (TRIO.gexp M r L d0 0 (n - 1))]
          simp only [Prod.mk.injEq]
          constructor
          · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, by omega, h3, h4⟩
          · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, by omega, h3, h4⟩
        by_cases hP1 : par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + (j + 1)) = some m ∧
            col (TRIO.gexp M r L d0 0 (n - 1)) (r + (j + 1)) =
              (entry (TRIO.gexp M r L d0 0 (n - 1)) 0 m + 1, entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j),
                entry (TRIO.gexp M r L d0 0 (n - 1)) 2 m + 1)
        · rw [if_pos (hcond.mpr hP1), if_pos hP1]
          simp only [Option.map_some, Option.some.injEq]
          rw [if_pos (by omega)]; omega
        · rw [if_neg (fun h => hP1 (hcond.mp h)), if_neg hP1,
            upgFind_child _ _ (m + L) _ rfl, upgFind_child _ _ m _ rfl,
            childOn_shift hlen hL hA hd0e hn hj0 hj hmr]
          cases hco : (ancL (TRIO.gexp M r L d0 0 (n - 1)) (r + j)).find?
              (fun q => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 q = some m)) with
          | none => rfl
          | some c =>
            have hcmem := List.mem_of_find?_eq_some hco
            have hcpar : par (TRIO.gexp M r L d0 0 (n - 1)) 0 c = some m := by
              have := List.find?_some hco; simpa using this
            have hcm : m < c := par_lt _ 0 c m hcpar
            have hcj : c < r + j := mem_ancL_lt hcmem
            have hca : c - r < (n - 1) * L := by omega
            have hpc : par (TRIO.gexp M r L d0 0 n) 1 (c + L) =
                (par (TRIO.gexp M r L d0 0 (n - 1)) 1 c).map (fun p => if r ≤ p then p + L else p) := by
              rw [show c + L = r + L + (c - r) by omega,
                par1_copy hlen hL hA hd0e hn hpath (by omega) hca, show r + (c - r) = c by omega]
            have hcc : col (TRIO.gexp M r L d0 0 n) (c + L) =
                (entry (TRIO.gexp M r L d0 0 (n - 1)) 0 c + d0, entry (TRIO.gexp M r L d0 0 (n - 1)) 1 c,
                  entry (TRIO.gexp M r L d0 0 (n - 1)) 2 c) := by
              rw [show c + L = r + L + (c - r) by omega, col_copy (d0 := d0) hlen hL hn hca,
                show r + (c - r) = c by omega]
            have he0c : entry (TRIO.gexp M r L d0 0 n) 0 (c + L) =
                entry (TRIO.gexp M r L d0 0 (n - 1)) 0 c + d0 := by
              rw [show c + L = r + L + (c - r) by omega, e0_copy (d0 := d0) hlen hL hn hca,
                show r + (c - r) = c by omega]
            have hok : (par (TRIO.gexp M r L d0 0 n) 1 (c + L) = some (m + L) ∧
                  col (TRIO.gexp M r L d0 0 n) (c + L) =
                    (entry (TRIO.gexp M r L d0 0 n) 0 (m + L) + 1,
                      entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j),
                      entry (TRIO.gexp M r L d0 0 n) 2 (m + L) + 1) ∧
                  entry (TRIO.gexp M r L d0 0 n) 0 (c + L) <
                    entry (TRIO.gexp M r L d0 0 n) 0 (r + L + (j + 1))) ↔
                (par (TRIO.gexp M r L d0 0 (n - 1)) 1 c = some m ∧
                  col (TRIO.gexp M r L d0 0 (n - 1)) c =
                    (entry (TRIO.gexp M r L d0 0 (n - 1)) 0 m + 1,
                      entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j),
                      entry (TRIO.gexp M r L d0 0 (n - 1)) 2 m + 1) ∧
                  entry (TRIO.gexp M r L d0 0 (n - 1)) 0 c <
                    entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + (j + 1))) := by
              rw [hpc, hcc, he0c, he0b, hem0, hem2, map_phi1_eq hmr,
                col_eq_entries (TRIO.gexp M r L d0 0 (n - 1)) c]
              simp only [Prod.mk.injEq]
              constructor
              · rintro ⟨h1, ⟨h2, h3, h4⟩, h5⟩; exact ⟨h1, ⟨by omega, h3, h4⟩, by omega⟩
              · rintro ⟨h1, ⟨h2, h3, h4⟩, h5⟩; exact ⟨h1, ⟨by omega, h3, h4⟩, by omega⟩
            simp only [Option.map_some, Option.filter_some]
            by_cases hP : par (TRIO.gexp M r L d0 0 (n - 1)) 1 c = some m ∧
                col (TRIO.gexp M r L d0 0 (n - 1)) c =
                  (entry (TRIO.gexp M r L d0 0 (n - 1)) 0 m + 1,
                    entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j),
                    entry (TRIO.gexp M r L d0 0 (n - 1)) 2 m + 1) ∧
                entry (TRIO.gexp M r L d0 0 (n - 1)) 0 c <
                  entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + (j + 1))
            · rw [if_pos (decide_eq_true (hok.mpr hP)), if_pos (decide_eq_true hP)]
              simp only [Option.map_some, Option.some.injEq]
              rw [if_pos (by omega)]
            · rw [if_neg (fun h => hP (hok.mp (of_decide_eq_true h))),
                if_neg (fun h => hP (of_decide_eq_true h))]
              rfl
      · rw [if_neg hmr]
        have hmlt' : m < r := by omega
        have hem : ∀ y, entry (TRIO.gexp M r L d0 0 n) y m = entry (TRIO.gexp M r L d0 0 (n - 1)) y m := by
          intro y
          rw [entry_gexp_pre hlen (by omega) y (by omega), entry_gexp_pre hlen (by omega) y (by omega)]
        rw [hem 0, hem 2]
        -- the `i + 1` clause fails in both
        have hno : ∀ (G : Mat) (c : Nat) (Lc : Nat × Nat × Nat), Lc.1 = entry G 0 m + 1 →
            par G 0 c ≠ some m → ¬ (par G 1 c = some m ∧ col G c = Lc) := by
          intro G c Lc hLc hc ⟨h1, h2⟩
          apply hc
          apply par0_of_upgshape h1
          have : entry G 0 c = (col G c).1 := rfl
          rw [this, h2, hLc]
        rw [if_neg (hno (TRIO.gexp M r L d0 0 n) (r + L + (j + 1)) _ (by simp [hem 0])
            (copyN_not_child hlen hL hA hd0e hn (by omega) (by omega) hmlt')),
          if_neg (hno (TRIO.gexp M r L d0 0 (n - 1)) (r + (j + 1)) _ rfl
            (copyP_not_child hlen hL hA hd0e hn (by omega) (by omega) hmlt'))]
        rw [upgFind_child _ _ m _ (by simp [hem 0]), upgFind_child _ _ m _ rfl,
          childOn_same hlen hL hA hd0e hn hj0 hj hmlt']
        cases hco : (ancL (TRIO.gexp M r L d0 0 (n - 1)) (r + j)).find?
            (fun q => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 q = some m)) with
        | none => rfl
        | some c =>
          have hcmem := List.mem_of_find?_eq_some hco
          have hcpar : par (TRIO.gexp M r L d0 0 (n - 1)) 0 c = some m := by
            have := List.find?_some hco; simpa using this
          obtain ⟨S, hSP, -, hS⟩ := ancL_copy hlen hL hA hd0e hn j hj0 hj
          have hcr : c ≤ r := by
            rw [hSP] at hcmem
            rcases List.mem_append.mp hcmem with hcS | hcS
            · exfalso
              have := hS c hcS
              exact copyP_not_child hlen hL hA hd0e hn (by omega) (by omega) hmlt' hcpar
            · rcases List.mem_cons.mp hcS with rfl | hcS
              · exact Nat.le_refl _
              · exact Nat.le_of_lt (mem_ancL_lt hcS)
          have hcrx : c < r + L := by omega
          -- the test is the same at `c`
          obtain ⟨S1, hSP1, -, -⟩ := ancL_copy hlen hL hA hd0e hn (j + 1) (by omega) hj1
          have hrA : Anc0 (TRIO.gexp M r L d0 0 (n - 1)) r (r + (j + 1)) :=
            anc0_of_mem_ancL (by rw [hSP1]; simp)
          have hrlt := anc0_interval hrA (r + (j + 1)) (by omega) (Nat.le_refl _)
          have hcle : entry (TRIO.gexp M r L d0 0 (n - 1)) 0 c ≤ entry (TRIO.gexp M r L d0 0 (n - 1)) 0 r := by
            rw [entry_gexp_pre hlen (by omega) 0 hcrx, entry_gexp_pre hlen (by omega) 0 (by omega)]
            rcases Nat.eq_or_lt_of_le hcr with heq | hlt
            · rw [heq]
            · rw [hSP] at hcmem
              rcases List.mem_append.mp hcmem with hcS | hcS
              · have := hS c hcS; omega
              · rcases List.mem_cons.mp hcS with rfl | hcS
                · exact Nat.le_refl _
                · exact Nat.le_of_lt (anc0_interval (anc0_of_mem_ancL hcS) r (mem_ancL_lt hcS) (Nat.le_refl _))
          have he0b : entry (TRIO.gexp M r L d0 0 n) 0 (r + L + (j + 1)) =
              entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + (j + 1)) + d0 := e0_copy (d0 := d0) hlen hL hn hj1
          have hok : (par (TRIO.gexp M r L d0 0 n) 1 c = some m ∧
                col (TRIO.gexp M r L d0 0 n) c =
                  (entry (TRIO.gexp M r L d0 0 (n - 1)) 0 m + 1,
                    entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j),
                    entry (TRIO.gexp M r L d0 0 (n - 1)) 2 m + 1) ∧
                entry (TRIO.gexp M r L d0 0 n) 0 c < entry (TRIO.gexp M r L d0 0 n) 0 (r + L + (j + 1))) ↔
              (par (TRIO.gexp M r L d0 0 (n - 1)) 1 c = some m ∧
                col (TRIO.gexp M r L d0 0 (n - 1)) c =
                  (entry (TRIO.gexp M r L d0 0 (n - 1)) 0 m + 1,
                    entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j),
                    entry (TRIO.gexp M r L d0 0 (n - 1)) 2 m + 1) ∧
                entry (TRIO.gexp M r L d0 0 (n - 1)) 0 c <
                  entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + (j + 1))) := by
            rw [par_gexp_pre hlen (by omega) 1 hcrx, par_gexp_pre hlen (by omega) 1 hcrx,
              col_gexp_pre hlen (by omega) hcrx, col_gexp_pre hlen (by omega) hcrx, he0b,
              entry_gexp_pre (m := n) hlen (by omega) 0 hcrx,
              entry_gexp_pre (m := n - 1) hlen (by omega) 0 hcrx]
            rw [entry_gexp_pre (m := n - 1) hlen (by omega) 0 hcrx] at hcle
            constructor
            · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2, by omega⟩
            · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2, by omega⟩
          simp only [Option.filter_some]
          by_cases hP : par (TRIO.gexp M r L d0 0 (n - 1)) 1 c = some m ∧
              col (TRIO.gexp M r L d0 0 (n - 1)) c =
                (entry (TRIO.gexp M r L d0 0 (n - 1)) 0 m + 1,
                  entry (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + j),
                  entry (TRIO.gexp M r L d0 0 (n - 1)) 2 m + 1) ∧
              entry (TRIO.gexp M r L d0 0 (n - 1)) 0 c <
                entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + (j + 1))
          · rw [if_pos (decide_eq_true (hok.mpr hP)), if_pos (decide_eq_true hP)]
            simp only [Option.map_some, Option.some.injEq]
            rw [if_neg (by omega)]
          · rw [if_neg (fun h => hP (hok.mp (of_decide_eq_true h))),
              if_neg (fun h => hP (of_decide_eq_true h))]
            rfl

end

end Ytosk
