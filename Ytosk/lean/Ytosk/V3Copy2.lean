/-
**3 行・t = 1: 先頭部分と、写しの列の上げ。**

- `gexp_take_x`: N・P の x = r + L より前は M と同じ列（`Prefix.lean` の補題がそのまま使える）。
- 上げの後半（祖先の中の探索）は、P_1 = m の行 0 の子で経路上にある列 c_m だけを調べる（`upgFind_child`）。
  条件 col q = (M_{m,0} + 1, …) から q の行 0 の親は m になるから。
- `upg_copy`: 写しの列 x + j（0 < j）の上げは P の r + j の上げを「r より後ろなら L ずらす」もの。
  上げの行き先が r（c_m が P の r）のときは同じ列 r（N では写しの 0 番目の r）になる。
-/
import Ytosk.V3Copy1
import Ytosk.Prefix

namespace Ytosk

/-! ## 先頭部分 -/

section
variable {M : Mat} {r L d0 d1 : Nat} (hlen : r + L + 1 = M.length)
include hlen

theorem gexp_getD_pre {m i : Nat} (hm : 1 ≤ m) (hi : i < r + L) :
    (TRIO.gexp M r L d0 d1 m).getD i (0, 0, 0) = M.getD i (0, 0, 0) := by
  rcases Nat.lt_or_ge i r with h | h
  · exact TRIO.gexp_getD_low hlen h
  · have := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := m)
      (k := 0) (q := i - r) hlen (by omega) (by omega)
    rw [show r + (0 * L + (i - r)) = i by omega, show r + (i - r) = i by omega] at this
    rw [this, TRIO.getD_eq_entries]
    simp

/-- **Before `x` the expansion is `M`.** -/
theorem gexp_take_x {m : Nat} (hm : 1 ≤ m) :
    (TRIO.gexp M r L d0 d1 m).take (r + L) = M.take (r + L) := by
  have hl : (TRIO.gexp M r L d0 d1 m).length = r + m * L := TRIO.gexp_length hlen
  have hmL : L ≤ m * L := by have := Nat.mul_le_mul_right L hm; simpa using this
  apply List.ext_getElem
  · simp only [List.length_take, hl]; omega
  · intro i h1 h2
    simp only [List.getElem_take]
    have hi : i < r + L := by simp at h1; omega
    have hg := gexp_getD_pre (d0 := d0) (d1 := d1) hlen hm hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
    simpa using hg

theorem par_gexp_pre {m : Nat} (hm : 1 ≤ m) (k : Nat) {i : Nat} (hi : i < r + L) :
    par (TRIO.gexp M r L d0 d1 m) k i = par M k i := by
  rw [← par_take _ k i hi, gexp_take_x hlen hm, par_take M k i hi]

theorem col_gexp_pre {m : Nat} (hm : 1 ≤ m) {i : Nat} (hi : i < r + L) :
    col (TRIO.gexp M r L d0 d1 m) i = col M i := by
  rw [← col_take _ hi, gexp_take_x hlen hm, col_take M hi]

theorem entry_gexp_pre {m : Nat} (hm : 1 ≤ m) (y : Nat) {i : Nat} (hi : i < r + L) :
    entry (TRIO.gexp M r L d0 d1 m) y i = entry M y i := by
  rw [← entry_take _ y hi, gexp_take_x hlen hm, entry_take M y hi]

end

/-! ## 上げの後半は経路上の m の子だけを見る -/

theorem find?_unique {l : List Nat} {p g : Nat → Bool} (hpg : ∀ a ∈ l, p a = true → g a = true)
    (huniq : ∀ a ∈ l, ∀ b ∈ l, g a = true → g b = true → a = b) :
    l.find? p = (l.find? g).filter p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun b hb => hpg b (List.mem_cons_of_mem _ hb))
      (fun b hb c hc => huniq b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc))
    simp only [List.find?_cons]
    cases hga : g a <;> cases hpa : p a
    · simpa using ih'
    · exact absurd (hpg a List.mem_cons_self hpa) (by simp [hga])
    · simp only [Option.filter_some, hpa, Bool.false_eq_true, ↓reduceIte]
      rw [List.find?_eq_none]
      intro b hb hpb
      have := huniq a List.mem_cons_self b (List.mem_cons_of_mem _ hb) hga
        (hpg b (List.mem_cons_of_mem _ hb) hpb)
      subst this
      simp [hpa] at hpb
    · rw [Option.filter_some, if_pos hpa]

/-- Two members of an ancestor list with the same row-0 parent are equal. -/
theorem ancL_par_unique {M : Mat} {n a b m : Nat} (ha : a ∈ ancL M n) (hb : b ∈ ancL M n)
    (hpa : par M 0 a = some m) (hpb : par M 0 b = some m) : a = b := by
  have hAa := anc0_of_mem_ancL ha
  have hAb := anc0_of_mem_ancL hb
  rcases anc0_total hAa hAb with h | h
  · by_contra hne
    have := anc0_par h hne hpb
    have h1 := this.le
    have h2 := par_lt M 0 a m hpa
    omega
  · by_contra hne
    have := anc0_par h (Ne.symm hne) hpa
    have h1 := this.le
    have h2 := par_lt M 0 b m hpb
    omega

/-- A column with the upgrade shape over `m` is a row-0 child of `m`. -/
theorem par0_of_upgshape {M : Mat} {q m : Nat} (h1 : par M 1 q = some m)
    (h2 : entry M 0 q = entry M 0 m + 1) : par M 0 q = some m := by
  have hA := anc0_of_par M 1 m q h1
  have hmq := par_lt M 1 q m h1
  rw [par0_spec]
  refine ⟨hmq, by omega, fun j hj1 hj2 => ?_⟩
  have := anc0_interval hA j hj1 (by omega)
  omega

/-- The search of `upg` finds the child of `m` on the path, if it passes the test. -/
theorem upgFind_child (M : Mat) (n m : Nat) (Lc : Nat × Nat × Nat) (hL : Lc.1 = entry M 0 m + 1)
    (e : Nat) :
    (ancL M n).find? (fun q => decide (par M 1 q = some m ∧ col M q = Lc ∧ entry M 0 q < e)) =
      ((ancL M n).find? (fun q => decide (par M 0 q = some m))).filter
        (fun q => decide (par M 1 q = some m ∧ col M q = Lc ∧ entry M 0 q < e)) := by
  apply find?_unique
  · intro a _ h
    simp only [decide_eq_true_eq] at h ⊢
    obtain ⟨h1, h2, _⟩ := h
    apply par0_of_upgshape h1
    have : entry M 0 a = (col M a).1 := rfl
    rw [this, h2, hL]
  · intro a ha b hb hga hgb
    simp only [decide_eq_true_eq] at hga hgb
    exact ancL_par_unique ha hb hga hgb

end Ytosk
