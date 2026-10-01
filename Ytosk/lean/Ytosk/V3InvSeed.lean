/-
**M から周期的な種 S を作る（最後の列 x を、展開でそこに来るコピーの根の列に替える）。**

S = M.take x ++ [col r + (d0, d1, 0)]。展開は S と M で同じ（`gexp_congr`: gexp は先頭とブロックの値・ガード
だけで決まる）。S の x の親は、t ≥ 1 では行 0 が変わらないので M の x の親（`seed_par_x`）、t = 0 では
r の親（`seed_par_x0`）。
-/
import Ytosk.V3InvPer4

namespace Ytosk

open T Classical

/-- The seed of `M`: the last column replaced by `col r + (d0, d1, 0)`. -/
def seedOf (M : Mat) (r d0 d1 : Nat) : Mat :=
  M.take (M.length - 1) ++ [(entry M 0 r + d0, entry M 1 r + d1, entry M 2 r)]

/-! ## 展開は先頭とブロックだけで決まる -/

theorem gexp_congr {X M : Mat} {r L d0 d1 n : Nat} (hX : r + L ≤ X.length) (hM : r + L ≤ M.length)
    (hag : ∀ j, j < r + L → X.getD j (0, 0, 0) = M.getD j (0, 0, 0)) :
    TRIO.gexp X r L d0 d1 n = TRIO.gexp M r L d0 d1 n := by
  unfold TRIO.gexp TRIO.gcopies TRIO.gcopy
  congr 1
  · apply List.ext_getElem
    · simp only [List.length_take]; omega
    · intro i h1 h2
      simp only [List.length_take] at h1
      have := hag i (by omega)
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
      simpa using this
  · congr 1
    funext k
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range'] at hj
    have hjL : j < r + L := by omega
    have he : ∀ y, TRIO.entry X y j = TRIO.entry M y j := by
      intro y; unfold TRIO.entry; rw [hag j hjL]
    have hle : TRIO.le1 X r j ↔ TRIO.le1 M r j := by
      constructor
      · exact TRIO.le1_of_agree (by omega) (by omega) (fun x hx => (hag x (by omega)).symm)
      · exact TRIO.le1_of_agree (by omega) (by omega) (fun x hx => hag x (by omega))
    rw [he 0, he 1, he 2]
    simp only [hle]

/-! ## 種の値と親 -/

section
variable {M : Mat} {r d0 d1 : Nat} {x : Nat} (hx : x + 1 = M.length)
include hx

theorem seed_len : (seedOf M r d0 d1).length = M.length := by
  unfold seedOf; simp [List.length_take]; omega

theorem seed_getD_lt {j : Nat} (hj : j < x) :
    (seedOf M r d0 d1).getD j (0, 0, 0) = M.getD j (0, 0, 0) := by
  unfold seedOf
  rw [TRIO.getD_append_left (by simp [List.length_take]; omega), TRIO.getD_take (by omega)]

theorem seed_entry_lt (y : Nat) {j : Nat} (hj : j < x) : entry (seedOf M r d0 d1) y j = entry M y j := by
  unfold entry; rw [seed_getD_lt hx hj]

theorem seed_getD_x : (seedOf M r d0 d1).getD x (0, 0, 0) = (entry M 0 r + d0, entry M 1 r + d1, entry M 2 r) := by
  unfold seedOf
  have hl : (M.take (M.length - 1)).length = x := by simp [List.length_take]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]), hl, Nat.sub_self]
  rfl

theorem seed_e0x : entry (seedOf M r d0 d1) 0 x = entry M 0 r + d0 := by
  rw [entry0_getD, seed_getD_x hx]
theorem seed_e1x : entry (seedOf M r d0 d1) 1 x = entry M 1 r + d1 := by
  rw [entry1_getD, seed_getD_x hx]
theorem seed_e2x : entry (seedOf M r d0 d1) 2 x = entry M 2 r := by
  rw [entry2_getD, seed_getD_x hx]

theorem seed_col_lt {j : Nat} (hj : j < x) : col (seedOf M r d0 d1) j = col M j := by
  unfold col; rw [seed_getD_lt hx hj]

theorem seed_take : (seedOf M r d0 d1).take x = M.take x := by
  apply List.ext_getElem
  · simp [List.length_take, seed_len hx]
  · intro i h1 h2
    simp only [List.length_take, seed_len hx] at h1
    have := seed_getD_lt (r := r) (d0 := d0) (d1 := d1) hx (j := i) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [seed_len hx]; omega), List.getElem?_eq_getElem (by omega)] at this
    simpa using this

theorem seed_par_lt (y : Nat) {j : Nat} (hj : j < x) : par (seedOf M r d0 d1) y j = par M y j := by
  rw [← par_take _ y j hj, seed_take hx, par_take M y j hj]

theorem seed_anc0_lt {a b : Nat} (hb : b < x) : Anc0 (seedOf M r d0 d1) a b ↔ Anc0 M a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Anc0.refl _
    | @step b c hp _ ih =>
      have := par_lt _ 0 c b hp
      rw [seed_par_lt hx 0 hb] at hp
      exact Anc0.step hp (ih (by omega))
  · intro h
    induction h with
    | refl => exact Anc0.refl _
    | @step b c hp _ ih =>
      have := par_lt _ 0 c b hp
      rw [← seed_par_lt (r := r) (d0 := d0) (d1 := d1) hx 0 hb] at hp
      exact Anc0.step hp (ih (by omega))

/-- **The parent of `x` in the seed when row 0 is unchanged** (`t ≥ 1`). -/
theorem seed_par_x (he : entry M 0 r + d0 = entry M 0 x) :
    par (seedOf M r d0 d1) 0 x = par M 0 x :=
  par0_congr (fun j hj => by
    rcases Nat.lt_or_ge j x with h | h
    · exact seed_entry_lt hx 0 h
    · have : j = x := by omega
      subst this; rw [seed_e0x hx, he])

end

end Ytosk
