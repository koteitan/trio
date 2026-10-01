/-
**Ytosk の展開を trio 本体の `gexp`（先頭 ++ コピー）の形で書く。**
これで trio 本体のコピーの親の補題（`gexp_nextrel0_mir` など）が使える。
-/
import Ytosk.Bridge
import Gtrans

namespace Ytosk

theorem parent_eq_of_par {M : Mat} {t r x : Nat} (ht : t ≤ 2) (hx : x < M.length)
    (hp : par M t x = some r) : TRIO.parent M t x = r := by
  have hn : TRIO.nextR M t r x := (nextR_iff M ht hx).mp hp
  have h1 : TRIO.nextR M t (TRIO.parent M t x) x := by
    unfold TRIO.parent; exact Classical.epsilon_spec (p := fun j0 => TRIO.nextR M t j0 x) ⟨r, hn⟩
  have := (nextR_iff M ht hx).mpr h1; rw [hp] at this; exact (Option.some.inj this).symm

theorem hasParent_of_par {M : Mat} {t r x : Nat} (ht : t ≤ 2) (hx : x < M.length)
    (hp : par M t x = some r) : TRIO.hasParent M t x :=
  ⟨r, (nextR_iff M ht hx).mp hp, fun j hj => by
    have := (nextR_iff M ht hx).mpr hj; rw [hp] at this; exact (Option.some.inj this).symm⟩

/-- **The expansion as `gexp`.** -/
theorem expand_eq_gexp (M : Mat) (n : Nat) (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    {r : Nat} (hp : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r) :
    expand M n = TRIO.gexp M r (M.length - 1 - r)
      (if 0 < TRIO.srow M (M.length - 1) then TRIO.entry M 0 (M.length - 1) - TRIO.entry M 0 r else 0)
      (if 1 < TRIO.srow M (M.length - 1) then TRIO.entry M 1 (M.length - 1) - TRIO.entry M 1 r else 0)
      n := by
  have ht : TRIO.srow M (M.length - 1) ≤ 2 := by unfold TRIO.srow; split_ifs <;> omega
  have hx : M.length - 1 < M.length := by omega
  rw [expand_eq_oper M n hM, TRIO.oper_gcopies n (by omega) hz (hasParent_of_par ht hx hp),
    parent_eq_of_par ht hx hp]
  rfl

/-- Row-0 parent inside a copy. -/
theorem par0_gexp_mir {M : Mat} {j0 Lb d0 d1 n k qa qb : Nat} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hqb : qb < Lb) (h : par M 0 (j0 + qb) = some (j0 + qa)) :
    par (TRIO.gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + qb)) = some (j0 + (k * Lb + qa)) := by
  have hbnd : j0 + (k * Lb + qb) < (TRIO.gexp M j0 Lb d0 d1 n).length := by
    rw [TRIO.gexp_length hlen]
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  exact (par0_iff _ hbnd).mpr
    (TRIO.gexp_nextrel0_mir hlen hk hqb ((par0_iff M (by omega)).mp h))

/-- Row-0 parent of the root of copy `k ≥ 1`: the copy `k - 1` of the parent of the last column. -/
theorem par0_gexp_root {M : Mat} {j0 Lb d0 d1 n k qp : Nat} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hk1 : 1 ≤ k) (hqp : qp < Lb)
    (hd0e : TRIO.entry M 0 (j0 + Lb) = TRIO.entry M 0 j0 + d0)
    (h : par M 0 (j0 + Lb) = some (j0 + qp)) :
    par (TRIO.gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + 0)) = some (j0 + ((k - 1) * Lb + qp)) := by
  have hLb : 0 < Lb := by omega
  have hbnd : j0 + (k * Lb + 0) < (TRIO.gexp M j0 Lb d0 d1 n).length := by
    rw [TRIO.gexp_length hlen]
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  exact (par0_iff _ hbnd).mpr
    (TRIO.gexp_nextrel0_root hlen hk hk1 hqp hd0e ((par0_iff M (by omega)).mp h))

theorem entry_take (M : Mat) {l q : Nat} (i : Nat) (hq : q < l) : entry (M.take l) i q = entry M i q := by
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hq]

/-- The row-0 parent depends only on the columns up to the column itself. -/
theorem par0_take (M : Mat) {l i : Nat} (hi : i < l) : par (M.take l) 0 i = par M 0 i := by
  cases i with
  | zero => simp [par, prev, climb]
  | succ c =>
    apply Option.ext
    intro a
    simp only [par, prev]
    rw [climb_prev_iff _ a c (c + 1 + 1) (by omega), climb_prev_iff _ a c (c + 1 + 1) (by omega)]
    have he : ∀ q, q ≤ c + 1 → entry (M.take l) 0 q = entry M 0 q := fun q hq =>
      entry_take M 0 (by omega)
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, fun j hj1 hj2 => ?_⟩
      · simpa [he a (by omega), he (c + 1) (le_refl _)] using h2
      · have := h3 j hj1 hj2; simpa [he j (by omega), he (c + 1) (le_refl _)] using this
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, fun j hj1 hj2 => ?_⟩
      · simpa [he a (by omega), he (c + 1) (le_refl _)] using h2
      · have := h3 j hj1 hj2; simpa [he j (by omega), he (c + 1) (le_refl _)] using this

/-- Before the last column, the row-0 parents after expansion are those of `M`. -/
theorem par0_expand_prefix (M : Mat) {n i : Nat} (hM : 2 ≤ M.length) (hn : 1 ≤ n)
    (hi : i < M.length - 1) : par (expand M n) 0 i = par M 0 i := by
  have h1 : (expand M n).take (M.length - 1) = M.take (M.length - 1) := by
    rw [expand_eq_oper M n hM]; exact TRIO.oper_take_prefix (by omega) hn (le_refl _)
  rw [← par0_take (expand M n) hi, h1, par0_take M hi]

end Ytosk
