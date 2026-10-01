/-
**3 行・t = 2・q = r（主の場合）: 組み立て。**

主の場合（x へ上げる列がない、x と r はのりしろの子でない）では、種は o(r) だけ。
- D = DepS M {o(r)} は x より前で DepX M x と同じ（`depS_iff_depX`）。
- x より前の数え方は N と M で同じ（コピーの列から x より前への上げはない、を仮定 hIU に置く）。
-/
import Ytosk.V3T2S
import Ytosk.V3DepLhd

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r)
  (hXu : ∀ i, upg M i ≠ some (r + L)) (hXb : ∀ p, col M (r + L) ≠ bump M p)
  (hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p)
include hlen hL hp hXu hXb hrb

omit hlen hL hp hXb hrb in
theorem isUpg_x_false : isUpg M (r + L) = false := by
  unfold isUpg; rw [List.any_eq_false]; intro k _ hk; exact hXu k (of_decide_eq_true hk)

omit hrb in
theorem counted_r_x : Counted M r (r + L) :=
  ⟨hXb r, by rw [isUpg_x_false hXu]; simp⟩

omit hrb in
theorem depS_sub_depX {b : Bool} {i : Nat} (h : DepS M (fun b i => b = true ∧ i = r) b i) :
    DepX M (r + L) b i := by
  induction h with
  | seed hs =>
    obtain ⟨rfl, rfl⟩ := hs
    exact DepX.ochild (mem_children_iff.mpr ⟨by omega, hp⟩) (hXb _)
      (by rw [isUpg_x_false hXu]; simp) DepX.leaf
  | ochild hc hcb hcu _ ih => exact DepX.ochild hc hcb hcu ih
  | ov _ ih => exact DepX.ov ih
  | vpar h1 hpm _ ih => exact DepX.vpar h1 hpm ih
  | vupg h1 h2 hu _ ih => exact DepX.vupg h1 h2 hu ih
  | vbump h1 h2 hj hjb hk _ ih => exact DepX.vbump h1 h2 hj hjb hk ih

/-- **`D` from `o(r)` is `DepX` below `x`.** -/
theorem depS_iff_depX {b : Bool} {i : Nat} (hi : i < r + L) :
    DepS M (fun b i => b = true ∧ i = r) b i ↔ DepX M (r + L) b i := by
  constructor
  · exact depS_sub_depX hlen hL hp hXu hXb
  · intro h
    revert hi
    induction h with
    | leaf => intro h; omega
    | @ochild i c hc hcb hcu _ ih =>
      intro hi
      have hcl := (mem_children hc).2
      rcases Nat.lt_or_ge c (r + L) with h | h
      · exact DepS.ochild hc hcb hcu (ih h)
      · have hcx : c = r + L := by omega
        have hpc := (mem_children_iff.mp hc).2
        rw [hcx, hp] at hpc
        cases hpc
        exact DepS.seed ⟨rfl, rfl⟩
    | ov _ ih => intro hi; exact DepS.ov (ih hi)
    | @vpar i m h1 hpm _ ih =>
      intro hi; exact DepS.vpar h1 hpm (ih (by have := par_lt M 1 i m hpm; omega))
    | @vupg i k h1 h2 hu _ ih =>
      intro hi
      have hkl := upg_lt (by omega) hu
      have hkx : k ≠ r + L := fun h => hXu i (h ▸ hu)
      exact DepS.vupg h1 h2 hu (ih (by omega))
    | @vbump i j k h1 h2 hj hjb hk _ ih =>
      intro hi
      have hkl := (mem_children hk).2
      rcases Nat.lt_or_ge k (r + L) with h | h
      · exact DepS.vbump h1 h2 hj hjb hk (ih h)
      · exfalso
        have hkx : k = r + L := by omega
        have hpk := (mem_children_iff.mp hk).2
        rw [hkx, hp] at hpk
        cases hpk
        exact hrb i (mem_children_iff.mp hj).2 hjb

end

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn2 : 2 ≤ n)
  (hXu : ∀ i, upg M i ≠ some (r + L)) (hXb : ∀ p, col M (r + L) ≠ bump M p)
  (he2r : entry M 2 r = 0)
  (hIU : ∀ j c, r + L ≤ j → c < r + L → upg (TRIO.gexp M r L d0 d1 n) j ≠ some c)
include hlen hL hp hd0e hn2 hXu hXb he2r hIU

omit hIU in
theorem upg_N2_pre {j : Nat} (hj : j + 1 < r + L) :
    upg (TRIO.gexp M r L d0 d1 n) j = upg M j := by
  rw [← upg_take _ hj, gexp_take_x hlen (by omega), upg_take M hj]

/-- **Upgrades into columns before `x`** are the same in `N` and `M`. -/
theorem isUpg_N2 {c : Nat} (hc : c < r + L) :
    isUpg (TRIO.gexp M r L d0 d1 n) c = isUpg M c := by
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hxm1 := upg_N2_xm1 (d1 := d1) hlen hL hp hd0e (by omega) hn2 he2r (hXu _)
  apply Bool.eq_iff_iff.mpr
  unfold isUpg
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨j, hj, hu⟩
    have hu' : upg (TRIO.gexp M r L d0 d1 n) j = some c := by simpa using hu
    have hj' := List.mem_range.mp hj
    refine ⟨j, List.mem_range.mpr ?_, ?_⟩
    · rcases Nat.lt_or_ge j (r + L) with h | h
      · omega
      · exact absurd hu' (hIU j c h hc)
    · rcases Nat.lt_or_ge (j + 1) (r + L) with h | h
      · rw [upg_N2_pre hlen hL hp hd0e hn2 hXu hXb he2r h] at hu'; simpa using hu'
      · rcases Nat.lt_or_ge j (r + L) with h' | h'
        · have : j = r + L - 1 := by omega
          rw [this, hxm1] at hu'; rw [this]; simpa using hu'
        · exact absurd hu' (hIU j c h' hc)
  · rintro ⟨j, hj, hu⟩
    have hu' : upg M j = some c := by simpa using hu
    have hj' := List.mem_range.mp hj
    have hjx : j < r + L := by
      by_contra h
      have : j + 1 = M.length := by omega
      unfold upg at hu'; rw [if_pos (Or.inr (Or.inr this))] at hu'; cases hu'
    refine ⟨j, List.mem_range.mpr (by rw [hlN]; omega), ?_⟩
    rcases Nat.lt_or_ge (j + 1) (r + L) with h | h
    · rw [upg_N2_pre hlen hL hp hd0e hn2 hXu hXb he2r h]; simpa using hu'
    · have : j = r + L - 1 := by omega
      rw [this, hxm1]; rw [this] at hu'; simpa using hu'

omit hIU in
/-- **`topped` before `x`** is the same. -/
theorem topped_N2 {c : Nat} (hc : c < r + L) :
    topped (TRIO.gexp M r L d0 d1 n) c = topped M c := by
  unfold topped
  rw [children_N2 hlen hL hp hd0e (by omega) hn2 hc]
  cases hl : (children M c).getLast? with
  | none => rfl
  | some d =>
    have hd := List.mem_of_getLast? hl
    have hdl := (mem_children hd).2
    simp only
    rcases Nat.lt_or_ge d (r + L) with h | h
    · rw [col_gexp_pre hlen (by omega) h, show bump (TRIO.gexp M r L d0 d1 n) c = bump M c by
        unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hc, entry_gexp_pre hlen (by omega) 1 hc]]
    · have hdx : d = r + L := by omega
      subst hdx
      have h1 : ¬ col (TRIO.gexp M r L d0 d1 n) (r + L) = bump (TRIO.gexp M r L d0 d1 n) c := by
        intro h'
        have : entry (TRIO.gexp M r L d0 d1 n) 2 (r + L) = (col (TRIO.gexp M r L d0 d1 n) (r + L)).2.2 := rfl
        rw [h', (entry_xprime hlen hL hp hd0e (by omega) hn2).1, he2r] at this; simp [bump] at this
      simp only [decide_eq_false h1, decide_eq_false (hXb c)]

/-- **Counting before `x`** is the same. -/
theorem counted_N2 {i c : Nat} (hi : i < r + L) (hc : c < r + L) :
    Counted (TRIO.gexp M r L d0 d1 n) i c ↔ Counted M i c := by
  unfold Counted
  rw [col_gexp_pre hlen (by omega) hc, show bump (TRIO.gexp M r L d0 d1 n) i = bump M i by
      unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi],
    isUpg_N2 hlen hL hp hd0e hn2 hXu hXb he2r hIU hc, topped_N2 hlen hL hp hd0e hn2 hXu hXb he2r hc]

/-- **The counted children before `x`** are the same (given that `x′` counts at `r`). -/
theorem CL_N2 (hxcN : Counted (TRIO.gexp M r L d0 d1 n) r (r + L)) {i : Nat} (hi : i < r + L) :
    CL (TRIO.gexp M r L d0 d1 n) i = CL M i := by
  unfold CL
  rw [children_N2 hlen hL hp hd0e (by omega) hn2 hi]
  apply List.filter_congr
  intro c hc
  have hcl := (mem_children hc).2
  rcases Nat.lt_or_ge c (r + L) with h | h
  · simp only [counted_N2 hlen hL hp hd0e hn2 hXu hXb he2r hIU hi h]
  · have hcx : c = r + L := by omega
    have hpc := (mem_children_iff.mp hc).2
    rw [hcx, hp] at hpc; cases hpc
    rw [hcx]
    have hM : Counted M r (r + L) := ⟨hXb r, by rw [isUpg_x_false hXu]; simp⟩
    simp only [decide_eq_true hxcN, decide_eq_true hM]

end

end Ytosk
