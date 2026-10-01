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

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn2 : 2 ≤ n)
  (hXu : ∀ i, upg M i ≠ some (r + L)) (hXb : ∀ p, col M (r + L) ≠ bump M p)
  (hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p)
  (he2r : entry M 2 r = 0)
  (hIU : ∀ j c, r + L ≤ j → c < r + L → upg (TRIO.gexp M r L d0 d1 n) j ≠ some c)
include hlen hL hp hd0e hn2 hXu hXb hrb he2r hIU

/-- **Outside `D`, `N` has the values of `M` before `x`.** -/
theorem t2_off {ρ σ : Valn} {rkN : Bool → Nat → Nat} (hC : Cons M ρ)
    (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN) :
    ∀ i, i < r + L → (¬ DepS M (fun b i => b = true ∧ i = r) true i → σ.o i = ρ.o i) ∧
      (¬ DepS M (fun b i => b = true ∧ i = r) false i → σ.v i = ρ.v i) := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  set D := DepS M (fun b i => b = true ∧ i = r) with hD
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hbumpN : ∀ i, i < r + L → bump N i = bump M i := fun i hi => by
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi]
  have hcolx : ∀ i, col N (r + L) ≠ bump N i := by
    intro i h'
    have : entry N 2 (r + L) = (col N (r + L)).2.2 := rfl
    rw [h', (entry_xprime hlen hL hp hd0e (by omega) hn2).1, he2r] at this; simp [bump] at this
  have hupgN : ∀ i, i < r + L → upg N i = upg M i := by
    intro i hi
    rcases Nat.lt_or_ge (i + 1) (r + L) with h | h
    · exact upg_N2_pre hlen hL hp hd0e hn2 hXu hXb he2r h
    · have : i = r + L - 1 := by omega
      rw [this]; exact upg_N2_xm1 hlen hL hp hd0e (by omega) hn2 he2r (hXu _)
  have key := cons_agree (τ := ρ) (fun b i => r + L ≤ i ∨ D b i) hCN hRN
  have hres := key (by
    intro i hi hE
    simp only [not_or] at hE
    have hix : i < r + L := by omega
    rw [(hC i (by omega)).1]
    unfold oRhs
    rw [children_N2 hlen hL hp hd0e (by omega) hn2 hix]
    congr 3
    apply List.map_congr_left
    intro c hc
    have hcl := (mem_children hc).2
    have hcx : c < r + L := by
      by_contra h'
      have : c = r + L := by omega
      have hpc := (mem_children_iff.mp hc).2
      rw [this, hp] at hpc; cases hpc
      exact hE.2 (DepS.seed ⟨rfl, rfl⟩)
    exact (cnt_eq_of (counted_N2 hlen hL hp hd0e hn2 hXu hXb he2r hIU hix hcx) rfl).symm) (by
    intro i hi hE
    simp only [not_or] at hE
    have hix : i < r + L := by omega
    rw [(hC i (by omega)).2]
    symm
    apply vRhs_eq_of (entry_gexp_pre hlen (by omega) 1 hix) (entry_gexp_pre hlen (by omega) 2 hix)
    · intro _; rw [par_gexp_pre hlen (by omega) 1 hix]
    · intro _ _; rw [hupgN i hix]
    · intro _ _
      rw [children_N2 hlen hL hp hd0e (by omega) hn2 hix]
      congr 2
      apply List.map_congr_left
      intro j hj
      have hjl := (mem_children hj).2
      apply bumpTerm_eq_of
      · rcases Nat.lt_or_ge j (r + L) with h | h
        · rw [col_gexp_pre hlen (by omega) h, hbumpN i hix]
        · have : j = r + L := by omega
          rw [this]
          exact ⟨fun h' => absurd h' (hcolx i), fun h' => absurd h' (hXb i)⟩
      · intro hjb
        have hjx : j < r + L := by
          by_contra h'
          have : j = r + L := by omega
          rw [this] at hjb; exact hXb i hjb
        rw [children_N2 hlen hL hp hd0e (by omega) hn2 hjx]) (by
    intro i hi hE
    simp only [not_or] at hE
    have hix : i < r + L := by omega
    refine ⟨fun h => ?_, fun c hc hcnt h => ?_⟩
    · rcases h with h | h
      · omega
      · exact hE.2 (DepS.ov h)
    · rw [children_N2 hlen hL hp hd0e (by omega) hn2 hix] at hc
      have hcl := (mem_children hc).2
      have hcx : c < r + L := by
        by_contra h'
        have : c = r + L := by omega
        have hpc := (mem_children_iff.mp hc).2
        rw [this, hp] at hpc; cases hpc
        exact hE.2 (DepS.seed ⟨rfl, rfl⟩)
      rcases h with h | h
      · omega
      · have hcM := (counted_N2 hlen hL hp hd0e hn2 hXu hXb he2r hIU hix hcx).mp hcnt
        exact hE.2 (DepS.ochild hc hcM.1 hcM.2 h)) (by
    intro i hi hE he1
    simp only [not_or] at hE
    have hix : i < r + L := by omega
    rw [entry_gexp_pre hlen (by omega) 1 hix] at he1
    refine ⟨fun m hm h => ?_, fun he2 k hk h => ?_, fun he2 j hj hjb k hk h => ?_⟩
    · rw [par_gexp_pre hlen (by omega) 1 hix] at hm
      rcases h with h | h
      · have := par_lt M 1 i m hm; omega
      · exact hE.2 (DepS.vpar he1 hm h)
    · rw [entry_gexp_pre hlen (by omega) 2 hix] at he2
      rw [hupgN i hix] at hk
      have hkl := upg_lt (by omega) hk
      have hkx : k ≠ r + L := fun h' => hXu i (h' ▸ hk)
      rcases h with h | h
      · omega
      · exact hE.2 (DepS.vupg he1 he2 hk h)
    · rw [entry_gexp_pre hlen (by omega) 2 hix] at he2
      rw [children_N2 hlen hL hp hd0e (by omega) hn2 hix] at hj
      have hjl := (mem_children hj).2
      have hjx : j < r + L := by
        by_contra h'
        have : j = r + L := by omega
        rw [this] at hjb; exact hcolx i hjb
      rw [col_gexp_pre hlen (by omega) hjx, hbumpN i hix] at hjb
      rw [children_N2 hlen hL hp hd0e (by omega) hn2 hjx] at hk
      have hkl := (mem_children hk).2
      have hkx : k < r + L := by
        by_contra h'
        have : k = r + L := by omega
        have hpk := (mem_children_iff.mp hk).2
        rw [this, hp] at hpk; cases hpk
        exact hrb i (mem_children_iff.mp hj).2 hjb
      rcases h with h | h
      · omega
      · exact hE.2 (DepS.vbump he1 he2 hj hjb hk h))
  intro i hi
  have h := hres i (by rw [hlN]; omega)
  exact ⟨fun hd => h.1 (by rintro (h' | h'); omega; exact hd h'),
    fun hd => h.2 (by rintro (h' | h'); omega; exact hd h')⟩

/-- **Row 0 at or after `x` in `N` is positive.** -/
theorem e0_N2_pos (hR0 : R0P M) {j : Nat} (hj0 : r + L ≤ j) (hj : j < r + n * L) :
    0 < entry (TRIO.gexp M r L d0 d1 n) 0 j := by
  obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL (by omega) hj
  have hk1 : 1 ≤ k := by
    by_contra h; have : k = 0 := by omega
    subst this; omega
  have h := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := n)
    (k := k) (q := q) hlen hk hq
  have he : entry (TRIO.gexp M r L d0 d1 n) 0 (r + (k * L + q)) = entry M 0 (r + q) + k * d0 := by
    unfold entry; rw [h]; rfl
  have hR := hR0 _ _ hp
  have : d0 ≤ k * d0 := Nat.le_mul_of_pos_left d0 hk1
  rw [he]; omega

/-- **The root value**: only columns before `x` are roots, in `N` and in `M`. -/
theorem root_N2 (hR0 : R0P M) (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0)
    {ρ σ : Valn} (hG : Good3 M ρ) (hGN : Good3 (TRIO.gexp M r L d0 d1 n) σ)
    (hle : ∀ i, i < r + L → σ.o i ≤ ρ.o i)
    (hstrict : ∀ R, R < r + L → Anc0 M R (r + L) → col M R = (0, 0, 0) → σ.o R < ρ.o R) :
    isOT (root (TRIO.gexp M r L d0 d1 n) σ) = true ∧ root (TRIO.gexp M r L d0 d1 n) σ < root M ρ := by
  classical
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hcol0 : ∀ {N : Mat} {i : Nat}, entry N 0 i ≠ 0 → col N i ≠ (0, 0, 0) := by
    intro N i h hc
    rw [col_eq_entries] at hc
    simp only [Prod.mk.injEq] at hc
    exact h hc.1
  set f' : Nat → T := fun i => if col M i = (0, 0, 0) then σ.o i else z with hf'
  set f : Nat → T := fun i => if col M i = (0, 0, 0) then ρ.o i else z with hf
  have hot' : ∀ i, i < r + L → isOT (f' i) = true := by
    intro i hi; simp only [hf']; split
    · exact hGN.ot_o i (by rw [hlN]; omega)
    · rfl
  have hot : ∀ i, i < r + L → isOT (f i) = true := by
    intro i hi; simp only [hf]; split
    · exact hG.ot_o i (by omega)
    · rfl
  have hrootN : root (TRIO.gexp M r L d0 d1 n) σ = sumN ((List.range (r + L)).map f') := by
    unfold root
    rw [hlN, show r + n * L = (r + L) + (n * L - L) by omega, List.range_add, List.map_append]
    have hz : ∀ t ∈ (List.map (fun x => r + L + x) (List.range (n * L - L))).map
        (fun i => if col (TRIO.gexp M r L d0 d1 n) i = (0, 0, 0) then σ.o i else z), t = z := by
      intro t ht
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
      have hk' := List.mem_range.mp hk
      rw [if_neg (hcol0 (by
        have := e0_N2_pos hlen hL hp hd0e hn2 hXu hXb hrb he2r hIU hR0 (j := r + L + k) (by omega)
          (by omega); omega))]
    rw [sumN_append_zeros (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      have hir := List.mem_range.mp hi
      split
      · exact hGN.ot_o i (by rw [hlN]; omega)
      · rfl) _ hz]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [col_gexp_pre hlen (by omega) (List.mem_range.mp hi)]
  have hrootM : root M ρ = sumN ((List.range (r + L)).map f) := by
    unfold root
    rw [← hlen, List.range_succ, List.map_append, List.map_singleton]
    have hx0 : entry M 0 (r + L) ≠ 0 := by have := hR0 _ _ hp; omega
    rw [if_neg (hcol0 hx0), sumN_snoc_z (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      have hir := List.mem_range.mp hi
      split
      · exact hG.ot_o i (by omega)
      · rfl)]
  rw [hrootN, hrootM]
  refine ⟨isOT_sumN _ (fun t ht => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht; exact hot' i (List.mem_range.mp hi)), ?_⟩
  obtain ⟨R, hRA, hR0c, hRl⟩ := root_t1 hR01 hR12 h00 (r + L)
  have he0R : entry M 0 R = 0 := by rw [col_eq_entries] at hR0c; simp only [Prod.mk.injEq] at hR0c; exact hR0c.1
  have hRx : R < r + L := by
    by_contra h
    have : R = r + L := by have := hRA.le; omega
    rw [this] at he0R; have := hR0 _ _ hp; omega
  apply sumN_range_lt f' f (r + L) hRx hot' hot
  · intro i hi; simp only [hf', hf]; split
    · exact hle i hi
    · exact le_refl _
  · simp only [hf', hf]; rw [if_pos hR0c, if_pos hR0c]; exact hstrict R hRx hRA hR0c
  · intro i h1 h2
    have hn' := hcol0 (hRl i h1 (by omega))
    simp only [hf', hf]; exact ⟨if_neg hn', if_neg hn'⟩

/-- **`t = 2`, `q = r`, the main case** (no column upgrades to `x`): the value of `N = M[n]` (`n ≥ 2`) is
standard and below that of `M`. Hypotheses beyond the structural invariants and `ValInv` of `M`:
`N`'s evaluation (`Good3`), the copies do not upgrade into columns before `x` (`hIU`), `x′` counts at `r`,
`VSmallNew` for `N`, and the seed at `r` (`o_N(r) = ψ_{v(r)}(X)` with `X` closed and below a term of the
fundamental sequence of `o_M(r)`). -/
theorem t2_qr_main (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M)
    (hUAB : UAB M) (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    {ρ σ : Valn} {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hGN : Good3 (TRIO.gexp M r L d0 d1 n) σ)
    (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hAbsC : BumpAbsC M (r + L) ρ)
    (hVNN : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL M i = Lc ++ [cs] → σ.v cs ≠ ρ.v cs →
      ∀ s y, ρ.o cs = psi s y z →
        lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
        VSmallV (σ.v cs))
    (hxcN : Counted (TRIO.gexp M r L d0 d1 n) r (r + L))
    (hseed : ∃ X K, σ.o r = psi (ρ.v r) X z ∧ Closed (ρ.v r) X ∧
      psi (ρ.v r) X z ≤ fs (ρ.o r) (natT K)) :
    isOT (root (TRIO.gexp M r L d0 d1 n) σ) = true ∧ root (TRIO.gexp M r L d0 d1 n) σ < root M ρ := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  set S : Bool → Nat → Prop := fun b i => b = true ∧ i = r with hS
  have hx : r + L + 1 = M.length := hlen
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hoff := t2_off hlen hL hp hd0e hn2 hXu hXb hrb he2r hIU hC hCN hRN
  have hiff : ∀ b i, i < r + L → (DepS M S b i ↔ DepX M (r + L) b i) :=
    fun b i hi => depS_iff_depX hlen hL hp hXu hXb hrb hi
  have hbumpN : ∀ i, i < r + L → bump N i = bump M i := fun i hi => by
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi]
  have hcl := fun i hi => CL_N2 hlen hL hp hd0e hn2 hXu hXb he2r hIU hxcN (i := i) hi
  have hupgN : ∀ i, i < r + L → upg N i = upg M i := by
    intro i hi
    rcases Nat.lt_or_ge (i + 1) (r + L) with h | h
    · exact upg_N2_pre hlen hL hp hd0e hn2 hXu hXb he2r h
    · have : i = r + L - 1 := by omega
      rw [this]; exact upg_N2_xm1 hlen hL hp hd0e (by omega) hn2 he2r (hXu _)
  have hdl := deps_lhd_gen (S := S) (bnd := r + L) hC hG hCN hGN hRM (by omega) (by rw [hlN]; omega)
    hF hVS hTD hKD hoff
    (by
      rintro b i ⟨hb, hi'⟩ _ _ _
      subst hb
      rw [hi']
      show Lhd z (σ.o r) (ρ.o r)
      obtain ⟨X, K, hXo, hcl', hle⟩ := hseed
      have hrM : r < M.length := by omega
      have hclr : CL M r ≠ [] := by
        intro h
        have : r + L ∈ CL M r := by
          unfold CL; rw [List.mem_filter]
          exact ⟨mem_children_iff.mpr ⟨by omega, hp⟩, by
            simpa using counted_r_x hlen hL hp hXu hXb⟩
        rw [h] at this; simp at this
      have hor := o_cl_eq hC hG hrM
      have harg := arg_lt_of_cl hC hG hrM hclr
      rw [hXo]
      rw [hor] at hle ⊢
      exact seed_closed (by rw [← hor]; exact hG.ot_o r hrM) (ne_of_gt harg) hcl' hle)
    (by
      intro c hc hd
      unfold CL; rw [List.filter_eq_nil_iff]
      intro d hdc
      simp only [decide_eq_true_eq]
      exact uncnt_of_depvX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hp hc
        ((hiff false c hc).mp hd) hdc)
    (by intro c hc h; rw [hcl c hc]; exact h)
    (by
      intro i hi hns hD hv
      have hir : i ≠ r := fun h => hns ⟨rfl, h⟩
      rcases hOS_t1X hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hp i hi ((hiff true i hi).mp hD) with
        ⟨hvX, _⟩ | ⟨_, Lp, c0, R, hch, hcb0, hcu0, hR, hLnd⟩
      · exact absurd ((hiff false i hi).mpr hvX) hv
      · cases hD with
        | seed h => exact absurd h hns
        | ov h => exact absurd h hv
        | @ochild _ c hc hcb hcu hdc =>
          have hcnt : Counted M i c := ⟨hcb, hcu⟩
          have hcR : ∀ d ∈ R, ¬ Counted M i d := fun d h hd => by
            rcases hR d h with h' | h'
            · exact hd.1 h'
            · exact hd.2 h'
          have hcl' := (mem_children hc).2
          have hcx : c < r + L := by
            by_contra h'
            have : c = r + L := by omega
            have hpc := (mem_children_iff.mp hc).2
            rw [this, hp] at hpc; cases hpc; exact hir rfl
          have hcc0 : c = c0 := by
            have hc' := hc
            rw [hch] at hc'
            rcases List.mem_append.mp hc' with h | h
            · exact absurd ((hiff true c hcx).mp hdc) (hLnd c h hcnt)
            · rcases List.mem_cons.mp h with h | h
              · exact h
              · exact absurd hcnt (hcR c h)
          rw [← hcc0] at hch
          obtain ⟨hLs, _⟩ := sib_order (children_sorted M i) hch
          have hclM : CL M i = Lp.filter (fun d => decide (Counted M i d)) ++ [c] := by
            unfold CL
            rw [hch, List.filter_append, List.filter_cons, if_pos (by simpa using hcnt)]
            have : R.filter (fun d => decide (Counted M i d)) = [] := by
              rw [List.filter_eq_nil_iff]; intro d hd; simpa using hcR d hd
            rw [this]
          refine ⟨_, c, hclM, by rw [hcl i hi, hclM], hdc, hcx, fun d hd => ?_⟩
          have hd' := List.mem_filter.mp hd
          have hdc' : Counted M i d := by simpa using hd'.2
          have := hLs d hd'.1
          exact ⟨fun h => hLnd d hd'.1 hdc' ((hiff true d (by omega)).mp h), by omega⟩)
    hVNN
    (by
      intro i hi _ hD
      have hDX := (hiff false i hi).mp hD
      obtain ⟨he1, hpnd, hcase⟩ := dv_shapeX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXb hp hi hDX
      refine ⟨entry_gexp_pre hlen (by omega) 1 hi, entry_gexp_pre hlen (by omega) 2 hi,
        par_gexp_pre hlen (by omega) 1 hi,
        fun m hm h => hpnd m hm ((hiff false m (by have := par_lt M 1 i m hm; omega)).mp h),
        hupgN i hi, fun k hk _ => ?_, fun h2 => ?_⟩
      · have hkl := upg_lt (by omega) hk
        have hkx : k ≠ r + L := fun h' => hXu i (h' ▸ hk)
        omega
      · rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j, k, hch, hjb, hchj, hdk, hKnd, hLnd⟩
        · exact absurd h2' h2
        · have hj : j ∈ children M i := by rw [hch]; simp
          have hjl := (mem_children hj).2
          have hjx : j < r + L := by
            by_contra h'
            have : j = r + L := by omega
            rw [this] at hjb; exact hXb i hjb
          have hk : k ∈ children M j := by rw [hchj]; simp
          have hkl := (mem_children hk).2
          have hkx : k < r + L := by
            by_contra h'
            have : k = r + L := by omega
            have hpk := (mem_children_iff.mp hk).2
            rw [this, hp] at hpk; cases hpk
            exact hrb i (mem_children_iff.mp hj).2 hjb
          have hKk : ∀ d ∈ Kb, d < k := (sib_order (children_sorted M j) (R := []) (by rw [hchj])).1
          have hLj : ∀ d ∈ Lb, d < j := (sib_order (children_sorted M i) (R := []) (by rw [hch])).1
          refine ⟨Lb, Kb, j, k, hch, by rw [children_N2 hlen hL hp hd0e (by omega) hn2 hi, hch], hjb,
            by rw [col_gexp_pre hlen (by omega) hjx, hbumpN i hi]; exact hjb, hchj,
            by rw [children_N2 hlen hL hp hd0e (by omega) hn2 hjx, hchj], hkx,
            entry_gexp_pre hlen (by omega) 1 hkx,
            fun d hd => ⟨fun h => hKnd d hd ((hiff true d (by have := hKk d hd; omega)).mp h),
              by have := hKk d hd; omega⟩,
            fun d hd e he h => (hLnd d hd e he).2 ((hiff true e (hLnd d hd e he).1).mp h),
            fun d hd => ?_⟩
          have hdj := hLj d hd
          apply bumpTerm_eq_of
          · rw [col_gexp_pre hlen (by omega) (by omega), hbumpN i hi]
          · intro _
            rw [children_N2 hlen hL hp hd0e (by omega) hn2 (by omega)]
            apply List.map_congr_left
            intro e he
            have hex := (hLnd d hd e he).1
            exact (hoff e hex).1 (fun h => (hLnd d hd e he).2 ((hiff true e hex).mp h)))
    (by
      intro i hi h1 h2
      apply hAbsC i h1 h2
      intro j hj hjb hjx
      exfalso
      have hxj : r + L ∈ children M j := by rw [hjx]; simp
      have hpx := (mem_children_iff.mp hxj).2
      rw [hp] at hpx; cases hpx
      exact hrb i (mem_children_iff.mp hj).2 hjb)
  apply root_N2 hlen hL hp hd0e hn2 hXu hXb hrb he2r hIU hR0 hR01 hR12 h00 hG hGN
  · intro i hi
    by_cases hd : DepS M S true i
    · exact le_of_lt (hdl true i hd hi).1
    · rw [(hoff i hi).1 hd]
  · intro R hR hRA _
    have hxn : ∀ p, ((∃ t, col M p = bump M t) ∨ isUpg M p = true) → p ≠ r + L := by
      intro p hp' e
      subst e
      rcases hp' with ⟨t, hb⟩ | hu
      · exact hXb t hb
      · rw [isUpg_x_false hXu] at hu; cases hu
    exact (hdl true R ((hiff true R hR).mpr (dep_anc_xG hUAT hZ2 hR12 hBE hx hxn hRA)) hR).1

end

end Ytosk
