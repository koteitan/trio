/-
**構造の不変条件は展開で保たれる**（`SInv`、すべての t・すべての n）。

- 列ごとの性質（R0P・Z2・R12・R01・左上が 0）は trio 本体の展開の補題（`r1ok_oper`・`z2ok_oper`・
  `noninc_oper`・`z0ok_oper`）から出す。R0P には r1ok の残りの成分「行 1 は行 0 の親より高々 1 大きい」
  （`R1S`）が要るので、補助の不変条件 `SInvX` に入れる。
- 実測（SRO からの乱択展開、長さ ≤ 20、異なる行列 69523 個）: SInv の 10 個の性質と R1S は例外 0。
-/
import Ytosk.V3InvTake2

namespace Ytosk

open T

/-- Row 1 rises by at most one from the row-0 parent. -/
def R1S (M : Mat) : Prop := ∀ c p, par M 0 c = some p → entry M 1 c ≤ entry M 1 p + 1

/-! ## 短い行列 -/

theorem par_zero_none (M : Mat) : ∀ t, par M t 0 = none
  | 0 => by simp [par, prev, climb]
  | t + 1 => by simp only [par]; rw [par_zero_none M t]; simp [climb]

theorem expand_short {M : Mat} (h : M.length < 2) (n : Nat) : expand M n = [] := by
  cases M with
  | nil => rfl
  | cons c l =>
    cases l with
    | cons _ _ => simp at h; omega
    | nil =>
      simp only [expand]
      split
      · rfl
      · simp only [List.length_singleton, Nat.sub_self]
        rw [par_zero_none]
        rfl

/-! ## 展開の場合分け -/

/-- **The expansion is a prefix, or a `gexp`.** -/
theorem expand_cases (M : Mat) (n : Nat) (hM : 2 ≤ M.length) :
    expand M n = M.take (M.length - 1) ∨
    ∃ r, par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r ∧
      expand M n = TRIO.gexp M r (M.length - 1 - r)
        (if 0 < TRIO.srow M (M.length - 1) then TRIO.entry M 0 (M.length - 1) - TRIO.entry M 0 r else 0)
        (if 1 < TRIO.srow M (M.length - 1) then TRIO.entry M 1 (M.length - 1) - TRIO.entry M 1 r else 0)
        n := by
  have hne : M ≠ [] := by intro h; subst h; simp at hM
  by_cases hz : TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0
  · left
    exact expand_zero_col (by omega) ((col_zero_iff M _).mpr hz) n
  · cases hp : par M (TRIO.srow M (M.length - 1)) (M.length - 1) with
    | some r => exact Or.inr ⟨r, rfl, expand_eq_gexp M n hM hz hp⟩
    | none =>
      left
      obtain ⟨c, l, rfl⟩ := List.exists_cons_of_ne_nil hne
      simp only [expand]
      rw [if_neg (fun h => hz ((col_zero_iff _ _).mp h))]
      have ht : (if entry (c :: l) 2 ((c :: l).length - 1) > 0 then 2
          else if entry (c :: l) 1 ((c :: l).length - 1) > 0 then 1 else 0) =
          TRIO.srow (c :: l) ((c :: l).length - 1) := rfl
      simp only at ht ⊢
      rw [ht, hp]

/-! ## 列ごとの性質: trio 本体の不変条件との橋渡し -/

theorem getD_out {M : Mat} {j : Nat} (h : M.length ≤ j) : M.getD j (0, 0, 0) = (0, 0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem entry0_getD (M : Mat) (j : Nat) : entry M 0 j = (M.getD j (0, 0, 0)).1 := rfl
theorem entry1_getD (M : Mat) (j : Nat) : entry M 1 j = (M.getD j (0, 0, 0)).2.1 := rfl
theorem entry2_getD (M : Mat) (j : Nat) : entry M 2 j = (M.getD j (0, 0, 0)).2.2 := rfl

theorem z2ok_of {M : Mat} (h : Z2 M) : TRIO.z2ok M := fun j _ => by
  have := h j; rw [entry2_getD] at this; exact this

theorem Z2_of_z2ok {M : Mat} (h : TRIO.z2ok M) : Z2 M := by
  intro j
  rw [entry2_getD]
  rcases Nat.lt_or_ge j M.length with hj | hj
  · exact h j hj
  · rw [getD_out hj]; simp

theorem noninc_of {M : Mat} (hZ2 : Z2 M) (hR12 : R12 M) : TRIO.noninc M := fun j _ => by
  have h2 := hZ2 j; have h12 := hR12 j
  rw [entry2_getD] at h2 h12; rw [entry1_getD] at h12
  by_cases h : (M.getD j (0, 0, 0)).2.1 = 0
  · rw [h12 h, h]
  · omega

theorem R12_of_noninc {M : Mat} (h : TRIO.noninc M) : R12 M := by
  intro j hj
  rw [entry2_getD]; rw [entry1_getD] at hj
  rcases Nat.lt_or_ge j M.length with hl | hl
  · have := h j hl; omega
  · rw [getD_out hl]

theorem z0ok_of {M : Mat} (hR01 : R01 M) (hR12 : R12 M) : TRIO.z0ok M := fun j _ h0 => by
  have h1 := hR01 j (by rw [entry0_getD]; exact h0)
  exact ⟨by rw [← entry1_getD]; exact h1, by rw [← entry2_getD]; exact hR12 j h1⟩

theorem R01_of_z0ok {M : Mat} (h : TRIO.z0ok M) : R01 M := by
  intro j hj
  rw [entry1_getD]; rw [entry0_getD] at hj
  rcases Nat.lt_or_ge j M.length with hl | hl
  · exact (h j hl hj).1
  · rw [getD_out hl]

theorem r1ok_of {M : Mat} (h00 : entry M 0 0 = 0) (hR0 : R0P M) (hR1 : R1S M) : TRIO.r1ok M := by
  intro j hj hpos
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; rw [← entry0_getD] at hpos; omega
    · exact h
  obtain ⟨p, hp⟩ := par0_some_of (M := M) hj0 (by rw [h00, entry0_getD]; exact hpos)
  obtain ⟨hpj, hlt, hbet⟩ := (par0_spec M).mp hp
  refine ⟨p, hpj, ?_, fun l h1 h2 => ?_, ?_⟩
  · have := hR0 j p hp; rw [entry0_getD, entry0_getD] at this; omega
  · have := hbet l h1 h2; rw [entry0_getD, entry0_getD] at this; exact this
  · have := hR1 j p hp; rw [entry1_getD, entry1_getD] at this; exact this

theorem R0P_R1S_of_r1ok {M : Mat} (h : TRIO.r1ok M) : R0P M ∧ R1S M := by
  have key : ∀ c p, par M 0 c = some p → entry M 0 c = entry M 0 p + 1 ∧ entry M 1 c ≤ entry M 1 p + 1 := by
    intro c p hp
    obtain ⟨hpc, hlt, _⟩ := (par0_spec M).mp hp
    have hc : c < M.length := by
      by_contra hc
      rw [entry0_getD M c, getD_out (by omega)] at hlt; simp at hlt
    obtain ⟨k, hkc, hk1, hkbet, hk2⟩ := h c hc (by rw [← entry0_getD]; omega)
    have hpk : par M 0 c = some k := (par0_spec M).mpr ⟨hkc, by rw [entry0_getD, entry0_getD]; omega,
      fun l h1 h2 => by rw [entry0_getD, entry0_getD]; exact hkbet l h1 h2⟩
    rw [hp] at hpk; cases hpk
    exact ⟨by rw [entry0_getD, entry0_getD]; omega, by rw [entry1_getD, entry1_getD]; exact hk2⟩
  exact ⟨fun c p hp => (key c p hp).1, fun c p hp => (key c p hp).2⟩

/-! ## 左上が 0 -/

theorem e00_expand {M : Mat} (h00 : entry M 0 0 = 0) (n : Nat) : entry (expand M n) 0 0 = 0 := by
  by_cases hM : M.length < 2
  · rw [expand_short hM]; rfl
  rcases expand_cases M n (by omega) with h | ⟨r, hr, h⟩
  · rw [h]; exact e00_take h00 _
  · rw [h]
    have hrx := par_lt M _ _ _ hr
    have hlen : r + (M.length - 1 - r) + 1 = M.length := by omega
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hr0
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; unfold TRIO.gexp; simp; rfl
      · have := TRIO.gexp_getD_mir (M := M)
          (d0 := if 0 < TRIO.srow M (M.length - 1) then TRIO.entry M 0 (M.length - 1) - TRIO.entry M 0 0 else 0)
          (d1 := if 1 < TRIO.srow M (M.length - 1) then TRIO.entry M 1 (M.length - 1) - TRIO.entry M 1 0 else 0)
          (k := 0) (q := 0) hlen hn (by omega)
        rw [entry0_getD]
        simp only [Nat.zero_mul, Nat.add_zero] at this
        rw [this]; simpa using h00
    · rw [entry0_getD, TRIO.gexp_getD_low hlen hr0, ← entry0_getD]; exact h00

/-! ## 展開で保たれる: 列ごとの性質 -/

theorem expand_oper {M : Mat} (hM : 2 ≤ M.length) (n : Nat) : expand M n = TRIO.oper M n :=
  expand_eq_oper M n hM

theorem Z2_expand {M : Mat} (h : Z2 M) (n : Nat) : Z2 (expand M n) := by
  by_cases hM : M.length < 2
  · rw [expand_short hM]; intro j; simp [entry]
  rw [expand_oper (by omega)]; exact Z2_of_z2ok (TRIO.z2ok_oper (z2ok_of h))

theorem R12_expand {M : Mat} (hZ2 : Z2 M) (h : R12 M) (n : Nat) : R12 (expand M n) := by
  by_cases hM : M.length < 2
  · rw [expand_short hM]; intro j _; rfl
  rw [expand_oper (by omega)]; exact R12_of_noninc (TRIO.noninc_oper (noninc_of hZ2 h))

theorem R01_expand {M : Mat} (hR12 : R12 M) (h : R01 M) (n : Nat) : R01 (expand M n) := by
  by_cases hM : M.length < 2
  · rw [expand_short hM]; intro j _; rfl
  rw [expand_oper (by omega)]; exact R01_of_z0ok (TRIO.z0ok_oper (z0ok_of h hR12))

theorem R0P_R1S_expand {M : Mat} (h00 : entry M 0 0 = 0) (hR0 : R0P M) (hR1 : R1S M) (n : Nat) :
    R0P (expand M n) ∧ R1S (expand M n) := by
  by_cases hM : M.length < 2
  · rw [expand_short hM]
    exact ⟨fun c p hp => by simp [par0_spec, entry] at hp,
      fun c p hp => by simp [par0_spec, entry] at hp⟩
  rw [expand_oper (by omega)]; exact R0P_R1S_of_r1ok (TRIO.r1ok_oper (r1ok_of h00 hR0 hR1))

end Ytosk
