/-
**評価が値を持つ（循環しない）こと: SRO 以外の標準形はすべて順位を持つ。**

部品はすべて構造の不変条件だけで証明済み: 基底 SRO[n]（brk_rk）、接頭辞（rk_take_all）、
t = 0（rk_N0）、t = 1（rk_N_t1、構造の仮定は hpath_of_par1・hxnb_t1・hiu_t1・hiux_t1・hnd_t1）、
t = 2（rk_expand_t2）。ここではそれを標準形についての帰納法にまとめる。
-/
import Ytosk.V3IndV
import Ytosk.V3BaseInd
import Ytosk.V3ExpT2I

namespace Ytosk

/-- **`t = 1`: every `M[n]` (`n ≥ 1`) has a ranking**, by induction on `n` from `M[1] = M.take x`. -/
theorem rk_gexp_t1 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    {rkM : Bool → Nat → Nat} (hRM : Rk M rkM) :
    ∀ n, 1 ≤ n → ∃ rk, Rk (TRIO.gexp M r L d0 0 n) rk := by
  have hrx : r ≠ r + L := by omega
  have hpath := hpath_of_par1 h1 hA hrx
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      refine ⟨rkM, ?_⟩
      rw [gexp_one_eq hlen]
      exact rk_take (by omega) hRM (hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT)
    · obtain ⟨rkP, hRP⟩ := ih hm
      have hn2 : 2 ≤ m + 1 := by omega
      have hRP' : Rk (TRIO.gexp M r L d0 0 (m + 1 - 1)) rkP := by
        rw [show m + 1 - 1 = m by omega]; exact hRP
      exact ⟨_, rk_N_t1 hlen hL hA hd0e hn2 hpath hx2
        (hxnb_t1 hlen hL hA hd0e hZ2 hZ1 h1 (m + 1) hn2) (hZ2 r)
        (hiu_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn2) (hiux_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn2)
        (hnd_t1 hlen hL hA hd0e hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 (m + 1) hn2) hRM hRP'⟩

/-- A matrix with a nonzero last column has at least two columns (the first is `(0,0,0)`). -/
theorem two_le_len_of_nonzero {M : Mat} (h00 : entry M 0 0 = 0) (hR01 : R01 M) (hR12 : R12 M)
    (hne : M ≠ []) (hz : col M (M.length - 1) ≠ (0, 0, 0)) : 2 ≤ M.length := by
  have h1 : 1 ≤ M.length := by
    cases M with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  by_contra h
  have hl : M.length - 1 = 0 := by omega
  apply hz
  rw [hl]
  have e1 := hR01 0 h00
  exact (col_zero_iff M 0).mpr ⟨h00, e1, hR12 0 e1⟩

/-- **Every standard matrix other than SRO has a ranking**, so the evaluator's equations have a
solution: the value is defined (no cycle). -/
theorem rk_std {M : Mat} (hM : Std M) (hS : M ≠ SRO) : ∃ rk, Rk M rk := by
  induction hM with
  | sro => exact absurd rfl hS
  | @exp M n hM ih =>
    by_cases hMS : M = SRO
    · subst hMS
      rw [expand_SRO_eq]
      exact ⟨_, brk_rk (L := 1 + 3 * n) (le_refl _)⟩
    obtain ⟨rkM, hRM⟩ := ih hMS
    obtain ⟨hX, hJ⟩ := sInvXJ_std hM hMS
    have S := hX.toSInv
    by_cases hE : M = []
    · subst hE
      exact ⟨rkM, fun i hi => by simp [expand] at hi⟩
    have hlen1 : 1 ≤ M.length := by
      cases M with
      | nil => exact absurd rfl hE
      | cons _ _ => simp
    have htake : ∀ j, j ≤ M.length → ∃ rk, Rk (M.take j) rk :=
      fun j hj => ⟨rkM, rk_take_all hRM S.r0p S.z2 S.sibDec S.z1c S.uab j hj⟩
    by_cases hz : col M (M.length - 1) = (0, 0, 0)
    · rw [expand_zero_last hE hz n]; exact htake _ (by omega)
    rcases Nat.lt_or_ge n 2 with hn | hn
    · rcases Nat.lt_or_ge n 1 with hn0 | hn1
      · obtain rfl : n = 0 := by omega
        obtain ⟨j, hj, he⟩ := expand_zero_take hE
        rw [he]; exact htake j (by omega)
      · obtain rfl : n = 1 := by omega
        rw [expand_one]; exact htake _ (by omega)
    have hlen2 := two_le_len_of_nonzero S.e00 S.r01 S.r12 hE hz
    have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
        TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
    obtain ⟨r, hr⟩ := parLast_of S.e00 S.r01 S.r12 hz
    have hsrow : TRIO.srow M (M.length - 1) = 0 ∨ TRIO.srow M (M.length - 1) = 1 ∨
        TRIO.srow M (M.length - 1) = 2 := by
      unfold TRIO.srow; split_ifs <;> simp
    rcases hsrow with h0 | h1t | h2
    · -- `t = 0`
      have he1 : entry M 1 (M.length - 1) = 0 := by
        unfold TRIO.srow at h0
        by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
        · rw [if_pos ha] at h0; cases h0
        · rw [if_neg ha] at h0
          by_cases hb : 0 < TRIO.entry M 1 (M.length - 1)
          · rw [if_pos hb] at h0; cases h0
          · show TRIO.entry M 1 (M.length - 1) = 0; omega
      have hx2 : entry M 2 (M.length - 1) = 0 := S.r12 _ he1
      rw [h0] at hr
      have hexp := expand_eq_gexp_t0 M n hlen2 hzT (by rw [h0]; exact hr) h0
      have hrx : r < M.length - 1 := par_lt M 0 _ r hr
      obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
      rw [hL] at hexp hr hx2
      simp only [Nat.add_sub_cancel_left] at hexp
      rw [hexp]
      exact ⟨_, rk_N0 (by omega) (by omega) hr (show 1 ≤ n by omega) S.r0p S.z2 hx2 hn hRM⟩
    · -- `t = 1`
      have hx2 : entry M 2 (M.length - 1) = 0 := by
        unfold TRIO.srow at h1t
        by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
        · rw [if_pos ha] at h1t; cases h1t
        · show TRIO.entry M 2 (M.length - 1) = 0; omega
      rw [h1t] at hr
      have hexp := expand_eq_gexp_t1 M n hlen2 hzT (by rw [h1t]; exact hr) h1t
      have hrx : r < M.length - 1 := par_lt M 1 _ r hr
      obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
      rw [hL] at hexp hr hx2
      simp only [Nat.add_sub_cancel_left] at hexp
      have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
      have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
        have := anc0_e0_lt hA (by omega); omega
      rw [hexp]
      exact rk_gexp_t1 (by omega) (by omega) hA hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hr hx2 hRM
        n (by omega)
    · -- `t = 2`
      exact rk_expand_t2 hX hJ hz h2 hRM n (by omega)

/-- **The value of every standard matrix other than SRO is defined.** -/
theorem val_std {M : Mat} (hM : Std M) (hS : M ≠ SRO) : ∃ t, Val M t := by
  obtain ⟨rk, hR⟩ := rk_std hM hS
  exact ⟨_, val_of_rk hR⟩

end Ytosk
