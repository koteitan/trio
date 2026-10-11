/-
**t = 0 の M[n] で「正の段の隙間なし」NoGapP が保たれる。**

N = M[n] = gexp M r L 0 0 n の値は目標の割り当て tauN（r より前は M、中間の写しは M、最後の写しは
M′ = M.take x の値、列は phi0 で対応）。行 1 の子 c を持つ列 p について:
- c の対応する列 r + q（または c 自身）は M で x より前にあり、行 1 の親は p の対応する列（`par1_copy0`）。
- p < r なら v_N(p) = v_M(p)（変わる v の列は x より前に行 1 の子を持たない、`chg_struct`）。
- p ≥ r なら v_N(p) は M か M′ の対応する列の v で、その列は行 1 の子を持つ。
-/
import Ytosk.V3PhiGap
import Ytosk.V3T0V

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB

/-- A column of `M` before `r` with a row-1 child below `x` keeps its `v` outside `DepX`. -/
theorem not_depX_of_par1 {p d : Nat} (hd : d < r + L) (hpd : par M 1 d = some p) :
    ¬ DepX M (r + L) false p := by
  intro hD
  have hpl := par_lt M 1 d p hpd
  exact ((chg_struct (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB
    (depX_chgX hD)).1 rfl (by omega)).2.2 d hd hpd

/-- **Any `VP Q` of the t = 0 expansion.** `hlow` is the agreement before `r` outside `DepX` (`hoffD` in
`V3T0M`), `hσBv` the agreement with `tauN` from `r` on. -/
theorem vP_t0 {Q : T → Prop} {ρ ρ' σ : Valn} {oMid : T} (hN : VP Q M ρ) (hN' : VP Q (M.take (r + L)) ρ')
    (hlow : ∀ i, i < r → ¬ DepX M (r + L) false i → σ.v i = ρ.v i)
    (hσBv : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length → σ.v i = (tauN r L n ρ ρ' oMid).v i) :
    VP Q (TRIO.gexp M r L 0 0 n) σ := by
  intro c p hc hpc
  rw [lenN0 hlen hn] at hc
  -- the column of `M` copied by `c` and its row-1 parent there
  obtain ⟨d, a, hd, hda, hpa⟩ : ∃ d a, d < r + L ∧ par M 1 d = some a ∧
      ((a < r ∧ p = a) ∨ (r ≤ a ∧ ∃ k, k < n ∧ p = a + k * L)) := by
    rcases Nat.lt_or_ge c r with hcr | hcr
    · rw [par_gexp_pre hlen hn 1 (by omega)] at hpc
      have := par_lt M 1 c p hpc
      exact ⟨c, p, by omega, hpc, Or.inl ⟨by omega, rfl⟩⟩
    · obtain ⟨k, q, hk, hq, rfl⟩ : ∃ k q, k < n ∧ q < L ∧ c = r + (k * L + q) := by
        refine ⟨(c - r) / L, (c - r) % L, ?_, Nat.mod_lt _ hL, ?_⟩
        · rw [Nat.div_lt_iff_lt_mul hL]; omega
        · have := Nat.div_add_mod (c - r) L; rw [Nat.mul_comm] at this; omega
      rw [par1_copy0 hlen hL hp hn hk hq] at hpc
      cases ha : par M 1 (r + q) with
      | none => rw [ha] at hpc; cases hpc
      | some a =>
        rw [ha] at hpc
        simp only [Option.map_some, Option.some.injEq] at hpc
        unfold shk at hpc
        by_cases hra : r ≤ a
        · rw [if_pos hra] at hpc
          exact ⟨r + q, a, by omega, ha, Or.inr ⟨hra, k, hk, hpc.symm⟩⟩
        · rw [if_neg hra] at hpc
          exact ⟨r + q, a, by omega, ha, Or.inl ⟨by omega, hpc.symm⟩⟩
  have hdM : d < M.length := by omega
  rcases hpa with ⟨har, rfl⟩ | ⟨hra, k, hk, rfl⟩
  · rw [hlow p har (not_depX_of_par1 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hd hda)]
    exact hN d p hdM hda
  · have hal : a < r + L := by have := par_lt M 1 d a hda; omega
    have hkn : (k + 1) * L ≤ n * L := Nat.mul_le_mul_right L (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hkn
    rw [hσBv _ (by omega) (by rw [lenN0 hlen hn]; omega)]
    have hphi : phi0 r L (a + k * L) = a := by
      have := phi0_copy (r := r) (L := L) (k := k) (q := a - r) (by omega)
      rw [show r + (k * L + (a - r)) = a + k * L by omega, show r + (a - r) = a by omega] at this
      exact this
    simp only [tauN]
    rw [if_neg (by omega), hphi]
    split
    · exact hN d a hdM hda
    · exact hN' d a (by rw [List.length_take]; omega) (by rw [par_take M 1 d hd]; exact hda)

/-- **`NoGapP` of the t = 0 expansion.** -/
theorem noGapP_t0 {ρ ρ' σ : Valn} {oMid : T} (hN : NoGapP M ρ) (hN' : NoGapP (M.take (r + L)) ρ')
    (hlow : ∀ i, i < r → ¬ DepX M (r + L) false i → σ.v i = ρ.v i)
    (hσBv : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length → σ.v i = (tauN r L n ρ ρ' oMid).v i) :
    NoGapP (TRIO.gexp M r L 0 0 n) σ :=
  vP_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hN hN' hlow hσBv

end

end Ytosk
