/-
**WfCofC4 (2026-11-01): `HRootKeep2` is a theorem.**

For `t = 2` (`lastTy A = 2`, bad root `r = P_2(x)`), `A[n] = gexp A r L d0 d1 n` with `d0 = e0(x) − e0(r) > 0`:
- `roots_N_d1` : `A[n]` has the roots of `A` (the copies ascend in row 0; `roots_N_t1` with `e0_gexp_d1`).
- `vals_before_root` : if `N.take K = A.take K` and `Rt < K` is a root column, then the values of `N` and `A`
  agree before `Rt` (both are the values of `A.take Rt`: `take_root_agree`, `rk_take_root`, `cons_unique`).
- `hRootKeep2 : HRootKeep2`, and `evalFSNZ2_of_C4` / `surj_of_C4` without it.
-/
import Ytosk.WfCofC3
import Ytosk.V3ExpT2C
import Ytosk.V3N0T1

namespace Ytosk.WfCofC4

open T Ytosk Ytosk.WfCofH2 Ytosk.WfCofH3 Ytosk.WfCofC1 Ytosk.WfCofC3

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **The roots of `M[n]` are those of `M`** (any `d1`). -/
theorem roots_N_d1 : roots (TRIO.gexp M r L d0 d1 n) = roots M := by
  rw [← roots_N_t1 hlen hL hA hd0e hn]
  unfold roots
  rw [TRIO.gexp_length hlen, TRIO.gexp_length hlen]
  apply List.filter_congr
  intro i hi
  have hiN := List.mem_range.mp hi
  rcases Nat.lt_or_ge i (r + L) with h | h
  · rw [col_gexp_pre hlen (by omega) h, col_gexp_pre hlen (by omega) h]
  · -- both columns have a positive row-0 entry
    have hpos : 0 < entry (TRIO.gexp M r L d0 0 n) 0 i := by
      have hex : 0 < entry M 0 (r + L) := by
        have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
      have hd0 : 0 < d0 := by
        have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · subst heq; rw [e0_gexp_x hlen hL hd0e hn]; exact hex
      · rw [show i = r + L + (i - (r + L)) by omega,
          e0_copy (d0 := d0) hlen hL hn (show i - (r + L) < (n - 1) * L by
            have : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
            omega)]
        omega
    have hpos' : 0 < entry (TRIO.gexp M r L d0 d1 n) 0 i := by rw [e0_gexp_d1 hlen]; exact hpos
    have h1 : col (TRIO.gexp M r L d0 d1 n) i ≠ (0, 0, 0) := by
      intro hc; have : entry (TRIO.gexp M r L d0 d1 n) 0 i = 0 := by unfold entry; unfold col at hc; rw [hc]; rfl
      omega
    have h2 : col (TRIO.gexp M r L d0 0 n) i ≠ (0, 0, 0) := by
      intro hc; have : entry (TRIO.gexp M r L d0 0 n) 0 i = 0 := by unfold entry; unfold col at hc; rw [hc]; rfl
      omega
    simp [h1, h2]

end

/-- **Values before a root column of a common prefix agree.** -/
theorem vals_before_root {A N : Mat} {K Rt : Nat} (hK : N.take K = A.take K) (hRK : Rt < K)
    (hKA : K ≤ A.length) (hKN : K ≤ N.length) (hR0 : col A Rt = (0, 0, 0))
    {ρ σ : Valn} {rkA rkN : Bool → Nat → Nat} (hC : Cons A ρ) (hR : Rk A rkA) (hCN : Cons N σ)
    (hRN : Rk N rkN) : ∀ i, i < Rt → σ.o i = ρ.o i ∧ σ.v i = ρ.v i := by
  have hRl : Rt < A.length := by omega
  have hRlN : Rt < N.length := by omega
  have htk : N.take Rt = A.take Rt := by
    have h := congrArg (fun l => List.take Rt l) hK
    simp only [List.take_take] at h
    simpa [Nat.min_eq_left hRK.le, Nat.min_eq_right hRK.le] using h
  have hcolN : col N Rt = (0, 0, 0) := by
    have h1 : col N Rt = col (N.take K) Rt := (col_take N hRK).symm
    rw [h1, hK, col_take A hRK, hR0]
  have hRkA := rk_take_root hR0 hRl hR
  have hRkN := rk_take_root hcolN hRlN hRN
  have hCA' := cons_of_rk hRkA
  have hCN' := cons_of_rk hRkN
  have hagA := take_root_agree hR0 hRl hC hCA' hRkA
  have hagN := take_root_agree hcolN hRlN hCN hCN' hRkN
  rw [htk] at hCN' hRkN hagN
  have hu := cons_unique hCN' hCA' hRkA
  intro i hi
  have hlt : i < (A.take Rt).length := by rw [List.length_take]; omega
  obtain ⟨hu1, hu2⟩ := hu i hlt
  obtain ⟨hA1, hA2⟩ := hagA i hi
  obtain ⟨hN1, hN2⟩ := hagN i hi
  exact ⟨by rw [← hN1, hu1, hA1], by rw [← hN2, hu2, hA2]⟩

/-- **`HRootKeep2`** holds. -/
theorem hRootKeep2 : HRootKeep2 := by
  intro A hAs hS hNE hz ht tA _ a b _ ρA rkA hCA hRA k σ rkN hCN hRN
  have hpos : 0 < A.length := List.length_pos_of_ne_nil hNE
  obtain ⟨r, hr0⟩ := parLast_of (sInv_std hAs hS).e00 (sInv_std hAs hS).r01 (sInv_std hAs hS).r12 hz
  have hsrow : TRIO.srow A (A.length - 1) = 2 := by rw [← WfCofH1.lastTy_eq]; exact ht
  have hr2 : par A 2 (A.length - 1) = some r := by rw [hsrow] at hr0; exact hr0
  have hrx : r < A.length - 1 := par_lt A 2 _ r hr2
  obtain ⟨L, hLd⟩ : ∃ L, L = A.length - 1 - r := ⟨_, rfl⟩
  have hlen : r + L + 1 = A.length := by omega
  have hL : 0 < L := by omega
  have hxe : A.length - 1 = r + L := by omega
  have hA0 : Anc0 A r (r + L) := by rw [← hxe]; exact anc0_of_par A 2 r _ hr2
  obtain ⟨d0, hd0d⟩ : ∃ d0, d0 = TRIO.entry A 0 (A.length - 1) - TRIO.entry A 0 r := ⟨_, rfl⟩
  have hd0e : entry A 0 (r + L) = entry A 0 r + d0 := by
    have := anc0_interval hA0 (r + L) (by omega) (le_refl _)
    rw [hd0d, hxe]; show entry A 0 (r + L) = entry A 0 r + (entry A 0 (r + L) - entry A 0 r); omega
  have hzT : ¬ (TRIO.entry A 0 (A.length - 1) = 0 ∧ TRIO.entry A 1 (A.length - 1) = 0 ∧
      TRIO.entry A 2 (A.length - 1) = 0) := fun h => hz ((col_zero_iff A _).mpr h)
  have hexp := expand_eq_gexp A (k + 2) (by omega) hzT hr0
  rw [hsrow, if_pos (by omega), if_pos (by omega), ← hLd, ← hd0d] at hexp
  set d1 := (if 1 < 2 then TRIO.entry A 1 (A.length - 1) - TRIO.entry A 1 r else 0) with hd1
  refine ⟨?_, ?_⟩
  · rw [hexp]; exact roots_N_d1 hlen hL hA0 hd0e (by omega)
  · intro Rt hRA0 hR0 c _ hc
    have hRt : Rt ≤ A.length - 1 := hRA0.le
    have hRtK : Rt < r + L := by
      rcases Nat.lt_or_ge Rt (r + L) with h | h
      · exact h
      · exfalso
        have hRx : Rt = r + L := by omega
        apply hz; rw [hxe, ← hRx]; exact hR0
    rw [hexp] at hCN hRN
    have hK := gexp_take_x (d0 := d0) (d1 := TRIO.entry A 1 (A.length - 1) - TRIO.entry A 1 r)
      (m := k + 2) hlen (by omega)
    have hlN := TRIO.gexp_length (M := A) (j0 := r) (Lb := L) (d0 := d0)
      (d1 := TRIO.entry A 1 (A.length - 1) - TRIO.entry A 1 r) (n := k + 2) hlen
    exact (vals_before_root hK hRtK (by omega) (by rw [hlN]; have : L ≤ (k + 2) * L := Nat.le_mul_of_pos_left L (by omega); omega) hR0 hCA hRA hCN hRN c hc).1

/-- **`EvalFSNZ 2`** with `HRootKeep2` discharged. -/
theorem evalFSNZ2_of_C4 (hD : Desc3) (hG : HGood3) (hT : HDiagT1) (hE : HEngPath) (hRS : HRootSP)
    (hDL : WfCofC2.HDiagLoc) (hDS : WfCofC2.HDiagStep) (hP : HCntPath0)
    (h1 : HNoSucc1) (hC : HCntRoot2) : EvalFSNZ 2 :=
  evalFSNZ2_of_C3 hD hG hT hE hRS hDL hDS hP h1 hRootKeep2 hC

/-- **Surjectivity** with the same hypotheses. -/
theorem surj_of_C4 (hD : Desc3) (hG : HGood3) (hT : HDiagT1) (hE : HEngPath) (hRS : HRootSP)
    (hDL : WfCofC2.HDiagLoc) (hDS : WfCofC2.HDiagStep) (hP : HCntPath0)
    (h1 : HNoSucc1) (hC : HCntRoot2) {t : T}
    (hot : isOT t = true) {n : Nat} {tN : T} (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ hD (evalFSNZ2_of_C4 hD hG hT hE hRS hDL hDS hP h1 hC) hot hvN hlt

end Ytosk.WfCofC4
