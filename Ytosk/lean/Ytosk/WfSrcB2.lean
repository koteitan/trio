/-
**Part (b), outside sub-case** (2026-10-31, WfSrcB).

A changing bump grandchild `c` of `i` whose subtree does not contain `x − 1`:
the interval condition `ICC` (from `chg_struct`) gives the next column `c′` after `c`'s subtree,
with `upg(c′ − 1) = c′`. Its row-1 parent `m′ = P1(c′ − 1)` is a strict ancestor of `c`, not `i` or `j`
(row 2), so it is `m` or above `m`. If `m′ = m` then `e1 m < e1 c`.
-/
import Ytosk.WfSrcB1

namespace Ytosk.WfSrcB

open T

set_option linter.unusedSectionVars false

/-- **Outside sub-case**: either `c` is above `m`'s row, or the next column after `c`'s subtree is an
upgrade from its previous column whose row-1 parent is a strict ancestor of `m`. -/
theorem outside_shape {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {x m i j c : Nat} (hx : x + 1 = M.length)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT)
    (hmi : par M 0 i = some m) (h2 : entry M 2 i ≠ 0)
    (hj : j ∈ children M i) (hb : col M j = bump M i) (hc : c ∈ children M j) (hcx : c < x)
    (hce : τ.o c ≠ ρ.o c) (hnA : ¬ Anc0 M c (x - 1)) :
    entry M 1 m < entry M 1 c ∨
      ∃ c' m', NextC M c c' ∧ c' < x ∧ upg M (c' - 1) = some c' ∧ par M 1 (c' - 1) = some m' ∧
        Anc0 M m' m ∧ m' ≠ m := by
  have hch : ChgX M x true c := by
    by_contra hn
    exact hce ((chg_off hx hC hG hT hRT c hcx).1 hn)
  obtain ⟨c', hN, hc'x, hup, _⟩ :=
    (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hch).2 c hcx (Anc0.refl c) hnA
  obtain ⟨m', hm'1, hm'c, hcol, _⟩ := upg_spec hup
  have hcc' : c < c' := hN.1
  have hAc : Anc0 M c (c' - 1) := hN.2.1 (c' - 1) (by omega) (by omega)
  have hAm' : Anc0 M m' (c' - 1) := anc0_of_par M 1 m' (c' - 1) hm'1
  have hm'lt := par_lt M 1 (c' - 1) m' hm'1
  -- m' is a strict ancestor of c
  have hm'c : Anc0 M m' c ∧ m' ≠ c := by
    rcases anc0_total hAm' hAc with h | h
    · refine ⟨h, ?_⟩
      intro he
      subst he
      exact hN.2.2 (anc0_of_par M 1 m' c' hm'c)
    · exfalso
      exact hN.2.2 (h.trans (anc0_of_par M 1 m' c' hm'c))
  have he2 : entry M 2 m' = 0 := by
    have h1 : entry M 2 c' = entry M 2 m' + 1 := by
      change (col M c').2.2 = _
      rw [hcol]
    have := S.z2 c'
    omega
  have hpj : par M 0 j = some i := (mem_children_iff.mp hj).2
  have hpc : par M 0 c = some j := (mem_children_iff.mp hc).2
  have hAj : Anc0 M m' j := anc0_par hm'c.1 hm'c.2 hpc
  have hmj : m' ≠ j := by
    intro he
    rw [he, e2_of_col hb] at he2
    omega
  have hAi : Anc0 M m' i := anc0_par hAj hmj hpj
  have hmi' : m' ≠ i := by
    intro he
    rw [he] at he2
    exact h2 he2
  have hAm : Anc0 M m' m := anc0_par hAi hmi' hmi
  by_cases hme : m' = m
  · left
    subst hme
    have h1 := par1_entry_lt hm'1
    have h2' := par1_between hm'1 c hAc (by have := hm'c.1.le; have := hm'c.2; omega)
    omega
  · right
    exact ⟨c', m', hN, hc'x, hup, hm'1, hAm, hme⟩

/-- **Residual (b, non-lost), narrowed**: `SrcBNonlost` with the outside sub-case replaced by its
witness: the next column `c′` after `c`'s subtree is the upgrade of `c′ − 1`, whose row-1 parent is a strict
ancestor of `m`. -/
def SrcBNonlost2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → ∀ x, x + 1 = M.length →
    par M 2 x = some (x - 1) → par M 0 x = some (x - 1) → par M 1 x = some (x - 1) →
    ∀ τ, Cons (M.take x) τ → ∀ i m j c, i < x → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      par M 0 i = some m → par M 1 i = some m → j ∈ children M i → col M j = bump M i →
      c ∈ children M j → c < x - 1 → τ.o c ≠ ρ.o c →
      (∃ B, children (M.take x) i = B ++ [j] ∧
        ∀ d ∈ B, bumpTerm (M.take x) τ i d = bumpTerm M ρ i d) →
      (∃ K, children M j = K ++ [c] ∧ ∀ d ∈ K, τ.o d = ρ.o d ∧ entry M 1 d < entry M 1 m) →
      entry M 1 c ≤ entry M 1 m → (Anc0 M c (x - 1) → entry M 1 c < entry M 1 m) →
      (¬ Anc0 M c (x - 1) → ∃ c' m', NextC M c c' ∧ c' < x ∧ upg M (c' - 1) = some c' ∧
        par M 1 (c' - 1) = some m' ∧ Anc0 M m' m ∧ m' ≠ m) →
      ¬ WfT2Abs.DropFail M ρ τ x i

/-- **Bridge**: the narrowed residual gives `SrcBNonlost`. -/
theorem srcBNonlost_of_2 (h : SrcBNonlost2) : SrcBNonlost := by
  intro M ρ rk C hB x hx hr hp0 hp1 τ hT i m j c hi h1 h2 hmi hm1 hj hb hc hcx hce hBr hK hrow hdesc
  have hRT : Rk (M.take x) rk := rk_take (by omega) C.I.rank
    (by have := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
        simpa only [show M.length - 1 = x from by omega] using this)
  refine h M ρ rk C hB x hx hr hp0 hp1 τ hT i m j c hi h1 h2 hmi hm1 hj hb hc hcx hce hBr hK hrow hdesc ?_
  intro hnA
  rcases outside_shape C.S C.I.cons C.I.good hx hT hRT hmi h2 hj hb hc (by omega) hce hnA with hh | hw
  · omega
  · exact hw

end Ytosk.WfSrcB
