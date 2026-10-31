/-
**Part (b) of `WfT2Src.T2AbsNSrcW`** (2026-10-31, WfSrcB).

Case (b): `P0 x = P1 x = x − 1` (x = r + L the last column).

- `par2_prev`: Bad2 gives `upg(x − 1) ≠ none`, so `e2(x − 1) = 0` and `P2 x = x − 1`. Hence `L = 1`.
- The lost grandchild `c = x − 1` gives the shape `i = P0(P0(x − 1))` by uniqueness of `P0`.
- A changing bump grandchild `c < x − 1`:
  - `e1 c > e1 m`: closed (`not_dropFail_of_high_grandchild`, via `failed_drop_grandchild_row_le`);
  - `e1 c = e1 m` and `x − 1` below `c`: the next column stays in `c`'s subtree, so
    `nonlost_return_value` gives `τ.v c = ρ.v m` and the window is empty;
  - the rest is the residual `SrcBNonlost`.
-/
import Ytosk.V3T2SrcReturn
import Ytosk.V3T2SrcWindow

namespace Ytosk.WfSrcB

open T

set_option linter.unusedSectionVars false

/-- In case (b) the row-2 parent of the last column is `x − 1`. -/
theorem par2_prev {M : Mat} (hZ2 : Z2 M) {x : Nat} (hp1 : par M 1 x = some (x - 1))
    {k : Nat} (hu : upg M (x - 1) = some k) (hx2 : entry M 2 x = 1) :
    par M 2 x = some (x - 1) := by
  have he := (upg_e12 hu).2
  have h0 : entry M 2 (x - 1) = 0 := by have := hZ2 (x - 1); omega
  show climb (par M 1) (fun q => decide (entry M 2 q < entry M 2 x)) (x + 1) (par M 1 x) = _
  rw [hp1]
  simp [climb, h0, hx2]

/-- In case (b), `L = 1`. -/
theorem L_eq_one {M : Mat} (hZ2 : Z2 M) (hB : Bad2 M) {r L : Nat} (hx : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hp1 : par M 1 (r + L) = some (r + L - 1))
    (hx2 : entry M 2 (r + L) = 1) : L = 1 := by
  obtain ⟨⟨k, hk⟩, _⟩ := hB
  rw [show M.length - 2 = r + L - 1 by omega] at hk
  have h := par2_prev hZ2 hp1 hk hx2
  rw [hr] at h
  have := par_lt M 2 (r + L) r hr
  injection h with h
  omega

/-- The row-2 entry of the last column is `1` (from `P2 x = r`). -/
theorem e2_last {M : Mat} (hZ2 : Z2 M) {r x : Nat} (hxN : x < M.length) (hr : par M 2 x = some r) :
    entry M 2 x = 1 := by
  obtain ⟨_, _, _, he2, _, _⟩ := (par2_iff M hxN).mp hr
  have h' : entry M 2 r < entry M 2 x := he2
  have := hZ2 x
  omega

/-- **Residual (b, non-lost)**: in case (b), a failed source window whose last changing bump grandchild
`c` is strictly before `x − 1`, not above `m`'s row, and not a same-row return of `m` above `x − 1`,
does not exist. Only the two unclosed sub-cases remain:
`x − 1` below `c` with `e1 c < e1 m`, or `x − 1` outside `c`'s subtree with `e1 c ≤ e1 m`. -/
def SrcBNonlost : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → ∀ x, x + 1 = M.length →
    par M 2 x = some (x - 1) → par M 0 x = some (x - 1) → par M 1 x = some (x - 1) →
    ∀ τ, Cons (M.take x) τ → ∀ i m j c, i < x → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      par M 0 i = some m → par M 1 i = some m → j ∈ children M i → col M j = bump M i →
      c ∈ children M j → c < x - 1 → τ.o c ≠ ρ.o c →
      (∃ B, children (M.take x) i = B ++ [j] ∧
        ∀ d ∈ B, bumpTerm (M.take x) τ i d = bumpTerm M ρ i d) →
      (∃ K, children M j = K ++ [c] ∧ ∀ d ∈ K, τ.o d = ρ.o d ∧ entry M 1 d < entry M 1 m) →
      entry M 1 c ≤ entry M 1 m → (Anc0 M c (x - 1) → entry M 1 c < entry M 1 m) →
      ¬ WfT2Abs.DropFail M ρ τ x i

/-- **Part (b)**: in case (b) every failed source window is at `i = P0(P0 r)` and `L = 1`,
given the non-lost residual. -/
theorem shape_b (hN : SrcBNonlost) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : Bad2 M) {r L : Nat} (hx : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r)
    (hp0 : par M 0 (r + L) = some (r + L - 1)) (hp1 : par M 1 (r + L) = some (r + L - 1))
    {τ : Valn} (hT : Cons (M.take (r + L)) τ) {i : Nat} (hi : i < r + L)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (hf : WfT2Abs.DropFail M ρ τ (r + L) i) :
    L = 1 ∧ ∃ p, par M 0 r = some p ∧ par M 0 p = some i := by
  have hx2 := e2_last C.S.z2 (by omega) hr
  have hL := L_eq_one C.S.z2 hB hx hr hp1 hx2
  subst hL
  refine ⟨rfl, ?_⟩
  have hGT : Good3 (M.take (r + 1)) τ := by
    have he : M.length - 1 = r + 1 := by omega
    rw [← he] at hT ⊢
    exact good3_take_any (Inv3W.ofV2 C.S C.I) C.toW (by omega) hT
  have hRT : Rk (M.take (r + 1)) rk := rk_take (by omega) C.I.rank
    (by have := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
        simpa only [show M.length - 1 = r + 1 from by omega] using this)
  obtain ⟨m, j, c, K, B, hmi, hm1, hj, hb, hc, hcx, hce, hB', hfixB, hK, hKT, hfix⟩ :=
    T2SrcQuiet.failed_drop_branch C hx hr hi h1 h2 hT hf
  by_cases hcl : c = r
  · subst hcl
    exact ⟨j, (mem_children_iff.mp hc).2, (mem_children_iff.mp hj).2⟩
  exfalso
  obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
  have hrow := T2SrcQuiet.failed_drop_grandchild_row_le C.S C.I.cons C.I.good
    hx hT hRT hGT hmi hm1 hj hb hc hcx hf
  have hiN : i < M.length := by omega
  have hm2 : entry M 2 m = 0 := by
    by_contra h
    exact no_par1_of_e2 C.S.z1c hiN (by have := C.S.z2 m; omega) hm1
  have hc2 := T2SrcQuiet.bump_grandchild_e2_zero hX hJ hj hb hc
  have hcr : c < r := by omega
  -- same-row return above x − 1
  have hdesc : Anc0 M c r → entry M 1 c < entry M 1 m := by
    intro hA
    by_contra hn
    have he : entry M 1 c = entry M 1 m := by omega
    have hnext : par M 0 (c + 1) = some c := child_succ hA (by omega)
    have h0c := C.S.r0p (c + 1) c hnext
    have h0j := C.S.r0p c j (mem_children_iff.mp hc).2
    have h0i := C.S.r0p j i (mem_children_iff.mp hj).2
    have h0m := C.S.r0p i m hmi
    have hv := T2SrcPrefix.nonlost_return_value C.S C.I.cons C.I.good hx hT hRT hmi hm1 hj hb hc
      (by omega) he hm2 hc2 (by omega)
    have hjx : j < r + 1 := Nat.lt_trans (mem_children hc).1 hcx
    apply T2SrcPrefix.not_dropFail_of_parent_le_child C.I.good hi (by omega) hT hGT
      (mem_take_children hj hjx) (by rw [col_take M hjx, bump_take M hi, hb])
      (mem_take_children hc hcx) _ hf
    rw [hm1]
    exact le_of_eq hv.symm
  have hr' : par M 2 (r + 1) = some (r + 1 - 1) := by simpa using hr
  exact hN M ρ rk C hB (r + 1) hx hr' hp0 hp1 τ hT i m j c hi h1 h2 hmi hm1 hj hb hc
    (by omega) hce ⟨B, hB', hfixB⟩
    ⟨K, hK, fun d hd => ⟨hfix d hd, T2SrcQuiet.failed_drop_earlier_row_lt hX hJ C.I.cons C.I.good
      hx hT hRT hGT hmi hm1 hj hb hc hcx (by rw [hK]; simp [hd])
      (by
        have hs := children_sorted M j
        rw [hK, List.pairwise_append] at hs
        exact hs.2.2 d hd c (by simp)) hf⟩⟩
    hrow hdesc hf

/-- **Residual (a)**: outside case (b) there is no failed source window. -/
def SrcA : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ τ, Cons (M.take (r + L)) τ →
      ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        (par M 0 (r + L) ≠ some (r + L - 1) ∨ par M 1 (r + L) ≠ some (r + L - 1)) →
        WfT2Src.SrcFacts M ρ τ (r + L) i → ¬ WfT2Abs.DropFail M ρ τ (r + L) i

/-- **Residual (c)**: the bound at the shape `L = 1`, `i = P0(P0 r)` of case (b). -/
def SrcC : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r, r + 2 = M.length → par M 2 (r + 1) = some r → par M 0 (r + 1) = some r → par M 1 (r + 1) = some r →
      ∀ τ, Cons (M.take (r + 1)) τ →
      ∀ p i, par M 0 r = some p → par M 0 p = some i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        WfT2Abs.DropFail M ρ τ (r + 1) i → WfT2Src.SrcFacts M ρ τ (r + 1) i →
        ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z → s < bumpW M ρ i →
          ¬ Lhd z s (bumpW M ρ i) → s < WfT2Abs.Bnd (ρ.v r)

/-- **Bridge**: `T2AbsNSrcW` from (a), the non-lost part of (b), and (c). -/
theorem t2AbsNSrcW_of (hA : SrcA) (hN : SrcBNonlost) (hC : SrcC) : WfT2Src.T2AbsNSrcW := by
  intro M ρ rk C hB2 hz h2 r L hlen hr τ hτ i hi h1 h2' hfail hfacts
  by_cases hb : par M 0 (r + L) = some (r + L - 1) ∧ par M 1 (r + L) = some (r + L - 1)
  · obtain ⟨hL, p, hp, hpi⟩ := shape_b hN C hB2 hlen hr hb.1 hb.2 hτ hi h1 h2' hfail
    subst hL
    refine ⟨rfl, ⟨p, hp, hpi⟩, ?_⟩
    have hb0 : par M 0 (r + 1) = some r := by simpa using hb.1
    have hb1 : par M 1 (r + 1) = some r := by simpa using hb.2
    exact hC M ρ rk C hB2 hz h2 r (by omega) hr hb0 hb1 τ hτ p i hp hpi h1 h2' hfail hfacts
  · exact False.elim (hA M ρ rk C hB2 hz h2 r L hlen hr τ hτ i hi h1 h2'
      (by
        by_contra hn
        push Not at hn
        exact hb hn) hfacts hfail)

end Ytosk.WfSrcB
