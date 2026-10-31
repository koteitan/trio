/-
**The lower-row case shared by (a) and (b) of `T2AbsNSrcW`** (2026-10-31, WfSrcP).

Shape (P): a bump grandchild `c` of `i` (`j` the bump child, `c` the last child of `j`) changes,
`c < x − 1`, `c` is a row-0 ancestor of `x − 1`, and `e1 c < e1 m` (`m = P0 i = P1 i`); every earlier
child of `j` is below `m`'s row. This is shape (A) of `WfSrcA.SrcARem2` and sub-case (P) of
`WfSrcB.SrcBNonlost2`.

- `PLow`: the shared residual (no frame condition (a)/(b)).
- `not_dropFail_of_lt_o`: if `v(P1 i) < τ.o c` the window is empty (no DropFail).
- `PLowRes`: `PLow` with the extra premise `¬ ρ.v m < τ.o c`; `pLow_of_res`.
- `SrcARem3` (only shape (B) left), `srcARem2_of : PLow → SrcARem3 → SrcARem2`.
- `SrcBNonlost3` (only (O′) left), `srcBNonlost2_of : PLow → SrcBNonlost3 → SrcBNonlost2`.
- `t2AbsNSrcW_of : PLowRes → SrcARem3 → SrcBNonlost3 → SrcCRes → WfT2Src.T2AbsNSrcW`.
-/
import Ytosk.WfSrcABC

namespace Ytosk.WfSrcP

open T

set_option linter.unusedSectionVars false

/-- A new grandchild value above the old parent value leaves no source absorption window. -/
theorem not_dropFail_of_lt_o {M : Mat} {ρ τ : Valn}
    (hG : Good3 M ρ) {x i j c : Nat} (hi : i < x) (hx : x ≤ M.length)
    (hGT : Good3 (M.take x) τ)
    (hj : j ∈ children (M.take x) i) (hb : col (M.take x) j = bump (M.take x) i)
    (hc : c ∈ children (M.take x) j)
    (hpO : vOpt ρ (par M 1 i) < τ.o c) : ¬ WfT2Abs.DropFail M ρ τ x i := by
  have hGo : ∀ t ∈ (children (M.take x) j).map τ.o, isOT t = true := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hGT.ot_o d (mem_children hd).2
  have hsum := T2SrcLeaf.mem_le_sumN hGo (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hpW := lt_of_lt_of_le hpO (le_trans hsum (T2SrcLeaf.child_sum_le_bumpW hGT hj hb))
  intro hf
  apply hf
  intro q hq _ hnT _
  exact False.elim (hnT (lt_of_le_of_lt
    (le_trans (summands_le_head (vOpt_ot hG (by omega)) q hq) (head_le_self _)) hpW))

/-- **Shared residual (P)**: shape (A) of (a) and sub-case (P) of (b), without the frame
condition that separates (a) from (b). -/
def PLow : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → ∀ x, x + 1 = M.length → (∃ r, par M 2 x = some r) →
    ∀ τ, Cons (M.take x) τ → ∀ i m j c (B K : List Nat), i < x → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      par M 0 i = some m → par M 1 i = some m → j ∈ children M i → col M j = bump M i →
      children (M.take x) i = B ++ [j] → children M j = K ++ [c] → c < x - 1 → τ.o c ≠ ρ.o c →
      (∀ d ∈ K, entry M 1 d < entry M 1 m) → Anc0 M c (x - 1) → entry M 1 c < entry M 1 m →
      ¬ WfT2Abs.DropFail M ρ τ x i

/-- **Narrowed residual (P)**: `PLow` when the old parent value is not below the new `o(c)`. -/
def PLowRes : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → ∀ x, x + 1 = M.length → (∃ r, par M 2 x = some r) →
    ∀ τ, Cons (M.take x) τ → ∀ i m j c (B K : List Nat), i < x → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      par M 0 i = some m → par M 1 i = some m → j ∈ children M i → col M j = bump M i →
      children (M.take x) i = B ++ [j] → children M j = K ++ [c] → c < x - 1 → τ.o c ≠ ρ.o c →
      (∀ d ∈ K, entry M 1 d < entry M 1 m) → Anc0 M c (x - 1) → entry M 1 c < entry M 1 m →
      ¬ ρ.v m < τ.o c →
      ¬ WfT2Abs.DropFail M ρ τ x i

theorem pLow_of_res (h : PLowRes) : PLow := by
  intro M ρ rk C hB x hx hr τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcx hce hKl hA hrow
  by_cases hlt : ρ.v m < τ.o c
  · have hGT : Good3 (M.take x) τ := by
      have he : M.length - 1 = x := by omega
      rw [← he] at hT ⊢
      exact good3_take_any (Inv3W.ofV2 C.S C.I) C.toW (by omega) hT
    have hcM : c ∈ children M j := by rw [hK]; simp
    have hjc : j < c := (mem_children hcM).1
    have hij : i < j := (mem_children hj).1
    have hjx : j < x := by omega
    have hjT : j ∈ children (M.take x) i := mem_take_children hj hjx
    have hbT : col (M.take x) j = bump (M.take x) i := by
      rw [col_take M hjx, bump_take M hi, hb]
    have hcT : c ∈ children (M.take x) j := mem_take_children hcM (by omega)
    apply not_dropFail_of_lt_o C.I.good hi (by omega) hGT hjT hbT hcT
    rw [hm1]
    exact hlt
  · exact h M ρ rk C hB x hx hr τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcx hce hKl hA hrow hlt

/-- `WfSrcA.SrcARem2` with shape (A) removed: only shape (B) is left. -/
def SrcARem3 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      (par M 0 (r + L) ≠ some (r + L - 1) ∨ par M 1 (r + L) ≠ some (r + L - 1)) →
      ∀ τ, Cons (M.take (r + L)) τ →
      ∀ i m j c (B K : List Nat), i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        par M 0 i = some m → par M 1 i = some m →
        j ∈ children M i → col M j = bump M i → children (M.take (r + L)) i = B ++ [j] →
        children M j = K ++ [c] → c < r + L - 1 → τ.o c ≠ ρ.o c →
        (∀ d ∈ K, entry M 1 d < entry M 1 m) → entry M 1 c ≤ entry M 1 m →
        (∃ c' q, NextC M c c' ∧ c' < r + L ∧ upg M (c' - 1) = some c' ∧ ChgX M (r + L) false c' ∧
            par M 0 c' = some q ∧ par M 1 (c' - 1) = some q ∧ Anc0 M q m ∧ q ≠ m) →
        ¬ WfT2Abs.DropFail M ρ τ (r + L) i

/-- **Bridge (a)**: `SrcARem2` from the shared residual and shape (B). -/
theorem srcARem2_of (hP : PLow) (h3 : SrcARem3) : WfSrcA.SrcARem2 := by
  intro M ρ rk C hB2 hz hs r L hx hr ha τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcl hce
    hearly hrow hsh
  rcases hsh with ⟨hA, hlt⟩ | hB
  · exact hP M ρ rk C hB2 (r + L) hx ⟨r, hr⟩ τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcl hce
      hearly hA hlt
  · exact h3 M ρ rk C hB2 hz hs r L hx hr ha τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcl hce
      hearly hrow hB

/-- `WfSrcB.SrcBNonlost2` with sub-case (P) removed: only (O′) is left. -/
def SrcBNonlost3 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → ∀ x, x + 1 = M.length →
    par M 2 x = some (x - 1) → par M 0 x = some (x - 1) → par M 1 x = some (x - 1) →
    ∀ τ, Cons (M.take x) τ → ∀ i m j c, i < x → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      par M 0 i = some m → par M 1 i = some m → j ∈ children M i → col M j = bump M i →
      c ∈ children M j → c < x - 1 → τ.o c ≠ ρ.o c →
      (∃ B, children (M.take x) i = B ++ [j] ∧
        ∀ d ∈ B, bumpTerm (M.take x) τ i d = bumpTerm M ρ i d) →
      (∃ K, children M j = K ++ [c] ∧ ∀ d ∈ K, τ.o d = ρ.o d ∧ entry M 1 d < entry M 1 m) →
      entry M 1 c ≤ entry M 1 m → ¬ Anc0 M c (x - 1) →
      (∃ c' m', NextC M c c' ∧ c' < x ∧ upg M (c' - 1) = some c' ∧
        par M 1 (c' - 1) = some m' ∧ Anc0 M m' m ∧ m' ≠ m) →
      ¬ WfT2Abs.DropFail M ρ τ x i

/-- **Bridge (b)**: `SrcBNonlost2` from the shared residual and (O′). -/
theorem srcBNonlost2_of (hP : PLow) (h3 : SrcBNonlost3) : WfSrcB.SrcBNonlost2 := by
  intro M ρ rk C hB x hx hr hp0 hp1 τ hT i m j c hi h1 h2 hmi hm1 hj hb hc hcx hce hBr hKr hrow
    hdesc hout
  by_cases hA : Anc0 M c (x - 1)
  · obtain ⟨B, hBj, _⟩ := hBr
    obtain ⟨K, hK, hKs⟩ := hKr
    exact hP M ρ rk C hB x hx ⟨x - 1, hr⟩ τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcx hce
      (fun d hd => (hKs d hd).2) hA (hdesc hA)
  · exact h3 M ρ rk C hB x hx hr hp0 hp1 τ hT i m j c hi h1 h2 hmi hm1 hj hb hc hcx hce hBr hKr hrow
      hA (hout hA)

/-- **Bridge**: `T2AbsNSrcW` from the narrowed shared residual, (a) shape (B), (b) (O′) and (c). -/
theorem t2AbsNSrcW_of (hP : PLowRes) (hA : SrcARem3) (hB : SrcBNonlost3) (hC : WfSrcC.SrcCRes) :
    WfT2Src.T2AbsNSrcW :=
  WfSrcABC.t2AbsNSrcW_of (srcARem2_of (pLow_of_res hP) hA) (srcBNonlost2_of (pLow_of_res hP) hB) hC

end Ytosk.WfSrcP
