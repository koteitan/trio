/-
**The frame shape with the bad-parent case (2026-10-31, WfAbsW).**

`FrameShape` (V3ExpT2BX, a field of `T2BelowXS`) is false at m = 31 of the 36-column matrix in `M[2]`
(`WfAbsWCex.not_frameShape`). `FrameShapeX` adds the fourth case: `v(m)` unchanged, the counted children of `m` are
`Lc ++ [c]` in `M` and `N`, `c` is argument-free in both and goes down only with the allowance `v(m)`
(both `o(c)` and `v(c)`). `frameShapeX_of_bad` derives it from the bump frame at `c` and `BadAbsShape`.
The consumers of `FrameShape` (V3T2FC, V3T2VSR, V3T2VSF, V3ExpT2FO, V3T2VRA, V3T2VRAPre, V3T2VRASeed) must handle
the fourth case to take `FrameShapeX`.
-/
import Ytosk.WfAbsWEta
import Ytosk.V3ExpT2BX

namespace Ytosk.WfAbsW

open T

set_option linter.unusedVariables false

/-- **`FrameShape` with the bad-parent case.** -/
def FrameShapeX (M N : Mat) (ρ σ : Valn) (i : Nat) : Prop :=
  FrameShape M N ρ σ i ∨
  (σ.v i = ρ.v i ∧ ∃ Lc c, CL M i = Lc ++ [c] ∧ CL N i = Lc ++ [c] ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧
    σ.o c = psi (σ.v c) z z ∧ ρ.o c = psi (ρ.v c) z z ∧
    Lhd (ρ.v i) (σ.v c) (ρ.v c) ∧ Lhd (ρ.v i) (σ.o c) (ρ.o c) ∧ Lhd z (σ.o i) (ρ.o i))

theorem FrameShape.toX {M N : Mat} {ρ σ : Valn} {i : Nat} (h : FrameShape M N ρ σ i) :
    FrameShapeX M N ρ σ i := Or.inl h

/-- **The bad parent has `FrameShapeX`** (fourth case), from the bump frame at the bad column. -/
theorem frameShapeX_of_bad {M N : Mat} {ρ σ : Valn} {i j m : Nat} {L : List Nat} {G' G : T}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : GoodOT N σ)
    (hiM : i < M.length) (hiN : i < N.length)
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (he1 : entry N 1 i = entry M 1 i)
    (he2 : entry N 2 i = entry M 2 i) (hV : vOpt σ (par N 1 i) = vOpt ρ (par M 1 i))
    (hchM : children M i = L ++ [j]) (hchN : children N i = L ++ [j])
    (hbL : ∀ d ∈ L, bumpTerm N σ i d = bumpTerm M ρ i d)
    (hbjM : bumpTerm M ρ i j = omega G) (hbjN : bumpTerm N σ i j = omega G')
    (hGot : isOT G = true) (hG'ot : isOT G' = true) (hS : BRelS G' G) (hlt : G' < G)
    (hTD : BumpTermDec M ρ)
    (hpN : ((CL N m).map σ.o).Pairwise (fun a b => b ≤ a))
    (hB : BadAbsShape M N ρ σ i) (hm : par M 0 i = some m) :
    FrameShapeX M N ρ σ m := by
  obtain ⟨m', Lc, hp0, hp1, hclMi, hclNi, hclM, hclN, hsame, hvm, _⟩ := hB
  rw [hm] at hp0; cases hp0
  have hmi : m < i := par_lt M 0 i m hm
  have hvl := v_bump_lhdV hC hG hCN hiM hiN h1 h2 he1 he2 hV hchM hchN hbL hbjM hbjN hGot hG'ot hS hlt hTD
  rw [hp1] at hvl
  have hoM : ρ.o i = psi (ρ.v i) z z :=
    o_of_no_counted hC hiM (hG.ot_v i hiM) (no_cnt_of_cl_nil hclMi)
  have hoN : σ.o i = psi (σ.v i) z z :=
    o_of_no_counted hCN hiN (hGN.ot_v i hiN) (no_cnt_of_cl_nil hclNi)
  right
  refine ⟨hvm, Lc, i, hclM, hclN, hsame, hoN, hoM, by simpa [vOpt] using hvl,
    by simpa [vOpt] using o_noarg_lhdV hvl hoM hoN, ?_⟩
  exact bad_parent_lhd hC hG hCN hGN hiM hiN (by omega) (by omega) h1 h2 he1 he2 hV hchM hchN hbL hbjM hbjN
    hGot hG'ot hS hlt hTD hp1 hclMi hclNi hclM hclN hvm hsame hpN

end Ytosk.WfAbsW
