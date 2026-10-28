/-
**3 行・t = 2・Bad2: 残り `WfT2Abs.T2AbsNSrc` の構造の部分（2026-10-29、WfT2Src）。**

落とし側の吸収が破れる列 i（`DropFail`）では、構造から次が出る（`src_facts`、証明済み）:
- 弱い枝: WkVA(τ.v i, ρ.v i)・WCSP・CntX（`weak_of_drop_failure`、x の親は bump の子でない `t2_xparNB`）。
  CntX の第 2 の場合は i で起きない（行 2 ≠ 0 の列は上げない）。
- bump 項が変わる: W_T(i) ≠ W_M(i)。よって x が i の bump の子か、i の bump の子 j の子 c < x で o が変わる。

残り `T2AbsNSrcW` は `T2AbsNSrc` の前件にこれらを足したもの（狭い）。橋 `t2AbsNSrc_of_W`。

測定（tmp/wf/WfT2Src/notes.md）: 形（L = 1・i = P0(P0 r)）は構造からは出ない。
落とし側の吸収が破れる列はすべて Bad2 の第 2 の選言（P0 x = x − 1 ∧ ¬BumpAbsC、UpgAbsX は真）にあり、
第 1 の選言（¬UpgAbsX）の行列（b2grow1 の 1879 個）では g で v が弱く変わる（1163 件、うち 1132 件は P0 x ≠ x − 1）が
吸収は破れない。つまり L = 1 は値の結論。
-/
import Ytosk.WfT2AbsSrc
import Ytosk.V3T2AbsNWeak

namespace Ytosk.WfT2Src

open T

set_option linter.unusedSectionVars false

/-- A column with row 2 ≠ 0 does not upgrade. -/
theorem upg_none_of_e2 {M : Mat} (hZ2 : Z2 M) {i : Nat} (h2 : entry M 2 i ≠ 0) : upg M i = none := by
  have h1 : entry M 2 i = 1 := by have := hZ2 i; omega
  unfold upg
  simp [h1]

/-- **`CntX` at a column with row 2 ≠ 0**: its second case (`UpgBad M ρ i`) does not occur. -/
theorem cntX_of_e2 {M : Mat} {ρ : Valn} {i : Nat} (hZ2 : Z2 M) (h2 : entry M 2 i ≠ 0) (h : CntX M ρ i) :
    (∀ c ∈ children M i, ¬ Counted M i c) ∨
      ((∀ c ∈ children M i, Counted M i c → c + 1 = M.length) ∧ UpgBad M ρ (M.length - 2) ∧ BadPos M) := by
  rcases h with h | ⟨_, _, k, W, _, hu, _⟩ | h
  · exact Or.inl h
  · rw [upg_none_of_e2 hZ2 h2] at hu; cases hu
  · exact Or.inr h

/-- **The bump term of `i` changes only through a bump child**: if `W_T(i) ≠ W_M(i)` then `x` is a child of `i`,
or a bump child `j` of `i` has `x` as a child or a child `c < x` whose `o` changes. -/
theorem bumpW_change {M : Mat} {x i : Nat} (hx : x + 1 = M.length) (hix : i < x) {ρ τ : Valn}
    (hne : bumpW (M.take x) τ i ≠ bumpW M ρ i) :
    x ∈ children M i ∨
      ∃ j ∈ children M i, col M j = bump M i ∧
        (x ∈ children M j ∨ ∃ c ∈ children M j, c < x ∧ τ.o c ≠ ρ.o c) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hxi, hj⟩ := hcon
  apply hne
  have hbi : bump (M.take x) i = bump M i := bump_take M hix
  have hlt : ∀ c ∈ children M i, c < x := fun c hc => by
    have := (mem_children hc).2
    have hcx : c ≠ x := fun h => hxi (h ▸ hc)
    omega
  have hterm : ∀ j ∈ children M i, bumpTerm (M.take x) τ i j = bumpTerm M ρ i j := by
    intro j hjM
    have hjx := hlt j hjM
    unfold bumpTerm
    rw [col_take M hjx, hbi]
    by_cases hb : col M j = bump M i
    · rw [if_pos hb, if_pos hb]
      obtain ⟨hxj, hc⟩ := hj j hjM hb
      have hch : children (M.take x) j = children M j := by
        rw [children_take, List.filter_eq_self]
        intro c hc'
        have := (mem_children hc').2
        have hcx : c ≠ x := fun h => hxj (h ▸ hc')
        simp only [decide_eq_true_eq]; omega
      rw [hch]
      congr 2
      apply List.map_congr_left
      intro c hc'
      have := (mem_children hc').2
      have hcx : c ≠ x := fun h => hxj (h ▸ hc')
      exact hc c hc' (by omega)
    · rw [if_neg hb, if_neg hb]
  have hfil : (children M i).filter (fun c => decide (c < x)) = children M i := by
    rw [List.filter_eq_self]
    intro c hc
    simpa using hlt c hc
  unfold bumpW
  rw [children_take, hfil]
  congr 3
  exact List.map_congr_left hterm

/-- **What the structure gives at a failed drop absorption** (`t = 2`, `x = r + L`). -/
def SrcFacts (M : Mat) (ρ τ : Valn) (x i : Nat) : Prop :=
  WkVA (τ.v i) (ρ.v i) ∧ WCSP M ρ i (τ.v i) ∧
    ((∀ c ∈ children M i, ¬ Counted M i c) ∨
      ((∀ c ∈ children M i, Counted M i c → c + 1 = M.length) ∧ UpgBad M ρ (M.length - 2) ∧ BadPos M)) ∧
    bumpW (M.take x) τ i ≠ bumpW M ρ i ∧
    (x ∈ children M i ∨
      ∃ j ∈ children M i, col M j = bump M i ∧ ∃ c ∈ children M j, c < x ∧ τ.o c ≠ ρ.o c)

/-- **`SrcFacts` at every failed drop absorption** (proved). -/
theorem src_facts {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) {r L : Nat}
    (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) {τ : Valn} (hτ : Cons (M.take (r + L)) τ)
    {i : Nat} (hi : i < r + L) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hfail : WfT2Abs.DropFail M ρ τ (r + L) i) : SrcFacts M ρ τ (r + L) i := by
  have IW := Inv3W.ofV2 C.S C.I
  have hA := anc0_of_par M 2 r (r + L) hr
  have hrx : r < r + L := par_lt M 2 _ _ hr
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hqb := t2_xparNB C.std C.ne IW hlen hr hq
  have hAbs : BumpAbsCB M (r + L) ρ := by
    have := C.RB.ab
    rwa [show M.length - 1 = r + L by omega] at this
  obtain ⟨hw, hc, hx⟩ := T2AbsNWeak.weak_of_drop_failure hAbs hτ hq hqb h1 h2 hfail
  have hne : bumpW (M.take (r + L)) τ i ≠ bumpW M ρ i := by
    intro heq
    apply hfail
    intro s _ _ hnT hlt
    exact absurd (heq ▸ hlt) hnT
  refine ⟨hw, hc, cntX_of_e2 C.S.z2 h2 hx, hne, ?_⟩
  rcases bumpW_change (by omega) hi hne with h | ⟨j, hj, hjb, hxj | hcj⟩
  · exact Or.inl h
  · exfalso
    have hpx := (mem_children_iff.mp hxj).2
    rw [hq] at hpx; cases hpx
    exact hqb i (mem_children_iff.mp hj).2 hjb
  · exact Or.inr ⟨j, hj, hjb, hcj⟩

/-- **Residual (narrowed `T2AbsNSrc`)**: `T2AbsNSrc` with the structural facts `SrcFacts` as an extra premise. -/
def T2AbsNSrcW : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ τ, Cons (M.take (r + L)) τ →
      ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → WfT2Abs.DropFail M ρ τ (r + L) i →
        SrcFacts M ρ τ (r + L) i →
        L = 1 ∧ (∃ p, par M 0 r = some p ∧ par M 0 p = some i) ∧
          ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z → s < bumpW M ρ i →
            ¬ Lhd z s (bumpW M ρ i) → s < WfT2Abs.Bnd (ρ.v r)

/-- **Bridge**: `T2AbsNSrc` from the narrowed residual. -/
theorem t2AbsNSrc_of_W (h : T2AbsNSrcW) : WfT2Abs.T2AbsNSrc := by
  intro M ρ rk C hB2 hz h2 r L hlen hr τ hτ i hi h1 h2' hfail
  exact h M ρ rk C hB2 hz h2 r L hlen hr τ hτ i hi h1 h2' hfail (src_facts C hlen hr hτ hi h1 h2' hfail)

end Ytosk.WfT2Src
