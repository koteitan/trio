/-
**3 行・t = 2・Bad2: `WfT2Src.T2AbsNSrcW` の (c) を 2 つの欄に分ける（2026-10-31、WfSrcC）。**

`T2AbsNSrcW` の結論は (a,b) 形 `L = 1 ∧ i = P0(P0 r)` と (c) 上界 `s < B(v(r))`（B(v) = ψ_v(Ω_{v+1})）。
ここでは
- `T2AbsNSrcAB`: 結論の形の部分だけ（(a)(b) の担当）。
- `SrcCRes`: 形 `L = 1`・`P0 r = p`・`P0 p = i` を前件に足した (c) の残り。結論は
  吸収されない加数 s（ψ(2) 以上、W_M(i) 未満）について (i) `s < o(r)` と
  (ii) s の添字が `v(r)` なら、その引数は `Ω_{v(r)+1}` 未満。
橋 `t2AbsNSrcW_of`: (i) と `o(r) = ψ_{v(r)}(Y)` から s の添字は v(r) 以下。v(r) 未満なら字句順で s < B(v(r))、
等しければ (ii)。

測定（tmp/wf/WfSrcC/notes.md）: 形の枠（L = 1・i = P0(P0 r)・p は i の bump 子・upg(r) あり、DropFail で絞らない）で
ほとんどの枠で `W_M(i) = o(r)`（例外 7 枠は p の子が複数で、窓 [o(r), W_M(i)) に加数がない）。(ii) より強い「o(r) 未満の加数はすべて B(v(r)) 未満」も例外 0。
-/
import Ytosk.WfT2Src

namespace Ytosk.WfSrcC

open T

set_option linter.unusedSectionVars false

/-- **The shape part of `T2AbsNSrcW`** (the conclusion's first two conjuncts). -/
def T2AbsNSrcAB : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ τ, Cons (M.take (r + L)) τ →
      ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → WfT2Abs.DropFail M ρ τ (r + L) i →
        WfT2Src.SrcFacts M ρ τ (r + L) i →
        L = 1 ∧ ∃ p, par M 0 r = some p ∧ par M 0 p = some i

/-- **Residual (c) in the shape `L = 1`, `i = P0(P0 r)`**: a non-absorbed summand `s ≥ ψ(2)` of `v(P1 i)` below the
bump term of `i` is (i) below `o(r)`, and (ii) if its subscript is `v(r)`, its argument is below `Ω_{v(r)+1}`.
(The stronger `W_M(i) ≤ o(r)` is false: deep2/t2ext have frames where `p` has several children; there no summand
lies in the window.) -/
def SrcCRes : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r, r + 2 = M.length → par M 2 (r + 1) = some r → ∀ τ, Cons (M.take (r + 1)) τ →
      ∀ i, i < r + 1 → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → WfT2Abs.DropFail M ρ τ (r + 1) i →
        WfT2Src.SrcFacts M ρ τ (r + 1) i →
        ∀ p, par M 0 r = some p → par M 0 p = some i →
        ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z → s < bumpW M ρ i →
          ¬ Lhd z s (bumpW M ρ i) →
            s < ρ.o r ∧ ∀ b, s = psi (ρ.v r) b z → b < psi (add (ρ.v r) one) z z

/-- `o(i)` is a single `ψ` term with subscript `v(i)`. -/
theorem o_psi_form {M : Mat} {ρ : Valn} (hC : Cons M ρ) {i : Nat} (hi : i < M.length)
    (hv : isOT (ρ.v i) = true) : ∃ Y, ρ.o i = psi (ρ.v i) Y z := by
  rw [(hC i hi).1]
  unfold oRhs
  show ∃ Y, add (sp (sf (ρ.v i)) z (sf (sumN ((children M i).map (cnt M ρ i))))) (sf z) = _
  rw [sp_eq_spArg, sf_ot hv]
  exact ⟨_, rfl⟩

/-- **The term step of the bridge**: a summand below `ψ_V(Y)` whose argument is small when its subscript is `V` is
below `B(V)`. -/
theorem lt_bnd_of_lt_psi {V Y s : T} (hs : ∃ a b, s = psi a b z) (hlt : s < psi V Y z)
    (harg : ∀ b, s = psi V b z → b < psi (add V one) z z) : s < WfT2Abs.Bnd V := by
  obtain ⟨a, b, rfl⟩ := hs
  unfold WfT2Abs.Bnd
  rcases psi_lt_psi_z_iff.mp hlt with ha | ⟨rfl, _⟩
  · exact psi_lt_psi_z_iff.mpr (Or.inl ha)
  · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, harg b rfl⟩)

/-- **Bridge**: `T2AbsNSrcW` from its shape part and the residual (c) in that shape. -/
theorem t2AbsNSrcW_of (hAB : T2AbsNSrcAB) (hCR : SrcCRes) : WfT2Src.T2AbsNSrcW := by
  intro M ρ rk C hB2 hz h2 r L hlen hr τ hτ i hi h1 h2' hfail hfacts
  obtain ⟨hL, p, hp, hpi⟩ := hAB M ρ rk C hB2 hz h2 r L hlen hr τ hτ i hi h1 h2' hfail hfacts
  subst hL
  refine ⟨rfl, ⟨p, hp, hpi⟩, ?_⟩
  intro s hs hs2 hlt hnl
  obtain ⟨hso, harg⟩ := hCR M ρ rk C hB2 hz h2 r (by omega) hr τ hτ i hi h1 h2' hfail hfacts p hp hpi
    s hs hs2 hlt hnl
  have hrM : r < M.length := by omega
  obtain ⟨Y, hY⟩ := o_psi_form C.I.cons hrM (C.I.good.ot_v r hrM)
  have hlt' : s < psi (ρ.v r) Y z := hY ▸ hso
  exact lt_bnd_of_lt_psi (mem_summands hs) hlt' harg

end Ytosk.WfSrcC
