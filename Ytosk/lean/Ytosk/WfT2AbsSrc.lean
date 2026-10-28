/-
**3 行・t = 2・Bad2: 残り `T2AbsNBad` を、M 側の残りと展開側の残りに分ける（2026-10-29、WfT2Abs）。**

落とし側の吸収が破れる列 i（`T2AbsNBad` の前件）で、実測（tmp/wf/WfT2Abs/notes.md）では
- 形: L = 1 で i = P0(P0 r)（r の祖父）、
- 吸収されない加数 q（q ≥ ψ(2)、q < W_M(i)、q ⋪ W_M(i)）は q < B(v(r))、B(v) = ψ_v(Ω_{v+1})、
- 展開側: B(v(r)) ≤ W_N(i)（W_N(i) = o_N(r) = ψ_{v(r)}(o_N(r+1))）。

`T2AbsNSrc` は M（と M.take x の評価 τ）だけの主張（展開 N を含まない）。`T2AbsNExp` は展開側の計算。
`t2AbsNBad_of` で両者から `T2AbsNBad` が出る。
-/
import Ytosk.V3T2BelowR

namespace Ytosk.WfT2Abs

open T

set_option linter.unusedSectionVars false

/-- `B(v) = ψ_v(Ω_{v+1})`. -/
def Bnd (v : T) : T := psi v (psi (add v one) z z) z

/-- The failure of the drop-side absorption at `i` (the premise of `T2AbsNBad`). -/
def DropFail (M : Mat) (ρ τ : Valn) (x i : Nat) : Prop :=
  ¬ (∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z → ¬ s < bumpW (M.take x) τ i →
      s < bumpW M ρ i → Lhd z s (bumpW M ρ i))

/-- **Residual (M side)**: at a column where the drop-side absorption fails, `L = 1`, `i` is the grandparent of `r`,
and every non-absorbed summand of `v(P_1 i)` is below `B(v(r))`. -/
def T2AbsNSrc : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ τ, Cons (M.take (r + L)) τ →
      ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → DropFail M ρ τ (r + L) i →
        L = 1 ∧ (∃ p, par M 0 r = some p ∧ par M 0 p = some i) ∧
          ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z → s < bumpW M ρ i →
            ¬ Lhd z s (bumpW M ρ i) → s < Bnd (ρ.v r)

/-- **Residual (expansion side)**: in the shape `L = 1`, `i = P_0(P_0 r)`, the new bump term of `i` is at least
`B(v(r))`. -/
def T2AbsNExp : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r, r + 2 = M.length → par M 2 (r + 1) = some r → ∀ p i, par M 0 r = some p → par M 0 p = some i →
      entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      ∀ n, 2 ≤ n → ∀ σ,
        Cons (TRIO.gexp M r 1 (entry M 0 (r + 1) - entry M 0 r) (entry M 1 (r + 1) - entry M 1 r) n) σ →
        Bnd (ρ.v r) ≤
          bumpW (TRIO.gexp M r 1 (entry M 0 (r + 1) - entry M 0 r) (entry M 1 (r + 1) - entry M 1 r) n) σ i

/-- **Bridge**: `T2AbsNBad` from the M-side residual and the expansion-side residual. -/
theorem t2AbsNBad_of (hS : T2AbsNSrc) (hE : T2AbsNExp) : T2AbsNBad := by
  intro M ρ rk C hB2 hz h2 r L hlen hr τ hτ i hi h1 h2' hfail n hn σ hCN s hs hs2 hnN hlt
  obtain ⟨hL, ⟨p, hp, hpi⟩, hsrc⟩ := hS M ρ rk C hB2 hz h2 r L hlen hr τ hτ i hi h1 h2' hfail
  subst hL
  have hB := hE M ρ rk C hB2 hz h2 r (by omega) hr p i hp hpi h1 h2' n hn σ hCN
  by_contra hlhd
  exact hnN (lt_of_lt_of_le (hsrc s hs hs2 hlt hlhd) hB)

end Ytosk.WfT2Abs
