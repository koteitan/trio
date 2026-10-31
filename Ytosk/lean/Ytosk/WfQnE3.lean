/-
**WfQnE3 (2026-11-01): the dependency closure of the bad columns (scope of the generalized t = 1 engine).**
Measured (tmp/wf/WfQnE/analyze.py `scope`): every deviation of the true valuation of `M[n]` from the engine's glue lies in
the `DepX`-closure `DepXB M B` of the set `B` of bad v-calls (bad shape, `W = o(r)`, a summand of `v(P₁ i)` in
`[A[ζ], A)`); outside it the glue is exact.  Here: the closure, its inclusion in `DepX` when `B ⊆ D`, and the
congruence lemmas (two valuations that agree off `DepXB` have the same right sides off `DepXB`).
-/
import Ytosk.V3Dep
import Ytosk.V3Exist

namespace Ytosk.WfQnE3
open T Ytosk

/-- **The dependency closure of a set `B` of v-calls** (the constructors of `DepX` with the leaves `B`). -/
inductive DepXB (M : Mat) (B : Nat → Prop) : Bool → Nat → Prop
  | leaf {i : Nat} : B i → DepXB M B false i
  | ochild {i c : Nat} : c ∈ children M i → col M c ≠ bump M i →
      ¬ (isUpg M c = true ∧ topped M c = true) → DepXB M B true c → DepXB M B true i
  | ov {i : Nat} : DepXB M B false i → DepXB M B true i
  | vpar {i m : Nat} : entry M 1 i ≠ 0 → par M 1 i = some m → DepXB M B false m → DepXB M B false i
  | vupg {i k : Nat} : entry M 1 i ≠ 0 → entry M 2 i = 0 → upg M i = some k → DepXB M B false k →
      DepXB M B false i
  | vbump {i j k : Nat} : entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → j ∈ children M i → col M j = bump M i →
      k ∈ children M j → DepXB M B true k → DepXB M B false i

/-- **The closure of bad calls stays inside `D`.** -/
theorem DepXB.sub {M : Mat} {B : Nat → Prop} {x : Nat} (hB : ∀ i, B i → DepX M x false i) :
    ∀ {b i}, DepXB M B b i → DepX M x b i := by
  intro b i h
  induction h with
  | leaf h => exact hB _ h
  | ochild hc hb hu _ ih => exact DepX.ochild hc hb hu ih
  | ov _ ih => exact DepX.ov ih
  | vpar h1 hm _ ih => exact DepX.vpar h1 hm ih
  | vupg h1 h2 hk _ ih => exact DepX.vupg h1 h2 hk ih
  | vbump h1 h2 hj hb hk _ ih => exact DepX.vbump h1 h2 hj hb hk ih

/-- Two valuations that agree off the closure. -/
def AgreeOffB (M : Mat) (B : Nat → Prop) (ρ₁ ρ₂ : Valn) : Prop :=
  (∀ i, ¬ DepXB M B true i → ρ₁.o i = ρ₂.o i) ∧ (∀ i, ¬ DepXB M B false i → ρ₁.v i = ρ₂.v i)

theorem oRhs_nodepB {M : Mat} {B : Nat → Prop} {i : Nat} {ρ₁ ρ₂ : Valn} (h : AgreeOffB M B ρ₁ ρ₂)
    (hi : ¬ DepXB M B true i) : oRhs M ρ₁ i = oRhs M ρ₂ i := by
  apply oRhs_congr
  · exact h.2 i (fun hv => hi (DepXB.ov hv))
  · intro c hc hb hu
    exact h.1 c (fun hd => hi (DepXB.ochild hc hb hu hd))

theorem vRhs_nodepB {M : Mat} {B : Nat → Prop} {i : Nat} {ρ₁ ρ₂ : Valn} (h : AgreeOffB M B ρ₁ ρ₂)
    (hi : ¬ DepXB M B false i) : vRhs M ρ₁ i = vRhs M ρ₂ i := by
  apply vRhs_congr
  · intro m h1 hm
    exact h.2 m (fun hd => hi (DepXB.vpar h1 hm hd))
  · intro k h1 h2 hk
    exact h.2 k (fun hd => hi (DepXB.vupg h1 h2 hk hd))
  · intro j hj h1 h2 hb k hk
    exact h.1 k (fun hd => hi (DepXB.vbump h1 h2 hj hb hk hd))

/-- With no bad calls the closure is empty: the generalized engine is the old one. -/
theorem DepXB.empty {M : Mat} : ∀ {b i}, ¬ DepXB M (fun _ => False) b i := by
  intro b i h
  induction h with
  | leaf h => exact h
  | ochild _ _ _ _ ih => exact ih
  | ov _ ih => exact ih
  | vpar _ _ _ ih => exact ih
  | vupg _ _ _ _ ih => exact ih
  | vbump _ _ _ _ _ _ ih => exact ih

end Ytosk.WfQnE3
