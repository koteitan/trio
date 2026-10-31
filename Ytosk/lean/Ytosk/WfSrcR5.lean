/-
**`WfT2Src.T2AbsNSrcW` from the round-5 residuals (2026-10-31).**

- The lower-row case shared by (a) and (b): `WfSrcP.PLowRes`.
- The next-column case of (a): `ATerm` (only the terminal shape `WfSrcO.Term` of the change chain).
- The next-column case of (b): `BTerm` (only the terminal shape `WfSrcO.TermB`).
- (c): `WfSrcC2.SrcC3Res`.
-/
import Ytosk.WfSrcO1
import Ytosk.WfSrcP1
import Ytosk.WfSrcC2b

namespace Ytosk.WfSrcR5

open T

set_option linter.unusedSectionVars false

/-- **Residual (a), next-column case**: only the terminal shape of the change chain is left. -/
def ATerm : Prop :=
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
        ¬ Anc0 M c (r + L - 1) → WfSrcO.Term M (r + L) m c →
        ¬ WfT2Abs.DropFail M ρ τ (r + L) i

theorem srcARem3_of (h : ATerm) : WfSrcP.SrcARem3 := by
  intro M ρ rk C hB2 hz hs r L hx hr ha τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcl hce
    hearly hrow hsh
  obtain ⟨c', q, hN, hc'x, hup, hchg, hq0, hq1, hqm, hqne⟩ := hsh
  have hnA : ¬ Anc0 M c (r + L - 1) := fun hA =>
    hN.2.2 (anc_between hA c' (by have := hN.1; omega) (by omega))
  exact h M ρ rk C hB2 hz hs r L hx hr ha τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcl hce
    hearly hrow hnA
    (WfSrcO.chain_term C.S (x := r + L) (by omega) (r + L - c') c' (le_refl _) hc'x hup hchg q hq0 hq1
      hqm hqne c hN.1)

/-- **Residual (b), next-column case**: only the terminal shape `TermB` is left. -/
def BTerm : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → ∀ x, x + 1 = M.length →
    par M 2 x = some (x - 1) → par M 0 x = some (x - 1) → par M 1 x = some (x - 1) →
    ∀ τ, Cons (M.take x) τ → ∀ i m j c, i < x → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      par M 0 i = some m → par M 1 i = some m → j ∈ children M i → col M j = bump M i →
      c ∈ children M j → c < x - 1 → τ.o c ≠ ρ.o c →
      (∃ B, children (M.take x) i = B ++ [j] ∧
        ∀ d ∈ B, bumpTerm (M.take x) τ i d = bumpTerm M ρ i d) →
      (∃ K, children M j = K ++ [c] ∧ ∀ d ∈ K, τ.o d = ρ.o d ∧ entry M 1 d < entry M 1 m) →
      entry M 1 c ≤ entry M 1 m → ¬ Anc0 M c (x - 1) → WfSrcO.TermB M x m c →
      ¬ WfT2Abs.DropFail M ρ τ x i

theorem srcBNonlost3_of (h : BTerm) : WfSrcP.SrcBNonlost3 := by
  intro M ρ rk C hB x hx hr hp0 hp1 τ hT i m j c hi h1 h2 hmi hm1 hj hb hc hcx hce hBr hKr hrow hnA _
  have hRT : Rk (M.take x) rk := rk_take (by omega) C.I.rank
    (by have := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
        simpa only [show M.length - 1 = x from by omega] using this)
  exact h M ρ rk C hB x hx hr hp0 hp1 τ hT i m j c hi h1 h2 hmi hm1 hj hb hc hcx hce hBr hKr hrow hnA
    (WfSrcO.termB_of_term C.S hx hB hp0
      (WfSrcO.term_of_outside C.S C.I.cons C.I.good hx hT hRT hmi h2 hj hb hc (by omega) hce hnA hrow))

/-- **Bridge**: `T2AbsNSrcW` from `PLowRes`, `ATerm`, `BTerm` and `SrcC3Res`. -/
theorem t2AbsNSrcW_of (hP : WfSrcP.PLowRes) (hA : ATerm) (hB : BTerm) (hC : WfSrcC2.SrcC3Res) :
    WfT2Src.T2AbsNSrcW :=
  WfSrcB.t2AbsNSrcW_of
    (WfSrcABC.srcA_of_rem2 (WfSrcP.srcARem2_of (WfSrcP.pLow_of_res hP) (srcARem3_of hA)))
    (WfSrcB.srcBNonlost_of_2 (WfSrcP.srcBNonlost2_of (WfSrcP.pLow_of_res hP) (srcBNonlost3_of hB)))
    (WfSrcC2.srcC_of_c3 hC)

end Ytosk.WfSrcR5
