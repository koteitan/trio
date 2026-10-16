/-
**t = 0 の Inv3V2 を、T0CutResGGC でなく M の書き換える枠の B が閉じていること（RwClosed）で（2026-10-17、t0）。**

`t0DF_ofS`: V3T0Inv2 の `t0DF_ofC` の写しで、D の帰納法を V3T0DepS の `t0_otdS`（影の枠を直接扱う）に替えたもの。
`expT0V2_of3`: top の `ExpT0V2` を、残り `T0RwRes`（標準形 M の RwClosed）と N の 2 つの残りから。
-/
import Ytosk.V3T0Inv2
import Ytosk.V3T0DepS

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`T0DF` from the core bundles**, `PH3cG`, `VSmallRA` and `RwClosed` of `M` (no cut residual). -/
theorem t0DF_ofS {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M)
    (hS : M ≠ SRO) (I : Inv3C M ρ rk) (R : Res3C M ρ rk) (hPH : PH3cG M ρ) (hVA : VSmallRA M ρ)
    (hClB : RwClosed M ρ)
    (hAbW : ∀ r L, r + L + 1 = M.length → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 → T0AbsW M r L ρ) :
    T0DF M ρ := by
  intro r L hlen hL hp he1 n hn σ hCN
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hab0 := hAbW r L hlen hp he1
  have h := t0_otdS hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab hab0 hDr.ws hDr.vst hDr.ua I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    (hVA.toP (r + L) r) hPH hClB
    (t0_shape3C hM hS I R hlen hL hp he1) (t0IVResC_holds M ρ rk r L hM hS I R hlen hL hp he1) n hn σ hCN
  intro i hi
  refine ⟨fun hd => ?_, (h i hi).2⟩
  obtain ⟨h1, h2, _, h4, h5⟩ := (h i hi).1 hd
  exact ⟨h1, h2, trivial, h4, h5⟩

/-- **Residual: the state of every rewriting frame is closed**, for the standard forms in top's step context. -/
def T0RwRes : Prop := ∀ M ρ rk, StepCtxV2 M ρ rk → RwClosed M ρ

/-- **Residual: the weak absorption** at the `t = 0` expansions (replaces the strong `AbsSR`, which is false
on standard forms under the exact `◁`; drop, 2026-10-17). -/
def T0AbWRes : Prop := ∀ M ρ rk, StepCtxV2 M ρ rk → ∀ r L, r + L + 1 = M.length → par M 0 (r + L) = some r →
  entry M 1 (r + L) = 0 → T0AbsW M r L ρ

/-- **top's `ExpT0V2`** from `T0RwRes`, `T0AbWRes` and the two residual fields of `N` (no cut residual and no
strong absorption). -/
theorem expT0V2_of4 (hRw : T0RwRes) (hAbW : T0AbWRes)
    (hLeaf : T0NRes (fun N σ _ => TP1LeafG N σ ∧ TP1WLeafG N σ)) (hFrm : T0NRes TakeFrameV2) :
    ExpT0V2 := by
  intro M ρ rk C hz hs0 n hn2
  obtain ⟨r, L, hlen, hL, hp, he1, hexp⟩ := t0_shapeS C.S hz hs0
  rw [hexp n]
  have hpre := (C.pre (r + L) (by omega) (by omega)).1
  obtain ⟨ρN, rkN, IN, _, _⟩ := t0_final_inv3V2D C.std C.ne C.S C.I hlen hL hp he1 C.R.drop
    (hAbW M ρ rk C r L hlen hp he1) hpre
    (t0DF_ofS C.std C.ne (C.I.toC C.S) ⟨C.R.drop⟩ C.I.ph C.I.vra.toLast (hRw M ρ rk C)
      (fun r' L' hl' hp' he' => hAbW M ρ rk C r' L' hl' hp' he'))
    (hLeaf M ρ rk r L C hlen hL hp he1) (hFrm M ρ rk r L C hlen hL hp he1)
    n hn2
  exact ⟨ρN, rkN, IN⟩

/-- `expT0V2_of4` with the strong absorption `AbsSR` of the step context (the earlier interface). -/
theorem expT0V2_of3 (hRw : T0RwRes)
    (hLeaf : T0NRes (fun N σ _ => TP1LeafG N σ ∧ TP1WLeafG N σ)) (hFrm : T0NRes TakeFrameV2) :
    ExpT0V2 :=
  expT0V2_of4 hRw (fun M ρ rk C r L hlen hp he1 => T0AbsW.of_strong (C.R.abS r
    (by rw [show M.length - 1 = r + L by omega]; exact hp) (by rw [show M.length - 1 = r + L by omega]; exact he1)))
    hLeaf hFrm

end Ytosk
