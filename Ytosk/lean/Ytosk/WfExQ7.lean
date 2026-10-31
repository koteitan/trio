/-
**WfExQ7 (2026-11-01): `ExpStepQ` of `Inv3V3` for the q = r chain, with the exact remaining list.**

`expStepQ_V3X`: `ExpStepQ PnV3 (ExDQX M r L ρ) M r L d0 ρ` (the `hPs` of WfQrH7.qr_chainH3 with `Pn = PnV3`) from
- proved (WfExQ2/4/5/6): `cons`, `good`, `rank`, `rootS`, `rootP`, `fo`, `kd`, `td`, and `ph`, `fc3`, `fc` up to their
  leaf residuals;
- remaining:
  * `hOmPH : OmQRes PH' …`, `hOmF3 : OmQRes F3' …`, `hOmFC : FCOmRes …` (frames of `M` before `x` whose child is a
    leaf `Ω_{t+1}` with `v(i) ≤ t`, at the new value; for `glueZ` these were `frameQROmN_t1S` / `frameClosedOmN_t1S`),
  * `hVSF : ExpStepQR PnV3 VSmallF …`, `hVRA : ExpStepQR PnV3 VSmallRAll …` (component conditions of the new `v`
    values; for `glueZ` these were `VSFRes2`/`PassRootRes` and `T1VSRAllStep`),
  * `hFr : FrameAtN M r L d0` (the nine last-column frame fields of `M[n]` and the two leaf conditions;
    WfExQ3: from the global `HFrameV3`).
`exDQX_of_loc`: the extra facts `ExDQX` follow from the C_strip conjuncts of `hLocH` and its premise `ρP.o r < o(x)`.
-/
import Ytosk.WfExQ6
import Ytosk.WfExQ3

namespace Ytosk.WfExQ7
open T Ytosk Ytosk.G Ytosk.WfExQ1 Ytosk.WfExQ2 Ytosk.WfExQ4 Ytosk.WfExQ5 Ytosk.WfExQ6 Ytosk.WfQrL1 Ytosk.WfQrL7
  Ytosk.WfQrH6

set_option linter.unusedSectionVars false

/-- `ExDQX` from `hLocH`'s C_strip conjuncts and its premise on `ρP.o r`. -/
theorem exDQX_of_loc {M : Mat} {r L : Nat} {ρ σ : Valn} (n : Nat) (ρP : Valn)
    (hlt : ρP.o r < ρ.o (r + L))
    (ho : ∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS)
    (hv : ∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) :
    ExDQX M r L ρ n ρP σ.o σ.v :=
  ⟨exDQ_of_strip n ρP ho hv, le_of_lt hlt⟩

/-- **`ExpStepQ` of `Inv3V3` with `ExDQX`, from the exact remaining list.** -/
theorem expStepQ_V3X {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hOmPH : OmQRes PH' M r L d0 ρ) (hOmF3 : OmQRes F3' M r L d0 ρ) (hOmFC : FCOmRes M r L d0 ρ)
    (hVSF : ExpStepQR PnV3 (fun N σ => VSmallF N σ) (ExDQX M r L ρ) M r L d0 ρ)
    (hVRA : ExpStepQR PnV3 (fun N σ => VSmallRAll N σ) (ExDQX M r L ρ) M r L d0 ρ)
    (hFr : FrameAtN M r L d0) :
    ExpStepQ PnV3 (ExDQX M r L ρ) M r L d0 ρ := by
  intro n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  obtain ⟨_, _, ⟨rkN, hR⟩, hS, hP⟩ :=
    expStepQ_easy hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00 h1 hx2
      I.rank I.rootP PnV3 n hn ρP oq vq hCP hGP hPP hCN hGN hEx.1
  have hph := expStepQR_ph3c S I hlen hL hd0e h1 hx2 hOmPH n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  have hf3 := expStepQR_fc3 S I hlen hL hd0e h1 hx2 hOmF3 n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  have hfc := expStepQR_fc S I hlen hL hd0e h1 hx2 hOmFC n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  have hfo := expStepQR_fo S I hlen hL hd0e h1 hx2 (ExDQX M r L ρ) n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  obtain ⟨hkd, htd⟩ := expStepQR_bumpDec S I hlen hL hd0e h1 hx2 n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  have hvs := hVSF n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  have hvra := hVRA n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  obtain ⟨F, hTP, hTPW⟩ := hFr n hn _ rkN hCN hR hGN
  exact ⟨rkN, inv3V3_of_parts hCN hGN hR hS hP ⟨hvs, hfc, hfo, hkd, htd, hph, hf3, hvra⟩ F hTP hTPW⟩

end Ytosk.WfExQ7
