/-
**t = 2 の生産者を差し込んだ現状の最上位（2026-10-16、top）。**

- `trio_terminates_main_V2_t2`: `trio_terminates_main_V2_glob` の `ExpT2V2`・`R2V2` を t2 の
  `expT2V2_of`・`r2V2_of`（V3ExpT2V2）で埋めたもの。枠と葉は共通の残り `HFrameV2`・`HLeafV2`。
- `T2SeedPResRV2`・`t2SeedPResV2_of`: 種の残り `T2SeedPResV2` を、t2 が M だけで決まる欄を外した
  `T2SeedPResR`（V3T2SeedRes）に替える。
- `trio_terminates_main_V2_t2R`: 上の最上位で種の残りを `T2SeedPResRV2` に替えたもの。
- C の欄（2026-10-16 追記）: 構造の残り T2SeedCNext は標準形で偽なので、C の欄は T2SeedCRes ∧ T2SeedCBig に
  替えた。`HSibV2`（どの標準形でも値の残り UpgSibV、V3CBigV）と C の残り T2SeedCRes から CBig を出す
  （`t2SeedPResR_of_sib`）。`trio_terminates_main_V2_t2S` はその形の最上位。
- `trio_terminates_main_V2_cur`: 現状の最上位。T2VSFCV2 は t2 の `t2VSFCV2_of`（V3T2VSFC）、t = 1 の結論
  ExpT1OutV2 は t1 の `expT1Out_V2_glob`（V3T1VSRAll、残りは HFrameV2・HLeafV2 だけ）、t = 0 は t0 の
  `expT0V2_of3`（V3T0Inv2S、切り口の残りの代わりに T0RwRes）で埋めた。HSibV2 は難しい形 `HSibHardV2`（V3SibV）に絞った。
-/
import Ytosk.V3ExpT2V2
import Ytosk.V3T2SeedRes
import Ytosk.V3CBigV
import Ytosk.V3T2VSFC
import Ytosk.V3T1VSRAll
import Ytosk.V3T0Inv2S
import Ytosk.V3SibV

namespace Ytosk

open T

/-- **The current top theorem with the `t = 2` producers plugged in.** -/
theorem trio_terminates_main_V2_t2 (hD : HDropV2) (hSd : HSeedV2) (hA : HAbSV2)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hCut : T0CutResGGC)
    (h1 : ExpT1V2)
    (hB : T2BelowXRes) (hFO : T2FOSeedV2) (hPR : T2SeedPResV2) (hVF : T2VSFCV2) (hVA : T2VRAV2) :
    WellFounded Step' :=
  trio_terminates_main_V2_glob hD hSd hA hF hLf hCut h1
    (expT2V2_of hB hFO hPR hVF hVA hF hLf) (r2V2_of hB)

/-- **t2-seed, reduced**: the seed residual with the fields fixed by `M` alone removed (V3T2SeedRes). -/
def T2SeedPResRV2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedPResR M ρ

theorem t2SeedPResV2_of (h : T2SeedPResRV2) : T2SeedPResV2 := by
  intro M ρ rk C hz h2
  exact t2SeedPRes_of C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ (h M ρ rk C hz h2)

/-- **The current top theorem with the reduced seed residual.** -/
theorem trio_terminates_main_V2_t2R (hD : HDropV2) (hSd : HSeedV2) (hA : HAbSV2)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hCut : T0CutResGGC)
    (h1 : ExpT1V2)
    (hB : T2BelowXRes) (hFO : T2FOSeedV2) (hPR : T2SeedPResRV2) (hVF : T2VSFCV2) (hVA : T2VRAV2) :
    WellFounded Step' :=
  trio_terminates_main_V2_t2 hD hSd hA hF hLf hCut h1 hB hFO (t2SeedPResV2_of hPR) hVF hVA

/-- **The value residual `UpgSibV` of every standard matrix.** -/
def HSibV2 : Prop :=
  ∀ N σ, Std N → N ≠ SRO → Cons N σ → Good3 N σ → UpgSibV N σ

/-- **The hard shapes of `UpgSibV` of every standard matrix** (V3SibV). -/
def HSibHardV2 : Prop :=
  ∀ N σ, Std N → N ≠ SRO → Cons N σ → Good3 N σ → UpgSibVHard N σ

theorem hSib_of_hard (h : HSibHardV2) : HSibV2 := fun N σ hN hS hC hG =>
  upgSibV_of_hard (sInvXJ_std hN hS).1 (S1_std hN) hC hG (h N σ hN hS hC hG)

/-- `T2SeedPResR` with the C field reduced to `T2SeedCRes`. -/
structure T2SeedPResRC (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQRResR M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → T2SeedSVResR M ρ r L
  qn : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNResR M ρ r L q Lc
  C : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCRes M ρ r L q

/-- **t2-seed, reduced, without CBig.** -/
def T2SeedPResRCV2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedPResRC M ρ

theorem t2SeedPResR_of_sib (hSib : HSibV2) (h : T2SeedPResRCV2) : T2SeedPResRV2 := by
  intro M ρ rk C hz h2
  have H := h M ρ rk C hz h2
  refine ⟨H.qr, H.sv, H.qn, fun r L q hlen hr hq hqr hncl => ⟨H.C r L q hlen hr hq hqr hncl, ?_⟩⟩
  have hL : 0 < L := by
    have := par_lt M 0 (r + L) q hq
    have := par_lt M 2 (r + L) r hr; omega
  obtain ⟨I1, _⟩ := C.pre (r + L) (by omega) (by omega)
  exact G.t2SeedCBig_of_sibV C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hlen hr hq hqr hncl
    (H.C r L q hlen hr hq hqr hncl)
    (fun τ hτ hG => hSib _ τ (std_take C.std (r + L) (by omega)) (ne_SRO_of_rk I1.rank) hτ hG)

/-- **The current top theorem with `HSibV2`** in place of the false `T2SeedCNext`. -/
theorem trio_terminates_main_V2_t2S (hD : HDropV2) (hSd : HSeedV2) (hA : HAbSV2)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hCut : T0CutResGGC)
    (h1 : ExpT1V2)
    (hB : T2BelowXRes) (hFO : T2FOSeedV2) (hPR : T2SeedPResRCV2) (hSib : HSibV2) (hVF : T2VSFCV2)
    (hVA : T2VRAV2) : WellFounded Step' :=
  trio_terminates_main_V2_t2R hD hSd hA hF hLf hCut h1 hB hFO (t2SeedPResR_of_sib hSib hPR) hVF hVA

/-- **The current top theorem**: everything committed so far plugged in. The hypotheses are the named
residuals: drop `HDropV2`・`HSeedV2`・`HAbSV2`; shared `HFrameV2`・`HLeafV2`; t0 `T0RwRes`;
t2 `T2BelowXRes`・`T2FOSeedV2`・`T2SeedPResRCV2`・`FDsh`・`T2SeedVSFV2`・`T2SeedFCV2`・`T2VRAV2`; top `HSibHardV2`. -/
theorem trio_terminates_main_V2_cur (hD : HDropV2) (hSd : HSeedV2) (hA : HAbSV2)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hRw : T0RwRes)
    (hB : T2BelowXRes) (hFO : T2FOSeedV2) (hPR : T2SeedPResRCV2) (hSib : HSibHardV2)
    (hFD : FDsh) (hSV : T2SeedVSFV2) (hSF : T2SeedFCV2) (hVA : T2VRAV2) : WellFounded Step' :=
  terminates_of_desc3 (desc3_V2O hD hSd hA (hTake_of_glob hF hLf)
    (expT0V2_of3 hRw (t0Leaf_of_glob hLf) (t0Frame_of_glob hF))
    (expT1Out_V2_glob hF hLf)
    (expT2V2_of hB hFO (t2SeedPResV2_of (t2SeedPResR_of_sib (hSib_of_hard hSib) hPR)) (t2VSFCV2_of hB hFD hSV hSF) hVA hF hLf)
    (r2V2_of hB))

end Ytosk
