/-
**全員の生産者を差し込んだ現状の最上位（2026-10-16〜17、top）。**

- `T2SeedPResRV2`・`t2SeedPResV2_of`: 種の残り `T2SeedPResV2` を、t2 が M だけで決まる欄を外した
  `T2SeedPResR`（V3T2SeedRes）に替える。
- 種の残り `T2SeedPResRC`: qr は t2 の T2SeedQRResR、sv は t2 の T2SVStrict（rw を出す、V3T2SeedRes2）と lhd、
  qn は base だけ（unc = QNUncRes は UpgSibV から、V3QNUncV）、C は T2SeedCRes だけ（CBig は UpgSibV から）。
- C の欄: 構造の残り T2SeedCNext は標準形で偽なので、C の欄は T2SeedCRes ∧ T2SeedCBig に替えた。
  `HSibV2`（どの標準形でも値の残り UpgSibV、V3CBigV）と C の残り T2SeedCRes から CBig を出す
  （`t2SeedPResR_of_sib`）。HSibV2 は難しい形 `HSibHardV2`（V3SibV）に絞った（`hSib_of_hard`）。
- `expT0Out_of4`: t0 の `t0_final_inv3V2D` の下降まで含めた結論 ExpT0OutV2（残り T0RwRes・T0AbWRes と N の 2 つ）。
  最上位は t = 0 の下降もここから受け、偽の強い吸収 HAbSV2 を使わない（2026-10-17）。
- `trio_terminates_main_V2_cur`: 現状の最上位。T2VSFCV2 は t2 の `t2VSFCV2_of`（V3T2VSFC）、T2VRAV2 は t2 の
  `t2VRAV2_of`（V3T2VRA）、t = 1 の結論
  ExpT1OutV2 は t1 の `expT1Out_V2_glob`（V3T1VSRAll）、t = 0 は `expT0Out_of4`。
-/
import Ytosk.V3ExpT2V2
import Ytosk.V3T2SeedRes
import Ytosk.V3CBigV
import Ytosk.V3T2VSFC
import Ytosk.V3T1VSRAll
import Ytosk.V3T0Inv2S
import Ytosk.V3SibV
import Ytosk.V3QNUncV
import Ytosk.V3T2SeedRes2
import Ytosk.V3T2VRA

namespace Ytosk

open T

/-- **t2-seed, reduced**: the seed residual with the fields fixed by `M` alone removed (V3T2SeedRes). -/
def T2SeedPResRV2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedPResR M ρ

theorem t2SeedPResV2_of (h : T2SeedPResRV2) : T2SeedPResV2 := by
  intro M ρ rk C hz h2
  exact t2SeedPRes_of C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ (h M ρ rk C hz h2)

/-- **The value residual `UpgSibV` of every standard matrix.** -/
def HSibV2 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ → UpgSibV N σ

/-- **The hard shapes of `UpgSibV` of every standard matrix** (V3SibV). -/
def HSibHardV2 : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ → UpgSibVHard N σ

theorem hSib_of_hard (h : HSibHardV2) : HSibV2 := fun N σ rk hN hS hC hR hG =>
  upgSibV_of_hard (sInvXJ_std hN hS).1 (sInvXJ_std hN hS).2 (S1_std hN) hC hR hG (h N σ rk hN hS hC hR hG)

/-- **The seed residuals left at the top** (2026-10-17): `qr` as t2's `T2SeedQRResR`; `sv` as t2's
`T2SVStrict` (V3T2SeedRes2, gives `rw`) and the `lhd` field; `qn` only the `base` field (the `unc` field
`QNUncRes` comes from `UpgSibV`, V3QNUncV); `C` only `T2SeedCRes` (`T2SeedCBig` comes from `UpgSibV`, V3CBigV). -/
structure T2SeedPResRC (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQRResR M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → T2SVStrict M ρ r L ∧
      ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k →
        Lhd z (psi (ρ.v r) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) z) (ρ.o r)
  qn : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
      spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ∧
      ∀ k, ρ.v r < tqN (ρ.v r) (qnS M ρ r L q) t1 k ∧
        ¬ shf (ρ.v r) (qnS M ρ r L q) (tqN (ρ.v r) (qnS M ρ r L q) t1 k) < succ (qnS M ρ r L q) ∧
        (1 ≤ k → tqN (ρ.v r) (qnS M ρ r L q) t1 k < ρ.v q ∧
          (tqN (ρ.v r) (qnS M ρ r L q) t1 k = ρ.v q ∨ Lhd z (tqN (ρ.v r) (qnS M ρ r L q) t1 k) (ρ.v q)))
  C : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCRes M ρ r L q

/-- **t2-seed, reduced** (the residuals of `T2SeedPResRC`). -/
def T2SeedPResRCV2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedPResRC M ρ

theorem t2SeedPResR_of_sib (hSib : HSibV2) (h : T2SeedPResRCV2) : T2SeedPResRV2 := by
  intro M ρ rk C hz h2
  have H := h M ρ rk C hz h2
  have IW := Inv3W.ofV2 C.S C.I
  refine ⟨H.qr, fun r L hlen hr hq hux => ?_, fun r L q hlen hr hq hqr Lc hCL => ?_,
    fun r L q hlen hr hq hqr hncl => ⟨H.C r L q hlen hr hq hqr hncl, ?_⟩⟩
  · obtain ⟨hSt, hlhd⟩ := H.sv r L hlen hr hq hux
    exact ⟨sv_rw_of C.std C.ne IW ⟨C.R.drop⟩ hlen hr hq hux hSt, hlhd⟩
  · exact t2SeedQNResR_of2 C.std C.ne IW hlen hr hq hqr hCL
      ⟨qnUncRes_of_sibV C.std C.ne IW hlen hr hq hqr hCL (hSib M ρ rk C.std C.ne C.I.cons C.I.rank C.I.good),
        H.qn r L q hlen hr hq hqr Lc hCL⟩
  · have hL : 0 < L := by
      have := par_lt M 0 (r + L) q hq
      have := par_lt M 2 (r + L) r hr; omega
    obtain ⟨I1, _⟩ := C.pre (r + L) (by omega) (by omega)
    exact G.t2SeedCBig_of_sibV C.std C.ne IW ⟨C.R.drop⟩ hlen hr hq hqr hncl
      (H.C r L q hlen hr hq hqr hncl)
      (fun τ hτ hG => hSib _ τ rk (std_take C.std (r + L) (by omega)) (ne_SRO_of_rk I1.rank) hτ I1.rank hG)

/-- **`ExpT0OutV2` from t0's residuals** (`expT0V2_of4` with the descent of `t0_final_inv3V2D` kept). -/
theorem expT0Out_of4 (hRw : T0RwRes) (hAbW : T0AbWRes)
    (hLeaf : T0NRes (fun N σ _ => TP1LeafG N σ ∧ TP1WLeafG N σ)) (hFrm : T0NRes TakeFrameV2) :
    ExpT0OutV2 := by
  intro M ρ rk C hz hs0 n hn2
  obtain ⟨r, L, hlen, hL, hp, he1, hexp⟩ := t0_shapeS C.S hz hs0
  rw [hexp n]
  have hpre := (C.pre (r + L) (by omega) (by omega)).1
  exact t0_final_inv3V2D C.std C.ne C.S C.I hlen hL hp he1 C.R.drop
    (hAbW M ρ rk C r L hlen hp he1) hpre
    (t0DF_ofS C.std C.ne (C.I.toC C.S) ⟨C.R.drop⟩ C.I.ph C.I.vra.toLast (hRw M ρ rk C)
      (fun r' L' hl' hp' he' => hAbW M ρ rk C r' L' hl' hp' he'))
    (hLeaf M ρ rk r L C hlen hL hp he1) (hFrm M ρ rk r L C hlen hL hp he1)
    n hn2

/-- **The current top theorem**: everything committed so far plugged in. The hypotheses are the named
residuals: drop `HDropV2`・`HSeedV2`; shared `HFrameV2`・`HLeafV2`; t0 `T0RwRes`・`T0AbWRes`;
t2 `T2BelowXRes`・`T2FOSeedV2`・`T2SeedPResRCV2`・`FDsh`・`T2SeedVSFV2`・`T2SeedFCV2`・`QVRAsh` and the three
`T2VRAV2` parts (seed columns, prefix levels, copy levels); top `HSibHardV2`.
None of them is the false strong absorption `HAbSV2`. -/
theorem trio_terminates_main_V2_cur (hD : HDropV2) (hSd : HSeedV2)
    (hF : HFrameV2) (hLf : HLeafV2)
    (hRw : T0RwRes) (hAbW : T0AbWRes)
    (hB : T2BelowXRes) (hFO : T2FOSeedV2) (hPR : T2SeedPResRCV2) (hSib : HSibHardV2)
    (hFD : FDsh) (hSV : T2SeedVSFV2) (hSF : T2SeedFCV2) (hsh : QVRAsh)
    (hVSd : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeed M)
    (hVPr : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAPre M ρ)
    (hVCp : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRACopy M) : WellFounded Step' :=
  terminates_of_desc3 (desc3_V2O hD hSd (hTake_of_glob hF hLf)
    (expT0Out_of4 hRw hAbW (t0Leaf_of_glob hLf) (t0Frame_of_glob hF))
    (expT1Out_V2_glob hF hLf)
    (expT2V2_of hB hFO (t2SeedPResV2_of (t2SeedPResR_of_sib (hSib_of_hard hSib) hPR)) (t2VSFCV2_of hB hFD hSV hSF)
      (t2VRAV2_of hsh hB hVSd hVPr hVCp) hF hLf)
    (r2V2_of hB))

end Ytosk
