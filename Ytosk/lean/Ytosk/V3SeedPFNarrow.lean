/-
**t = 2: fields of `SeedPFResV3R` that are already proved (2026-11-06).**

`SeedPFResV3R` (V3C2QKids) carries the relation bundles `QRRel`, `QNRel`, `CRel` (V3SeedPF).  Some of their fields have
proofs from October on the plain context (`Std`, `M ≠ SRO`, `Inv3W`):
- `QRRel.ks` (`v(r) + k < v(x)`): `v(x) = v(r) + ω` (`v_x_qr`) and `app_natT_lt_add_w` (V3T2SeedRes).
- `QNRel.Bc`: `qn_Bc` (V3T2SeedRes).
- `QNRel.σB`: `qn_sigmaB` (V3T2QNSig) from the narrower value residual `unc`: the uncounted children `d` of `r`
  before `q` have `qnS < v(d)`.
- `CRel.un` is the C1 premise itself; `CRel.vqP` from it: `c_vqP_of_un` (V3T2CVq).
- `QNRel.base` for every `k` from `k = 0` (`V < t₁`, `t₁` standard from the state of `M.take x`): `tqN_facts`.
The bundles `QRRelR`, `QNRelR`, `CRelR` keep the rest; `SeedPFResV3R2`, `SeedVFResV3R2` and the entry points
`hSF_of3`, `hSP_of3`, `hN_of7` use them.
-/
import Ytosk.V3C2QKids

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- `QRRel` without `ks`. -/
structure QRRelR (M : Mat) (ρ : Valn) (r L : Nat) (Lc : List Nat) : Prop where
  w1 : ∀ τ, Cons (M.take (r + L)) τ → ¬ t2B (ρ.v r) ρ Lc < t2W1 (M.take (r + L)) (ρ.v r) τ r

/-- `QNRel` without `Bc`, with `σB` replaced by the value residual `unc`, and `base` only at `k = 0` (the other
`k` follow by `tqN_facts`). -/
structure QNRelR (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop where
  unc : ∀ d ∈ children M r, d < q → ¬ Counted M r d → qnS M ρ r L q < ρ.v d
  base : ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ∧
    ρ.v r < t1

/-- `CRel` without `un` and `vqP`. -/
structure CRelR (M : Mat) (ρ : Valn) (r L q : Nat) : Prop where
  decP : ∀ τ, Cons (M.take (r + L)) τ → ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] →
    ∃ s y, τ.o c0 = psi s y z ∧ qnS M ρ r L q < s
  rw : ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
    step (ρ.v r) (t2X1 M r L τ) (qnS M ρ r L q) (step (qnS M ρ r L q) z (qnS M ρ r L q)
      (sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)) z) z =
    sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)

theorem qrRel_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk)
    {r L : Nat} {Lc : List Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (h : QRRelR M ρ r L Lc) : QRRel M ρ r L Lc :=
  ⟨fun k => by rw [v_x_qr I hlen hr]; exact app_natT_lt_add_w _ k, h.w1⟩

theorem qnRel_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} {Lc : List Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hCL : CL M r = Lc ++ [q])
    (h : QNRelR M ρ r L q Lc) : QNRel M ρ r L q Lc := by
  refine ⟨qn_sigmaB hM hS I hlen hr hq hqr hCL h.unc, qn_Bc hM hS I hlen hr hq hqr hCL, fun τ hτ => ?_⟩
  obtain ⟨t1, heq, hVt⟩ := h.base τ hτ
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hrM : r < M.length := by omega
  have hτ' : Cons (M.take (M.length - 1)) τ := by rw [show M.length - 1 = r + L by omega]; exact hτ
  have hG := good3_take_anyV3U I (Ctx.drop (by omega)) (by omega) hτ'
  rw [show M.length - 1 = r + L by omega] at hG
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hot := hG.ot_o r hrT
  rw [o_cl_eq hτ hG hrT] at hot
  have hst := isOT_arg hot
  rw [heq] at hst
  have ht1 : isOT t1 = true := isOT_sub (isOT_app_right hst)
  have hF := tqN_facts (I.good.ot_v r hrM) (qnS_ot I hrM L q) (qnS_gt M ρ r L q) hVt ht1
  exact ⟨t1, heq, fun k => ⟨(hF k).2.1, (hF k).2.2⟩⟩

theorem cRel_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hun : upg M (r + L - 1) = none)
    (h : CRelR M ρ r L q) : CRel M ρ r L q :=
  ⟨h.decP, hun, c_vqP_of_un hM hS I hlen hr hq hqr hun, h.rw⟩

/-- `SeedPFResV3R` with the narrower relation bundles. -/
structure SeedPFResV3R2 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → QRRelR M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → SVRel M ρ r L
  qn : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → QNRelR M ρ r L q Lc
  C1 : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → CRelR M ρ r L q ∧ T2SeedCBig M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QPF M r L r

theorem seedPFResV3R_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk) (h : SeedPFResV3R2 M ρ) :
    SeedPFResV3R M ρ :=
  ⟨fun r L hlen hr hq hXu Lc hLc => qrRel_of I hlen hr (h.qr r L hlen hr hq hXu Lc hLc), h.sv,
    fun r L q hlen hr hq hqr Lc hLc => qnRel_of hM hS I Ctx hlen hr hq hqr hLc (h.qn r L q hlen hr hq hqr Lc hLc),
    fun r L q hlen hr hq hqr hncl hun => ⟨cRel_of hM hS I hlen hr hq hqr hun (h.C1 r L q hlen hr hq hqr hncl hun).1,
      (h.C1 r L q hlen hr hq hqr hncl hun).2⟩, h.C2r⟩

/-- `SeedVFResV3R` with the narrower relation bundles. -/
structure SeedVFResV3R2 (M : Mat) (ρ : Valn) : Prop where
  pf : SeedPFResV3R2 M ρ
  qnDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom M ρ r L q Lc
  cDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → T2SeedCDom M ρ r L q
  C2r : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFr QVF M r L r

theorem seedVFResV3R_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk) (h : SeedVFResV3R2 M ρ) :
    SeedVFResV3R M ρ :=
  ⟨seedPFResV3R_of hM hS I Ctx h.pf, h.qnDom, h.cDom, h.C2r⟩

/-- **The inputs hSF, hSP and hN** with the narrower seed bundles. -/
theorem hSF_of3 (hRes : T2AtV3 (fun M ρ => SeedPFResV3R2 M ρ)) (hK : T2AtV3 (fun M ρ => C2Kids M ρ))
    (hC2 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFO.T2C2RootRel M ρ r L q)) :
    T2AtV3 (fun M _ => T2SeedFrames G.QT2F M) :=
  hSF_of2 (fun M ρ rk C hz h2 => seedPFResV3R_of C.std C.ne (coreW C.S C.I) C (hRes M ρ rk C hz h2)) hK hC2

theorem hSP_of3 (hRes : T2AtV3 (fun M ρ => SeedPFResV3R2 M ρ)) (hK : T2AtV3 (fun M ρ => C2Kids M ρ))
    (hC2 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFO.T2C2RootRel M ρ r L q)) :
    T2AtV3 (fun M _ => T2SeedFrames G.QT2P M) :=
  hSP_of2 (fun M ρ rk C hz h2 => seedPFResV3R_of C.std C.ne (coreW C.S C.I) C (hRes M ρ rk C hz h2)) hK hC2

theorem hN_of7 (hBXU : T2AtV3 T2BelowAtV3U) (hVF : T2AtV3 (fun M ρ => SeedVFResV3R2 M ρ))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M))
    (hK : T2AtV3 (fun M ρ => C2Kids M ρ))
    (hQN : T2AtV3 (fun M ρ => ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc))
    (hC : T2AtV3 (fun M _ => T2VRASeedC M))
    (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc2 M))
    (hVD : T2AtV3 (fun M _ => T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M))
    (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M)) :
    T2SmallV3 :=
  hN_of6 hBXU (fun M ρ rk C hz h2 => seedVFResV3R_of C.std C.ne (coreW C.S C.I) C (hVF M ρ rk C hz h2))
    hFD hK hQN hC hCopy hVD hAG

#print axioms hSF_of3
#print axioms hSP_of3
#print axioms hN_of7

end Ytosk.V3Main.SeedPF
