/-
**V3SeedPFAll (2026-11-05): the PH/FC3 seed frames and the inputs hSF, hSP on the V3 context.**

The per-configuration producers of V3SeedPF (qr, qn, sv, C) are joined as in `G.seed_frames_PF`, with
- the source and prefix data taken from `StepCtx3` (no `Res3W`; the prefix values are `drop1 M x rk`),
- the residuals restricted to the fields actually read (`QRRel`, `QNRel`, `SVRel`, `CRel` + `T2SeedCBig`),
- the C configuration split by `upg M (x − 1)`: `none` (C1) uses `CRel` (whose field `un` holds there);
  `some k` (C2, where `un` is false, tmp/claude/measure_un.py) keeps the seed frames as the named residual.
`hSF_of`, `hSP_of` join this with the QFO input `hFO_of_C2rel` (V3SeedFOC2).
-/
import Ytosk.V3SeedPF

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The PH/FC3 seed property. -/
abbrev QPF (a : T) (Lv : List T) (cv : T) : Prop := QPHs a Lv cv ∧ QF3s a Lv cv

/-- **The residuals of the PH/FC3 seed frames on the V3 context**: only the fields actually read. -/
structure SeedPFResV3 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → QRRel M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → SVRel M ρ r L
  qn : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → QNRel M ρ r L q Lc
  C1 : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → CRel M ρ r L q ∧ T2SeedCBig M ρ r L q
  C2 : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → ∀ i, (i = r ∨ i = q) → SeedFr QPF M r L i

/-- **PH3cG and FC3 at the seed frames of every `M[n]`** (`t = 2`) on the V3 context. -/
theorem seed_frames_PFV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hRes : SeedPFResV3 M ρ) : T2SeedFrames QPF M := by
  have hM := Ctx.std
  have hS := Ctx.ne
  have I : Inv3W M ρ rk := coreW Ctx.S Ctx.I
  have hP : PH3cG M ρ := Ctx.I.ph
  have hF : FC3 M ρ := Ctx.I.fc3
  have hx : ∀ r L, r + L + 1 = M.length → M.length - 1 = r + L := fun r L h => by omega
  refine t2_seed_frames_of (Q := QPF) hM hS I ?_ ?_ ?_ ?_
  · intro r L hlen hr hq hXu Lc hLc n hn hlow σ hσ _ Lc' c R' hcl
    have J := Ctx.pre (r + L) (by have := par_lt M 2 _ r hr; omega) (by omega)
    exact seed_frames_qrV3 hM hS I Ctx hz h2 hlen hr hq hXu hLc (hRes.qr r L hlen hr hq hXu Lc hLc) J.cons
      ⟨rk, J.rank⟩ hP hF n hn hlow σ hσ Lc' c R' hcl
  · intro r L hlen hr hq hux n hn hlow σ hσ hG Lc' c R' hcl
    have J := Ctx.pre (r + L) (by have := par_lt M 2 _ r hr; omega) (by omega)
    have hSV := hRes.sv r L hlen hr hq hux
    have hFix := t2SeedSVFix_holdsV3 hM hS I Ctx hlen hr hq hux
    have hrN : r < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n).length := by
      have hc : c ∈ children _ r := cl_mem_children (by rw [hcl]; simp)
      have := mem_children hc; omega
    have hdec : ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n)
        r).map σ.o).Pairwise (fun a b => b ≤ a) := by
      rw [← cvals_eq_map hσ hG]; exact hG.dec r hrN
    exact seed_frames_svV3 hM hS I Ctx hz h2 hlen hr hq hux hSV hFix J.cons J.rank ⟨J.fo, J.ph, J.fc3⟩
      n hn hlow σ hσ hdec Lc' c R' hcl
  · intro r L q hlen hr hq hqr Lc hLc i hi n hn hlow σ hσ hG Lc' c R' hcl
    have J := Ctx.pre (r + L) (by have := par_lt M 2 _ r hr; omega) (by omega)
    have hQN := hRes.qn r L q hlen hr hq hqr Lc hLc
    have hFC := t2SeedQNFC_holdsV3 hM hS I Ctx hlen hr hq hqr hLc
    exact seed_frames_qnV3 hM hS I Ctx hz h2 hlen hr hq hqr hLc hQN hFC J.cons ⟨rk, J.rank⟩ hP hF
      n hn hlow σ hσ hG i hi Lc' c R' hcl
  · intro r L q hlen hr hq hqr hncl i hi n hn hlow σ hσ hG Lc' c R' hcl
    cases hu : upg M (r + L - 1) with
    | none =>
      have J := Ctx.pre (r + L) (by have := par_lt M 2 _ r hr; omega) (by omega)
      obtain ⟨hCR, hBig⟩ := hRes.C1 r L q hlen hr hq hqr hncl hu
      have hFix := t2SeedCFix_ofV3 hM hS I Ctx hlen hr hq hqr hncl hCR hBig
      exact seed_frames_CV3 hM hS I Ctx hz h2 hlen hr hq hqr hncl hCR hFix J.cons J.rank ⟨J.fo, J.ph, J.fc3⟩
        n hn hlow σ hσ hG i hi Lc' c R' hcl
    | some k =>
      exact hRes.C2 r L q k hlen hr hq hqr hncl hu i hi n hn hlow σ hσ hG Lc' c R' hcl

/-- **The input hSF** from the PH/FC3 residuals and the C2 root relation of the QFO input. -/
theorem hSF_of (hRes : T2AtV3 (fun M ρ => SeedPFResV3 M ρ))
    (hC2 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFO.T2C2RootRel M ρ r L q)) :
    T2AtV3 (fun M _ => T2SeedFrames G.QT2F M) := by
  intro M ρ rk C hz h2
  have hFO := SeedFO.hFO_of_C2rel hC2 M ρ rk C hz h2
  have hPF := seed_frames_PFV3 C hz h2 (hRes M ρ rk C hz h2)
  intro r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl
  exact ⟨hFO r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl, (hPF r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl).2⟩

/-- **The input hSP** from the same residuals. -/
theorem hSP_of (hRes : T2AtV3 (fun M ρ => SeedPFResV3 M ρ))
    (hC2 : T2AtV3 (fun M ρ => ∀ r L q k,
      r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → SeedFO.T2C2RootRel M ρ r L q)) :
    T2AtV3 (fun M _ => T2SeedFrames G.QT2P M) := by
  intro M ρ rk C hz h2
  have hFO := SeedFO.hFO_of_C2rel hC2 M ρ rk C hz h2
  have hPF := seed_frames_PFV3 C hz h2 (hRes M ρ rk C hz h2)
  intro r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl
  exact ⟨hFO r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl, (hPF r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl).1⟩

end Ytosk.V3Main.SeedPF
