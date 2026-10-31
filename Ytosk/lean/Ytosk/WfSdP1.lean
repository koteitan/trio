/-
**WfSdP1: the seed condition `SeedC2` of `t = 1`, `q = r` from the `PV2` drop conclusion (2026-11-01).**

`qr_seedC_of2` concludes the old form (weak seed `Ω_{w′}` with `SmallSelf w′`, false on graftD). Here the weak branch
of `WfDrE2.SeedC2` (`SeedOK μ b_r μ Ω_{w′}` and `γ_1 = ψ_μ(b + Ω_{w′}) ◁ ψ_μ(b_r)`) is derived from the component
condition `WCS2 μ w′` at `μ = v(r)` (`seedC2_weak_of_wcs2`, by `lhd_weak_childA`). In the weak case `w′ = V + 1`
(`V = v(P₁ r)`, `r = x − 1`), and the absorption hypothesis at `x − 1` is taken in the form
`strong ∨ WCS2 (v(r)) (V + 1)` (`UAwR`; measured 0 failures, tmp/wf/WfSdP/notes.md).
- `seedC2_weak_of_wcs2`, `qr_seedC2_of` (copy of `qr_seedC_of2`), `qr_final4SGW2` (`qr_final4SGW` without `hseedC`).
-/
import Ytosk.WfSdH3

namespace Ytosk

open T

/-- **The weak branch of `SeedC2` from `WCS2 μ w′`.** -/
theorem seedC2_weak_of_wcs2 {μ b w' : T} (hb : AllGeT (psi (succ μ) z z) b)
    (hsot : isOT (psi w' z z) = true) (hwμ : w' < μ) (hW : WCS2 μ w') :
    SeedOK μ (app b (psi (succ μ) z z)) μ (psi w' z z) ∧
      Lhd z (psi μ (app b (psi w' z z)) z) (psi μ (app b (psi (succ μ) z z)) z) := by
  have hOm : psi w' z z < psi (succ μ) z z :=
    psi_lt_psi_z_iff.mpr (Or.inl (lt_trans hwμ (lt_succ_self μ)))
  have hle : psi w' z z ≤ app b (psi w' z z) := le_app_of_allGe hOm hb
  have hsmall : ∀ u, ¬ lt μ u = true → ∀ g ∈ comps u (psi w' z z),
      g ≤ app b (psi w' z z) ∨ ∃ d ∈ comps u μ, g ≤ d := by
    intro u hu g hg
    have hg' : g = z ∨ g ∈ comps u w' := by
      simp only [comps, List.mem_append] at hg
      rcases hg with hg | hg
      · split at hg
        · simp at hg
        · simp only [List.mem_cons, List.mem_append] at hg
          rcases hg with h | h | h
          · exact Or.inl h
          · simp at h
          · exact Or.inr h
      · simp at hg
    rcases hg' with rfl | hg'
    · exact Or.inl (z_le _)
    · rcases hW u hu g hg' with h | h
      · exact Or.inl (le_trans h hle)
      · exact Or.inr h
  refine ⟨⟨hsot, hOm, ?_, ?_, ?_⟩, ?_⟩
  · rw [fs_br, psi_lt_psi_z_iff]; exact Or.inl hwμ
  · intro g hg
    simp [comps, (lt_iff_lt _ _).mp hwμ] at hg
  · intro u c0 c1 h1 _ hu g hg
    rw [fs_br] at h1
    rcases hsmall u hu g hg with h | ⟨d, hd, hgd⟩
    · refine ⟨c0, List.mem_append_left _ ?_, le_trans h (le_of_lt h1)⟩
      simp only [comps, List.mem_append]; left; rw [if_neg hu]; simp
    · refine ⟨d, List.mem_append_left _ ?_, hgd⟩
      simp only [comps, List.mem_append]; left; rw [if_neg hu]; simp [hd]
  · have hdrop : Lhd z (psi μ b z) (psi μ (app b (psi (succ μ) z z)) z) :=
      lhd_psi μ (lhd_prefix (by simp))
    exact lhd_weak_childA hdrop (by simp) hsmall (app_lt_app_left b hOm)

/-- **`SeedC2` from the `PV2` drop conclusion** (copy of `qr_seedC_of2`; the absorption at `x − 1` in the form
`strong ∨ WCS2 (v(r)) (V + 1)`). -/
theorem qr_seedC2_of {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ : Valn} {rkM : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rkM) i ∧ PV2 M ρ (drop1 M (r + L) rkM) i)
    (hr : r < r + L) {b : T} (hro : ρ.o r = psi (ρ.v r) (app b (psi (succ (ρ.v r)) z z)) z)
    (hb : AllGeT (psi (succ (ρ.v r)) z z) b)
    (hlt : (drop1 M (r + L) rkM).o r < ρ.o r)
    (hUAs : ∀ k W, r + 1 = r + L → upg M r = some k → ρ.v k = add (vOpt ρ (par M 1 r)) W → W ≠ z →
      (∀ s ∈ summands (vOpt ρ (par M 1 r)), s < W → Lhd z s W) ∨
        WCS2 (ρ.v r) (add (vOpt ρ (par M 1 r)) one))
    (h3 : NoBad3 M ρ ∨ r + 2 = M.length) :
    SeedC2 (ρ.v r) b ((drop1 M (r + L) rkM).o r) := by
  have hrM : r < M.length := by omega
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  obtain ⟨hPO, hsing⟩ := (hdrop r hr).1
  have hold : (LhdE ((drop1 M (r + L) rkM).o r) (ρ.o r) ∨
      (WkOA ((drop1 M (r + L) rkM).o r) (ρ.o r) ∧ ∃ w, ρ.o r = psi w z z)) →
      SeedC2 (ρ.v r) b ((drop1 M (r + L) rkM).o r) := by
    intro h
    left
    rw [← hro]
    rcases h with hl | ⟨_, w, hw⟩
    · rcases hl with he | hl
      · exact absurd (he ▸ hlt) (lt_irrefl' _)
      · exact hl
    · rw [hro] at hw
      exact absurd (T.psi.inj hw).2.1 (fun he => absurd (app_eq_z he).2 (by simp))
  rcases hPO with hl | ⟨hW, hw | hnl⟩
  · exact hold (Or.inl hl)
  · exact hold (Or.inr ⟨hW, hw⟩)
  have common : ∀ k W, r + 2 = M.length → upg M r = some k → ρ.v k = add (vOpt ρ (par M 1 r)) W → W ≠ z →
      ¬ (∀ s ∈ summands (vOpt ρ (par M 1 r)), s < W → Lhd z s W) →
      WkVA ((drop1 M (r + L) rkM).v r) (ρ.v r) →
      SeedC2 (ρ.v r) b ((drop1 M (r + L) rkM).o r) := by
    intro k W hi2 hu hvk hWz hbad hWV
    rcases hUAs k W (by omega) hu hvk hWz with h | hSm
    · exact absurd h hbad
    have h12 := upg_e12 hu
    have h2r : entry M 2 r = 0 := by have := hZ2 r; omega
    have hvr := v_last_take (x := r + L) (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1
      (r := r) (by omega) h12.1 h2r
    have hVot : isOT (add (vOpt ρ (par M 1 r)) one) = true := isOT_add (vOpt_ot hG hrM) isOT_one
    rw [sf_ot hVot] at hvr
    obtain ⟨w', w, X, hs, _, _⟩ := hW
    obtain ⟨σ0, hs0⟩ := o_psi_sub hC1 hrT
    rw [hs] at hs0
    simp only [psi.injEq] at hs0
    have hw' : w' = (drop1 M (r + L) rkM).v r := by rw [hs0.1, sf_ot (hdrop r hr).2.2]
    rw [hw'] at hs
    have hsot : isOT (psi ((drop1 M (r + L) rkM).v r) z z) = true := by rw [← hs]; exact hsing.1
    have hW2 : WCS2 (ρ.v r) ((drop1 M (r + L) rkM).v r) := by rw [hvr]; exact hSm
    obtain ⟨hSO, hL⟩ := seedC2_weak_of_wcs2 hb hsot hWV.1 hW2
    refine Or.inr ⟨_, hs, hWV.1, ?_, ?_⟩
    · rw [hs]; exact hSO
    · rw [hs]; exact hL
  rcases (hdrop r hr).2.1 with hl | ⟨hWV, _, hn | ⟨_, _, k, W, hi2, hu, hvk, hWz, hbad⟩ | ⟨_, hub, hbp⟩⟩
  · exact absurd hl hnl
  · exact hold (Or.inr ⟨hW, _, o_of_no_counted hC hrM (hG.ot_v r hrM) hn⟩)
  · exact common k W hi2 hu hvk hWz hbad hWV
  · rcases h3 with h3 | h3
    · exact absurd ⟨hub, hbp⟩ h3
    obtain ⟨k, W, _, hu, hvk, hWz, hbad⟩ := hub
    have e : M.length - 2 = r := by omega
    rw [e] at hu hvk hbad
    exact common k W h3 hu hvk hWz hbad hWV

/-- **The absorption at `x − 1` with the component condition at `v(x − 1)`** (`UAwR`; measured 0 failures). -/
def UAwR (M : Mat) (ρ : Valn) (x : Nat) : Prop :=
  ∀ i k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
    (∀ s ∈ summands (vOpt ρ (par M 1 i)), s < W → Lhd z s W) ∨
      WCS2 (ρ.v i) (add (vOpt ρ (par M 1 i)) one)

/-- **`qr_final4SGW` without `hseedC`**: the seed condition from `qr_seedC2_of` and `UAwR`. -/
theorem qr_final4SGW2 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
    (hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rkM) i ∧ PV2 M ρ (drop1 M (r + L) rkM) i)
    (hUAR : UAwR M ρ (r + L)) (h3 : NoBad3 M ρ ∨ r + 2 = M.length)
    (hTP : TP1WC M ρ) (hTPL : TPLoWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r)) (hAU' : AbsUWL M ρ)
    (hAU0 : AbsUW0 M ρ rkM) (hAD' : AbsDWAt M ρ (fun _ => (drop1 M (r + L) rkM).o r))
    (hTP1 : TP1C M ρ) (hTS : TrigS0 M ρ rkM) (hTPN : TPLoN M ρ) (hADN : AbsDN M ρ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1W Pn M r L d0 ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  obtain ⟨b0, hro, hbe, hb⟩ := qr_o_r hlen hR0 hSD h1 hx2 hq hC hG hRM
  have hbb : b0 = qrB M ρ r (r + L) := hbe
  rw [hbb] at hro hb
  have hlt := qr_seed_lt2 hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq hC hG hRM hdrop
  have hseedC := qr_seedC2_of hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hRM hdrop (par_lt M 1 (r + L) r h1) hro hb
    hlt (fun k W hi hu hvk hWz => hUAR r k W hi hu hvk hWz) h3
  exact qr_final4SGW hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hq hC hG hRM hKD hTD hdrop
    hseedC hTP hTPL hAU' hAU0 hAD' hTP1 hTS hTPN hADN hsM hpM Pn hP1 hPs

end Ytosk
