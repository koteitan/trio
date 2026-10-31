/-
**WfQnA16 (2026-11-01): t1_main_vlocSX2 = `WfQnA13.t1_main_vlocSX` with the seeds reduced to the bad-leaf facts.**
Residuals: `hin` (TPLoSXIn), `hrB` (`o(r)` off the closure), `hVlt` (`V < A` at bad calls), `hnest` (no nested bad
call), `hRwin` (window absorption at bad calls), `hRest` (`WfQnA15.ResT1Bv`: `hVSN`/`hHard`/`hAbsW` in the
closure), `hPsB` (`WfQnA8.StepT1B`).
-/
import Ytosk.WfQnA15

namespace Ytosk.WfQnA16
open T Ytosk Ytosk.WfQnE3 Ytosk.WfBad Ytosk.WfQnE2

section

theorem t1_main_vlocSX2 {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hTP : TP1C M ρ) (hTPLX : TPLoSX M ρ rkM) (hADX : AbsDSX M ρ rkM) (hAUS : AbsUS M ρ rkM)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rkM) i ∧ PV2 M ρ (drop1 M (r + L) rkM) i)
    (hne : (drop1 M (r + L) rkM).o r ≠ ρ.o r)
    {μ br vr : T} (hμr : μ = vr) (hro : ρ.o r = psi vr br z)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rkM))
    -- the residuals of the bad closure
    (hin : ∀ m, WfQnH3.TPLoSXIn M ρ r μ (gamS μ br ((drop1 M (r + L) rkM).o r) m))
    (hrB : ∀ n, 2 ≤ n → ¬ DepXB M (BadSet M (r + L) ρ r (gamS μ br ((drop1 M (r + L) rkM).o r) (n - 2))) true r)
    (hVlt : ∀ m i, BadSet M (r + L) ρ r (gamS μ br ((drop1 M (r + L) rkM).o r) m) i → vOpt ρ (par M 1 i) < ρ.o r)
    (hnest : ∀ m i, BadSet M (r + L) ρ r (gamS μ br ((drop1 M (r + L) rkM).o r) m) i → ∀ j ∈ children M i,
      col M j = bump M i → ∀ k ∈ children M j,
        ¬ DepXB M (BadSet M (r + L) ρ r (gamS μ br ((drop1 M (r + L) rkM).o r) m)) true k)
    (hRwin : ∀ m i, BadSet M (r + L) ρ r (gamS μ br ((drop1 M (r + L) rkM).o r) m) i →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < fsD (ρ.o r) (gamS μ br ((drop1 M (r + L) rkM).o r) m) → q < ρ.o r →
        Lhd z q (ρ.o r))
    (hRest : WfQnA15.ResT1Bv M r L d0 ρ μ br ((drop1 M (r + L) rkM).o r)
      (fun n => BadSet M (r + L) ρ r (gamS μ br ((drop1 M (r + L) rkM).o r) (n - 2))))
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM))
    (hPsB : WfQnA8.StepT1B Pn M r L d0 ρ μ br ((drop1 M (r + L) rkM).o r)
      (fun n => BadSet M (r + L) ρ r (gamS μ br ((drop1 M (r + L) rkM).o r) (n - 2)))) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r < r + L := by omega
  have hrM : r < M.length := by omega
  have hvr : ρ.v r = vr := by
    obtain ⟨y0, hy0⟩ := o_psi_sub hC hrM
    rw [hro] at hy0; simp only [psi.injEq] at hy0
    rw [hy0.1, sf_ot (hG.ot_v r hrM)]
  have hF1 : ∀ i, r < i → i < r + L → DepX M (r + L) true i → ¬ DepX M (r + L) false i →
      lt μ (ρ.v i) = true := by
    intro i h2 h3 h4 h5
    rw [hμr, ← hvr]
    exact hF1_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hC hG hRM i h2 h3 h4 h5
  have hox : ρ.o (r + L) = psi (succ μ) z z := by
    rw [o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2, hvr, hμr]
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq
  -- the base `M.take x`
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hv1r : (drop1 M (r + L) rkM).v r = ρ.v r :=
    base_v_r hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hA (by omega) hqr hpath
  have hv1 : (drop1 M (r + L) rkM).v r = μ := by rw [hv1r, hvr, hμr]
  have hotv : ∀ i, i < r + L → isOT ((drop1 M (r + L) rkM).v i) = true :=
    fun i hi => (hdrop i hi).2.2
  have hoto : ∀ i, i < r + L → isOT ((drop1 M (r + L) rkM).o i) = true :=
    fun i hi => (hdrop i hi).1.2.1
  -- the seed
  obtain ⟨σ, hs, hσz, hσge⟩ := seed_arg_ge hlen hR0 hZ2 hSD hZ1 hUAB h1 hqr hC1 hRk1 hotv hoto hv1
  have hsot : isOT (psi μ σ z) = true := by rw [← hs]; exact hoto r hrx
  obtain ⟨hseedΩ, hseedfix⟩ := seed_fix hsot hσz hσge
  rw [← hs] at hseedΩ hseedfix
  -- `b_r`
  have hcof0 := t1_cof0 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hox hF1 hOS
  have hcof : ∀ b i, DepX M (r + L) b i → r < i → (i < r + L ∨ (i = r + L ∧ b = true)) →
      cof (valB ρ b i) = .big μ := fun b i hD hri hp => (hcof0 b i hD hri hp).1
  obtain ⟨hcb, hbr⟩ := hcb_of_cof hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hOS hcof h1 hx2 hqr hR12 hBE hro
  have hbrl := last_br_of_cof hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hOS hcof h1 hx2 hqr hR12 hBE hro
  have hrot : isOT (psi vr br z) = true := by rw [← hro]; exact hG.ot_o r hrM
  have hμ : ¬ lt μ vr = true := by rw [hμr]; exact lt_irrefl' _
  -- the seed condition
  obtain ⟨hlhd0, _⟩ := base_seed hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hrx (hdrop r hrx).1 hv1r hne
  have hlhd : Lhd z (psi μ σ z) (psi μ br z) := by
    rw [← hs]; rw [hro, ← hμr] at hlhd0; exact hlhd0
  have hσb : σ < br := by
    have := hlhd.1; rw [psi_lt_psi_z_iff] at this
    rcases this with h | ⟨_, h⟩
    · exact absurd h (lt_irrefl' _)
    · exact h
  have hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true →
      SeedOK a' br μ ((drop1 M (r + L) rkM).o r) := by
    intro a' ha' hot'
    rw [hs]
    exact seedOK_of_lhd_top hot' hcb (by rw [hμr]; exact ha') hsot hσb hlhd
  have hHx : HoleT μ br vr (ρ.o (r + L)) := Or.inl (by rw [hox]; exact cof_omega_succ μ)
  have hS2 := hS2_t1 hR0 hA (by omega)
  have hS3 := hS3_t1 h1 hA (by omega) hlen hR0 hZ2 hSD hZ1
  have hlast : M.length - 1 = r + L := by omega
  have hroμ : ρ.o r = psi μ br z := by simpa only [← hμr] using hro
  have hseedle : ∀ m, (drop1 M (r + L) rkM).o r ≤
      gamS μ br ((drop1 M (r + L) rkM).o r) m := by
    intro m
    induction m with
    | zero => exact le_refl _
    | succ m ih => exact le_trans ih (gamS_mono hrot hcb hμ (hS vr (lt_irrefl' _) hrot) m).le
  -- `VLocal` off the closure, at every level
  have hVm : ∀ m i, i < r + L → DepX M (r + L) false i →
      ¬ DepXB M (BadSet M (r + L) ρ r (gamS μ br ((drop1 M (r + L) rkM).o r) m)) false i →
      VLocal M (r + L) ρ (gamS μ br ((drop1 M (r + L) rkM).o r) m) μ i := by
    intro m
    have hζfix := gamS_fix hrot hcb hμ (hS vr (lt_irrefl' _) hrot) hbrl hseedfix hseedΩ m
    have hζΩ := gamS_ge_omfix (isOT_arg hrot) hcb hbrl hseedΩ m
    have hok : ∀ t, isOT t = true → HoleT μ br vr t →
        isOT (fsD t (gamS μ br ((drop1 M (r + L) rkM).o r) m)) = true ∧
        fsD t (gamS μ br ((drop1 M (r + L) rkM).o r) m) < t :=
      fun t hot hH => hok_of_holeT hrot hcb hμ hS hot hH m
    have hADζ := WfQnE2.hADζX_of_absDSX hADX (by simpa only [hlast] using h1)
      (by simpa only [hlast] using hqr) (by simpa only [hlast] using hx2) hroμ
      (by simpa only [hlast] using hseedle m)
    have hAUζ := hAUζ_of_absUS hAUS (by simpa only [hlast] using h1)
      (by simpa only [hlast] using hqr) (by simpa only [hlast] using hx2) hroμ
      (by simpa only [hlast] using hseedle m)
    have hTPLc := WfQnH3.tplB_of_tpLoSX hTPLX (hin m) (by simpa only [hlast] using h1)
      (by simpa only [hlast] using hqr) (by simpa only [hlast] using hx2) hroμ (by simpa only [hlast] using hox)
      (by simpa only [hlast] using hseedle m)
    simp only [hlast] at hADζ hAUζ hTPLc
    cases m with
    | zero =>
      exact WfQnH2.vlocal_t1_atXB (X := σ) hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD
        hrx hA hro hcb hμr hbr hHx hF1 hOS hS2 hS3 hTPLc hAUζ hbrl hs hσz hζfix hζΩ hok hADζ rfl
    | succ m =>
      have hne' : gamS μ br ((drop1 M (r + L) rkM).o r) m ≠ z := by
        intro h
        have := gamS_ge_omfix (isOT_arg hrot) hcb hbrl hseedΩ m
        rw [h] at this
        exact T.not_lt_z _ (lt_of_lt_of_le (T.z_lt_psi _ _ _) this)
      exact WfQnH2.vlocal_t1_atXB (X := fs br (gamS μ br ((drop1 M (r + L) rkM).o r) m)) hlen hR0 hZ2 hSD
        hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hA hro hcb hμr hbr hHx hF1 hOS hS2 hS3
        hTPLc hAUζ hbrl rfl (fs_ne_z_big hcb hne') hζfix hζΩ hok hADζ rfl
  have hTPLm : ∀ m, WfQnH3.TPLB M (r + L) ρ (BadSet M (r + L) ρ r (gamS μ br ((drop1 M (r + L) rkM).o r) m)) μ
      (gamS μ br ((drop1 M (r + L) rkM).o r) m) := by
    intro m
    have hTPLc := WfQnH3.tplB_of_tpLoSX hTPLX (hin m) (by simpa only [hlast] using h1)
      (by simpa only [hlast] using hqr) (by simpa only [hlast] using hx2) hroμ (by simpa only [hlast] using hox)
      (by simpa only [hlast] using hseedle m)
    simpa only [hlast] using hTPLc
  -- (W) from TP1 (no `VLocal`)
  have hseed1 := seed_ge_one hlen hR0 hZ2 hSD hZ1 hUAB h1 hqr hC1 hv1
    (by rw [hμr, ← hvr]; exact hG.ot_v r hrM)
  have hW := WfQnH3.hW_of_TP1_0 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hA hro hcb hμr hbr hox
    hF1 hOS hS2 hS3 hTP hseed1
  have hna : ∀ m i, BadSet M (r + L) ρ r (gamS μ br ((drop1 M (r + L) rkM).o r) m) i →
      WfQnL6.BumpNA M (r + L) ρ (gamS μ br ((drop1 M (r + L) rkM).o r) m) i := by
    intro m i hBi
    obtain ⟨hi, hdi, _, _, h2i, _, _⟩ := id hBi
    have hζfix := gamS_fix hrot hcb hμ (hS vr (lt_irrefl' _) hrot) hbrl hseedfix hseedΩ m
    have hζΩ := gamS_ge_omfix (isOT_arg hrot) hcb hbrl hseedΩ m
    have hok : ∀ t, isOT t = true → HoleT μ br vr t →
        isOT (fsD t (gamS μ br ((drop1 M (r + L) rkM).o r) m)) = true ∧
        fsD t (gamS μ br ((drop1 M (r + L) rkM).o r) m) < t :=
      fun t hot hH => hok_of_holeT hrot hcb hμ hS hot hH m
    have hTPLc := WfQnH3.tplB_of_tpLoSX hTPLX (hin m) (by simpa only [hlast] using h1)
      (by simpa only [hlast] using hqr) (by simpa only [hlast] using hx2) hroμ (by simpa only [hlast] using hox)
      (by simpa only [hlast] using hseedle m)
    simp only [hlast] at hTPLc
    cases m with
    | zero =>
      exact WfQnA14.bump_naB (X := σ) hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD
        hrx hA hro hcb hμr hbr hHx hF1 hOS hS2 hS3 hTPLc hbrl hs hσz hζfix hζΩ hok i hi hdi h2i (hnest 0 i hBi)
    | succ m =>
      have hne' : gamS μ br ((drop1 M (r + L) rkM).o r) m ≠ z := by
        intro h
        have := gamS_ge_omfix (isOT_arg hrot) hcb hbrl hseedΩ m
        rw [h] at this
        exact T.not_lt_z _ (lt_of_lt_of_le (T.z_lt_psi _ _ _) this)
      exact WfQnA14.bump_naB (X := fs br (gamS μ br ((drop1 M (r + L) rkM).o r) m)) hlen hR0 hZ2 hSD
        hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hA hro hcb hμr hbr hHx hF1 hOS hS2 hS3
        hTPLc hbrl rfl (fs_ne_z_big hcb hne') hζfix hζΩ hok i hi hdi h2i (hnest (m + 1) i hBi)
  have hSd : SeedOK μ br μ ((drop1 M (r + L) rkM).o r) := by
    have := hS vr (lt_irrefl' vr) hrot; rwa [← hμr] at this
  have hRes := WfQnA15.resT1B_of (vr := vr) hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq hC hG hroμ hcb hSd hox
    hVlt hnest hRwin hna hRest
  exact WfQnA12.t1_main_dropG2B hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hqr hC hG hRM
    hVS hF hFO hKD hTD hdrop hne hcb hμr hbr hro hF1 (B := fun n => BadSet M (r + L) ρ r
      (gamS μ br ((drop1 M (r + L) rkM).o r) (n - 2)))
    (fun n i h => h.2.1) hrB (fun n _ => hVm (n - 2)) (fun n _ => hTPLm (n - 2)) hbrl hW hsM hpM hG1 hRes
    Pn hP1 hPsB
end

end Ytosk.WfQnA16
