/-
**WfQnA8 (2026-11-01): the induction on `n` of the q ≠ r engine with the bad closure (t1_chainB).**
`t1_chainB` = `t1_chain` (V3ChainT1) where the valuation of `M[n]` is the true one (`cons_of_rk` of the ranking
`rk_N_t1`), not the glue: off the closure of the bad calls `B n` (at `ζ = gamS μ b_r seed (n − 2)`) it is the glue
(`WfQnH5.t1_E1B`), on the closure it drops by `◁` (`WfQnA3.engine_t1B`), it is Good3 (`WfQnA7.good3_N_t1B`), and
the root drops (`WfQnL7.root_N_E3` with (E3) from the engine).
Hypotheses beyond `t1_chain`: `hO`/`hV` only off the closure, the holes `hHole` (WfQnH3.hole0), `r` off the closure
(`hrB`), the engine residuals at each level (`hRes`: seeds, `hVSN`, `hHard`, `hAbsW`), and the step of the carried
property for the true valuation (`hPsB`).
-/
import Ytosk.WfQnA7
import Ytosk.V3ChainT1

namespace Ytosk.WfQnA8
open T Ytosk Ytosk.WfQnE3

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

/-- **All `n ≥ 2`** (`t = 1`, `q ≠ r`) with the true valuation of `M[n]`. -/
theorem t1_chainB (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ n, 2 ≤ n → ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ n, 2 ≤ n → ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : ∀ n, 2 ≤ n → isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    (hnd : ∀ n, 2 ≤ n → ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    (hndN : ∀ n, 2 ≤ n → ∀ a, a < (n - 1) * L → ∀ g, g < r + L →
      (par (TRIO.gexp M r L d0 0 n) 1 (r + L + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 n) (r + L + a) = some g) → ¬ DepX M (r + L) false g)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (h1 : par M 1 (r + L) = some r) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ)
    (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    {μ br vr seed : T}
    (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed)
    (hHx : HoleT μ br vr (ρ.o (r + L)))
    (hox : ∀ ζ, fsD (ρ.o (r + L)) ζ = ζ)
    (hro : ρ.o r = psi vr br z) (hrD : DepX M (r + L) true r)
    {B : Nat → Nat → Prop} (hB : ∀ n i, B n i → DepX M (r + L) false i)
    (hrB : ∀ n, 2 ≤ n → ¬ DepXB M (B n) true r)
    (hO : ∀ n i, i < r + L → DepX M (r + L) true i → ¬ DepXB M (B n) true i →
      OLocal M (r + L) ρ (gamS μ br seed (n - 2)) μ vr br i)
    (hV : ∀ n i, i < r + L → DepX M (r + L) false i → ¬ DepXB M (B n) false i →
      VLocal M (r + L) ρ (gamS μ br seed (n - 2)) μ i)
    (hHole : ∀ b i, DepX M (r + L) b i → i < r + L → HoleT μ br vr (valB ρ b i))
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0c : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hsR : ∀ m, Single (fsD (ρ.o Rt) (gamS μ br seed m)))
    -- the base `M[1] = M.take x`
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hr1 : ρ1.o r = seed)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (hgam : ∀ m, gamS μ br seed m ≤ ρ.o (r + L) ∧ gamS μ br seed m ≠ z)
    (hgS : ∀ m, ∃ a X, gamS μ br seed m = psi a X z)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    -- the engine residuals at each level, for the true valuation `σ` of `M[n]`
    (hRes : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP → ρP.o r = gamS μ br seed (n - 2) →
      Cons (TRIO.gexp M r L d0 0 n) σ →
      (∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M (B n) true i) →
        σ.o i = (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => gamS μ br seed (n - 2))).o i) →
      (∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M (B n) false i) →
        σ.v i = (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => gamS μ br seed (n - 2))).v i) →
      (∀ i, B n i → i < r + L → Lhd z (σ.v i) (ρ.v i) ∧ isOT (σ.v i) = true) ∧
      (∀ i (Lc : List Nat) c, i < r + L → DepXB M (B n) true i → CL (TRIO.gexp M r L d0 0 n) i = Lc ++ [c] →
        σ.v c ≠ ρ.v c →
        ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o))) ∧
      (∀ i (Lc : List Nat) c s y y', i < r + L → DepXB M (B n) true i →
        CL (TRIO.gexp M r L d0 0 n) i = Lc ++ [c] → ρ.o c = psi s y z →
        σ.o c = psi s y' z → lt (ρ.v i) s = true →
        (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s y' z) = true) →
        (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
        (split y' (psi (succ s) z z)).1 < (split y (psi (succ s) z z)).1 →
        ∀ g ∈ comps (ρ.v i) y', g ≤ H s y') ∧
      (∀ i, i < r + L → DepXB M (B n) false i → ¬ B n i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < psi z two z →
          ¬ q < bumpW (TRIO.gexp M r L d0 0 n) σ i → q < bumpW M ρ i → Lhd z q (bumpW M ρ i)))
    (Pn : Mat → Valn → Prop) (hP1 : Pn (TRIO.gexp M r L d0 0 1) ρ1)
    (hPsB : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP → Pn (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Cons (TRIO.gexp M r L d0 0 n) σ → Good3 (TRIO.gexp M r L d0 0 n) σ →
      (∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M (B n) true i) →
        σ.o i = (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => gamS μ br seed (n - 2))).o i) →
      (∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M (B n) false i) →
        σ.v i = (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => gamS μ br seed (n - 2))).v i) →
      Pn (TRIO.gexp M r L d0 0 n) σ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧ ρN.o r = gamS μ br seed (n - 1) ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  obtain ⟨q, hq⟩ := par0_of_anc hA (by have := par_lt M 1 (r + L) r h1; omega)
  have hμ : ¬ lt μ vr = true := by rw [hμr]; exact lt_irrefl' _
  have step : ∀ n, 2 ≤ n → ∀ ρP rkP, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Rk (TRIO.gexp M r L d0 0 (n - 1)) rkP → Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Pn (TRIO.gexp M r L d0 0 (n - 1)) ρP → ρP.o r = gamS μ br seed (n - 2) →
      (∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
        (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
          upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ρ.v g = ρP.v g) →
      ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
        Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧ ρN.o r = gamS μ br seed (n - 1) ∧
        (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
        isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧
        root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
    intro n hn ρP rkP hCP hRP hGP hPP hPr hPv
    set ζ := gamS μ br seed (n - 2) with hζ
    have hlN := len_N (d0 := d0) (n := n) hlen hn
    have hlP := len_P (d0 := d0) (n := n) hlen
    have hxNl : r + L < (TRIO.gexp M r L d0 0 n).length := by
      rw [hlN]; have := Nat.mul_le_mul_right L (show 1 ≤ n - 1 by omega); simp at this; omega
    have hxN : (shiftV ρP L).o (r + L) = fsD (ρ.o (r + L)) ζ := by
      show ρP.o (r + L - L) = _; rw [show r + L - L = r by omega, hox]; exact hPr
    have hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
        (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
          upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
        (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => ζ)).v g = ρP.v g := by
      intro g hg a ha hr
      rw [glueZ_v_lt ρ _ _ (by omega) (hnd n hn g hg a ha hr)]
      exact hPv g hg a ha hr
    have hRN := rk_N_t1 hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) (hnd n hn)
      hRM hRP
    have hCN := cons_of_rk hRN
    set σ := rhsIt (TRIO.gexp M r L d0 0 n) (rkBound (TRIO.gexp M r L d0 0 n)
      (rkN M (r + L) L rkM rkP (rkBound M rkM) (rkBound M rkM + rkBound (TRIO.gexp M r L d0 0 (n - 1)) rkP)))
      with hσ
    have hE := WfQnH5.t1_E1B hlen hL hA hd0e hn hpath hx2 (hxnb n hn) (hiu n hn) (hiux n hn) hRM (hB n)
      (hndN n hn) hz2 hC hG hCP hagree hCN hRN hrot hcb hμr hbr hS hHx hxN (hO n) (hV n)
    obtain ⟨hSeedB, hVSN, hHard, hAbsW⟩ := hRes n hn ρP σ hCP hGP hPr hCN hE.1 hE.2
    have hok : ∀ t, isOT t = true → HoleT μ br vr t → isOT (fsD t ζ) = true ∧ fsD t ζ < t :=
      fun t hot hH => hok_of_holeT hrot hcb hμ hS hot hH (n - 2)
    have hOTD : ∀ b j, j < r + L → DepX M (r + L) b j → isOT (fsD (valB ρ b j) ζ) = true := by
      intro b j hj hd
      apply (hok _ _ (hHole b j hd hj)).1
      cases b
      · exact hG.ot_v j (by omega)
      · exact hG.ot_o j (by omega)
    have hOTout : ∀ b j, r + L ≤ j → j < (TRIO.gexp M r L d0 0 n).length → isOT (valB σ b j) = true := by
      intro b j hj hjN
      cases b
      · show isOT (σ.v j) = true
        rw [hE.2 j hjN (fun h => by omega), glueZ_v_ge _ _ _ hj]
        exact hGP.ot_v _ (by rw [hlP]; rw [hlN] at hjN; omega)
      · show isOT (σ.o j) = true
        rw [hE.1 j hjN (fun h => by omega), glueZ_o_ge _ _ _ hj]
        exact hGP.ot_o _ (by rw [hlP]; rw [hlN] at hjN; omega)
    have hEng := WfQnA3.engine_t1B hlen hL hd0e hn hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr hq (hB n) hC hG hCN hRM
      hF hFO hVS hTD hKD hE.1 hE.2 hOTD hOTout hSeedB hVSN hHard hAbsW
    have hleD : ∀ c, c < r + L → DepX M (r + L) true c → fsD (ρ.o c) ζ ≤ ρ.o c ∧ fsD (ρ.o c) ζ ≠ z := by
      intro c hc hd
      have hH : HoleT μ br vr (ρ.o c) := by simpa only [valB, cond_true] using hHole true c hd hc
      have hk := hok _ (hG.ot_o c (by omega)) hH
      refine ⟨hk.2.le, single_ne_z ?_⟩
      exact single_fsD (o_psi_form hC (by omega)) (holeT_not_succ hH)
        (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hH)) (hgS (n - 2)) hk.1
    have hlex : ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z := by rw [hPr]; exact hgam (n - 2)
    have hGN := WfQnA7.good3_N_t1B hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) (hB n)
      hC hG hCN hGP hOS hE.1 hE.2 hOTD hleD hEng hlex
    refine ⟨σ, _, hCN, hRN, hGN, hPsB n hn ρP σ hCP hGP hPP hCN hGN hE.1 hE.2, ?_, ?_, ?_⟩
    · -- the value at `r`
      rw [hE.1 r (by omega) (fun h => hrB n hn h.2), glueZ_o_dep ρ _ _ (by omega) hrD, hro,
        fsD_here hbr hcb, ← hμr]
      rw [show n - 1 = (n - 2) + 1 by omega]; rfl
    · intro g hg hd
      rw [hE.2 g (by omega) (fun h => hd (DepXB.sub (hB n) h.2))]
      exact glueZ_v_lt ρ _ _ hg hd
    · -- the root
      have hRx : Rt < r + L := by
        rcases Nat.eq_or_lt_of_le hRA.le with h | h
        · exfalso
          have h1' : entry M 0 (r + L) ≠ 0 := by
            have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
          have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hR0c; rw [hR0c]; rfl
          rw [h] at hR0e; exact h1' hR0e
        · exact h
      have hRt : HoleT μ br vr (ρ.o Rt) := by simpa only [valB, cond_true] using hHole true Rt hRd hRx
      have hlt := (hok _ (hG.ot_o Rt (by omega)) hRt).2
      exact WfQnL7.root_N_E3 (Z := fun _ => ζ) hlen hL hA hd0e hn hRA hR0c hRlast hRd hsM hpM (hB n) hE.1
        (hsR (n - 2)) hlt
        (fun hb => WfQnH8.e3_root hCN hRx hxNl.le
          (fun b i hD hi => hEng b i (WfQnH8.depS_iff.mp hD) hi) hb)
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    exact step 2 (le_refl _) ρ1 rk1 hC1 hR1 hG1 hP1 hr1 (fun g hg a ha hr => hPv1 g hg a (by omega) hr)
  | succ n hn ih =>
    obtain ⟨ρP, rkP, hCP, hRP, hGP, hPP, hPr, hPd, _⟩ := ih
    apply step (n + 1) (by omega) ρP rkP (by simpa using hCP) (by simpa using hRP) (by simpa using hGP)
      (by simpa using hPP)
      (by rw [show n + 1 - 2 = n - 1 by omega]; exact hPr)
    intro g hg a ha hr
    exact (hPd g (by omega) (hnd (n + 1) (by omega) g hg a ha hr)).symm

end

end Ytosk.WfQnA8
