/-
**WfQnA9 (2026-11-01): t1_mainB, the q ≠ r engine with the bad closure at the level of `t1_main` (V3MainT1).**
-/
import Ytosk.WfQnA8

namespace Ytosk.WfQnA9
open T Ytosk Ytosk.WfQnE3

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

theorem t1_mainB (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ n, 2 ≤ n → ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ n, 2 ≤ n → ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : ∀ n, 2 ≤ n → isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    (hnd : ∀ n, 2 ≤ n → ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    (hqr : par M 0 (r + L) ≠ some r)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (h1 : par M 1 (r + L) = some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ)
    (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    {μ br vr seed : T}
    (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed)
    (hseed : ∃ σ, seed = psi μ σ z)
    (hoxv : ρ.o (r + L) = psi (succ μ) z z)
    (hro : ρ.o r = psi vr br z) (hrD : DepX M (r + L) true r)
    (hF1 : ∀ i, r < i → i < r + L → DepX M (r + L) true i → ¬ DepX M (r + L) false i →
      lt μ (ρ.v i) = true)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    {B : Nat → Nat → Prop} (hB : ∀ n i, B n i → DepX M (r + L) false i)
    (hrB : ∀ n, 2 ≤ n → ¬ DepXB M (B n) true r)
    (hV : ∀ n, 2 ≤ n → ∀ i, i < r + L → DepX M (r + L) false i → ¬ DepXB M (B n) false i →
      VLocal M (r + L) ρ (gamS μ br seed (n - 2)) μ i)
    (hTPL : ∀ n, 2 ≤ n → WfQnH3.TPLB M (r + L) ρ (B n) μ (gamS μ br seed (n - 2)))
    (hbrl : last br ≠ psi (succ μ) z z)
    (hndN : ∀ n, 2 ≤ n → ∀ a, a < (n - 1) * L → ∀ g, g < r + L →
      (par (TRIO.gexp M r L d0 0 n) 1 (r + L + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 n) (r + L + a) = some g) → ¬ DepX M (r + L) false g)
    (hS2 : ∀ i k, i ≤ r → DepX M (r + L) false i → entry M 2 i = 0 → upg M i = some k → k ≤ r)
    (hS3 : ∀ i j k, i ≤ r → j ∈ children M i → col M j = bump M i → k ∈ children M j →
      DepX M (r + L) true k → k ≤ r)
    (hW : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → Counted M i c →
      DepX M (r + L) true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      lt (preState M ρ i L') (fsD y (gamS μ br seed m)) = true)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0c : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hr1 : ρ1.o r = seed)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    (hRes : WfQnA8.ResT1B M r L d0 ρ μ br seed B)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (TRIO.gexp M r L d0 0 1) ρ1) (hPsB : WfQnA8.StepT1B Pn M r L d0 ρ μ br seed B) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧ ρN.o r = gamS μ br seed (n - 1) ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hx : r + L + 1 = M.length := hlen
  have hrx : r < r + L := by omega
  have hμot : isOT μ = true := isOT_cof_mu (isOT_arg hrot) hcb
  have hHx : HoleT μ br vr (ρ.o (r + L)) := Or.inl (by rw [hoxv]; exact cof_omega_succ μ)
  have hox : ∀ ζ, fsD (ρ.o (r + L)) ζ = ζ := fun ζ => by
    rw [hoxv]; exact fsD_leaf (isSucc_succ μ) (succ_ne_z μ)
  have hμ : ¬ lt μ vr = true := by rw [hμr]; exact lt_irrefl' _
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hH0 := WfQnH3.hole0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hA hro hcb hμr hbr hoxv hF1 hOS
    hS2 hS3
  have hζ : ∀ m, ∃ X, gamS μ br seed m = psi μ X z := by
    intro m
    cases m with
    | zero => exact hseed
    | succ k => exact ⟨_, rfl⟩
  have hO : ∀ n, 2 ≤ n → ∀ i, i < r + L → DepX M (r + L) true i → ¬ DepXB M (B n) true i →
      OLocal M (r + L) ρ (gamS μ br seed (n - 2)) μ vr br i := fun n hn =>
    WfQnH3.olocal_t1B hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hA hro hcb hμr hbr hoxv hF1
      hOS hS2 hS3 hqr (hTPL n hn) hbrl (hζ _)
      (fun t hot hH => (hok_of_holeT hrot hcb hμ hS hot hH (n - 2)).1) (hW (n - 2))
  have hRx : Rt < r + L := by
    rcases Nat.eq_or_lt_of_le hRA.le with h | h
    · exfalso
      have h1' : entry M 0 (r + L) ≠ 0 := by
        have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
      have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hR0c; rw [hR0c]; rfl
      rw [h] at hR0e; exact h1' hR0e
    · exact h
  have hHole : ∀ b i, DepX M (r + L) b i → i < r + L → HoleT μ br vr (valB ρ b i) :=
    fun b i hd hi => (hH0 b i hd (Or.inl hi)).1
  have hsR : ∀ m, Single (fsD (ρ.o Rt) (gamS μ br seed m)) := by
    intro m
    have hHR : HoleT μ br vr (ρ.o Rt) := by simpa only [valB, cond_true] using hHole true Rt hRd hRx
    obtain ⟨X, hX⟩ := hζ m
    exact single_fsD (o_psi_form hC (by omega)) (holeT_not_succ hHR)
      (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHR)) ⟨μ, X, hX⟩
      (hok_of_holeT hrot hcb hμ hS (hG.ot_o Rt (by omega)) hHR m).1
  exact WfQnA8.t1_chainB hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hndN hR0 hZ2 hSD hZ1 hUAT hUAB h1 hqr
    hC hG hRM hF hFO hVS hTD hKD hrot hcb hμr hbr hS hHx hox hro hrD hB hrB hO hV hHole hRA hR0c hRlast hRd
    hsM hpM hsR hC1 hR1 hr1 hPv1 hOS
    (fun m => ⟨by rw [hoxv]; exact (gamS_lt_om hrot hcb hμ (hS vr (lt_irrefl' vr) hrot) m).le,
      by obtain ⟨X, hX⟩ := hζ m; rw [hX]; simp⟩)
    (fun m => by obtain ⟨X, hX⟩ := hζ m; exact ⟨μ, X, hX⟩) hG1 hRes Pn hP1 hPsB
end

end Ytosk.WfQnA9
