/-
**WfQnA12 (2026-11-01): t1_main_dropG2B = `t1_main_dropG2` (WfDrL4) for the q ≠ r engine with the bad closure**
(the base and the seed from the drop lemma `PO`/`PV2`).
-/
import Ytosk.WfQnA11
import Ytosk.WfDrL4

namespace Ytosk.WfQnA12
open T Ytosk Ytosk.WfQnE3

section

theorem t1_main_dropG2B {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    -- the remaining hypotheses of the drop lemma
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rkM) i ∧ PV2 M ρ (drop1 M (r + L) rkM) i)
    (hne : (drop1 M (r + L) rkM).o r ≠ ρ.o r)
    {μ br vr : T}
    (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z) (hro : ρ.o r = psi vr br z)
    (hF1 : ∀ i, r < i → i < r + L → DepX M (r + L) true i → ¬ DepX M (r + L) false i →
      lt μ (ρ.v i) = true)
    {B : Nat → Nat → Prop} (hB : ∀ n i, B n i → DepX M (r + L) false i)
    (hrB : ∀ n, 2 ≤ n → ¬ DepXB M (B n) true r)
    (hV : ∀ n, 2 ≤ n → ∀ i, i < r + L → DepX M (r + L) false i → ¬ DepXB M (B n) false i →
      VLocal M (r + L) ρ (gamS μ br ((drop1 M (r + L) rkM).o r) (n - 2)) μ i)
    (hTPL : ∀ n, 2 ≤ n → WfQnH3.TPLB M (r + L) ρ (B n) μ (gamS μ br ((drop1 M (r + L) rkM).o r) (n - 2)))
    (hbrl : last br ≠ psi (succ μ) z z)
    (hW : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → Counted M i c →
      DepX M (r + L) true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      lt (preState M ρ i L') (fsD y (gamS μ br ((drop1 M (r + L) rkM).o r) m)) = true)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rkM))
    (hRes : WfQnA8.ResT1B M r L d0 ρ μ br ((drop1 M (r + L) rkM).o r) B)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM))
    (hPsB : WfQnA8.StepT1B Pn M r L d0 ρ μ br ((drop1 M (r + L) rkM).o r) B) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r ≠ r + L := by omega
  have hr : r < r + L := by omega
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hpath := hpath_of_par1 h1 hA hrx
  have hv : (drop1 M (r + L) rkM).v r = ρ.v r :=
    base_v_r hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hA hrx hqr hpath
  have hrM : r < M.length := by omega
  have hvr : ρ.v r = vr := by
    obtain ⟨y0, hy0⟩ := o_psi_sub hC hrM
    rw [hro] at hy0; simp only [psi.injEq] at hy0
    rw [hy0.1, sf_ot (hG.ot_v r hrM)]
  have hrot : isOT (psi vr br z) = true := by rw [← hro]; exact hG.ot_o r hrM
  have hoxv : ρ.o (r + L) = psi (succ μ) z z := by
    rw [o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2, hvr, hμr]
  obtain ⟨hlhd, hot⟩ := base_seed hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hr (hdrop r hr).1 hv hne
  apply WfQnA11.t1_main_structB hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hqr hC hG hRM
    hF hFO hVS hTD hKD hrot hcb hμr hbr hoxv hro hF1 (by rw [← hvr]; exact hv) hot hlhd _ hB hrB hV hTPL hbrl
    hW hsM hpM hG1 hRes Pn hP1 hPsB
  intro g hg a ha h
  rw [gexp_one_eq hlen] at h
  exact base_v_read hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hg ha h
end

end Ytosk.WfQnA12
