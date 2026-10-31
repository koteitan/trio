/-
**WfQnA11 (2026-11-01): t1_main_structB = `t1_main_struct` (V3StructT1) for the q ≠ r engine with the bad closure**
(structural hypotheses discharged as there; `hndN` from `WfQnH1.hndN_of_hnd'`).
-/
import Ytosk.WfQnA10
import Ytosk.WfQnH1

namespace Ytosk.WfQnA11
open T Ytosk Ytosk.WfQnE3

theorem t1_main_structB {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ)
    (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    {μ br vr : T}
    (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hoxv : ρ.o (r + L) = psi (succ μ) z z) (hro : ρ.o r = psi vr br z)
    (hF1 : ∀ i, r < i → i < r + L → DepX M (r + L) true i → ¬ DepX M (r + L) false i →
      lt μ (ρ.v i) = true)
    (hv1 : (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).v r = vr)
    (hs1ot : isOT ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) = true)
    (hs1lhd : Lhd z ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) (ρ.o r))
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) →
      ρ.v g = (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).v g)
    {B : Nat → Nat → Prop} (hB : ∀ n i, B n i → DepX M (r + L) false i)
    (hrB : ∀ n, 2 ≤ n → ¬ DepXB M (B n) true r)
    (hV : ∀ n, 2 ≤ n → ∀ i, i < r + L → DepX M (r + L) false i → ¬ DepXB M (B n) false i →
      VLocal M (r + L) ρ (gamS μ br ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) (n - 2)) μ i)
    (hTPL : ∀ n, 2 ≤ n → WfQnH3.TPLB M (r + L) ρ (B n) μ (gamS μ br ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) (n - 2)))
    (hbrl : last br ≠ psi (succ μ) z z)
    (hW : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → Counted M i c →
      DepX M (r + L) true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      lt (preState M ρ i L')
        (fsD y (gamS μ br ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) m)) = true)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hG1 : Good3 (M.take (r + L)) (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)))
    (hRes : WfQnA8.ResT1B M r L d0 ρ μ br ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) B)
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)))
    (hPsB : WfQnA8.StepT1B Pn M r L d0 ρ μ br ((rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rkM)).o r) B) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ Pn (TRIO.gexp M r L d0 0 n) ρN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r ≠ r + L := by omega
  obtain ⟨q, hq⟩ := par0_of_anc hA hrx
  have hpath := hpath_of_par1 h1 hA hrx
  obtain ⟨Rt, hRA, hRt0, hRlast⟩ := root_t1 hR01 hR12 h00 (r + L)
  have hnd := hnd_t1 hlen hL hA hd0e hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2
  exact WfQnA10.t1_main2B hlen hL hA hd0e hpath hx2
    (hxnb_t1 hlen hL hA hd0e hZ2 hZ1 h1) (hZ2 r)
    (fun n hn => hiu_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn)
    (fun n hn => hiux_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn)
    hnd hqr hR0 hZ2 hSD hZ1 hUAT hUAB h1 hC hG hRM hF hFO hVS hTD hKD hrot hcb hμr hbr hoxv hro
    (dep_anc_x hUAT hZ2 hR12 hBE hlen hx2 hA) hF1
    (hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq)
    (hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT) hv1 hs1ot hs1lhd hPv1 hB hrB hV hTPL hbrl
    (fun n hn => WfQnH1.hndN_of_hnd' hlen hL hA hd0e hn hpath (hZ2 r) (hnd n hn))
    (hS2_t1 hR0 hA hrx) (hS3_t1 h1 hA hrx hlen hR0 hZ2 hSD hZ1) hW
    hRA hRt0 hRlast (dep_anc_x hUAT hZ2 hR12 hBE hlen hx2 hRA) hsM hpM hG1 hRes Pn hP1 hPsB

end Ytosk.WfQnA11
