/-
**3 行・t = 1・q ≠ r（n ≥ 2）: 構造の仮定と基底を外した形。**

`t1_main_struct`（構造の仮定なし）の基底の仮定（hv1・hs1ot・hs1lhd・hPv1）を、落とす補題 `drop_all` と
`V3BaseDrop` から与える。残る仮定は値についてのものだけ（値の不変条件、r と x の値、枠の値の条件、
落とす補題の残りの仮定、o(r) が実際に変わること）。
-/
import Ytosk.V3StructT1
import Ytosk.V3BaseDrop

namespace Ytosk

open T

/-- The valuation of `M.take x` from the ranking of `M`. -/
noncomputable def drop1 (M : Mat) (x : Nat) (rk : Bool → Nat → Nat) : Valn :=
  rhsIt (M.take x) (rkBound (M.take x) rk)

/-- **`t = 1`, `q ≠ r`, all `n ≥ 2`**, with the base from the drop lemma. -/
theorem t1_main_drop {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmall M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    -- the remaining hypotheses of the drop lemma
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hBump : ∀ i, i < r + L → (∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j,
        k < r + L → PO ρ (drop1 M (r + L) rkM) k ∧ PV M ρ (drop1 M (r + L) rkM) k) →
      ChgX M (r + L) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → PV M ρ (drop1 M (r + L) rkM) i)
    (hX1 : ∀ i k W, i + 1 = r + L → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
      ∀ r' ∈ summands (vOpt ρ (par M 1 i)), r' < W → Lhd z r' W)
    (hne : (drop1 M (r + L) rkM).o r ≠ ρ.o r)
    {μ br vr : T}
    (hrot : isOT (psi vr br z) = true) (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
    (hoxv : ρ.o (r + L) = psi (succ μ) z z) (hro : ρ.o r = psi vr br z)
    (hF1 : ∀ i, r < i → i < r + L → DepX M (r + L) true i → ¬ DepX M (r + L) false i →
      lt μ (ρ.v i) = true)
    (hV : ∀ m i, i < r + L → DepX M (r + L) false i →
      VLocal M (r + L) ρ (gamS μ br ((drop1 M (r + L) rkM).o r) m) μ i)
    (hW : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      lt (preState M ρ i L') (fsD y (gamS μ br ((drop1 M (r + L) rkM).o r) m)) = true)
    (hLo : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      DepX M (r + L) true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z →
        fsD (split y (psi (succ s) z z)).2 (gamS μ br ((drop1 M (r + L) rkM).o r) m) ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z →
        (split (fsD y (gamS μ br ((drop1 M (r + L) rkM).o r) m)) (psi (succ s) z z)).2 = z))
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r ≠ r + L := by omega
  have hr : r < r + L := by omega
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rkM) := cons_of_rk hRk1
  have hpath := hpath_of_par1 h1 hA hrx
  have hdrop := drop_all (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hF hFO hArgT hBump hX1
  have hv : (drop1 M (r + L) rkM).v r = ρ.v r :=
    base_v_r hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hA hrx hqr hpath
  have hrM : r < M.length := by omega
  have hvr : ρ.v r = vr := by
    obtain ⟨y0, hy0⟩ := o_psi_sub hC hrM
    rw [hro] at hy0; simp only [psi.injEq] at hy0
    rw [hy0.1, sf_ot (hG.ot_v r hrM)]
  obtain ⟨hlhd, hot⟩ := base_seed hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hr (hdrop r hr).1 hv hne
  apply t1_main_struct hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hqr hC hG hRM
    hrot hcb hμr hbr hoxv hro hF1 (by rw [← hvr]; exact hv) hot hlhd _ hV hW hLo hsM hpM
  intro g hg a ha h
  rw [gexp_one_eq hlen] at h
  exact base_v_read hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hg ha h

end Ytosk
