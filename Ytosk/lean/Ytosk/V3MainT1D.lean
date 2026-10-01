/-
**3 行・t = 1・q ≠ r（n ≥ 2）: 構造の仮定と基底を外した形。**

`t1_main_struct`（構造の仮定なし）の基底の仮定（hv1・hs1ot・hs1lhd・hPv1）を、落とす補題 `drop_all` と
`V3BaseDrop` から与える。残る仮定は値についてのものだけ（値の不変条件、r と x の値、枠の値の条件、
落とす補題の残りの仮定（M′ の値の小ささ・枠の引数の条件）、o(r) が実際に変わること）。
-/
import Ytosk.V3StructT1
import Ytosk.V3BaseDrop
import Ytosk.V3BumpDrop

namespace Ytosk

open T

/-- The valuation of `M.take x` from the ranking of `M`. -/
noncomputable def drop1 (M : Mat) (x : Nat) (rk : Bool → Nat → Nat) : Valn :=
  rhsIt (M.take x) (rkBound (M.take x) rk)

/-- **The value of the last column** (`t = 1`): `o(x) = ψ_{v(r)+1}(0)`. -/
theorem o_last_t1 {M : Mat} {x r : Nat} {ρ : Valn} (hx : x + 1 = M.length) (hC : Cons M ρ)
    (hG : Good3 M ρ) (h1 : par M 1 x = some r) (hx1 : entry M 1 x ≠ 0) (hx2 : entry M 2 x = 0) :
    ρ.o x = psi (succ (ρ.v r)) z z := by
  have hxM : x < M.length := by omega
  have hrM : r < M.length := by have := par_lt M 1 x r h1; omega
  have hvr := hG.ot_v r hrM
  have hup : upg M x = none := by unfold upg; rw [if_pos (Or.inr (Or.inr hx))]
  have hvx : ρ.v x = succ (ρ.v r) := by
    rw [(hC x hxM).2]; unfold vRhs
    rw [if_neg hx1, if_pos hx2, hup, h1]
    show sf (add (ρ.v r) one) = succ (ρ.v r)
    rw [add_one_eq_succ hvr, sf_ot (by rw [← add_one_eq_succ hvr]; exact isOT_add hvr rfl)]
  have hnc : ∀ c ∈ children M x, ¬ Counted M x c := by
    intro c hc; have := (mem_children hc).1; have := (mem_children hc).2; omega
  rw [o_of_no_counted hC hxM (by rw [hvx, ← add_one_eq_succ hvr]; exact isOT_add hvr rfl) hnc, hvx]

/-- **Value invariant**: at an upgrade `i → k`, the summands of `v(P_1 i)` absorbed by the bump term `W` of
`v(k) = v(P_1 i) + W` are `◁ W` (measured: they are `1`). -/
def UpgAbs (M : Mat) (ρ : Valn) : Prop :=
  ∀ i k W, upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
    ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W

/-- **Value hypothesis on the drop**: `UpgAbs` at `x − 1` only (the only place the drop lemma uses it;
the global `UpgAbs` is false on a matrix reachable from SRO, while this form has no exception in the
random expansions from SRO up to length 20). -/
def UpgAbsX (M : Mat) (x : Nat) (ρ : Valn) : Prop :=
  ∀ i k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
    ∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W

theorem UpgAbs.x {M : Mat} {ρ : Valn} (h : UpgAbs M ρ) (x : Nat) : UpgAbsX M x ρ :=
  fun i k W _ hu hv hW => h i k W hu hv hW

/-- **`t = 1`, `q ≠ r`, all `n ≥ 2`**, with the base from the drop lemma. -/
theorem t1_main_drop {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    -- the remaining hypotheses of the drop lemma
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbs M ρ) (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    (hne : (drop1 M (r + L) rkM).o r ≠ ρ.o r)
    {μ br vr : T}
    (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z) (hro : ρ.o r = psi vr br z)
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
  have hdrop := drop_all (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hVSt hF hFO hArgT
    (bump_drop (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hKD hTD hAbs hWS)
    hUA
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
  apply t1_main_struct hlen hL hd0e hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 h1 hx2 hqr hC hG hRM
    hrot hcb hμr hbr hoxv hro hF1 (by rw [← hvr]; exact hv) hot hlhd _ hV hW hLo hsM hpM
  intro g hg a ha h
  rw [gexp_one_eq hlen] at h
  exact base_v_read hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hg ha h

end Ytosk
