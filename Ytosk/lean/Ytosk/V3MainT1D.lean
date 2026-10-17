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

/-- **The strong absorption everywhere** (2026-10-17): assumed only by the superseded routes (the old `t = 0`
engines `t0_otd*`, `t0_vsmallR*`, `t0_main`, and the old top theorems `trio_terminates*`, `desc_step` …), which the
current top theorem `trio_terminates_main_V2_cur` does not use. It is false on standard matrices. -/
def OldUpgAbs : Prop := ∀ (M : Mat) (x : Nat) (ρ : Valn), UpgAbsX M x ρ

theorem UpgAbs.x {M : Mat} {ρ : Valn} (h : UpgAbs M ρ) (x : Nat) : UpgAbsX M x ρ :=
  fun i k W _ hu hv hW => h i k W hu hv hW

/-- **`UpgAbsX` with the weak alternative** (2026-10-12, drop-fix): the absorbed summands are `◁ W`, or the new
`v(x − 1) = V + 1` has the component condition `WCSP`, the parent of `x − 1` is not a bump child and `x` is not of
type `t = 0` (T2Ext: …(5,1,0)(4,2,0)(5,3,1), `x − 1` loses its upgrade to an ancestor, `V = ω`, `W = Ω_ω`, where
`UpgAbsX` is false). 2026-10-17: the last condition was `entry M 2 x ≠ 0`; it is now `entry M 1 x ≠ 0`, because the
same happens at `t = 1` with `q = r = x − 1`: …(15,0,0)(13,2,0)(14,3,0) (T2Ext, see desc.md). The second conjunct
(2026-10-17, for the `q = r` engine of t1) is `SmallSelf (V + 1)` of V3SeedWeak written out: every component of
`V + 1` is below `Ω_{V+1}` (CS is too strong: t1's probe_qrseed, 3 cases). -/
def UpgAbsXW (M : Mat) (x : Nat) (ρ : Valn) : Prop :=
  ∀ i k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
    (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
      (WCSP M ρ i (add (vOpt ρ (par M 1 i)) one) ∧
          (∀ g ∈ comps z (add (vOpt ρ (par M 1 i)) one), g < psi (add (vOpt ρ (par M 1 i)) one) z z) ∧
          NBPar M i ∧ (entry M 1 (i + 1) ≠ 0 ∨ T0Easy M (i + 1)))

/-- **`UpgAbsXW` without the row-1 condition** (2026-10-17): the weak alternative for every type of `x`.
On the 11 sets the strong form fails at `t = 0` only on 2 standard matrices of std_a
(…(5,1,0)(4,2,0)(4,0,0) and …(4,2,0)(5,0,0)), where this form holds. -/
def UpgAbsXW0 (M : Mat) (x : Nat) (ρ : Valn) : Prop :=
  ∀ i k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
    (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
      (WCSP M ρ i (add (vOpt ρ (par M 1 i)) one) ∧
          (∀ g ∈ comps z (add (vOpt ρ (par M 1 i)) one), g < psi (add (vOpt ρ (par M 1 i)) one) z z) ∧
          NBPar M i)

/-- `UpgAbsXW` from the form without the row-1 condition and the strong form at `t = 0` outside the easy shape. -/
theorem UpgAbsXW.of0 {M : Mat} {x : Nat} {ρ : Valn} (h : UpgAbsXW0 M x ρ)
    (h0 : entry M 1 x = 0 → ¬ T0Easy M x → UpgAbsX M x ρ) : UpgAbsXW M x ρ := by
  intro i k W hi hu hv hW
  by_cases hx : entry M 1 x = 0 ∧ ¬ T0Easy M x
  · exact Or.inl (h0 hx.1 hx.2 i k W hi hu hv hW)
  · rcases h i k W hi hu hv hW with h1 | ⟨h2, h3, h4⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h2, h3, h4, ?_⟩
      rw [hi]
      by_cases hx1 : entry M 1 x = 0
      · exact Or.inr (by by_contra hn; exact hx ⟨hx1, hn⟩)
      · exact Or.inl hx1

theorem UpgAbsX.toW {M : Mat} {x : Nat} {ρ : Valn} (h : UpgAbsX M x ρ) : UpgAbsXW M x ρ :=
  fun i k W hi hu hv hW => Or.inl (h i k W hi hu hv hW)

/-- **At `t = 0` outside the easy shape the weak alternative is void**: it needs `entry M 1 x ≠ 0` or
`T0Easy M x`. -/
theorem UpgAbsXW.toX {M : Mat} {x : Nat} {ρ : Valn} (h : UpgAbsXW M x ρ) (hx1 : entry M 1 x = 0)
    (hh : ¬ T0Easy M x) : UpgAbsX M x ρ := fun i k W hi hu hv hW =>
  (h i k W hi hu hv hW).resolve_right (fun h' => by
    rcases h'.2.2.2 with h1 | h1
    · exact h1 (by rw [hi]; exact hx1)
    · exact hh (by rw [hi] at h1; exact h1))

/-- The strong form when the parent of `x` is `x − 1` and its parent is a bump child. -/
theorem UpgAbsXW.toX_xm1 {M : Mat} {x : Nat} {ρ : Valn} (h : UpgAbsXW M x ρ) (hx1 : entry M 1 x = 0)
    (hp : par M 0 x = some (x - 1)) (hnb : ¬ NBPar M (x - 1)) : UpgAbsX M x ρ :=
  h.toX hx1 (fun he => hnb (he.2 hp))

/-- The strong form when the parent `r` of `x` is a bump child. -/
theorem UpgAbsXW.toX_bump {M : Mat} {x : Nat} {ρ : Valn} (h : UpgAbsXW M x ρ) (hx1 : entry M 1 x = 0)
    {r g : Nat} (hp : par M 0 x = some r) (hg : par M 0 r = some g) (hb : col M r = bump M g) :
    UpgAbsX M x ρ :=
  h.toX hx1 (fun he => he.1 r g hp hg hb)

/-- **Under the strong `UpgAbsX` a weak `o` has the argument `0`** (the shape of `PO` before 2026-10-12): the
other weak case needs `UpgBad`, which `UpgAbsX` excludes. -/
theorem PO.zero_of_strong {M : Mat} {x : Nat} {ρ ρ' : Valn} {i : Nat} (hx : x + 1 = M.length)
    (hUA : UpgAbsX M x ρ) (hC : Cons M ρ) (hG : Good3 M ρ) (hiM : i < M.length)
    (hPO : PO ρ ρ' i) (hPV : PV M ρ ρ' i) :
    LhdE (ρ'.o i) (ρ.o i) ∨ (WkOA (ρ'.o i) (ρ.o i) ∧ ∃ w, ρ.o i = psi w z z) := by
  rcases hPO.1 with h | ⟨hW, hw | hnl⟩
  · exact Or.inl h
  · exact Or.inr ⟨hW, hw⟩
  rcases hPV.1 with hl | ⟨_, _, hn | ⟨_, _, k, W, hi2, hu, hvk, hWz, hbad⟩⟩
  · exact absurd hl hnl
  · exact Or.inr ⟨hW, _, o_of_no_counted hC hiM (hG.ot_v i hiM) hn⟩
  · exact absurd (hUA i k W (by omega) hu hvk hWz) hbad

/-- **Under the strong `UpgAbsX` a weak column has no counted child** (the other case of `CntX` needs
`UpgBad`, which `UpgAbsX` excludes). -/
theorem CntX.nocnt_of_strong {M : Mat} {x : Nat} {ρ : Valn} {i : Nat} (hx : x + 1 = M.length)
    (hUA : UpgAbsX M x ρ) (h : CntX M ρ i) : ∀ c ∈ children M i, ¬ Counted M i c := by
  rcases h with hn | ⟨_, _, k, W, hi2, hu, hvk, hWz, hbad⟩
  · exact hn
  · exact absurd (hUA i k W (by omega) hu hvk hWz) hbad

/-- **Away from `x − 1` a weak `o` has the argument `0`** without any absorption hypothesis: the other weak
case needs `UpgBad`, which lives only at `x − 1`. -/
theorem PO.zero_of_ne {M : Mat} {ρ ρ' : Valn} {i : Nat} (hi : i + 2 ≠ M.length)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hiM : i < M.length)
    (hPO : PO ρ ρ' i) (hPV : PV M ρ ρ' i) :
    LhdE (ρ'.o i) (ρ.o i) ∨ (WkOA (ρ'.o i) (ρ.o i) ∧ ∃ w, ρ.o i = psi w z z) := by
  rcases hPO.1 with h | ⟨hW, hw | hnl⟩
  · exact Or.inl h
  · exact Or.inr ⟨hW, hw⟩
  rcases hPV.1 with hl | ⟨_, _, hn | ⟨_, _, k, W, hi2, _⟩⟩
  · exact absurd hl hnl
  · exact Or.inr ⟨hW, _, o_of_no_counted hC hiM (hG.ot_v i hiM) hn⟩
  · exact absurd hi2 hi

/-- **Away from `x − 1` a weak column has no counted child** without any absorption hypothesis. -/
theorem CntX.nocnt_of_ne {M : Mat} {ρ : Valn} {i : Nat} (hi : i + 2 ≠ M.length) (h : CntX M ρ i) :
    ∀ c ∈ children M i, ¬ Counted M i c := by
  rcases h with hn | ⟨_, _, k, W, hi2, _⟩
  · exact hn
  · exact absurd hi2 hi

/-- **The `PO` at the parent `r` of a `t = 0` column `x`** without the strong absorption when `r ≠ x − 1`
(`PO.zero_of_ne`); when `r = x − 1` the strong form, from `hS` in the easy shape. -/
theorem PO.zero_t0 {M : Mat} {x : Nat} {ρ ρ' : Valn} {r : Nat} (hx : x + 1 = M.length)
    (hUA : UpgAbsXW M x ρ) (hx1 : entry M 1 x = 0) (hp : par M 0 x = some r)
    (hS : par M 0 x = some (x - 1) → NBPar M (x - 1) → UpgAbsX M x ρ)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hrM : r < M.length) (hPO : PO ρ ρ' r) (hPV : PV M ρ ρ' r) :
    LhdE (ρ'.o r) (ρ.o r) ∨ (WkOA (ρ'.o r) (ρ.o r) ∧ ∃ w, ρ.o r = psi w z z) := by
  by_cases hr : r = x - 1
  · have hp' : par M 0 x = some (x - 1) := by rw [← hr]; exact hp
    by_cases hnb : NBPar M (x - 1)
    · exact PO.zero_of_strong hx (hS hp' hnb) hC hG hrM hPO hPV
    · exact PO.zero_of_strong hx (hUA.toX_xm1 hx1 hp' hnb) hC hG hrM hPO hPV
  · exact PO.zero_of_ne (by omega) hC hG hrM hPO hPV

/-- **No counted child of a weak parent `r` of a `t = 0` column `x`** in the easy shape. -/
theorem CntX.nocnt_t0 {M : Mat} {x : Nat} {ρ : Valn} {r : Nat} (hx : x + 1 = M.length)
    (hUA : UpgAbsXW M x ρ) (hx1 : entry M 1 x = 0) (hp : par M 0 x = some r)
    (hS : par M 0 x = some (x - 1) → NBPar M (x - 1) → UpgAbsX M x ρ) (h : CntX M ρ r) :
    ∀ c ∈ children M r, ¬ Counted M r c := by
  by_cases hr : r = x - 1
  · have hp' : par M 0 x = some (x - 1) := by rw [← hr]; exact hp
    by_cases hnb : NBPar M (x - 1)
    · exact CntX.nocnt_of_strong hx (hS hp' hnb) h
    · exact CntX.nocnt_of_strong hx (hUA.toX_xm1 hx1 hp' hnb) h
  · have hrx : r < x := par_lt M 0 x r hp
    exact CntX.nocnt_of_ne (by omega) h

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
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ) (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsXW M (r + L) ρ)
    (hne : (drop1 M (r + L) rkM).o r ≠ ρ.o r)
    {μ br vr : T}
    (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z) (hro : ρ.o r = psi vr br z)
    (hF1 : ∀ i, r < i → i < r + L → DepX M (r + L) true i → ¬ DepX M (r + L) false i →
      lt μ (ρ.v i) = true)
    (hV : ∀ m i, i < r + L → DepX M (r + L) false i →
      VLocal M (r + L) ρ (gamS μ br ((drop1 M (r + L) rkM).o r) m) μ i)
    (hW : ∀ m i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → Counted M i c →
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
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rkM))
    (Pn : Mat → Valn → Prop) (hP1 : Pn (M.take (r + L)) (drop1 M (r + L) rkM)) (hPs : ExpStepT1 Pn M r L d0 ρ) :
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
    hrot hcb hμr hbr hoxv hro hF1 (by rw [← hvr]; exact hv) hot hlhd _ hV hW hLo hsM hpM hG1 Pn hP1 hPs
  intro g hg a ha h
  rw [gexp_one_eq hlen] at h
  exact base_v_read hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hg ha h

end Ytosk
