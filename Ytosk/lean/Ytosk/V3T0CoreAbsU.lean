/- Port of the t=0 core engine to the upgrade-aware absorption input. -/
import Ytosk.WfDrL4
import Ytosk.V3T0AbsUpg
import Ytosk.V3T0DepAbsU
import Ytosk.WfT2X2

namespace Ytosk
open T Ytosk.WfAbsW Ytosk.WfT2X
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem t0_coreG2U {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hJ : RowJ M) (hBL : BumpLeaf M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hdrop0 : ∀ k, k < r + L → PO ρ (drop1 M (r + L) rkM) k ∧ PV2 M ρ (drop1 M (r + L) rkM) k)
    (hVT0 : ValInv (M.take (r + L)) (drop1 M (r + L) rkM))
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbsU : T0AbsWU M r L ρ)
    (hSd : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hLast : ∀ n, 2 ≤ n → ∀ g, par M 0 r = some g → Counted M g r →
      Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hN : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      (∀ i, i < r → DepX M (r + L) true i → isOT (σ.o i) = true) ∧ VSmallNewN M r ρ σ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L 0 0 n) ρN ∧ Rk (TRIO.gexp M r L 0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L 0 0 n) ρN ∧ FrameOT (TRIO.gexp M r L 0 0 n) ρN ∧
      FrameClosed (TRIO.gexp M r L 0 0 n) ρN ∧
      BumpKidsDec (TRIO.gexp M r L 0 0 n) ρN ∧ BumpTermDec (TRIO.gexp M r L 0 0 n) ρN ∧
      (∀ P, RWC P M ρ → RWC P (M.take (r + L)) (drop1 M (r + L) rkM) →
        (∀ i, i < r → ¬ (par M 0 r = some i ∧ Counted M i r) →
          ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → DepX M (r + L) true c →
            QP P (ρ.v i) (Lc.map ρ.o) (ρN.o c)) →
        (∀ g, par M 0 r = some g → Counted M g r → ∀ Lc, CL M g = Lc ++ [r] →
          ∀ cv, (cv = omid M r L ρ ∨ cv = (drop1 M (r + L) rkM).o r) → QP P (ρ.v g) (Lc.map ρ.o) cv) →
        RWC P (TRIO.gexp M r L 0 0 n) ρN) ∧
      ((roots (TRIO.gexp M r L 0 0 n)).map ρN.o).Pairwise (fun a b => b ≤ a) ∧
      isOT (root (TRIO.gexp M r L 0 0 n) ρN) = true ∧ root (TRIO.gexp M r L 0 0 n) ρN < root M ρ := by
  intro n hn2
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := hR12 _ he1
  -- the drop `M.take x`
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  set ρ' := drop1 M (r + L) rkM with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hdrop := hdrop0
  have hoff := chg_off (show r + L + 1 = M.length from hlen) hC hG hC1 hRk1
  have hVT : ValInv (M.take (r + L)) ρ' := hVT0
  have hnx : ¬ DepX M (r + L) false (r + L) := not_depX_v_x he1
  have hD := dep_strict02 (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hx2 hp hnx
  -- the expansion `N`
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hnl : (n - 1) * L + L = n * L := by rw [← Nat.succ_mul]; congr 1; omega
  have hRN := rk_N0 hlen hL hp hn hR0 hZ2 hx2 hn2 hRM
  set rkN : Bool → Nat → Nat := fun b i => rkM b (phi0 r L i) with hrkN
  set σ := rhsIt N (rkBound N rkN) with hσ
  have hCN : Cons N σ := cons_of_rk hRN
  obtain ⟨hOTD, hVNN⟩ := hN n hn2 σ hCN
  refine ⟨σ, rkN, hCN, hRN, ?_⟩
  -- the values of `N`
  have hvC := t0_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB) hC hG hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB) hC hG hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i) := by
    intro i hi
    have h := hvD i (by rw [hlN]; omega)
    exact ⟨fun hd => by rw [h.1 (fun h' => hd h'.2), tau_o_lt hi],
      fun hd => by rw [h.2 (fun h' => hd h'.2), tau_v_lt hi]⟩
  have hσB : ∀ i, r ≤ i → i < N.length → σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i :=
    fun i hri hiN => (hvC i hiN).1 (fun h => by omega)
  have hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ := by
    intro k hk
    have : k * L + L ≤ n * L := by
      have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
    rw [hσB _ (by omega) (by rw [hlN]; omega)]
    exact tau_o_root hk hL
  have hσlast : σ.o (r + (n - 1) * L) = ρ'.o r := by
    rw [hσB _ (by omega) (by rw [hlN]; omega)]
    have := tau_o_last (r := r) (L := L) (n := n) (ρ := ρ) (ρ' := ρ') (oMid := omid M r L ρ) hL
    rwa [Nat.add_zero, Nat.add_zero] at this
  have hGT := good3_take2 (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop
  have hGN : GoodOT N σ := goodOT_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN
    hRN hGT hσB (fun i hi hd => (hoffD i hi).1 hd) hOTD
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG
  -- roots, frames
  have hsN : ∀ i ∈ roots N, Single (σ.o i) := fun i hi =>
    single_oT hCN hGN (by unfold roots at hi; exact List.mem_range.mp (List.mem_filter.mp hi).1)
  have hOXle : omid M r L ρ ≤ ρ.o r := by
    rw [hor, hom]; exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one _⟩))
  have hlt0 : ρ'.o r < ρ.o r :=
    hD true r (depLike_r hlen hL hp hx2 (depLike_depX M (r + L))) (by omega)
  have hO'le : ρ'.o r ≤ omid M r L ρ := by
    obtain ⟨_, s', y', hs'⟩ := (hdrop r (by omega)).1.2
    have h := hlt0
    rw [hs', hor] at h
    rw [hs', hom]
    rcases psi_lt_psi_z_iff.mp h with h1 | ⟨rfl, h2⟩
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h1))
    · exact psi_le_psi_arg ((lt_succ_iff (x := _)).mp h2)
  have hσBv : ∀ i, r ≤ i → i < N.length → σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i :=
    fun i hri hiN => (hvC i hiN).2 (fun h => by omega)
  have hFOT : FrameOT (M.take (r + L)) ρ' :=
    frameOT_take (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hFO
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z := by
    intro s' y' hs hne
    obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
    rw [hs] at hy0; simp only [psi.injEq] at hy0
    have hv'ot := (hdrop r (by omega)).2.2
    rw [sf_ot hv'ot] at hy0
    have hCv : ChgX M (r + L) false r := by
      by_contra hn'; apply hne; rw [hy0.1]; exact (hoff r (by omega)).2 hn'
    have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl (by omega)
    have ho := o_of_no_counted hC1 hrT hv'ot hT.2.1
    rw [hs] at ho; simp only [psi.injEq] at ho; exact ho.2.1
  have hss : ∀ d, d < r → σ.v d ≠ ρ.v d → σ.o d = psi (σ.v d) z z := by
    intro d hd hne
    have hdv : DepX M (r + L) false d := by
      by_contra hn'; exact hne ((hoffD d hd).2 hn')
    exact o_N_noc hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hd
      (cl_nil_of_depv hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hd hdv)
  have hRW : ∀ P, RWC P M ρ → RWC P (M.take (r + L)) ρ' →
      (∀ i, i < r → ¬ (par M 0 r = some i ∧ Counted M i r) →
        ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → DepX M (r + L) true c →
          QP P (ρ.v i) (Lc.map ρ.o) (σ.o c)) →
      (∀ g, par M 0 r = some g → Counted M g r → ∀ Lc, CL M g = Lc ++ [r] →
        ∀ cv, (cv = omid M r L ρ ∨ cv = ρ'.o r) → QP P (ρ.v g) (Lc.map ρ.o) cv) →
      RWC P N σ := fun P hM hT hDP hG0 =>
    rwc_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN P hM hC1 hGT hT
      (fun i hri hiN => ⟨hσB i hri hiN, hσBv i hri hiN⟩) hoffD hσmid hσlast (hLast n hn2) hO'le hy' hDP hG0
  by_cases hrg : ∃ g, par M 0 r = some g
  · obtain ⟨g, hg⟩ := hrg
    have hgr : g < r := par_lt M 0 r g hg
    have hrc : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
    have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
    -- the drop at `r`
    have hDr : DepX M (r + L) true r := depLike_r hlen hL hp hx2 (depLike_depX M (r + L))
    have hlt : ρ'.o r < ρ.o r := hD true r hDr (by omega)
    obtain ⟨hS1N, hS2, hS3⟩ := hSd n hn2 σ hCN g hg
    have hS1 : Counted M g r → Lhd z (σ.o g) (ρ.o g) := fun hc => by
      obtain ⟨X, X', hX, hX', -, hl, -⟩ := hS1N hc
      rw [hX, hX']; exact hl
    have hG0le : ∀ g', par M 0 r = some g' → col M r = bump M g' → entry M 1 g' ≠ 0 → entry M 2 g' ≠ 0 →
        sumN ((children (M.take (r + L)) r).map ρ'.o) ≤ sumN ((children (M.take (r + L)) r).map ρ.o) :=
      fun _ _ _ _ _ => g0le_of_po2 hG hVT.g hdrop
    -- the propagation and the root
    have hAbsFrame := hAbsU n hn2 σ hCN
    have hAbsX := bdxu_absX hAbsFrame.1
    have hdl := t0_dep_lhdU hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hg hRM
      hoffD hF hFO hVS hTD hKD (Bd := fun i => BdXU M N ρ σ r i) hAbsX bdxu_up bdxu_F bdxu_cl hAbsFrame.2
      hVNN hS3 hS1 hS2
    refine ⟨good3_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hC1
      hGT
      hσB (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => le_of_lt (PX.lt (hdl true d hD hd))) hσmid hσlast
      (hLast n hn2) (fun _ _ _ => hlt0),
      frameOT_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hFO hFOT
        (fun i hri hiN => ⟨hσB i hri hiN, hσBv i hri hiN⟩) hoffD (fun g' hg' hcnt' => by
          have hgg : g' = g := Option.some.inj (hg'.symm.trans hg)
          subst hgg
          have hσvg : σ.v g' = ρ.v g' := (hoffD g' hgr).2 (fun hd =>
            uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hp (by omega) hd hrc hcnt')
          exact frameOT_g0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hg' hcnt'
            (fun c hc hd => (hoffD c hc).1 hd) hσvg hσmid hσlast (hLast n hn2 g' hg' hcnt') hlt0 hy' hFO
            (hOTD g' hgr (DepX.ochild hrc hcnt'.1 hcnt'.2 hDr))),
      frameClosed_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hF hVT.fc
        (fun i hri hiN => ⟨hσB i hri hiN, hσBv i hri hiN⟩) hoffD hσmid hσlast (hLast n hn2) hC1 hGT
        hlt0.le hO'le hy' (fun d hd hD => le_of_lt (PX.lt (hdl true d hD hd))) hss,
      bumpKidsDec_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hKD hVT.kd hσB
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => le_of_lt (PX.lt (hdl true d hD hd))) hσmid hσlast
        hOXle hO'le,
      bumpTermDec_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hKD hTD hVT.td hσB
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => le_of_lt (PX.lt (hdl true d hD hd))) hσmid hσlast
        hO'le hG0le, hRW,
      rootP_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hR01 hR12 h00 hpM
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => le_of_lt (PX.lt (hdl true d hD hd)))
        (fun h => absurd h (by rw [hg]; simp)) hσmid hσlast hOXle hO'le, ?_⟩
    apply root_N_A hlen hL hp hn hR0 hR01 hR12 h00 hg hG hGN
    · intro i hi
      by_cases hd : DepX M (r + L) true i
      · exact le_of_lt (PX.lt (hdl true i hd hi))
      · rw [(hoffD i hi).1 hd]
    · intro R hR hRA _
      exact PX.lt (hdl true R (dep_anc_x hUAT hZ2 hR12 hBE hx hx2 hRA) hR)
  · have hrn : par M 0 r = none := by
      cases h : par M 0 r with
      | none => rfl
      | some g => exact absurd ⟨g, h⟩ hrg
    have hσG : ∀ i, i < r → σ.o i = ρ.o i := fun i hi => (hoffD i hi).1 (fun hd => by
      have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn true i hd; omega)
    have hOX : mulT (omid M r L ρ) n < ρ.o r := by rw [hor, hom]; exact (lhd_mulT (η := z) n).1
    refine ⟨good3_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hC1
      hGT
      hσB (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => absurd hd (by
        have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn true d hD; omega))
      hσmid hσlast (hLast n hn2) (fun g hg => absurd hg (by rw [hrn]; simp)),
      frameOT_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hFO hFOT
        (fun i hri hiN => ⟨hσB i hri hiN, hσBv i hri hiN⟩) hoffD
        (fun g hg => absurd hg (by rw [hrn]; simp)),
      frameClosed_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hF hVT.fc
        (fun i hri hiN => ⟨hσB i hri hiN, hσBv i hri hiN⟩) hoffD hσmid hσlast (hLast n hn2) hC1 hGT
        hlt0.le hO'le hy' (fun d hd hD => absurd hd (by
          have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn true d hD; omega)) hss,
      bumpKidsDec_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hKD hVT.kd hσB
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => absurd hd (by
          have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn true d hD; omega))
        hσmid hσlast hOXle hO'le,
      bumpTermDec_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hKD hTD hVT.td hσB
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => absurd hd (by
          have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn true d hD; omega))
        hσmid hσlast hO'le (fun g hg => absurd hg (by rw [hrn]; simp)), hRW, ?_, ?_⟩
    · exact rootP_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hR01 hR12 h00 hpM
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => absurd hd (by
          have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn true d hD; omega))
        (fun _ => hσG) hσmid hσlast hOXle hO'le
    have hpN := rootP_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hR01 hR12 h00 hpM
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => absurd hd (by
          have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn true d hD; omega))
        (fun _ => hσG) hσmid hσlast hOXle hO'le
    exact root_N_B hlen hL hp hn hR01 hR12 h00 hrn hn2 hsM hpM hsN hpN hσG hσmid hσlast hOX
end Ytosk
