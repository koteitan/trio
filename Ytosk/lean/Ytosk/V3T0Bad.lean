/-
**3 行・t = 0 のエンジンを、落とす補題の結論と種の事実から動かす（2026-10-25、Bad2 用）。**

旧エンジン（`t0_core`・`t0_otdS`）は落とす補題の残り DropRes の欄（argT・vst・ws・ua・ab）を受け取り、中で
`drop_all`・`drop_pres` を呼び、種 S1・S2・S3 を ws の NoBad3・ua の NBParX から出していた。接ぎ木の悪い形
`Bad2` ではこれらの欄が偽になる（DropRes の形 A が成り立たない）が、落とす補題の結論（`PO`・`PV`）と
`ValInv` は `HDropU` から出る。

- `T0SeedsN`: `N = M[n]` の種の事実（S1 の節（`◁` と `RClaim`）、S2、S3）。S1 の `◁` は節から出る。
- `t0_coreG`・`t0_otdG`: 旧エンジンの写しで、DropRes の欄の代わりに落とす補題の結論・`ValInv`・種の事実を取る。
  `BumpTermDec` の仮定は `o′(r) ≤ omid` だけ（`g3_lt`）、`hG0le` は `PO` から（`g0le_of_po`）。
-/
import Ytosk.V3T0Inv2S

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The seed facts of `N = M[n]`** (`t = 0`, `r = P_0(x)`, `g = P_0(r)`): S1 (`o(g)` drops by `◁` as a node with `RClaim`
when `r` counts at `g`), S2 (`v(g)` when `r` is the bump child of `g`) and S3 (`v(p)` when
`g` is the bump child of `p`). -/
def T0SeedsN (M : Mat) (ρ : Valn) (r L n : Nat) (σ : Valn) : Prop :=
  ∀ g, par M 0 r = some g →
    (Counted M g r → ∃ X X', ρ.o g = psi (ρ.v g) X z ∧ σ.o g = psi (ρ.v g) X' z ∧
      isOT (psi (ρ.v g) X' z) = true ∧ Lhd z (psi (ρ.v g) X' z) (psi (ρ.v g) X z) ∧
      ∀ U : T → Prop, RClaimU U ρ σ g) ∧
    (col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → Lhd z (σ.v g) (ρ.v g)) ∧
    (∀ pp, par M 0 g = some pp → entry M 1 pp ≠ 0 → entry M 2 pp ≠ 0 → col M g = bump M pp →
      Lhd z (σ.v pp) (ρ.v pp))

/-- **The sum of the children of `r` does not grow in the drop** (from `PO` at every column of `M.take x`). -/
theorem g0le_of_po {M : Mat} {x r : Nat} {ρ ρ' : Valn} (hG : Good3 M ρ) (hGT : Good3 (M.take x) ρ')
    (hdrop : ∀ k, k < x → PO ρ ρ' k ∧ PV M ρ ρ' k) :
    sumN ((children (M.take x) r).map ρ'.o) ≤ sumN ((children (M.take x) r).map ρ.o) := by
  have hlt : ∀ c ∈ children (M.take x) r, c < x ∧ c < M.length := by
    intro c hc
    have := (mem_children hc).2
    rw [List.length_take] at this; omega
  apply sumN_le2 (forall2_map_le (fun c hc => (hdrop c (hlt c hc).1).1.le))
  · intro t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    exact hGT.ot_o c (mem_children hc).2
  · intro t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    exact hG.ot_o c (hlt c hc).2

/-- **`t0_core` from the drop's conclusion and the seed facts** (no DropRes field). -/
theorem t0_coreG {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hJ : RowJ M) (hBL : BumpLeaf M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hdrop0 : ∀ k, k < r + L → PO ρ (drop1 M (r + L) rkM) k ∧ PV M ρ (drop1 M (r + L) rkM) k)
    (hVT0 : ValInv (M.take (r + L)) (drop1 M (r + L) rkM))
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbsS : T0AbsW M r L ρ)
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
  have hD := dep_strict0 (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hx2 hp hnx
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
  have hGT := good3_take (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop
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
      fun _ _ _ _ _ => g0le_of_po hG hVT.g hdrop
    -- the propagation and the root
    have hdl := t0_dep_lhd hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hg hRM
      hoffD hF hVS hTD hKD (hAbsS n hn2 σ hCN) hVNN hS3 hS1 hS2
    refine ⟨good3_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hC1
      hGT
      hσB (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => le_of_lt (hdl true d hD hd).1) hσmid hσlast
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
        hlt0.le hO'le hy' (fun d hd hD => le_of_lt (hdl true d hD hd).1) hss,
      bumpKidsDec_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hKD hVT.kd hσB
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => le_of_lt (hdl true d hD hd).1) hσmid hσlast
        hOXle hO'le,
      bumpTermDec_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hKD hTD hVT.td hσB
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => le_of_lt (hdl true d hD hd).1) hσmid hσlast
        hO'le hG0le, hRW,
      rootP_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hR01 hR12 h00 hpM
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => le_of_lt (hdl true d hD hd).1)
        (fun h => absurd h (by rw [hg]; simp)) hσmid hσlast hOXle hO'le, ?_⟩
    apply root_N_A hlen hL hp hn hR0 hR01 hR12 h00 hg hG hGN
    · intro i hi
      by_cases hd : DepX M (r + L) true i
      · exact le_of_lt (hdl true i hd hi).1
      · rw [(hoffD i hi).1 hd]
    · intro R hR hRA _
      exact (hdl true R (dep_anc_x hUAT hZ2 hR12 hBE hx hx2 hRA) hR).1
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

/-- **`t0_otdS` from the drop's conclusion and the seed facts** (no DropRes field). -/
theorem t0_otdG {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hJ : RowJ M) (hBL : BumpLeaf M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hdrop0 : ∀ k, k < r + L → PO ρ (drop1 M (r + L) rkM) k ∧ PV M ρ (drop1 M (r + L) rkM) k)
    (hVT0 : ValInv (M.take (r + L)) (drop1 M (r + L) rkM))
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbsS : T0AbsW M r L ρ)
    (hSd : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hLast : ∀ n, 2 ≤ n → ∀ g, par M 0 r = some g → Counted M g r →
      Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hVR : VSmallRP M (r + L) r ρ)
    (hPH : PH3cG M ρ)
    (hVchgRN : ∀ g, par M 0 r = some g → ∀ s' y', (drop1 M (r + L) rkM).o r = psi s' y' z → s' ≠ ρ.v r →
      ¬ psi (ρ.v r) z z < psi (succ (ρ.v g)) z z → ¬ psi s' z z < psi (succ (ρ.v g)) z z)
    (hG0N : ∀ n, 2 ≤ n → ∀ g, par M 0 r = some g →
      Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      ∀ Lc0 : List Nat, CL M g = Lc0 ++ [r] → ∀ s y, ρ.o r = psi s y z →
        ¬ (lt (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true)) :
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i, i < r → (DepX M (r + L) true i → isOT (σ.o i) = true ∧ Lhd z (σ.o i) (ρ.o i) ∧ (∀ U : T → Prop, (∀ u, U u → PathLv M (r + L) r ρ i u) → RClaimU U ρ σ i) ∧
        (σ.v i ≠ ρ.v i → σ.o i = psi (σ.v i) z z) ∧
        (σ.v i = ρ.v i → ∀ X X', ρ.o i = psi (ρ.v i) X z → σ.o i = psi (ρ.v i) X' z → X' ≠ X → REr X X')) ∧
        (DepX M (r + L) false i → isOT (σ.v i) = true ∧ Lhd z (σ.v i) (ρ.v i)) := by
  intro n hn2 σ hCN
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
  have hD := dep_strict0 (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hx2 hp hnx
  -- the expansion `N`
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hnl : (n - 1) * L + L = n * L := by rw [← Nat.succ_mul]; congr 1; omega
  have hRN := rk_N0 hlen hL hp hn hR0 hZ2 hx2 hn2 hRM
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
  have hGT := good3_take (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG
  -- roots, frames
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
  by_cases hrg : ∃ g, par M 0 r = some g
  · obtain ⟨g, hg⟩ := hrg
    have hgr : g < r := par_lt M 0 r g hg
    have hrc : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
    have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
    -- the drop at `r`
    have hDr : DepX M (r + L) true r := depLike_r hlen hL hp hx2 (depLike_depX M (r + L))
    have hlt : ρ'.o r < ρ.o r := hD true r hDr (by omega)
    obtain ⟨hS1N, hS2, hS3⟩ := hSd n hn2 σ hCN g hg
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
    intro i hi
    have hdep := t0_dep_otS hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hg hRM hC1 hGT hσB hσBv
      hoffD hσmid hσlast hF hVS hVR hFO hTD hKD (hAbsS n hn2 σ hCN) hlt
      hS1N hy' (hLast n hn2 g hg) hS3 hS2
      hPH (hVchgRN g hg) (hG0N n hn2 g hg)
    refine ⟨fun hd => ?_, fun hd => ⟨(hdep false i hi).1, (hdep false i hi).2.1 hd⟩⟩
    obtain ⟨hot, hlt, hR, hRE⟩ := hdep true i hi
    refine ⟨hot, hlt hd, hR rfl hd, fun hne => ?_, hRE rfl hd⟩
    have hdv : DepX M (r + L) false i := by
      by_contra hn'; exact hne ((hoffD i hi).2 hn')
    exact o_N_noc' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hi
      (cl_nil_of_depv' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hi hdv) (hdep false i hi).1
  · have hrn : par M 0 r = none := by
      cases h : par M 0 r with
      | none => rfl
      | some g => exact absurd ⟨g, h⟩ hrg
    intro i hi
    refine ⟨fun hd => ?_, fun hd => ?_⟩
    · have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn true i hd
      omega
    · have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn false i hd
      omega


/-- **`T0DF` from the drop's conclusion and the seed facts** (as `t0DF_ofS`). -/
theorem t0DF_ofG {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M)
    (hS : M ≠ SRO) (I : Inv3C M ρ rk) (D : T0DropF M ρ rk) (hPH : PH3cG M ρ) (hVA : VSmallRA M ρ)
    (hAbW : ∀ r L, r + L + 1 = M.length → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 → T0AbsW M r L ρ)
    (hSd : ∀ r L, r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
      ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ) :
    T0DF M ρ := by
  intro r L hlen hL hp he1 n hn σ hCN
  have hDP := D.po
  have hDV := D.vt
  rw [show M.length - 1 = r + L by omega] at hDP hDV
  have hab0 := hAbW r L hlen hp he1
  have h := t0_otdG hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab (sInvXJ_std hM hS).2 (sInvXJ_std hM hS).1.loc.2.2.2 I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDP hDV I.kd I.td hab0 (hSd r L hlen hL hp he1) I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    (hVA.toP (r + L) r) hPH
    (t0_shape3C hM hS I (D) hlen hL hp he1) (t0IVResC_holds M ρ rk r L hM hS I hlen hL hp he1)
    n hn σ hCN
  intro i hi
  refine ⟨fun hd => ?_, (h i hi).2⟩
  obtain ⟨h1, h2, _, h4, h5⟩ := (h i hi).1 hd
  exact ⟨h1, h2, trivial, h4, h5⟩

/-- **`t = 0`, `n ≥ 2`: `Inv3V2` of `M[n]` and the descent from the drop's conclusion and the seed facts** (as
`t0_final_inv3V2D`, no DropRes). -/
theorem t0_final_inv3V2G {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r L : Nat}
    (hM : Std M) (hS : M ≠ SRO) (S : SInv M) (I : Inv3V2 M ρ rk)
    (hlen : r + L + 1 = M.length) (hL : 0 < L) (hp : par M 0 (r + L) = some r)
    (he1 : entry M 1 (r + L) = 0)
    (D : T0DropF M ρ rk) (hAbW : T0AbsW M r L ρ)
    (hSd : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → T0SeedsN M ρ r L n σ)
    (I1 : Inv3V2 (M.take (r + L)) (drop1 M (r + L) rk) rk)
    (hDF : T0DF M ρ)
    (hLeaf : ∀ n, 2 ≤ n → ∀ σ rkN, Cons (TRIO.gexp M r L 0 0 n) σ → Rk (TRIO.gexp M r L 0 0 n) rkN →
      Good3 (TRIO.gexp M r L 0 0 n) σ →
      TP1LeafG (TRIO.gexp M r L 0 0 n) σ ∧ TP1WLeafG (TRIO.gexp M r L 0 0 n) σ)
    (hFrm : ∀ n, 2 ≤ n → ∀ σ rkN, Cons (TRIO.gexp M r L 0 0 n) σ → Rk (TRIO.gexp M r L 0 0 n) rkN →
      Good3 (TRIO.gexp M r L 0 0 n) σ → TakeFrameV2 (TRIO.gexp M r L 0 0 n) σ rkN) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (TRIO.gexp M r L 0 0 n) ρN rkN ∧
      isOT (root (TRIO.gexp M r L 0 0 n) ρN) = true ∧ root (TRIO.gexp M r L 0 0 n) ρN < root M ρ := by
  intro n hn2
  have hn : 1 ≤ n := by omega
  have IC := I.toC S
  have hx : r + L + 1 = M.length := hlen
  have hDP := D.po
  have hDV := D.vt
  rw [show M.length - 1 = r + L by omega] at hDP hDV
  have hx2 : entry M 2 (r + L) = 0 := S.r12 _ he1
  obtain ⟨σ, rkN, hCN, hRN, hGN, hFON, hFCN, hKDN, hTDN, _, hpN, hot, hlt⟩ :=
    t0_coreG hlen hL S.r0p S.z2 S.sibDec S.z1c S.uat S.uab (sInvXJ_std hM hS).2 (sInvXJ_std hM hS).1.loc.2.2.2 S.r12 S.bumpE2 S.r01 S.e00 hp he1 I.cons I.good
      I.rank I.vs I.fc I.fo hDP hDV I.kd I.td hAbW hSd I.rootS I.rootP
      (fun n hn g hg hc => counted_last0 hlen hL hp he1 S.r0p S.z2 S.sibDec S.z1c S.uab S.r12 hn hg hc)
      (fun n hn σ hCN => ⟨fun i hi hd => ((hDF r L hlen hL hp he1 n hn σ hCN i hi).1 hd).1,
        t0_vsmallNewN hlen hL hp he1 S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 I.cons I.good I.rank hn hCN⟩)
      n hn2
  have hctx : T0CtxC M ρ rk r L n σ rkN :=
    ⟨hM, hS, IC, D, hlen, hL, hp, he1, trivial, hn2, hCN, hRN, hGN, hFON, hFCN, hKDN, hTDN⟩
  have hvs := t0_vsmallF_atC (t0VSD_atC hDF.toH) t0IVResC_holds r L n σ rkN hctx
  -- the side facts of the frames of `N` (as in `t0_core`)
  have hcnt := hcnt_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  set ρ' := drop1 M (r + L) rk with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hdrop : ∀ k, k < r + L → PO ρ ρ' k ∧ PV M ρ ρ' k := hDP
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hnx : ¬ DepX M (r + L) false (r + L) := not_depX_v_x he1
  have hD := dep_strict0 (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 hdrop hx2 hp hnx
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hvC := t0_vals hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp S.r0p S.z2 S.sibDec S.z1c S.uat S.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp S.r0p S.z2 S.sibDec S.z1c S.uat S.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i) := by
    intro i hi
    have h := hvD i (by rw [hlN]; omega)
    exact ⟨fun hd => by rw [h.1 (fun h' => hd h'.2), tau_o_lt hi],
      fun hd => by rw [h.2 (fun h' => hd h'.2), tau_v_lt hi]⟩
  have hσB : ∀ i, r ≤ i → i < N.length → σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i ∧
      σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i :=
    fun i hri hiN => ⟨(hvC i hiN).1 (fun h => by omega), (hvC i hiN).2 (fun h => by omega)⟩
  have hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ := by
    intro k hk
    have : k * L + L ≤ n * L := by
      have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
    rw [(hσB _ (by omega) (by rw [hlN]; omega)).1]
    exact tau_o_root hk hL
  have hσlast : σ.o (r + (n - 1) * L) = ρ'.o r := by
    have hnl : (n - 1) * L + L = n * L := by rw [← Nat.succ_mul]; congr 1; omega
    rw [(hσB _ (by omega) (by rw [hlN]; omega)).1]
    have := tau_o_last (r := r) (L := L) (n := n) (ρ := ρ) (ρ' := ρ') (oMid := omid M r L ρ) hL
    rwa [Nat.add_zero, Nat.add_zero] at this
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 hx2 hn2 I.cons I.good
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
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z := by
    intro s' y' hs hne
    obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
    rw [hs] at hy0; simp only [psi.injEq] at hy0
    have hv'ot := (hdrop r (by omega)).2.2
    rw [sf_ot hv'ot] at hy0
    have hCv : ChgX M (r + L) false r := by
      by_contra hn'; apply hne; rw [hy0.1]; exact (hoff r (by omega)).2 hn'
    have hT := (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hCv).1 rfl (by omega)
    have ho := o_of_no_counted hC1 hrT hv'ot hT.2.1
    rw [hs] at ho; simp only [psi.injEq] at ho; exact ho.2.1
  have hdl : ∀ d, d < r → DepX M (r + L) true d → σ.o d ≤ ρ.o d := fun d hd hdd =>
    le_of_lt ((hDF r L hlen hL hp he1 n hn2 σ hCN d hd).1 hdd).2.1.1
  have hss : ∀ d, d < r → σ.v d ≠ ρ.v d → σ.o d = psi (σ.v d) z z := by
    intro d hd hne
    have hdv : DepX M (r + L) false d := by
      by_contra hn'; exact hne ((hoffD d hd).2 hn')
    exact ((hDF r L hlen hL hp he1 n hn2 σ hCN d hd).1 (DepX.ov hdv)).2.2.2.1 hne
  have hLastN : ∀ g, par M 0 r = some g → Counted M g r → Counted N g (r + (n - 1) * L) :=
    fun g hg hc => counted_last0 hlen hL hp he1 S.r0p S.z2 S.sibDec S.z1c S.uab S.r12 hn2 hg hc
  have hph : PH3cG N σ := G.ph3c_N_t0 hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 hx2 hn2
    I.cons I.good hCN hGN.toOT I.ph I1.ph hσB hoffD hσmid hσlast hLastN hC1 I1.good (le_of_lt hlt0) hO'le
    hy' hdl hss
  have hfc3 : FC3 N σ := G.fc3_N_t0 hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 hx2 hn2
    I.cons I.good hCN hGN.toOT I.fc3 I1.fc3 hσB hoffD hσmid hσlast hLastN hC1 I1.good (le_of_lt hlt0) hO'le
    hy' hdl hss
  have hvra : VSmallRAll N σ := vsmallRAll_N_t0 hlen hL hp hn S.r0p S.z2 S.sibDec S.z1c S.uat S.uab he1 hx2 hn2
    I.cons I.good hCN hGN.toOT hC1 hRk1 I1.good hdrop hσB hoffD hσmid hσlast hLastN hO'le hy' hdl hss I.vra
  obtain ⟨hTP, hTPW⟩ := hLeaf n hn2 σ rkN hCN hRN hGN
  have F := hFrm n hn2 σ rkN hCN hRN hGN
  exact ⟨σ, rkN, ⟨hCN, hGN, hRN, hvs, hFCN, hFON, hKDN, hTDN, hph, hfc3, hvra,
    F.ads, F.aus, tp1C_of_ph3cG hCN hGN.toOT hph hTP, F.tplos, tp1WC_of_ph3cG hCN hGN.toOT hph hTPW,
    F.tplow, F.auwl, F.auw0, F.adw, F.trigs, F.tplon, F.adn, rootS_of_good hCN hGN, hpN⟩, hot, hlt⟩

end Ytosk
