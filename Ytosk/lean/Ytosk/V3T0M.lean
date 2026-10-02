/-
**3 行・t = 0・n ≥ 2: 組み立て。**

- r に親 g があるとき: N と M の根はどちらも r より前の列だけ（`root_N_A`）。D の呼び出しは ◁ で真に下がり
  （`t0_dep_lhd`、種 `t0_S1`・`t0_S2`）、D の外は同じ値なので、根の和は真に下がる。
- r が根のとき: r より前は値が変わらず、M の根 r（値 ψ_v(Y0 + 1)）が N ではコピーの根
  ψ_v(Y0) × (n − 1) と M.take x での r の値に替わる（`root_N_B`）。
-/
import Ytosk.V3T0Bump
import Ytosk.V3T0RW

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
include hlen hL hp hn

/-- **The root value when `r` has a parent**: only the columns before `r` are roots, in both. -/
theorem root_N_A (hR0 : R0P M) (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0)
    {g : Nat} (hg : par M 0 r = some g) {ρ σ : Valn} (hG : Good3 M ρ)
    (hGN : GoodOT (TRIO.gexp M r L 0 0 n) σ)
    (hle : ∀ i, i < r → σ.o i ≤ ρ.o i)
    (hstrict : ∀ R, R < r → Anc0 M R (r + L) → col M R = (0, 0, 0) → σ.o R < ρ.o R) :
    isOT (root (TRIO.gexp M r L 0 0 n) σ) = true ∧ root (TRIO.gexp M r L 0 0 n) σ < root M ρ := by
  classical
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have he0r : 0 < entry M 0 r := by have := hR0 r g hg; omega
  have he0x : entry M 0 (r + L) = entry M 0 r + 1 := hR0 _ _ hp
  set f' : Nat → T := fun i => if col M i = (0, 0, 0) then σ.o i else z with hf'
  set f : Nat → T := fun i => if col M i = (0, 0, 0) then ρ.o i else z with hf
  have hcol0 : ∀ {N : Mat} {i : Nat}, entry N 0 i ≠ 0 → col N i ≠ (0, 0, 0) := by
    intro N i h hc
    rw [col_eq_entries] at hc
    simp only [Prod.mk.injEq] at hc
    exact h hc.1
  have hot' : ∀ i, i < r → isOT (f' i) = true := by
    intro i hi; simp only [hf']; split
    · exact hGN.ot_o i (by rw [hlN]; have : L ≤ n * L := Nat.le_mul_of_pos_left L hn; omega)
    · rfl
  have hot : ∀ i, i < r → isOT (f i) = true := by
    intro i hi; simp only [hf]; split
    · exact hG.ot_o i (by omega)
    · rfl
  have hrootN : root (TRIO.gexp M r L 0 0 n) σ = sumN ((List.range r).map f') := by
    unfold root
    rw [hlN, List.range_add, List.map_append]
    rw [sumN_append_zeros (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      have hir := List.mem_range.mp hi
      split
      · exact hGN.ot_o i (by rw [hlN]; have : L ≤ n * L := Nat.le_mul_of_pos_left L hn; omega)
      · rfl)]
    · congr 1
      apply List.map_congr_left
      intro i hi
      rw [col_pre0 hlen hL hp hn (by have := List.mem_range.mp hi; omega)]
    · intro t ht
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
      have hk' := List.mem_range.mp hk
      have := e0_copies_ge hlen hL hp hn (j := r + k) (by omega) (by omega)
      rw [if_neg (hcol0 (by omega))]
  have hrootM : root M ρ = sumN ((List.range r).map f) := by
    unfold root
    rw [← hlen]
    have hz : ∀ t ∈ (List.map (fun x => r + x) (List.range (L + 1))).map
        (fun i => if col M i = (0, 0, 0) then ρ.o i else z), t = z := by
      intro t ht
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
      have hk' := List.mem_range.mp hk
      have he : entry M 0 (r + k) ≠ 0 := by
        rcases Nat.lt_or_ge k L with h | h
        · have := e0_B_ge hlen hL hp h; omega
        · rw [show r + k = r + L by omega, he0x]; omega
      rw [if_neg (hcol0 he)]
    rw [show r + L + 1 = r + (L + 1) by omega, List.range_add, List.map_append,
      sumN_append_zeros (fun t ht => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
        have hir := List.mem_range.mp hi
        split
        · exact hG.ot_o i (by omega)
        · rfl) _ hz]
  rw [hrootN, hrootM]
  refine ⟨isOT_sumN _ (fun t ht => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht; exact hot' i (List.mem_range.mp hi)), ?_⟩
  obtain ⟨R, hRA, hR0c, hRl⟩ := root_t1 hR01 hR12 h00 (r + L)
  have he0R : entry M 0 R = 0 := by rw [col_eq_entries] at hR0c; simp only [Prod.mk.injEq] at hR0c; exact hR0c.1
  have hRr : R < r := by
    by_contra h
    have hRx := hRA.le
    rcases Nat.lt_or_ge R (r + L) with h' | h'
    · have := e0_B_ge hlen hL hp (q := R - r) (by omega); rw [show r + (R - r) = R by omega] at this; omega
    · rw [show R = r + L by omega, he0x] at he0R; omega
  apply sumN_range_lt f' f r hRr hot' hot
  · intro i hi; simp only [hf', hf]; split
    · exact hle i hi
    · exact le_refl _
  · simp only [hf', hf]; rw [if_pos hR0c, if_pos hR0c]; exact hstrict R hRr hRA hR0c
  · intro i h1 h2
    have hn' := hcol0 (hRl i h1 (by omega))
    simp only [hf', hf]; exact ⟨if_neg hn', if_neg hn'⟩

/-- **The root value when `r` is a root**: the root `r` of `M` (value `X`) becomes the copy roots
`O × (n − 1)` and `X′ ≤ O`, with `O · n < X`. -/
theorem root_N_B (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0) (hrn : par M 0 r = none)
    (hn2 : 2 ≤ n) {ρ σ : Valn} {O X' : T}
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hsN : ∀ i ∈ roots (TRIO.gexp M r L 0 0 n), Single (σ.o i))
    (hpN : ((roots (TRIO.gexp M r L 0 0 n)).map σ.o).Pairwise (fun a b => b ≤ a))
    (hσG : ∀ i, i < r → σ.o i = ρ.o i)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = O) (hσlast : σ.o (r + (n - 1) * L) = X')
    (hOX : mulT O n < ρ.o r) :
    isOT (root (TRIO.gexp M r L 0 0 n) σ) = true ∧ root (TRIO.gexp M r L 0 0 n) σ < root M ρ := by
  rw [root_eq_roots hsN hpN, root_eq_roots hsM hpM]
  refine ⟨isOT_sumN _ (fun t ht => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht; exact (hsN i hi).1), ?_⟩
  have hrM := roots_M_root hlen hL hp hn hR01 hR12 h00 hrn
  have hrN := roots_N_root hlen hL hp hn hR01 hR12 h00 hrn
  set RG := (List.range r).filter (fun i => decide (col M i = (0, 0, 0))) with hRG
  have hRGv : RG.map σ.o = RG.map ρ.o := List.map_congr_left (fun i hi => by
    have := List.mem_range.mp (List.mem_filter.mp hi).1; exact hσG i this)
  have hcv : ((List.range n).map (fun k => r + k * L)).map σ.o = List.replicate (n - 1) O ++ [X'] := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel] at hσlast
    rw [List.range_succ, List.map_append, List.map_append, List.map_singleton, List.map_singleton,
      Nat.add_sub_cancel, hσlast]
    congr 1
    rw [List.map_map, List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
    exact hσmid k (by have := List.mem_range.mp hk; omega)
  have hsN' : ∀ t ∈ RG.map ρ.o ++ (List.replicate (n - 1) O ++ [X']), Single t := by
    intro t ht
    have : t ∈ (RG ++ (List.range n).map (fun k => r + k * L)).map σ.o := by
      rw [List.map_append, hRGv, hcv]; exact ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp this
    exact hsN i (by rw [hrN]; exact hi)
  have hsM' : ∀ t ∈ RG.map ρ.o ++ [ρ.o r], Single t := by
    intro t ht
    have : t ∈ (RG ++ [r]).map ρ.o := by rw [List.map_append, List.map_singleton]; exact ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp this
    exact hsM i (by rw [hrM]; exact hi)
  rw [hrN, List.map_append, hRGv, hcv] at hpN ⊢
  rw [hrM, List.map_append, List.map_singleton] at hpM ⊢
  rw [sumN_append_dec hsN' hpN, sumN_append_dec hsM' hpM, sumN_singleton (hsM' _ (by simp))]
  apply app_lt_app_left
  have hp2 := (List.pairwise_append.mp hpN).2.1
  have hs2 : ∀ t ∈ List.replicate (n - 1) O ++ [X'], Single t := fun t ht => hsN' t (List.mem_append_right _ ht)
  have hO : Single O := hs2 O (List.mem_append_left _ (List.mem_replicate.mpr ⟨by omega, rfl⟩))
  rw [sumN_append_dec hs2 hp2, sumN_replicate hO, sumN_singleton (hs2 _ (by simp))]
  have hX'O : X' ≤ O := (List.pairwise_append.mp hp2).2.2 O
    (List.mem_replicate.mpr ⟨by omega, rfl⟩) X' (by simp)
  have hle : app (mulT O (n - 1)) X' ≤ mulT O n := by
    rw [show n = (n - 1) + 1 by omega, mulT_succ', Nat.add_sub_cancel]
    rcases (le_iff _ _).mp hX'O with h | h
    · exact le_of_lt (app_lt_app_left _ h)
    · rw [h]
  exact lt_of_le_of_lt hle hOX

/-- **When `r` is a root, nothing before `r` is in `D`.** -/
theorem nodep_G_root (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M)
    (hUAB : UAB M) (he1 : entry M 1 (r + L) = 0) (hrn : par M 0 r = none) :
    ∀ b i, DepX M (r + L) b i → r ≤ i := by
  have hArx : Anc0 M r (r + L) := anc0_of_par M 0 r (r + L) hp
  -- a child at or after `r` of a column is in the subtree of `r`, so the column is at or after `r`
  have hsub : ∀ {i c}, c ∈ children M i → r ≤ c → r ≤ i := by
    intro i c hc hrc
    have hcl := (mem_children hc).2
    have hpc := (mem_children_iff.mp hc).2
    by_cases hcr : c = r
    · rw [hcr, hrn] at hpc; cases hpc
    · have hAc : Anc0 M r c := anc_between hArx c hrc (by omega)
      exact (anc0_par hAc (Ne.symm hcr) hpc).le
  intro b i h
  induction h with
  | leaf => omega
  | ochild hc _ _ _ ih => exact hsub hc ih
  | ov _ ih => exact ih
  | @vpar i m _ hpm _ ih => have := par_lt M 1 i m hpm; omega
  | @vupg i k _ _ hu hdk ih =>
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    have hkr : k ≠ r := by
      rintro rfl; exact not_depX_v_r hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB he1 hdk
    rcases hcase with h | ⟨_, h⟩ <;> omega
  | @vbump i j k _ _ hj _ hk _ ih => exact hsub hj (hsub hk ih)

end

/-- **`t = 0`, all `n ≥ 2`, with `Good3` of `M[n]`** (from its standard values `GoodOT`): `M[n]` has a value, standard at the root and below the root value of `M`.
Hypotheses: those of the drop lemma (as `t0_n1`, without `hVL`: the shape of `D` is `dv_shape` and the
strictness of the drop is `dep_strict0`), and for `N = M[n]`: its valuation satisfies `Good3`,
`VSmallNewN` and the root values do not increase; the last copy root counts at `g` when `r` does;
`hVr` (a changed `v(r)` in `M.take x` is small in a rewriting frame of `g`); in the bump case the
last copy's sum drops in the strong relation (`g0_drop_rel`, with `v_lhd_B`) and seed S2 is `t0_S2G`. -/
theorem t0_core {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ)
    (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
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
  have hdrop := drop_all (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hVSt hF hFO hArgT
    (bump_drop (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hKD hTD hAbs hWS) hUA
  have hoff := chg_off (show r + L + 1 = M.length from hlen) hC hG hC1 hRk1
  have hVT : ValInv (M.take (r + L)) ρ' :=
    drop_pres (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC
      ⟨hG, hVS, hF, hFO, hKD, hTD⟩ ⟨hArgT, hVSt, hWS, hUA, hAbs⟩ hC1 hRk1
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
    have hl : Lhd z (ρ'.o r) (ρ.o r) := by
      rcases (hdrop r (by omega)).1.1 with hE | ⟨_, w, hw⟩
      · exact lhd_of_lhdE_lt hE hlt
      · exfalso
        rw [hor] at hw; simp only [psi.injEq] at hw
        have := lt_app_one (spArg (ρ.v r) z
          (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r))))
        rw [hw.2.1] at this; exact T.not_lt_z _ this
    -- seed S1
    have hS1 : Counted M g r → Lhd z (σ.o g) (ρ.o g) := by
      intro hcnt'
      have hσvg : σ.v g = ρ.v g := (hoffD g hgr).2 (fun hd =>
        uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hp (by omega) hd hrc hcnt')
      exact t0_S1 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hg hcnt' hF
        (fun c hc hd => (hoffD c hc).1 hd) hσvg hσmid hσlast (hLast n hn2 g hg hcnt') hl hy'
    have hG0le : ∀ g', par M 0 r = some g' → col M r = bump M g' → entry M 1 g' ≠ 0 → entry M 2 g' ≠ 0 →
        sumN ((children (M.take (r + L)) r).map ρ'.o) ≤ sumN ((children (M.take (r + L)) r).map ρ.o) := by
      intro g' hg' hjb h1 h2
      have hgg : g' = g := Option.some.inj (hg'.symm.trans hg)
      rw [hgg] at hjb h1 h2
      exact (brelS_lhdE (g0_drop_rel (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG
        hC1 hRk1 hKD hWS h1 h2 hrc hjb hxr (o_x_one hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG)
        (fun k _ hk => hdrop k hk)
        (fun k hk hkx _ => v_lhd_B (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hp
          hC hG hC1 hRk1 hKD hTD hAbs hWS hUA hdrop k (mem_children hk).1 hkx)).2).le
    -- seed S2
    have hS2 : col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → Lhd z (σ.v g) (ρ.v g) := by
      intro hjb h1 h2
      have hgD : DepX M (r + L) false g := DepX.vbump h1 h2 hrc hjb hxr DepX.leaf
      obtain ⟨_, hpnd, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hp (by omega) hgD
      rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j', k', hch, _, hchj, _, hKnd, hLnd⟩
      · exact absurd h2' h2
      · have hchM := children_g_last hlen hL hp hg
        have hjr : j' = r := by
          have := congrArg List.getLast? (hch.symm.trans hchM)
          simpa using this
        subst hjr
        -- the children of `r` in `M.take x` and the last copy
        have hdropR : isOT (sumN ((children (M.take (j' + L)) j').map ρ'.o)) = true ∧
            BRelS (sumN ((children (M.take (j' + L)) j').map ρ'.o))
              (sumN ((children (M.take (j' + L)) j').map ρ.o)) :=
          g0_drop_rel (show j' + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hKD hWS
            h1 h2 hrc hjb hxr (o_x_one hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG)
            (fun k _ hk => hdrop k hk)
            (fun k hk hkx _ => v_lhd_B (show j' + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hp
              hC hG hC1 hRk1 hKD hTD hAbs hWS hUA hdrop k (mem_children hk).1 hkx)
        have hG0ot : isOT (sumN ((children (M.take (j' + L)) j').map ρ.o)) = true := isOT_sumN _ (fun t ht => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
          rw [children_take, List.mem_filter] at hc
          exact hG.ot_o c (mem_children hc.1).2)
        have hcopy : ∀ k, k < n → bumpTerm N σ g (j' + k * L) =
            omega (sumN (((children M j').filter (fun c => decide (c < j' + L))).map
              (σ.o ∘ shk j' (k * L)))) := by
          intro k hk
          have hcolk : col N (j' + k * L) = bump N g := by
            rw [col_root0 hlen hL hp hn hk, bump_pre0 hlen hL hp hn (by omega)]; exact hjb
          unfold bumpTerm
          rw [if_pos hcolk]
          have hch0 := children_copy0 hlen hL hp hn (k := k) (q := 0) hk hL
          rw [Nat.add_zero, Nat.add_zero] at hch0
          rw [hch0, List.map_map]
        apply t0_S2G (O' := omega (sumN ((children (M.take (j' + L)) j').map ρ'.o))) hlen hL hp hn hR0 hZ2
          hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hg hjb h1 h2 hTD hAbs
        · intro d hd hdr
          have hdL : d ∈ Lb := by
            rw [hch] at hd
            rcases List.mem_append.mp hd with h | h
            · exact h
            · simp at h; omega
          have hdg : par M 0 j' ≠ some d := by
            intro h'; rw [hg] at h'; cases h'; have := (mem_children hd).1; omega
          apply bumpTerm_eq_of
          · rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
          · intro _
            rw [children_pre0 hlen hL hp hn hdr hdg]
            apply List.map_congr_left
            intro e he
            have her := children_lt_r hlen hL hp hdr hdg he
            exact (hoffD e her).1 (hLnd d hdL e he).2
        · intro k hkn
          rw [hcopy k (by omega), children_take]
          congr 1; congr 1
          apply List.map_congr_left
          intro c hc
          rw [List.mem_filter] at hc
          have hcgt := (mem_children hc.1).1
          have hcx : c < j' + L := by simpa using hc.2
          obtain ⟨q', rfl⟩ : ∃ q', c = j' + q' := ⟨c - j', by omega⟩
          simp only [Function.comp]
          rw [shk_B, hσB _ (by omega) (by
            rw [hlN]; have : k * L + L ≤ n * L := by
              have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this
              exact this
            omega), tau_o_mid hkn (by omega) (by omega)]
        · rw [hcopy (n - 1) (by omega), children_take]
          congr 1; congr 1
          apply List.map_congr_left
          intro c hc
          rw [List.mem_filter] at hc
          have hcgt := (mem_children hc.1).1
          have hcx : c < j' + L := by simpa using hc.2
          obtain ⟨q', rfl⟩ : ∃ q', c = j' + q' := ⟨c - j', by omega⟩
          simp only [Function.comp]
          rw [shk_B, hσB _ (by omega) (by rw [hlN]; omega), tau_o_last (by omega)]
        · exact single_omega hdropR.1
        · exact brelS_lhdE (brelS_omega hdropR.1 hG0ot hdropR.2)
        · rw [par1_pre0 hlen hL hp hn hgr]
          cases hpp : par M 1 g with
          | none => rfl
          | some m =>
            have := par_lt M 1 g m hpp
            exact (hoffD m (by omega)).2 (hpnd m hpp)
    -- seed S3
    have hS3 : ∀ pp, par M 0 g = some pp → entry M 1 pp ≠ 0 → entry M 2 pp ≠ 0 → col M g = bump M pp →
        Lhd z (σ.v pp) (ρ.v pp) := by
      intro pp hpg h1 h2 hjb
      have hppg := par_lt M 0 g pp hpg
      have hgp : g ∈ children M pp := mem_children_iff.mpr ⟨by omega, hpg⟩
      have hpD : DepX M (r + L) false pp := DepX.vbump h1 h2 hgp hjb hrc hDr
      obtain ⟨_, hpnd, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hp (by omega) hpD
      rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j', k', hch, _, hchj, _, hKnd, hLnd⟩
      · exact absurd h2' h2
      · have hjg : j' = g := by
          by_contra hne
          have hgL : g ∈ Lb := by
            rw [hch] at hgp
            rcases List.mem_append.mp hgp with h | h
            · exact h
            · simp at h; exact absurd h.symm hne
          exact (hLnd g hgL r hrc).2 hDr
        subst hjg
        have hkr : k' = r := by
          have hchM := children_g_last hlen hL hp hg
          rw [hchj] at hchM
          have := congrArg List.getLast? hchM
          simpa using this
        rw [hkr] at hchj
        have hLj : ∀ d ∈ Lb, d < j' :=
          (sib_order (children_sorted M pp) (R := []) (by rw [hch])).1
        apply t0_S3 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hg hpg hjb h1 h2
          hTD hKD hAbs hch
        · intro d hd
          have hdg : par M 0 r ≠ some d := fun h =>
            (hLnd d hd r (mem_children_iff.mpr ⟨by have := hLj d hd; omega, h⟩)).2 hDr
          have hdj := hLj d hd
          apply bumpTerm_eq_of
          · rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
          · intro _
            rw [children_pre0 hlen hL hp hn (by omega) hdg]
            apply List.map_congr_left
            intro e he
            have her := children_lt_r hlen hL hp (by omega) hdg he
            exact (hoffD e her).1 (hLnd d hd e he).2
        · intro d hd hdr
          have hdK : d ∈ Kb := by
            rw [hchj] at hd
            rcases List.mem_append.mp hd with h | h
            · exact h
            · simp at h; omega
          exact (hoffD d hdr).1 (hKnd d hdK)
        · exact hor
        · intro k hk; rw [hσmid k hk, hom]
        · rw [hσlast]; exact hl
        · rw [par1_pre0 hlen hL hp hn (by omega)]
          cases hpp : par M 1 pp with
          | none => rfl
          | some m =>
            have := par_lt M 1 pp m hpp
            exact (hoffD m (by omega)).2 (hpnd m hpp)
        · intro k hk
          have : k * L < n * L := Nat.mul_lt_mul_of_pos_right hk hL
          exact hGN.ot_o _ (by rw [hlN]; omega)
    -- the propagation and the root
    have hdl := t0_dep_lhd hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hg hRM
      hoffD hF hVS hTD hKD hAbs hVNN hS3 hS1 hS2
    refine ⟨good3_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hC1
      hGT
      hσB (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => le_of_lt (hdl true d hD hd).1) hσmid hσlast
      (hLast n hn2) (fun _ _ _ => hl),
      frameOT_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hFO hFOT
        (fun i hri hiN => ⟨hσB i hri hiN, hσBv i hri hiN⟩) hoffD (fun g' hg' hcnt' => by
          have hgg : g' = g := Option.some.inj (hg'.symm.trans hg)
          subst hgg
          have hσvg : σ.v g' = ρ.v g' := (hoffD g' hgr).2 (fun hd =>
            uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hp (by omega) hd hrc hcnt')
          exact frameOT_g0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hg' hcnt'
            (fun c hc hd => (hoffD c hc).1 hd) hσvg hσmid hσlast (hLast n hn2 g' hg' hcnt') hl hy' hFO
            (hOTD g' hgr (DepX.ochild hrc hcnt'.1 hcnt'.2 hDr))),
      frameClosed_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hF hVT.fc
        (fun i hri hiN => ⟨hσB i hri hiN, hσBv i hri hiN⟩) hoffD hσmid hσlast (hLast n hn2) hC1 hGT
        hlt0.le hO'le hy' (fun d hd hD => le_of_lt (hdl true d hD hd).1) hss,
      bumpKidsDec_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hKD hVT.kd hσB
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => le_of_lt (hdl true d hD hd).1) hσmid hσlast
        hOXle hO'le,
      bumpTermDec_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hGN hKD hTD hVT.td hσB
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => le_of_lt (hdl true d hD hd).1) hσmid hσlast
        (fun _ => hl) hG0le, hRW,
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
        hσmid hσlast (fun h => absurd hrn h) (fun g hg => absurd hg (by rw [hrn]; simp)), hRW, ?_, ?_⟩
    · exact rootP_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hR01 hR12 h00 hpM
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => absurd hd (by
          have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn true d hD; omega))
        (fun _ => hσG) hσmid hσlast hOXle hO'le
    have hpN := rootP_N_t0 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hR01 hR12 h00 hpM
        (fun i hi hd => (hoffD i hi).1 hd) (fun d hd hD => absurd hd (by
          have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn true d hD; omega))
        (fun _ => hσG) hσmid hσlast hOXle hO'le
    exact root_N_B hlen hL hp hn hR01 hR12 h00 hrn hn2 hsM hpM hsN hpN hσG hσmid hσlast hOX


/-- **`t = 0`, all `n ≥ 2`**: `M[n]` has a value, standard at the root and below the root value of `M`.
Hypotheses: those of the drop lemma (as `t0_n1`, without `hVL`: the shape of `D` is `dv_shape` and the
strictness of the drop is `dep_strict0`), and for `N = M[n]`: its valuation satisfies `Good3`,
`VSmallNewN` and the root values do not increase; the last copy root counts at `g` when `r` does;
`hVr` (a changed `v(r)` in `M.take x` is small in a rewriting frame of `g`); in the bump case the
last copy's sum drops in the strong relation (`g0_drop_rel`, with `v_lhd_B`) and seed S2 is `t0_S2G`. -/
theorem t0_main' {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ)
    (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hLast : ∀ n, 2 ≤ n → ∀ g, par M 0 r = some g → Counted M g r →
      Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hN : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      Good3 (TRIO.gexp M r L 0 0 n) σ ∧ VSmallNewN M r ρ σ ∧
      (∀ i ∈ roots (TRIO.gexp M r L 0 0 n), Single (σ.o i)) ∧
      ((roots (TRIO.gexp M r L 0 0 n)).map σ.o).Pairwise (fun a b => b ≤ a)) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L 0 0 n) ρN ∧ Rk (TRIO.gexp M r L 0 0 n) rkN ∧
      isOT (root (TRIO.gexp M r L 0 0 n) ρN) = true ∧ root (TRIO.gexp M r L 0 0 n) ρN < root M ρ := by
  intro n hn2
  obtain ⟨ρN, rkN, hCN, hRN, _, _, _, _, _, _, _, h⟩ := t0_core hlen hL hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 hp he1 hC hG hRM
    hVS hF hFO hArgT hKD hTD hAbs hWS hVSt hUA hsM hpM hLast
    (fun n hn σ hCN => let h := hN n hn σ hCN;
      ⟨fun i hi _ => h.1.ot_o i (by rw [lenN0 hlen (by omega)]; omega), h.2.1⟩) n hn2
  exact ⟨ρN, rkN, hCN, hRN, h⟩

/-- `t0_main′` with the unused hypothesis `hVL` (kept for the existing callers). -/
theorem t0_main {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ)
    (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    {ζ μ : T} (_hVL : ∀ i, i < r + L → DepX M (r + L) false i → VLocal M (r + L) ρ ζ μ i)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hLast : ∀ n, 2 ≤ n → ∀ g, par M 0 r = some g → Counted M g r →
      Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hN : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      Good3 (TRIO.gexp M r L 0 0 n) σ ∧ VSmallNewN M r ρ σ ∧
      (∀ i ∈ roots (TRIO.gexp M r L 0 0 n), Single (σ.o i)) ∧
      ((roots (TRIO.gexp M r L 0 0 n)).map σ.o).Pairwise (fun a b => b ≤ a)) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L 0 0 n) ρN ∧ Rk (TRIO.gexp M r L 0 0 n) rkN ∧
      isOT (root (TRIO.gexp M r L 0 0 n) ρN) = true ∧ root (TRIO.gexp M r L 0 0 n) ρN < root M ρ :=
  t0_main' hlen hL hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hBE hR01 h00 hp he1 hC hG hRM hVS hF hFO hArgT hKD hTD
    hAbs hWS hVSt hUA hsM hpM hLast hN

end Ytosk
