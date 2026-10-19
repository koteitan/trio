import Ytosk.V3T0DepS
import Ytosk.V3DropWeak0
import Ytosk.V3T0UpgAbs

namespace Ytosk.T0UpgConsumer
open T

theorem drop_all_H0 {N : Mat} {x : Nat} (hx : x + 1 = N.length)
    (hR0 : R0P N) (hZ2 : Z2 N) (hSD : SibDec N) (hZ1 : Z1C N) (hUAT : UAT N) (hUAB : UAB N)
    {σ σ' : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ) (hI : ValInv N σ) (hD : DropResH0 N x σ σ')
    (hC' : Cons (N.take x) σ') (hRk' : Rk (N.take x) rk) :
    ∀ i, i < x → PO σ σ' i ∧ PV N σ σ' i :=
  DropWeak0.drop_all_hard hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hI.vs hD.vst hI.fc hI.fo hD.hard
    (bump_drop hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hI.g hC' hRk' hI.kd hI.td hD.ab hD.ws) hD.ua

theorem t0_otdS_weak {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hJ : RowJ M) (hBL : BumpLeaf M)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ) (hAbsS : T0AbsW M r L ρ)
    (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsXW0 M (r + L) ρ)
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
        ¬ (lt (spArg (ρ.v g) z (sumN (Lc0.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true))
    (hArgB : ∀ g, par M 0 r = some g → Counted M g r → r = r + L - 1 → NBPar M (r + L - 1) → ∀ n, 2 ≤ n →
      ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
        ∀ X X', ρ.o g = psi (ρ.v g) X z → σ.o g = psi (ρ.v g) X' z → Lhd z X' X) :
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
  have hdrop := DropWeak0.drop_all_hard (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hVSt hF hFO (hardArg_of_argT hArgT)
    (bump_drop (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hKD hTD hAbs hWS) hUA
  have hoff := chg_off (show r + L + 1 = M.length from hlen) hC hG hC1 hRk1
  have hVT : ValInv (M.take (r + L)) ρ' :=
    ⟨good3_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop,
      vsmallF_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hVS hVSt,
      frameClosed_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hF,
      frameOT_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hFO,
      bumpKidsDec_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hKD,
      bumpTermDec_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hTD⟩
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
    have hnzr : ∀ w, ρ.o r ≠ psi w z z := by
      intro w hw
      rw [hor] at hw; simp only [psi.injEq] at hw
      have := lt_app_one (spArg (ρ.v r) z
        (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r))))
      rw [hw.2.1] at this; exact T.not_lt_z _ this
    have hl' := T0UpgAbs.lhd_or_weak_t0 hx hUA he1 hp hg hC hG hC1 (by omega)
      (hdrop r (by omega)).1 (hdrop r (by omega)).2 hnzr hlt
    have hlB : ∀ i, par M 0 g = some i → col M g = bump M i → Lhd z (ρ'.o r) (ρ.o r) := by
      intro i hi hb
      apply T0UpgAbs.lhd_t0_of hx hUA he1 hp hC hG (by omega) (hdrop r (by omega)).1 (hdrop r (by omega)).2 hnzr hlt
      by_cases hr : r = r + L - 1
      · exact Or.inr (fun hnb => hnb g i (by rw [← hr]; exact hg) hi hb)
      · exact Or.inl hr
    have hl2 : Lhd z (ρ'.o r) (ρ.o r) ∨
        (∃ w', ρ'.o r = psi w' z z ∧ WkVA w' (ρ.v r) ∧ isOT (psi w' z z) = true) ∧
          (Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g r) ∧
          (Counted M g r → ∀ X X', ρ.o g = psi (ρ.v g) X z → σ.o g = psi (ρ.v g) X' z → Lhd z X' X) := by
      rcases hl' with hl | ⟨hrx, hnb, hCX, w', hw', hWk, _, hwot⟩
      · exact Or.inl hl
      · right
        refine ⟨⟨w', hw', hWk, hwot⟩, fun hc => ?_, fun hc => hArgB g hg hc hrx hnb n hn2 σ hCN⟩
        have hxcnt : Counted M r (r + L) := by
          refine ⟨fun h => ?_, fun h => ?_⟩
          · have h2 : entry M 2 (r + L) = (bump M r).2.2 := by
              show (col M (r + L)).2.2 = _; rw [h]
            rw [hx2] at h2; simp [bump] at h2
          · obtain ⟨hu, _⟩ := h
            unfold isUpg at hu
            obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hu
            have := upg_target_e2 (of_decide_eq_true hk)
            omega
        have he2r : entry M 2 r = 0 := by
          rcases hCX with hno | ⟨_, _, k, W, _, hu, _⟩
          · exact absurd hxcnt (hno _ hxr)
          · have := hZ2 r; have := (upg_e12 hu).2; omega
        exact counted_first0 hlen hL hp (by omega) hR0 hZ2 hx2 hn2 hg hc he2r
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
    have hG0le : ∀ g', par M 0 r = some g' → col M r = bump M g' → entry M 1 g' ≠ 0 → entry M 2 g' ≠ 0 →
        sumN ((children (M.take (r + L)) r).map ρ'.o) ≤ sumN ((children (M.take (r + L)) r).map ρ.o) := by
      intro g' hg' hjb h1 h2
      have hgg : g' = g := Option.some.inj (hg'.symm.trans hg)
      rw [hgg] at hjb h1 h2
      exact (brelS_lhdE (g0_drop_rel (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG
        hC1 hRk1 hKD hWS h1 h2 hrc hjb hxr (o_x_one hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG)
        (fun k _ hk => hdrop k hk)
        (fun k hk hkx _ => T0UpgAbs.v_lhd_bump_children hlen hR0 hZ2 hSD hZ1 hUAT hUAB hJ hBL hp hg hjb
          hC hG hC1 hRk1 hUA hdrop k hk hkx)).2).le
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
            (fun k hk hkx _ => T0UpgAbs.v_lhd_bump_children hlen hR0 hZ2 hSD hZ1 hUAT hUAB hJ hBL hp hg hjb
              hC hG hC1 hRk1 hUA hdrop k hk hkx)
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
          hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hg hjb h1 h2 hTD (hAbsS n hn2 σ hCN)
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
          hTD hKD (hAbsS n hn2 σ hCN) hch
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
        · rw [hσlast]; exact hlB pp hpg hjb
        · rw [par1_pre0 hlen hL hp hn (by omega)]
          cases hpp : par M 1 pp with
          | none => rfl
          | some m =>
            have := par_lt M 1 pp m hpp
            exact (hoffD m (by omega)).2 (hpnd m hpp)
        · intro k hk
          by_cases hkn : k + 1 < n
          · rw [hσmid k hkn]; exact isOT_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN
          · rw [show k = n - 1 by omega, hσlast]; exact hGT.ot_o r (by rw [List.length_take]; omega)
    intro i hi
    have hdep := t0_dep_otS hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hg hRM hC1 hGT hσB hσBv
      hoffD hσmid hσlast hF hVS hVR hFO hTD hKD (hAbsS n hn2 σ hCN) hlt hl2 hy' (hLast n hn2 g hg) hS3 hS2
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

#print axioms drop_all_H0
#print axioms t0_otdS_weak
end Ytosk.T0UpgConsumer
