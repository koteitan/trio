/-
**3 行・t = 0: drop-fix の VSmallR は M → M[n] で保たれる（main_GP の hVSRexp の t = 0 部分）。**

VSmallR は枠の性質（`QVR`）なので `frameQ_N_t0` で運ぶ。M・M.take x の枠は M の VSmallR と `vsmallR_take`。
- r より前の D の子: 添字が同じなら新しい引数 y′ は古い y より小さく（`t0_D_of_shape`）、書き換えと hi(y′) ≠ 0 の
  前提は古い側へ移る。添字が変わる子は引数 0 で書き換えない。
- g の枠: 状態は中間の写しで増えるだけ。子 omid = ψ_v(Y0) と o′(r) ≤ o(r) = ψ_v(Y0 + 1) の前提は古い側へ移る。
-/
import Ytosk.V3T0Col
import Ytosk.V3DropRH

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- `VSmallR` as a frame property. -/
def QVR (a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z →
    (lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true) →
    (split y (psi (succ s) z z)).1 ≠ z →
    ∀ u, ¬ lt a u = true → ∀ g ∈ comps u s,
      g ≤ psi s z z ∨ g ≤ spArg a z (sumN Lv) ∨ ∃ d ∈ comps u a, g ≤ d

theorem t0v_head_le_of_le : ∀ {t t' : T}, t ≤ t' → head t ≤ head t'
  | z, _, _ => z_le _
  | psi a b c, z, h => by
    rcases (le_iff _ _).mp h with h | h
    · exact absurd h (T.not_lt_z _)
    · cases h
  | psi a b c, psi a' b' c', h => by
    show psi a b z ≤ psi a' b' z
    rcases (le_iff _ _).mp h with h | h
    · rcases T.psi_lt_psi.mp h with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, _⟩
      · exact (le_iff _ _).mpr (Or.inl (T.psi_lt_psi.mpr (Or.inl h')))
      · exact (le_iff _ _).mpr (Or.inl (T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, h'⟩))))
      · exact le_refl _
    · cases h; exact le_refl _

/-- A high part survives going up. -/

theorem t0v_split_fst_ne_of_le {y' y θ : T} (h : (split y' θ).1 ≠ z) (hle : y' ≤ y) : (split y θ).1 ≠ z := by
  cases y' with
  | z => exact absurd rfl h
  | psi a b c =>
    have hn : ¬ lt (psi a b z) θ = true := by
      intro hl; apply h; simp [split, hl]
    cases y with
    | z =>
      rcases (le_iff _ _).mp hle with h' | h'
      · exact absurd h' (T.not_lt_z _)
      · cases h'
    | psi a' b' c' =>
      have hh : psi a b z ≤ psi a' b' z := t0v_head_le_of_le hle
      have hn' : ¬ lt (psi a' b' z) θ = true := fun hl => hn (lt_of_le_of_lt hh hl)
      simp [split, hn']


/-- **`VSmallR` of `N = M[n]`** (`t = 0`, `n ≥ 2`) from that of `M`, given the class residuals `T0Shape`
(the `D` columns before `r`: with the same `v` the argument drops by `◁`, with a new `v` it is `0`). -/
theorem t0_vsmallR (hU0 : OldUpgAbs) (hSh : T0Shape) : ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN → VSmallR M ρ →
    VSmallR (TRIO.gexp M r L 0 0 n) σ := by
  intro M ρ rk r L n σ rkN hctx hVR
  obtain ⟨hM, hS, I, R, hlen, hL, hp, he1, _, hn2, hCN, hRN, hGN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  set ρ' := drop1 M (r + L) rk with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hdrop := drop_all hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs hDr.vst
    I.fc I.fo hDr.argT
    (bump_drop hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td hDr.ab hDr.ws)
    hDr.ua
  have hVRT := vsmallR_take hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop hVR
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hvC := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
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
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good
  set Y0 := spArg (ρ.v r) z (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r)))
    with hY0
  -- the drop at `r`: `o′(r) ≤ o(r)`, and a new subscript comes with the argument `0`
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hO'le : ρ'.o r ≤ ρ.o r := by
    rcases PO.zero_t0 hx hDr.ua he1 hp (fun _ _ => hU0 _ _ _) I.cons I.good (by omega) (hdrop r (by omega)).1 (hdrop r (by omega)).2 hDr.ws.2.2 with hE | ⟨_, w, hw⟩
    · exact hE.le
    · exfalso
      rw [hor] at hw; simp only [psi.injEq] at hw
      have := lt_app_one Y0
      rw [hw.2.1] at this; exact T.not_lt_z _ this
  have hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z := by
    intro s' y' hs hne
    obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
    rw [hs] at hy0; simp only [psi.injEq] at hy0
    have hv'ot := (hdrop r (by omega)).2.2
    rw [sf_ot hv'ot] at hy0
    have hCv : ChgX M (r + L) false r := by
      by_contra hn'; apply hne; rw [hy0.1]; exact (hoff r (by omega)).2 hn'
    have hT := (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hCv).1 rfl (by omega)
    have ho := o_of_no_counted hC1 hrT hv'ot hT.2.1
    rw [hs] at ho; simp only [psi.injEq] at ho; exact ho.2.1
  apply frameQ_N_t0 hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hGN.toOT QVR
    (ρ' := ρ') hVR hVRT hσB hoffD
  · -- the frame of `g` with `r` counted
    intro g hg hgc
    have hgr : g < r := par_lt M 0 r g hg
    have hrg : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
    have hσvg : σ.v g = ρ.v g := by
      apply (hoffD g hgr).2
      intro hdv
      exact uncnt_of_depv (show r + L + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp
        (by omega) hdv hrg hgc
    apply g_frames_t0 hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hGN.toOT QVR
      hg hgc (fun c hc hd => (hoffD c hc).1 hd) hσvg hσmid hσlast
      (counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn2 hg hgc)
      (fun Lc c R hCL => hVR g (by omega) Lc c R hCL)
    intro Lc j cv hCL hcv s y hsy htr hhi u hu g' hg'
    -- the state grows with the middle copies
    have hgM : g < M.length := by omega
    obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hgM
    rw [hCL] at hsM hpM
    simp only [List.map_append, List.map_singleton] at hsM hpM
    have hOr : omid M r L ρ < ρ.o r := by
      rw [hom, hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one _⟩)
    have hsO : Single (omid M r L ρ) :=
      ⟨isOT_omid hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN,
        by rw [hom]; exact ⟨_, _, rfl⟩⟩
    have hmono : spArg (ρ.v g) z (sumN (Lc.map ρ.o)) ≤
        spArg (ρ.v g) z (sumN (Lc.map ρ.o ++ List.replicate j (omid M r L ρ))) := by
      have hs : ∀ t ∈ Lc.map ρ.o ++ List.replicate j (omid M r L ρ), Single t := by
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact hsM t (List.mem_append_left _ ht)
        · rw [(List.mem_replicate.mp ht).2]; exact hsO
      have hpw : (Lc.map ρ.o ++ List.replicate j (omid M r L ρ)).Pairwise (fun a b => b ≤ a) := by
        have hp1 := List.pairwise_append.mp hpM
        refine List.pairwise_append.mpr ⟨hp1.1, List.pairwise_replicate.mpr (Or.inr (le_refl _)), ?_⟩
        intro a ha b hb
        rw [(List.mem_replicate.mp hb).2]
        exact le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp))
      rw [sumN_append_dec hs hpw, spArg_app]
      apply le_spArg
      exact isOT_sumN _ (fun t ht => (hs t (List.mem_append_right _ ht)).1)
    -- the old frame of `r` (`o(r) = ψ_s(y0)` with `y ≤ y0`) fires and rewrites
    have hold : ∀ y0, ρ.o r = psi s y0 z → y ≤ y0 → g' ≤ psi s z z ∨
        g' ≤ spArg (ρ.v g) z (sumN (Lc.map ρ.o ++ List.replicate j (omid M r L ρ))) ∨
        ∃ d ∈ comps u (ρ.v g), g' ≤ d := by
      intro y0 hy0 hyy
      have htr0 : lt (spArg (ρ.v g) z (sumN (Lc.map ρ.o))) y0 = true ∧
          lt (psi (ρ.v g) z z) (psi s y0 z) = true :=
        ⟨show _ < y0 from lt_of_lt_of_le (lt_of_le_of_lt hmono (show _ < y from htr.1)) hyy,
          show _ < psi s y0 z from lt_of_lt_of_le (show _ < psi s y z from htr.2) (psi_le_psi_arg hyy)⟩
      rcases hVR g hgM Lc r [] hCL s y0 hy0 htr0 (t0v_split_fst_ne_of_le hhi hyy) u hu g' hg' with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (le_trans h hmono))
      · exact Or.inr (Or.inr h)
    rcases hcv with rfl | rfl
    · rw [hom] at hsy; simp only [psi.injEq] at hsy
      obtain ⟨hs1, hy1, _⟩ := hsy
      exact hold (app Y0 one) (by rw [hor, hs1]) (by rw [← hy1]; exact le_of_lt (lt_app_one _))
    · have hy0 : y ≠ z := fun h => by rw [h] at htr; exact T.not_lt_z _ htr.1
      rw [hsy, hor] at hO'le
      rcases (le_iff _ _).mp hO'le with h | h
      · rcases psi_lt_psi_z_iff.mp h with h1 | ⟨hs1, h2⟩
        · exact absurd (hy' s y hsy (fun he => by rw [he] at h1; exact lt_irrefl' _ h1)) hy0
        · exact hold (app Y0 one) (by rw [hor, hs1]) (le_of_lt h2)
      · simp only [psi.injEq] at h
        exact hold (app Y0 one) (by rw [hor, h.1]) (by rw [h.2.1])
  · -- the `D` frames before `r`
    intro i hi hng Lc c Rl hCL hDc s y hsy htr hhi u hu g' hg'
    have hcCL : c ∈ CL M i := by rw [hCL]; simp
    have hcM : c ∈ children M i := cl_mem_children hcCL
    have hccnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
    have hcr : c < r := by
      by_cases hig : par M 0 r = some i
      · have hle := children_g_le hlen hL hp hig hcM
        rcases Nat.lt_or_ge c r with h | h
        · exact h
        · exfalso; have : c = r := by omega
          rw [this] at hccnt; exact hng ⟨hig, hccnt⟩
      · exact children_lt_r hlen hL hp hi hig hcM
    obtain ⟨_, hsame, hchg⟩ := (t0_D_of_shape hU0) hSh hM hS I R hlen hL hp he1 hn2 hCN c hcr hDc
    by_cases hv : σ.v c = ρ.v c
    · obtain ⟨X, X', hX, hX', hlx⟩ := hsame hv
      rw [hX'] at hsy; simp only [psi.injEq] at hsy
      obtain ⟨hs1, hy1, _⟩ := hsy
      subst hs1 hy1
      have hyy : X' ≤ X := le_of_lt hlx.1
      have htr0 : lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) X = true ∧
          lt (psi (ρ.v i) z z) (psi (ρ.v c) X z) = true :=
        ⟨show _ < X from lt_of_lt_of_le (show _ < X' from htr.1) hyy,
          show _ < psi (ρ.v c) X z from lt_of_lt_of_le (show _ < psi (ρ.v c) X' z from htr.2) (psi_le_psi_arg hyy)⟩
      exact hVR i (by omega) Lc c Rl hCL (ρ.v c) X hX htr0 (t0v_split_fst_ne_of_le hhi hyy) u hu g' hg'
    · rw [hchg hv] at hsy; simp only [psi.injEq] at hsy
      rw [← hsy.2.1] at htr; exact absurd htr.1 (T.not_lt_z _)

/-- **`hVSRexp` for `t = 0`** (main_GP's form, restricted to `srow = 0`), from the class residuals of
`T0Shape` (the same ones as `hExp_t0_mainC2`) and the one-column drop `hLast` for the prefix. -/
theorem hVSRexp_t0 (hU0 : OldUpgAbs)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hIV : T0IVRes) (hII : T0IIRes) (hS : T0ShapeR3) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∀ ρN rkN, Inv3V (expand M n) ρN rkN → VSmallR (expand M n) ρN := by
  intro M ρ rk hM hSRO hE I R hVR hz hs0 n hn2 ρN rkN V
  obtain ⟨r, L, hlen, hL, hp, he1, hexp⟩ := t0_shape I hz hs0
  rw [hexp n] at V ⊢
  have hTx : ∃ τ rkT, Inv3 (M.take (r + L)) τ rkT ∧ Res3A (M.take (r + L)) τ rkT := by
    have hjS : M.take (r + L) ≠ SRO := by
      intro h
      have hRk1 : Rk (M.take (r + L)) rk :=
        rk_take (by omega) I.rank (by
          have := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
          rwa [show M.length - 1 = r + L by omega] at this)
      rw [h] at hRk1; exact not_val_SRO _ (val_of_rk hRk1)
    have hjE : M.take (r + L) ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [List.length_take, Nat.min_eq_left (by omega)] at this
      simp only [List.length_nil] at this; omega
    obtain ⟨τ, rkT, VT, RT⟩ := hTake_of_last hLast M ρ rk hM hSRO hE I R (r + L) (by omega) hjS hjE
    exact ⟨τ, rkT, Inv3.ofV (sInv_std (std_take hM (r + L) (by omega)) hjS) VT, RT⟩
  exact (t0_vsmallR hU0) (t0Shape_of (t0ShapeR_of (t0ShapeR2_of hIV hII hS))) M ρ rk r L n ρN rkN
    ⟨hM, hSRO, I, R, hlen, hL, hp, he1, hTx, hn2, V.cons, V.rank, V.good, V.fo, V.fc, V.kd, V.td⟩ hVR

end Ytosk
