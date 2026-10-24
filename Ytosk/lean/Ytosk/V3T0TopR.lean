/-
**3 行・t = 0: hExp と hVSRexp の最上位を RClaim 方式で（2026-10-12）。**

D の列は `t0_otdR`（V3T0DepR）から。型（ClsNode）を運ばないので T0IIRes・T0ShapeR3 は要らない。
代わりに M の `VSmallR` を使うので、hExp は `VSmallR M ρ` を受け取る形になる（main_GP の帰納法で運ばれている）。
残りの D の仮定（v が変わる子の添字の成分 T0VSResD は V3VSF の vs_changed_bound で証明、t0VSD_at）:
- M の PH3c（closure の大域の仮定）と `T0CutResG`（切り口が最後の加数 t の中なら κ < T′）。これで右端の変化 RE を D の帰納法で運び、
  古い枠が書き換えるなら新しい枠も書き換える（V3T0RE、t0_dep_otR）。`T0TrigRes`（V3T0Trig）はその帰結で、今は使わない。
枠の欄（TP1C・TP1WC・TrigOmC）の影の枠の残り `T0RWResCR` は、子の引数の関係を `◁` でなく `y′ < y` で受け取る。
-/
import Ytosk.V3T0DepR
import Ytosk.V3T0Top
import Ytosk.V3T0FrmJ
import Ytosk.V3T0IV

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Residual: a rewriting `D` frame of the cut kind keeps rewriting** (the state is not a prefix of the
high part of the old argument). -/
def T0TrigRes : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      (¬ ∃ R, (split y (psi (succ s) z z)).1 = app (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) R) →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y'

/-- **Residual: the cut in the last summand** (`T0CutRes` without the condition on the low part of `y′`). -/
def T0CutResG : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z →
      (split y (psi (succ s) z z)).2 = z →
      spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ≠ z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      ∀ P a x T', y = app P (psi a x z) → y' = app P T' →
      ∀ κ ∈ cutsNS s (psi a x z), spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = app P κ → κ < T'

/-- **The `D` columns before `r` of `N = M[n]`** at one matrix: standard, `◁`, `RClaim`, and `ψ_v(0)` when
`v` changes. -/
def T0DF (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L, r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i, i < r → (DepX M (r + L) true i → isOT (σ.o i) = true ∧ Lhd z (σ.o i) (ρ.o i) ∧ True ∧
        (σ.v i ≠ ρ.v i → σ.o i = psi (σ.v i) z z) ∧
        (σ.v i = ρ.v i → ∀ X X', ρ.o i = psi (ρ.v i) X z → σ.o i = psi (ρ.v i) X' z → X' ≠ X → REr X X')) ∧
        (DepX M (r + L) false i → isOT (σ.v i) = true ∧ Lhd z (σ.v i) (ρ.v i))

/-- `T0DF` without the RE slot (enough for `VSmallF` and the standard form of `N`). -/
def T0DFH (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L, r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i, i < r → (DepX M (r + L) true i → isOT (σ.o i) = true ∧ Lhd z (σ.o i) (ρ.o i) ∧ True ∧
        (σ.v i ≠ ρ.v i → σ.o i = psi (σ.v i) z z) ∧ True) ∧
        (DepX M (r + L) false i → isOT (σ.v i) = true ∧ Lhd z (σ.v i) (ρ.v i))

theorem T0DF.toH {M : Mat} {ρ : Valn} (h : T0DF M ρ) : T0DFH M ρ := by
  intro r L h1 h2 h3 h4 n hn σ hC i hi
  refine ⟨fun hd => ?_, (h r L h1 h2 h3 h4 n hn σ hC i hi).2⟩
  obtain ⟨a, b, c, d, _⟩ := (h r L h1 h2 h3 h4 n hn σ hC i hi).1 hd
  exact ⟨a, b, c, d, trivial⟩

/-- **`T0DF` from the residuals and `VSmallR` of `M`.** -/
theorem t0DF_of (hU0 : OldUpgAbs) (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3c M ρ)
    (hCut : T0CutResG) (hIV : T0IVRes) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hVR : VSmallR M ρ) : T0DF M ρ := by
  intro r L hlen hL hp he1 n hn σ hCN
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hab0 := R.abS.lo r (by rw [show M.length - 1 = r + L by omega]; exact hp)
    (by rw [show M.length - 1 = r + L by omega]; exact he1)
  have h := (t0_otdR hU0) hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab hab0 hDr.ws hDr.vst hDr.ua I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    hVR (hPH M ρ rk hM hS I R) (hCut M ρ rk r L hM hS I R hlen hL hp he1)
    (t0_shape3 hM hS I R hlen hL hp he1) (hIV M ρ rk r L hM hS I R hlen hL hp he1) n hn σ hCN
  intro i hi
  refine ⟨fun hd => ?_, (h i hi).2⟩
  obtain ⟨h1, h2, _, h4, h5⟩ := (h i hi).1 hd
  exact ⟨h1, h2, trivial, h4, h5⟩


/-- **The same-subscript form** of a `D` column from `◁`: the arguments decrease. -/
theorem df_same {M N : Mat} {ρ σ : Valn} {c : Nat} (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ)
    (hcM : c < M.length) (hcN : c < N.length) (hvot : isOT (σ.v c) = true) (hv : σ.v c = ρ.v c)
    (hl : Lhd z (σ.o c) (ρ.o c)) :
    ∃ X X', ρ.o c = psi (ρ.v c) X z ∧ σ.o c = psi (ρ.v c) X' z ∧ X' < X := by
  obtain ⟨X, hX⟩ := o_psi_sub hC hcM
  obtain ⟨X', hX'⟩ := o_psi_sub hCN hcN
  rw [sf_ot (hG.ot_v c hcM)] at hX
  rw [sf_ot hvot, hv] at hX'
  refine ⟨X, X', hX, hX', ?_⟩
  have h := hl.1
  rw [hX, hX'] at h
  rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
  · exact absurd h (lt_irrefl' _)
  · exact h

/-- **`VSmallR` of `N = M[n]`** (`t = 0`, `n ≥ 2`) from that of `M` and the `D` facts `T0DF`. -/
theorem t0_vsmallR_DF (hU0 : OldUpgAbs) : ∀ M ρ rk r L n σ rkN, T0Ctx M ρ rk r L n σ rkN → VSmallR M ρ → T0DF M ρ →
    VSmallR (TRIO.gexp M r L 0 0 n) σ := by
  intro M ρ rk r L n σ rkN hctx hVR hDF
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
    obtain ⟨_, hlD, _, hchg, _⟩ := (hDF r L hlen hL hp he1 n hn2 σ hCN c hcr).1 hDc
    have hcN' : c < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
    have hsame := fun hv => df_same I.cons I.good hCN (show c < M.length by omega) hcN' (hGN.ot_v c hcN') hv hlD
    by_cases hv : σ.v c = ρ.v c
    · obtain ⟨X, X', hX, hX', hlx⟩ := hsame hv
      rw [hX'] at hsy; simp only [psi.injEq] at hsy
      obtain ⟨hs1, hy1, _⟩ := hsy
      subst hs1 hy1
      have hyy : X' ≤ X := le_of_lt hlx
      have htr0 : lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) X = true ∧
          lt (psi (ρ.v i) z z) (psi (ρ.v c) X z) = true :=
        ⟨show _ < X from lt_of_lt_of_le (show _ < X' from htr.1) hyy,
          show _ < psi (ρ.v c) X z from lt_of_lt_of_le (show _ < psi (ρ.v c) X' z from htr.2) (psi_le_psi_arg hyy)⟩
      exact hVR i (by omega) Lc c Rl hCL (ρ.v c) X hX htr0 (t0v_split_fst_ne_of_le hhi hyy) u hu g' hg'
    · rw [hchg hv] at hsy; simp only [psi.injEq] at hsy
      rw [← hsy.2.1] at htr; exact absurd htr.1 (T.not_lt_z _)
/-- **The rewriting-frame field `P` at one matrix** (the body of `T0RWRes P` for this `M`). -/
def T0RWResAt (P : T → T → T → T → Prop) (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  ∀ (r L n : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → Good3 (TRIO.gexp M r L 0 0 n) σ →
    (∀ i, i < r → ¬ (par M 0 r = some i ∧ Counted M i r) →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → DepX M (r + L) true c →
        QP P (ρ.v i) (Lc.map ρ.o) (σ.o c)) ∧
    (∀ g, par M 0 r = some g → Counted M g r → ∀ Lc, CL M g = Lc ++ [r] →
      ∀ cv, (cv = omid M r L ρ ∨ cv = (drop1 M (r + L) rk).o r) → QP P (ρ.v g) (Lc.map ρ.o) cv)

/-- **The shadow-frame residual of a field `P`** (`T0RWResC` with the child relation `y′ < y` in place of
`y′ ◁ y`, which the `RClaim` scheme does not carry). -/
def T0RWResCR (P : T → T → T → T → Prop) : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L n : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → Good3 (TRIO.gexp M r L 0 0 n) σ →
    (∀ i, i < r → ¬ (par M 0 r = some i ∧ Counted M i r) →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → DepX M (r + L) true c →
        ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → y' < y → ¬ ClsA s y' y →
          QPS P (ρ.v i) (Lc.map ρ.o) (σ.o c)) ∧
    (∀ g, par M 0 r = some g → Counted M g r → ∀ Lc, CL M g = Lc ++ [r] →
      ∀ cv, (cv = omid M r L ρ ∨ cv = (drop1 M (r + L) rk).o r) → QPS P (ρ.v g) (Lc.map ρ.o) cv)

/-- **The field `P` at one matrix** from `T0DF` (class A and prefixes are free) and the shadow residual. -/
theorem t0RWResAt_of (P : T → T → T → T → Prop)
    (hPA : ∀ a B s y y', isOT (psi s y z) = true → (∀ q ∈ summands B, psi s y z ≤ q) → y' < y →
      ClsA s y' y → lt B y' = true → P a B s y')
    (hPpre : ∀ a B s y', lt B y' = true → (B = z ∨ ∃ R, y' = app B R) → P a B s y')
    (hC : T0RWResCR P) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hDF : T0DF M ρ) : T0RWResAt P M ρ rk := by
  intro r L n hM hSRO I R hlen hL hp he1 hn σ hCN hGN
  obtain ⟨hD, hG0⟩ := hC M ρ rk r L n hM hSRO I R hlen hL hp he1 hn σ hCN hGN
  refine ⟨?_, fun g hg hc Lc hcl cv hcv => qp_of_qps hPpre (hG0 g hg hc Lc hcl cv hcv)⟩
  intro i hi hng Lc c Rr hCL hDc s1 y1 hcv ht1 ht2
  have hlN := lenN0 hlen (show 1 ≤ n by omega) (M := M) (L := L)
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
  have hcMl : c < M.length := by omega
  have hiM : i < M.length := by omega
  have hcN : c < (TRIO.gexp M r L 0 0 n).length := by
    rw [hlN]; have := Nat.le_mul_of_pos_left L (show 0 < n by omega); omega
  set a := ρ.v i
  set B := spArg a z (sumN (Lc.map ρ.o)) with hBdef
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hiM
  rw [hCL] at hsM hpM
  simp only [List.map_append, List.map_cons] at hsM hpM
  have hpL := List.pairwise_append.mp hpM
  have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht)) hpL.1
  have hBc : ∀ q ∈ summands B, ρ.o c ≤ q := by
    obtain ⟨s0, y0, hs0⟩ := (single_o I.cons I.good hcMl).2
    rw [hs0]
    apply spArg_summands_ge ⟨s0, y0, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq
      have := hpL.2.2 q hq (ρ.o c) (by simp)
      rwa [hs0] at this
    · simp [summands]
  obtain ⟨_, hlD, _, hchg, _⟩ := (hDF r L hlen hL hp he1 n hn σ hCN c hcr).1 hDc
  by_cases hvc : σ.v c = ρ.v c
  · obtain ⟨X, X', hX, hX', hlX⟩ := df_same I.cons I.good hCN hcMl hcN (hGN.ot_v c hcN) hvc hlD
    rw [hcv] at hX'
    simp only [psi.injEq] at hX'
    obtain ⟨rfl, rfl, -⟩ := hX'
    by_cases hA : ClsA (ρ.v c) y1 X
    · have hcX : isOT (psi (ρ.v c) X z) = true := by rw [← hX]; exact I.good.ot_o c hcMl
      exact hPA a B (ρ.v c) X y1 hcX (fun q hq => by rw [← hX]; exact hBc q hq) hlX hA ht1
    · exact qp_of_qps hPpre (hD i hi hng Lc c Rr hCL hDc (ρ.v c) X y1 hX hcv hlX hA) (ρ.v c) y1 hcv ht1 ht2
  · have h0 := hchg hvc
    rw [hcv] at h0
    simp only [psi.injEq] at h0
    rw [h0.2.1] at ht1
    exact absurd ht1 (T.not_lt_z _)

/-- **The `D` part of `VSmallF` of `N = M[n]`** at one matrix (`T0VSResD` for this `M`), from `T0DF`: a counted
child `c` whose `v` changes is the last counted child, has no counted child (`o = Ω_v`), and `v′(c) ◁ v(c)`
(`vs_changed_bound`). -/
theorem t0VSD_at {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hDF : T0DFH M ρ) :
    ∀ r L n σ rkN, T0Ctx M ρ rk r L n σ rkN →
    ∀ i (Lc : List Nat) c (R : List Nat), i < r → c < r → CL M i = Lc ++ c :: R → σ.v c ≠ ρ.v c →
      ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) := by
  intro r L n σ rkN hctx i Lc c R hi hc hCL hv
  obtain ⟨hM, hS, I, _, hlen, hL, hp, he1, _, hn2, hCN, hRN, hGN, _⟩ := id hctx
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := I.r12 _ he1
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hoff := chg_off hx I.cons I.good hC1 hRk1
  have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hvD := t0_vals hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp I.r0p I.z2 I.sd I.z1 I.uat I.uab) I.cons I.good hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hdv : DepX M (r + L) false c := by
    by_contra hd
    apply hv
    rw [(hvD c (by rw [hlN]; omega)).2 (fun h' => hd h'.2), tau_v_lt hc]
  have hcN : c < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hlv : Lhd z (σ.v c) (ρ.v c) := ((hDF r L hlen hL hp he1 n hn2 σ hCN c hc).2 hdv).2
  have hvcot : isOT (σ.v c) = true := hGN.ot_v c hcN
  have hiM : i < M.length := by omega
  have hcM : c < M.length := by omega
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcch : c ∈ children M i := cl_mem_children hcCL
  have hccnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
  have hclc : CL M c = [] := cl_nil_of_depv' hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2
    I.cons I.good hc hdv
  have hoM : ρ.o c = psi (ρ.v c) z z := o_of_no_counted I.cons hcM (I.good.ot_v c hcM) (no_cnt_of_cl_nil hclc)
  -- `c` is the last counted child of `i`
  have hDi : DepX M (r + L) true i := DepX.ochild hcch hccnt.1 hccnt.2 (DepX.ov hdv)
  have hR : R = [] := by
    rcases hOS_t1 hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp i (by omega) hDi with
      ⟨_, hall⟩ | ⟨_, Lp, c0, Rch, hch, _, _, hRch, hLnd⟩
    · exfalso
      rcases hall c hcch with h | h
      · exact hccnt.1 h
      · exact hccnt.2 h
    have hcc0 : c = c0 := by
      have hc' := hcch
      rw [hch] at hc'
      rcases List.mem_append.mp hc' with h | h
      · exact absurd (DepX.ov hdv) (hLnd c h hccnt)
      · rcases List.mem_cons.mp h with h | h
        · exact h
        · exfalso
          rcases hRch c h with h' | h'
          · exact hccnt.1 h'
          · exact hccnt.2 h'
    subst hcc0
    obtain ⟨hLs, _⟩ := sib_order (children_sorted M i) hch
    have hsCL : (CL M i).Pairwise (· < ·) := List.Pairwise.filter _ (children_sorted M i)
    rw [hCL] at hsCL
    obtain ⟨_, hcR⟩ := sib_order hsCL rfl
    rw [List.eq_nil_iff_forall_not_mem]
    intro d hd
    have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
    have hdch : d ∈ children M i := cl_mem_children hdCL
    have hdcnt : Counted M i d := by unfold CL at hdCL; simpa using (List.mem_filter.mp hdCL).2
    have hcd := hcR d hd
    rw [hch] at hdch
    rcases List.mem_append.mp hdch with h | h
    · have := hLs d h; omega
    · rcases List.mem_cons.mp h with h | h
      · omega
      · rcases hRch d h with h' | h'
        · exact hdcnt.1 h'
        · exact hdcnt.2 h'
  subst hR
  -- the old frame of `i`
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hiM
  have hsMc : ∀ d ∈ CL M i, Single (ρ.o d) := fun d hd => single_o I.cons I.good
    (mem_children (cl_mem_children hd)).2
  have hformM := o_last_form I.cons hiM (I.good.ot_v i hiM) hCL hsMc hpM hoM
  rw [hCL] at hsM hpM
  simp only [List.map_append, List.map_cons, List.map_nil] at hsM hpM
  have hpL := List.pairwise_append.mp hpM
  have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht)) hpL.1
  have hBc : ∀ q ∈ summands (spArg (ρ.v i) z (sumN (Lc.map ρ.o))), psi (ρ.v c) z z ≤ q := by
    apply spArg_summands_ge ⟨ρ.v c, z, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq
      have := hpL.2.2 q hq (ρ.o c) (by simp)
      rwa [hoM] at this
    · simp [summands]
  have hot := I.good.ot_o i hiM
  rw [hformM] at hot
  exact vs_changed_bound hvcot hlv hBc (I.vs i hiM Lc c [] hCL) hot

/-- **`VSmallF` of `N = M[n]`** (`t = 0`) at one matrix, from the `D` part `hD` (for this `M`) and `T0VSResG`. -/
theorem t0_vsmallF_at (hU0 : OldUpgAbs) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hD : ∀ r L n σ rkN, T0Ctx M ρ rk r L n σ rkN →
      ∀ i (Lc : List Nat) c (R : List Nat), i < r → c < r → CL M i = Lc ++ c :: R → σ.v c ≠ ρ.v c →
        ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)))
    (hIV : T0IVRes) :
    ∀ r L n σ rkN, T0Ctx M ρ rk r L n σ rkN → VSmallF (TRIO.gexp M r L 0 0 n) σ := by
  intro r L n σ rkN hctx
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
  have hVT : ValInv (M.take (r + L)) ρ' :=
    drop_pres hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩ hDr hC1 hRk1
  have hdrop := drop_all hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs hDr.vst
    I.fc I.fo hDr.argT
    (bump_drop hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td hDr.ab hDr.ws)
    hDr.ua
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
  have hFO := qvs_of_vsmallF I.cons I.good I.vs
  have hFOT := qvs_of_vsmallF hC1 hVT.g hVT.vs
  apply vsmallF_of_qvs hCN hGN
  apply frameQ_N_t0 hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hGN.toOT QVS
    (ρ' := ρ') hFO hFOT hσB hoffD
  · -- the frame of `g` with `r` counted
    intro g hg hgc
    have hgr : g < r := par_lt M 0 r g hg
    have hrg : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
    have hσvg : σ.v g = ρ.v g := by
      apply (hoffD g hgr).2
      intro hdv
      exact uncnt_of_depv (show r + L + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hp
        (by omega) hdv hrg hgc
    apply g_frames_t0J hlen hL hp hn I.r0p I.z2 I.sd I.z1 I.uat I.uab he1 hx2 hn2 I.cons I.good hCN hGN.toOT QVS
      hg hgc (fun c hc hd => (hoffD c hc).1 hd) hσvg hσmid hσlast
      (counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn2 hg hgc)
      (fun Lc c R hCL => hFO g (by omega) Lc c R hCL)
    intro Lc j cv hCL hcv s y hsy g' hg'
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
    have hold : ∀ g'' ∈ comps (ρ.v g) (ρ.v r), g'' ≤ psi (ρ.v r) z z ∨
        g'' ≤ spArg (ρ.v g) z (sumN (Lc.map ρ.o ++ List.replicate j (omid M r L ρ))) := by
      intro g'' hg''
      rcases I.vs g hgM Lc r [] hCL g'' hg'' with h | h
      · exact Or.inl h
      · exact Or.inr (le_trans h hmono)
    rcases hcv with rfl | ⟨rfl, hj0⟩
    · rw [hom] at hsy; simp only [psi.injEq] at hsy
      rw [← hsy.1] at hg' ⊢
      exact hold g' hg'
    · have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
      obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
      rw [hsy] at hy0; simp only [psi.injEq] at hy0
      have hv'ot := hVT.g.ot_v r hrT
      rw [sf_ot hv'ot] at hy0
      rw [hy0.1] at hg' ⊢
      by_cases hv : ρ'.v r = ρ.v r
      · rw [hv] at hg' ⊢; exact hold g' hg'
      -- the drop at `r`: `x` is a counted child of `r`, so `v′(r) ◁ v(r)`
      obtain ⟨hPO, hPV⟩ := hdrop r (by omega)
      have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
      have hxcnt : Counted M r (r + L) := by
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have h2 : entry M 2 (r + L) = (bump M r).2.2 := by
            show (col M (r + L)).2.2 = _; rw [h]
          rw [hx2] at h2; simp [bump] at h2
        · obtain ⟨hu, _⟩ := h
          unfold isUpg at hu
          obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hu
          have hk' : upg M k = some (r + L) := by simpa using hk
          obtain ⟨m, _, _, hcol, _⟩ := upg_spec hk'
          have := e2_of_col hcol
          rw [hx2] at this; omega
      have hlv : Lhd z (ρ'.v r) (ρ.v r) := by
        rcases hPV.1 with h | ⟨_, _, hno⟩
        · rcases h with h | h
          · exact absurd h hv
          · exact h
        · rcases hno with hno | ⟨_, _, k, W, hi2, hu, hvk, hWz, hbad⟩ | ⟨_, ⟨k, W, hi2, hu, hvk, hWz, hbad⟩, _⟩
          · exact absurd hxcnt (hno _ hxr)
          · exact absurd ((hU0 M (r + L) ρ) r k W (by omega) hu hvk hWz) hbad
          · exact absurd ((hU0 M (r + L) ρ) _ k W (by omega) hu hvk hWz) hbad
      -- a changed `v(r)`: `o′(r) = ψ_{v′(r)}(0)`
      have hyz : y = z := by
        have hCv : ChgX M (r + L) false r := by
          by_contra hn'; exact hv ((hoff r (by omega)).2 hn')
        have hT := (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hCv).1 rfl (by omega)
        have ho := o_of_no_counted hC1 hrT hv'ot hT.2.1
        rw [hsy, hy0.1] at ho; simp only [psi.injEq] at ho; exact ho.2.1
      obtain ⟨d, hd, hgd⟩ := hlv.2 (ρ.v g) (ρ.v r) hlv.1 (le_refl _) g' hg'
      rcases List.mem_append.mp hd with hd | hd
      swap
      · simp [Gc, comps] at hd
        rw [hd] at hgd
        exact Or.inr (le_trans hgd (z_le _))
      rcases I.vs g hgM Lc r [] hCL d hd with hdo | hdB
      swap
      · exact Or.inr (le_trans hgd (le_trans hdB hmono))
      set Bg := spArg (ρ.v g) z (sumN (Lc.map ρ.o)) with hBg
      by_cases hB0 : Bg = z ∧ j = 0
      · -- no middle copy root counts: the old frame does not rewrite at `r` (`T0IVRes`), and `o′(r) ◁ o(r)`
        obtain ⟨Y0, hY0⟩ : ∃ Y0, ρ.o r = psi (ρ.v r) (app Y0 one) z := ⟨_, hor⟩
        have hnt := hIV M ρ rk r L hM hS I R hlen hL hp he1 n hn2 g hg hgc (hj0 hB0.2) Lc hCL _ _ hY0
        have hsMc : ∀ d ∈ CL M g, Single (ρ.o d) := fun d hd => single_o I.cons I.good
          (mem_children (cl_mem_children hd)).2
        have hformM := o_last_form I.cons hgM (I.good.ot_v g hgM) hCL hsMc
          (by have := (cl_vals I.cons I.good hgM).2; exact this) hY0
        have hot := I.good.ot_o g hgM
        rw [hformM] at hot
        unfold step at hot
        rw [if_neg (by rw [← hBg, hB0.1]; rw [← hBg, hB0.1] at hnt; exact hnt)] at hot
        rw [← hBg, hB0.1] at hot
        have hot2 : isOT (psi (ρ.v g) (psi (ρ.v r) (app Y0 one) z) z) := hot
        rw [← hY0] at hot2
        have hl0 : LhdE (ρ'.o r) (ρ.o r) := by
          rcases PO.zero_t0 hx hDr.ua he1 hp (fun _ _ => hU0 _ _ _) I.cons I.good (by omega) hPO hPV hDr.ws.2.2 with h | ⟨_, w, hw⟩
          · exact h
          · rw [hY0] at hw; simp only [psi.injEq] at hw
            exact absurd hw.2.1 (fun h => by cases Y0 <;> simp [app, one] at h)
        have hot' := ot_parent_lhd hot2 (single_o hC1 hVT.g hrT).1 hl0
        rw [hsy, hy0.1, hyz] at hot'
        by_cases hsa : ρ'.v r < ρ.v g
        · rw [comps_nil_of_lt hv'ot hsa] at hg'; simp at hg'
        · left
          apply le_of_lt
          apply ((isOT_psi_iff).mp hot').2.2.2.2 g'
          rw [comps_psi_z_of_ge hsa]
          simp [hg']
      · -- the state of `N` is at least `Ω_{v(r)}`
        right
        refine le_trans hgd (le_trans hdo ?_)
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
        have hsd := sumN_dec _ hs hpw
        have hge : ∀ t ∈ Lc.map ρ.o ++ List.replicate j (omid M r L ρ), psi (ρ.v r) z z ≤ t := by
          intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · have := (List.pairwise_append.mp hpM).2.2 t ht (ρ.o r) (by simp)
            refine le_trans ?_ this
            rw [hor]; exact psi_le_psi_arg (z_le _)
          · rw [(List.mem_replicate.mp ht).2, hom]; exact psi_le_psi_arg (z_le _)
        have hne : Lc.map ρ.o ++ List.replicate j (omid M r L ρ) ≠ [] := by
          intro he
          apply hB0
          rw [List.append_eq_nil_iff, List.map_eq_nil_iff, List.replicate_eq_nil_iff] at he
          refine ⟨?_, he.2⟩
          rw [hBg, he.1]; rfl
        apply le_of_summands_ge
        · apply spArg_ne_z
          right
          intro hz
          have h1 := hsd.2
          rw [hz] at h1
          simp [summands] at h1
          exact hne (by simp [h1.1, h1.2])
        · apply spArg_summands_ge ⟨ρ.v r, z, rfl⟩ _ z hsd.1
          · rw [hsd.2]; exact hge
          · simp [summands]
  · -- the `D` frames before `r`
    intro i hi hng Lc c R hCL hDc s y hsy g' hg'
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
    have hcN : c < N.length := by rw [hlN]; omega
    have he := o_cl_eq hCN hGN hcN
    rw [hsy] at he; simp only [psi.injEq] at he
    rw [he.1] at hg' ⊢
    by_cases hv : σ.v c = ρ.v c
    · rw [hv] at hg' ⊢
      exact I.vs i (by omega) Lc c R hCL g' hg'
    · exact hD r L n σ rkN hctx i Lc c R hi hcr hCL hv g' hg'

/-- `T0Rest` without `VSmallF` (which now comes per matrix from `T0DF`). -/
structure T0RestNV : Prop where
  ad : T0Field AbsD
  au : T0Field AbsU
  tplo : T0Field TPLo
  auw : T0Field AbsUW
  tplon : T0Field TPLoN
  adn : T0Field AbsDN
  tplow : T0Field TPLoW
  adw : T0Field AbsDW

/-- **`hExp_t0` at one matrix** (the residuals `T0DF`, `T0RWResAt` for this `M`). -/
theorem hExp_t0A {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hOTD : T0DF M ρ)
    (hVSF : ∀ r L n σ rkN, T0Ctx M ρ rk r L n σ rkN → VSmallF (TRIO.gexp M r L 0 0 n) σ) (hRest : T0RestNV)
    (hR1 : T0RWResAt PTP1 M ρ rk) (hR1W : T0RWResAt PTP1W M ρ rk) (hRT : T0RWResAt PTrig M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (hs0 : TRIO.srow M (M.length - 1) = 0)
    (hT : ∀ j, j < M.length → M.take j ≠ SRO → M.take j ≠ [] →
      ∃ τ rkT, Inv3 (M.take j) τ rkT ∧ Res3A (M.take j) τ rkT)
    (n : Nat) (hn2 : 2 ≤ n) :
    ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  obtain ⟨r, L, hlen, hL, hp, he1, hexp⟩ := t0_shape I hz hs0
  rw [hexp n]
  have hDr := R.drop
  rw [show M.length - 1 = r + L by omega] at hDr
  have hab0 := R.abS.lo r (by rw [show M.length - 1 = r + L by omega]; exact hp)
    (by rw [show M.length - 1 = r + L by omega]; exact he1)
  have hcore := t0_core hlen hL I.r0p I.z2 I.sd I.z1 I.uat I.uab (sInvXJ_std hM hS).2 (sInvXJ_std hM hS).1.loc.2.2.2 I.r12 I.be I.r01 I.e00 hp he1 I.cons I.good
    I.rank I.vs I.fc I.fo hDr.argT I.kd I.td hDr.ab (T0AbsW.of_strong hab0) hDr.ws hDr.vst hDr.ua I.rootS I.rootP
    (fun n hn g hg hc => counted_last0 hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uab I.r12 hn hg hc)
    (fun n hn σ hCN => ⟨fun i hi hd => ((hOTD r L hlen hL hp he1 n hn σ hCN i hi).1 hd).1,
      t0_vsmallNewN hlen hL hp he1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.cons I.good I.rank hn hCN⟩)
    n hn2
  obtain ⟨σ, rkN, hCN, hRN, hGN, hFON, hFCN, hKDN, hTDN, hRWN, hpN, _⟩ := hcore
  -- the prefix `M.take x`
  have hTx : ∃ τ rkT, Inv3 (M.take (r + L)) τ rkT ∧ Res3A (M.take (r + L)) τ rkT := by
    apply hT (r + L) (by omega)
    · intro h
      have hRk1 : Rk (M.take (r + L)) rk :=
        rk_take (by omega) I.rank (by
          have := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
          rwa [show M.length - 1 = r + L by omega] at this)
      rw [h] at hRk1; exact not_val_SRO _ (val_of_rk hRk1)
    · intro h
      have := congrArg List.length h
      rw [List.length_take, Nat.min_eq_left (by omega)] at this
      simp only [List.length_nil] at this; omega
  have hctx : T0Ctx M ρ rk r L n σ rkN :=
    ⟨hM, hS, I, R, hlen, hL, hp, he1, hTx, hn2, hCN, hRN, hGN, hFON, hFCN, hKDN, hTDN⟩
  have hvs := hVSF r L n σ rkN hctx
  have had := hRest.ad _ _ _ _ _ _ _ _ hctx
  have hau := hRest.au _ _ _ _ _ _ _ _ hctx
  have htplo := hRest.tplo _ _ _ _ _ _ _ _ hctx
  have hauw := hRest.auw _ _ _ _ _ _ _ _ hctx
  have htplon := hRest.tplon _ _ _ _ _ _ _ _ hctx
  have hadn := hRest.adn _ _ _ _ _ _ _ _ hctx
  have htplow := hRest.tplow _ _ _ _ _ _ _ _ hctx
  have hadw := hRest.adw _ _ _ _ _ _ _ _ hctx
  -- the rewriting-frame fields, with the prefix valuation `drop1`
  have hRk1 : Rk (M.take (r + L)) rk :=
    rk_take (by omega) I.rank (by
      have := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
      rwa [show M.length - 1 = r + L by omega] at this)
  obtain ⟨τ, rkT, IT, _⟩ := hTx
  have hAg : ∀ i, i < (M.take (r + L)).length →
      τ.o i = (drop1 M (r + L) rk).o i ∧ τ.v i = (drop1 M (r + L) rk).v i :=
    agree_of_cons IT.cons (cons_of_rk hRk1) IT.rank
  have hP : ∀ P, RWC P M ρ → RWC P (M.take (r + L)) τ → T0RWResAt P M ρ rk → RWC P (TRIO.gexp M r L 0 0 n) σ := by
    intro P hPM hPT hres
    obtain ⟨hD, hG0⟩ := hres r L n hM hS I R hlen hL hp he1 hn2 σ hCN hGN
    exact hRWN P hPM (rwc_congr hPT hAg) hD hG0
  have htp1 : TP1C (TRIO.gexp M r L 0 0 n) σ := hP PTP1 I.tp1 IT.tp1 hR1
  have htp1w : TP1WC (TRIO.gexp M r L 0 0 n) σ := hP PTP1W I.tp1w IT.tp1w hR1W
  have htrig : TrigOmC (TRIO.gexp M r L 0 0 n) σ :=
    rwc_trig.mp (hP PTrig (rwc_trig.mpr I.trig) (rwc_trig.mpr IT.trig) hRT)
  have V : Inv3V (TRIO.gexp M r L 0 0 n) σ rkN := ⟨hCN, hGN, hRN, hvs, hFCN, hFON, hKDN, hTDN, had, hau, htp1,
    htplo, htp1w, htplow, hauw, hadw, htrig, htplon, hadn, rootS_of_good hCN hGN, hpN⟩
  exact ⟨σ, rkN, V⟩

/-- **`hExp` for `t = 0` in the `RClaim` scheme** (`VSmallR M ρ` given, as carried by main_GP). Residuals:
PH3c of `M` and `T0CutResG` (the `D` frames; `T0IVRes` is proved, V3T0IV), `T0RestV`・`FrmLF`・`hNG` (value fields), and the
shadow frames `T0RWResCR`. No class residual (`T0IIRes`, `T0ShapeR3`). -/
theorem hExp_t0_topR (hU0 : OldUpgAbs)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hNG : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → NoGapP M ρ) (hFrm : FrmLF)
    (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3c M ρ)
    (hCut : T0CutResG) (hRest : T0RestV) (hC1 : T0RWResCR PTP1) (hC1W : T0RWResCR PTP1W) (hCT : T0RWResCR PTrig) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hVR hz hs0 n hn2
  have hIV := t0IVRes_holds
  have f : ∀ F, T0Field F → T0FieldG F := fun _ h M ρ rk r L n σ rkN hctx _ => h M ρ rk r L n σ rkN hctx
  have g : ∀ F, T0FieldG F → T0Field F := fun F h M ρ rk r L n σ rkN hctx =>
    h M ρ rk r L n σ rkN hctx (hNG M ρ rk hctx.1 hctx.2.1 hctx.2.2.1 hctx.2.2.2.1)
  have hFF := t0_frameFields hFrm (t0_absD hRest.phi) (f _ (t0_tplo hRest.tploR))
  have H2 : T0RestNV := ⟨g _ (t0_absD hRest.phi), g _ (t0_absU hRest.phi), g _ (f _ (t0_tplo hRest.tploR)),
    g _ (f _ (t0_absUW hRest.auwR)), g _ hFF.2.2, g _ (f _ (t0_absDN hRest.adnR)), g _ hFF.1, g _ hFF.2.1⟩
  have hDF := (t0DF_of hU0) hPH hCut hIV hM hS I R hVR
  apply hExp_t0A hDF ((t0_vsmallF_at hU0) (t0VSD_at hDF.toH) hIV) H2
    (t0RWResAt_of PTP1 (fun _ _ _ _ _ hc hBc hl hA ht => ptp1_classA hc hBc hl hA ht)
      (fun _ _ _ _ hlt hpre => ptp1_prefix hlt hpre) hC1 hDF)
    (t0RWResAt_of PTP1W (fun _ _ _ _ _ hc hBc hl hA ht => ptp1w_classA hc hBc hl hA ht)
      (fun _ _ _ _ hlt hpre => ptp1w_prefix hlt hpre) hC1W hDF)
    (t0RWResAt_of PTrig (fun _ _ _ _ _ hc hBc hl hA ht => ptrig_classA hc hBc hl hA ht)
      (fun _ _ _ _ hlt hpre => ptrig_prefix hlt hpre) hCT hDF)
    hM hS I R hz hs0 _ n hn2
  intro j hj hjS hjE
  obtain ⟨τ, rkT, V, R'⟩ := hTake_of_last hLast M ρ rk hM hS hE I R j hj hjS hjE
  exact ⟨τ, rkT, Inv3.ofV (sInv_std (std_take hM j (by omega)) hjS) V, R'⟩

/-- **`hVSRexp` for `t = 0` in the `RClaim` scheme.** -/
theorem hVSRexp_t0_topR (hU0 : OldUpgAbs)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3c M ρ)
    (hCut : T0CutResG) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
      ∀ n, 2 ≤ n → ∀ ρN rkN, Inv3V (expand M n) ρN rkN → VSmallR (expand M n) ρN := by
  intro M ρ rk hM hSRO hE I R hVR hz hs0 n hn2 ρN rkN V
  have hIV := t0IVRes_holds
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
  exact (t0_vsmallR_DF hU0) M ρ rk r L n ρN rkN
    ⟨hM, hSRO, I, R, hlen, hL, hp, he1, hTx, hn2, V.cons, V.rank, V.good, V.fo, V.fc, V.kd, V.td⟩ hVR
    ((t0DF_of hU0) hPH hCut hIV hM hSRO I R hVR)

end Ytosk
