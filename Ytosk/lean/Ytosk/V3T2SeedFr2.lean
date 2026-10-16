/-
**t = 2 の種の列の枠の VSmallF・FrameOT・FrameClosed（sv・C、2026-10-17、t2）。**

closure の `seed_frames_sv`・`seed_frames_C` と同じ枠のデータを使う。r の最後の枠は状態 X₁（M.take x での r の
引数）、子は ψ_{V′}(σ^{n−1} X₁)（sv では V′ = V + 1、C では V′ = s′）。前の枠は M.take x の枠。
- FrameClosed: PH3cG の種類（closure の `seed_kind`）から `frameDom_of_kind`。添字 V′ の成分は、sv では z か V の
  成分（自明）、C では名前つきの残り `T2SeedCDom`。C で X₁ = 0 のときは子が ψ_{s′}(Ω_{s′}) で `frameDom_first`。
- C の q の枠は qn と同じ（子の添字 = v_N(q)）。
-/
import Ytosk.V3T2CutDom

namespace Ytosk.G

open T

set_option linter.unusedSectionVars false

/-- **The residual of the C seed frames**: the components of `s′ = v_N(q)`. With `X₁ ≠ 0` at the levels `u ≤ V`
they are `0`, below `X₁` or components of `V`; at the level `V` they are below `Ω_{s′}` or `X₁`
（実測: 9 集合で例外 0）. -/
def T2SeedCDom (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ →
    (t2X1 M r L τ ≠ z → ∀ u, ¬ lt (ρ.v r) u = true → ∀ g ∈ comps u (qnS M ρ r L q),
      g = z ∨ g ≤ t2X1 M r L τ ∨ ∃ d ∈ comps u (ρ.v r), g ≤ d) ∧
    ∀ g ∈ comps (ρ.v r) (qnS M ρ r L q), g ≤ psi (qnS M ρ r L q) z z ∨ g ≤ t2X1 M r L τ

/-! ## sv -/

open Classical in
/-- **The seed frames of `r` in `M[n]`** (sv) for `QVSF`, `QFO` and `QFCo`. -/
theorem seed_frames_sv3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (hRes : T2SeedSVRes M ρ r L) (hFix : T2SeedSVFix M ρ r L)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : Rk (M.take (r + L)) rk0)
    (hTV : VSmallF (M.take (r + L)) τ0) (hTO : FrameOT (M.take (r + L)) τ0)
    (hTC : FrameClosed (M.take (r + L)) τ0) :
    SeedFr QVSF M r L r ∧ SeedFr QFO M r L r ∧ SeedFr QFCo M r L r := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set V := ρ.v r with hVdef
  set X1 := t2X1 M r L τ0 with hX1def
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hRk : ∀ m, 1 ≤ m → ∃ rk', Rk (TRIO.gexp M r L d0 d1 m) rk' := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hVot : isOT V = true := I.good.ot_v r hrM
  have hV' : isOT (succ V) = true := isOT_succ hVot
  have hVV : V < succ V := lt_succ_self V
  have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hrT : r < (M.take (r + L)).length := by omega
  have hvP : τ0.v r = V := v_take_of_untopped I hlen (par_lt M 0 _ _ hq) (topP_sv hlen I.z2 I.z1 hr hq hux) hC0
  have hX1e : X1 = spArg V z (sumN ((CL (M.take (r + L)) r).map τ0.o)) := by
    rw [hX1def]; unfold t2X1; rw [hvP]
  have hBhi := hFix.hi τ0 hC0
  have hFx := hFix.fix τ0 hC0
  -- the common data of the last frame
  have key : ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L d0 d1 m) τ → Good3 (TRIO.gexp M r L d0 d1 m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L d0 d1 n) σ → Good3 (TRIO.gexp M r L d0 d1 n) σ →
      Good3 (M.take (r + L)) τ0 ∧ isOT X1 = true ∧
      σ.o (r + L) = psi (succ V) (sh V (succ V) (shIt V (succ V) X1 (n - 2))) z ∧
      CL (TRIO.gexp M r L d0 d1 n) r = CL (M.take (r + L)) r ++ [r + L] ∧ σ.v r = τ0.v r ∧
      (∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d) ∧ SeedExt (succ V) X1 (shIt V (succ V) X1 (n - 2)) := by
    intro n hn hGlow σ hCN _
    have hG0 : Good3 (M.take (r + L)) τ0 := by
      have := hGlow 1 (le_refl 1) (by omega) τ0 (by rw [hP1]; exact hC0)
      rw [hP1] at this; exact this
    have hX1ot : isOT X1 = true := by
      have := hG0.ot_o r hrT
      rw [o_cl_eq hC0 hG0 hrT] at this
      rw [hX1def]; exact isOT_arg this
    obtain ⟨rkN, hRN⟩ := hRk n (by omega)
    obtain ⟨hox, hCLN, hvr, hval⟩ : σ.o (r + L) = psi (succ V) (sh V (succ V) (shIt V (succ V) X1 (n - 2))) z ∧
        CL (TRIO.gexp M r L d0 d1 n) r = CL (M.take (r + L)) r ++ [r + L] ∧ σ.v r = τ0.v r ∧
        ∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d := by
      rcases Nat.lt_or_ge n 3 with hn3 | hn3
      · have hn2 : n = 2 := by omega
        subst hn2
        have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hC0
        have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := hGlow 1 (le_refl 1) (by omega) τ0 hCP
        have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hR0
        obtain ⟨hCLN, hvr, hval, hox⟩ :=
          seed_frame_data_sv hM hS I R hz h2 hlen hr hq hux (topP_sv hlen I.z2 I.z1 hr hq hux) (le_refl 2) hCN hRN hCP hGP hRP hC0 hG0 hR0
        rw [← hd0def, ← hd1def] at hCLN hox
        rw [show (2 - 1 : Nat) = 1 from rfl, hP1, hvP, ← hX1e] at hox
        exact ⟨hox, hCLN, hvr, hval⟩
      · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
        have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
        have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
        obtain ⟨hCLN, hvr, hval, hox⟩ :=
          seed_frame_data_sv hM hS I R hz h2 hlen hr hq hux (topP_sv hlen I.z2 I.z1 hr hq hux) hn hCN hRN hCP hGP hRP hC0 hG0 hR0
        rw [← hd0def, ← hd1def] at hCLN hox
        have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
        have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
          have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
          omega
        have hval' := seed_r_value_sv hM hS I R hz h2 hlen hr hq hux hRes hC0 hR0 (n - 1) (by omega)
          (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP (cl_vals hCP hGP hrP).2
        have hform := o_cl_eq hCP hGP hrP
        rw [hval'] at hform
        simp only [psi.injEq] at hform
        have h21 := hform.2.1
        rw [← hform.1] at h21
        rw [← hform.1, ← h21, show n - 1 - 1 = n - 2 by omega] at hox
        exact ⟨hox, hCLN, hvr, hval⟩
    have hOT : ∀ j, j + 1 < n → isOT (psi V (shIt V (succ V) X1 j) z) = true := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have := hG0.ot_o r hrT
        rw [o_cl_eq hC0 hG0 hrT] at this
        show isOT (psi V X1 z) = true
        rw [hX1e]; rw [hvP] at this; exact this
      · obtain ⟨rkj, hRj⟩ := hRk (j + 1) (by omega)
        have hCj : Cons (TRIO.gexp M r L d0 d1 (j + 1)) (rhsIt _ (rkBound _ rkj)) := cons_of_rk hRj
        have hGj := hGlow (j + 1) (by omega) hj _ hCj
        have hlj : (TRIO.gexp M r L d0 d1 (j + 1)).length = r + (j + 1) * L := TRIO.gexp_length hlen
        have hrj : r < (TRIO.gexp M r L d0 d1 (j + 1)).length := by
          have : L ≤ (j + 1) * L := Nat.le_mul_of_pos_left L (by omega)
          omega
        have hv := seed_r_value_sv hM hS I R hz h2 hlen hr hq hux hRes hC0 hR0 (j + 1) (by omega)
          (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCj (cl_vals hCj hGj hrj).2
        have := hGj.ot_o r hrj
        rw [hv, show j + 1 - 1 = j by omega] at this
        exact this
    have hE : ∀ k, k + 1 < n → SeedExt (succ V) X1 (shIt V (succ V) X1 k) := by
      intro k
      induction k with
      | zero => intro _; exact Or.inl rfl
      | succ k ih =>
        intro hk
        have hcv : isOT (psi (succ V) (sh V (succ V) (shIt V (succ V) X1 k)) z) = true := by
          have := isOT_shTop (V' := succ V) hVot hV' hVV (hOT k (by omega)) (le_refl _)
          rwa [shf_self] at this
        have h := seed_ext (a := V) hVot hV' hVV hX1ot (isOT_shIt hVot hV' hVV hX1ot k) hBhi hFx (ih (by omega)) hcv
        rw [hRes.rw τ0 hC0 k] at h
        exact h
    exact ⟨hG0, hX1ot, hox, hCLN, hvr, hval, hE (n - 2) (by omega)⟩
  refine ⟨fun n hn hGlow σ hCN hGN => ?_, fun n hn hGlow σ hCN hGN => ?_, fun n hn hGlow σ hCN hGN => ?_⟩
  all_goals obtain ⟨hG0, hX1ot, hox, hCLN, hvr, hval, hEn⟩ := key n hn hGlow σ hCN hGN
  · refine seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr hval
      (fun Lc' c R' h => clField_of_vsmallF hC0 hG0 hTV r hrT Lc' c R' h) ?_
    rw [hox, hvP]
    intro s y hsy g hg
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, -⟩ := hsy
    left; rw [comps_succ_self hVot g hg]; exact z_le _
  · refine seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr hval
      (fun Lc' c R' h => hTO r hrT Lc' c R' h) ?_
    show isOT (psi (τ0.v r) (spArg (τ0.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o))) z) = true
    rw [← o_cl_eq hC0 hG0 hrT]; exact hG0.ot_o r hrT
  · have hxN : r + L < (TRIO.gexp M r L d0 d1 n).length := by
      rw [TRIO.gexp_length hlen]
      have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
      omega
    refine seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr hval
      (fun Lc' c R' h => clField_QFCo hG0 hTC r hrT Lc' c R' h) ⟨hGN.ot_o _ hxN, ?_⟩
    have hot := hGN.ot_o _ hxN
    rw [hox] at hot ⊢
    intro s y hsy ht
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, rfl, -⟩ := hsy
    have hst : spArg (τ0.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o)) = X1 := rfl
    rw [hst] at ht ⊢
    rw [hvP] at ht ⊢
    refine frameDom_of_kind hot
      (seed_kind hVot hV' hVV hX1ot (isOT_shIt hVot hV' hVV hX1ot (n - 2)) hBhi hFx hEn ht.1) ?_
    intro u hu g hg
    rcases comps_succ_sub u g hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨g, h, le_refl _⟩))

/-! ## C -/

open Classical in
/-- **The data of the last frames of the seeds `r` and `q` in `M[n]`** (C), from closure's `C_frame`. -/
theorem seed_last_C {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hRes : T2SeedCRes M ρ r L q) (hFix : T2SeedCFix M ρ r L q)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : Rk (M.take (r + L)) rk0) :
    ∀ n, 2 ≤ n →
    (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) m) τ) →
    ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
    Good3 (M.take (r + L)) τ0 ∧ isOT (t2X1 M r L τ0) = true ∧
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = CL (M.take (r + L)) r ++ [q] ∧
    (∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d) ∧ σ.v r = (ρ.v r) ∧ σ.v (r + L) = (qnS M ρ r L q) ∧ σ.v q = (qnS M ρ r L q) ∧
    σ.o q = psi (qnS M ρ r L q) (step (qnS M ρ r L q) z (qnS M ρ r L q) (sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ0) (n - 2))) z) z ∧
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) q = [r + L] ∧
    ((t2X1 M r L τ0) ≠ z → step (qnS M ρ r L q) z (qnS M ρ r L q) (sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ0) (n - 2))) z = sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ0) (n - 2)) ∧
      SeedExt (qnS M ρ r L q) (t2X1 M r L τ0) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ0) (n - 2))) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set V := ρ.v r with hVdef
  set s' := qnS M ρ r L q with hs'def
  set X1 := t2X1 M r L τ0 with hX1def
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hRk : ∀ m, 1 ≤ m → ∃ rk', Rk (TRIO.gexp M r L d0 d1 m) rk' := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hVot : isOT V = true := I.good.ot_v r hrM
  have hs'ot : isOT s' = true := qnS_ot I hrM L q
  have hVs' : V < s' := qnS_gt M ρ r L q
  have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hrT : r < (M.take (r + L)).length := by omega
  have hv0 : τ0.v r = V := v_take_of_untopped I hlen (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hC0
  have hX1e : X1 = spArg V z (sumN ((CL (M.take (r + L)) r).map τ0.o)) := by
    rw [hX1def]; unfold t2X1; rw [hv0]
  have hBhi := hFix.hi τ0 hC0
  have hFx := hFix.fix τ0 hC0
  intro n hn hGlow σ hCN _
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  have hG0 : Good3 (M.take (r + L)) τ0 := by
    have := hGlow 1 (le_refl 1) (by omega) τ0 (by rw [hP1]; exact hC0)
    rw [hP1] at this; exact this
  have hX1ot : isOT X1 = true := by
    have := hG0.ot_o r hrT
    rw [o_cl_eq hC0 hG0 hrT] at this
    rw [hX1def]; exact isOT_arg this
  have hvq : σ.v q = s' := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  have hvq0 : τ0.v q = σ.v q := by rw [hvq]; exact hRes.vqP τ0 hC0
  have hdata : CL (TRIO.gexp M r L d0 d1 n) r = CL (M.take (r + L)) r ++ [q] ∧
      (∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d) ∧ σ.v r = V ∧ σ.v (r + L) = s' ∧
      σ.o q = psi s' (step s' z s' (sh V s' (shIt V s' X1 (n - 2))) z) z ∧
      CL (TRIO.gexp M r L d0 d1 n) q = [r + L] := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn2 : n = 2 := by omega
      subst hn2
      have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hC0
      have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := hGlow 1 (le_refl 1) (by omega) τ0 hCP
      have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hR0
      obtain ⟨hCLN, hval, hvr, hvx, hoq, hCLNq⟩ := C_frame hM hS I R hz h2 hlen hr hq hqr (qP_C hM hS I hlen hr hq hqr hncl hRes.un) hRes.un
        (le_refl 2) hCN hRN hCP hGP hRP hC0 hG0 hR0 hv0 hvq0
      rw [← hd0def, ← hd1def] at hCLN hoq hCLNq
      rw [hvq, qnS_vxs] at hvx
      rw [show (2 - 1 : Nat) = 1 from rfl, hP1, hv0, hvq, hvx, ← hX1e] at hoq
      exact ⟨hCLN, hval, hvr, hvx, hoq, hCLNq⟩
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      obtain ⟨hCLN, hval, hvr, hvx, hoq, hCLNq⟩ := C_frame hM hS I R hz h2 hlen hr hq hqr (qP_C hM hS I hlen hr hq hqr hncl hRes.un) hRes.un
        hn hCN hRN hCP hGP hRP hC0 hG0 hR0 hv0 hvq0
      rw [← hd0def, ← hd1def] at hCLN hoq hCLNq
      have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
      have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hqP : q < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hval' := seed_r_value_C hM hS I R hz h2 hlen hr hq hqr hncl hRes hC0 hR0 (n - 1) (by omega)
        (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP (hGP.ot_o q hqP) (cl_vals hCP hGP hrP).2
      have hform := o_cl_eq hCP hGP hrP
      rw [hval'] at hform
      simp only [psi.injEq] at hform
      have h21 := hform.2.1
      rw [← hform.1] at h21
      rw [hvq, qnS_vxs] at hvx
      rw [← hform.1, ← h21, show n - 1 - 1 = n - 2 by omega, hvq, hvx] at hoq
      exact ⟨hCLN, hval, hvr, hvx, hoq, hCLNq⟩
  obtain ⟨hCLN, hval, hvr, hvx, hoq, hCLNq⟩ := hdata
  have hOT : ∀ j, j + 1 < n → isOT (psi V (shIt V s' X1 j) z) = true := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have := hG0.ot_o r hrT
      rw [o_cl_eq hC0 hG0 hrT] at this
      show isOT (psi V X1 z) = true
      rw [hX1e]; rw [hv0] at this; exact this
    · obtain ⟨rkj, hRj⟩ := hRk (j + 1) (by omega)
      have hCj : Cons (TRIO.gexp M r L d0 d1 (j + 1)) (rhsIt _ (rkBound _ rkj)) := cons_of_rk hRj
      have hGj := hGlow (j + 1) (by omega) hj _ hCj
      have hlj : (TRIO.gexp M r L d0 d1 (j + 1)).length = r + (j + 1) * L := TRIO.gexp_length hlen
      have hrj : r < (TRIO.gexp M r L d0 d1 (j + 1)).length := by
        have : L ≤ (j + 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hqj : q < (TRIO.gexp M r L d0 d1 (j + 1)).length := by
        have : L ≤ (j + 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hv := seed_r_value_C hM hS I R hz h2 hlen hr hq hqr hncl hRes hC0 hR0 (j + 1) (by omega)
        (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCj (hGj.ot_o q hqj) (cl_vals hCj hGj hrj).2
      have := hGj.ot_o r hrj
      rw [hv, show j + 1 - 1 = j by omega] at this
      exact this
  have hinner : ∀ k, k + 1 < n → X1 ≠ z → SeedExt s' X1 (shIt V s' X1 k) →
      step s' z s' (sh V s' (shIt V s' X1 k)) z = sh V s' (shIt V s' X1 k) := by
    intro k hk hX0 hEk
    have hYot := isOT_shIt hVot hs'ot hVs' hX1ot k
    have hall := allGe_sh hVot hs'ot hVs' hYot (seedExt_allGe hVot hs'ot hVs' hBhi hEk)
    have hYne : shIt V s' X1 k ≠ z := by
      rcases hEk with h | ⟨R0, _, _, h⟩ | ⟨hc3, _, _⟩
      · rw [h]; exact hX0
      · rw [h]; intro h'; cases hB : X1 with
        | z => exact hX0 hB
        | psi _ _ _ => rw [hB] at h'; simp at h'
      · intro h'
        rw [h'] at hc3
        have : (split z (psi (succ s') z z)).1 = z := rfl
        rw [this] at hc3
        simp [cutsNSG] at hc3
    have hne := sh_ne_z (V := V) (V' := s') hYne
    have hzlt : z < sh V s' (shIt V s' X1 k) := by
      cases h : sh V s' (shIt V s' X1 k) with
      | z => exact absurd h hne
      | psi _ _ _ => exact T.z_lt_psi _ _ _
    unfold step
    rw [if_pos ⟨hzlt, psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hzlt⟩)⟩]
    exact H_of_high hs'ot hall
  have hE : X1 ≠ z → ∀ k, k + 1 < n → SeedExt s' X1 (shIt V s' X1 k) := by
    intro hX0 k
    induction k with
    | zero => intro _; exact Or.inl rfl
    | succ k ih =>
      intro hk
      have hEk := ih (by omega)
      have hcv : isOT (psi s' (sh V s' (shIt V s' X1 k)) z) = true := by
        have := isOT_shTop (V' := s') hVot hs'ot hVs' (hOT k (by omega)) (le_refl _)
        rwa [shf_self] at this
      have h := seed_ext (a := V) hVot hs'ot hVs' hX1ot (isOT_shIt hVot hs'ot hVs' hX1ot k) hBhi hFx hEk hcv
      have hrw := hRes.rw τ0 hC0 k
      rw [hinner k (by omega) hX0 hEk] at hrw
      rw [hrw] at h
      exact h
  exact ⟨hG0, hX1ot, hCLN, hval, hvr, hvx, hvq, hoq, hCLNq,
    fun hX0 => ⟨hinner (n - 2) (by omega) hX0 (hE hX0 (n - 2) (by omega)), hE hX0 (n - 2) (by omega)⟩⟩

open Classical in
/-- **The seed frames of `r` and `q` in `M[n]`** (C) for `QVSF`, `QFO` and `QFCo`. -/
theorem seed_frames_C3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hRes : T2SeedCRes M ρ r L q) (hFix : T2SeedCFix M ρ r L q) (hDom : T2SeedCDom M ρ r L q)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : Rk (M.take (r + L)) rk0)
    (hTV : VSmallF (M.take (r + L)) τ0) (hTO : FrameOT (M.take (r + L)) τ0)
    (hTC : FrameClosed (M.take (r + L)) τ0) :
    ∀ i, (i = r ∨ i = q) → SeedFr QVSF M r L i ∧ SeedFr QFO M r L i ∧ SeedFr QFCo M r L i := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set V := ρ.v r with hVdef
  set s' := qnS M ρ r L q with hs'def
  set X1 := t2X1 M r L τ0 with hX1def
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L d0 d1 m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hRk : ∀ m, 1 ≤ m → ∃ rk', Rk (TRIO.gexp M r L d0 d1 m) rk' := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hVot : isOT V = true := I.good.ot_v r hrM
  have hs'ot : isOT s' = true := qnS_ot I hrM L q
  have hVs' : V < s' := qnS_gt M ρ r L q
  have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hrT : r < (M.take (r + L)).length := by omega
  have hv0 : τ0.v r = V := v_take_of_untopped I hlen (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hC0
  have hX1e : X1 = spArg V z (sumN ((CL (M.take (r + L)) r).map τ0.o)) := by
    rw [hX1def]; unfold t2X1; rw [hv0]
  have hBhi := hFix.hi τ0 hC0
  have hFx := hFix.fix τ0 hC0
  have key := fun n hn hGlow σ hCN hGN => seed_last_C hM hS I R hz h2 hlen hr hq hqr hncl hRes hFix hC0 hR0 n hn hGlow σ hCN hGN
  intro i hi
  refine ⟨fun n hn hGlow σ hCN hGN => ?_, fun n hn hGlow σ hCN hGN => ?_, fun n hn hGlow σ hCN hGN => ?_⟩
  all_goals
    obtain ⟨hG0, hX1ot, hCLN, hval, hvr, hvx, hvq, hoq, hCLNq, hX1n⟩ := key n hn hGlow σ hCN hGN
    have hxN : r + L < (TRIO.gexp M r L d0 d1 n).length := by
      rw [TRIO.gexp_length hlen]
      have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
      omega
    have hqN : q < (TRIO.gexp M r L d0 d1 n).length := by omega
    obtain ⟨y0, hy0⟩ := o_psi_sub hCN hxN
    rw [sf_ot (hGN.ot_v _ hxN), hvx] at hy0
    have hvr' : σ.v r = τ0.v r := by rw [hvr, hv0]
    have hfrq : ∀ {Q : T → List T → T → Prop}, Q (σ.v q) [] (σ.o (r + L)) →
        ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat),
          CL (TRIO.gexp M r L d0 d1 n) q = Lc' ++ c :: R' → Q (σ.v q) (Lc'.map σ.o) (σ.o c) := by
      intro Q h Lc' c R' hCL
      rw [hCLNq] at hCL
      rcases Lc' with _ | ⟨a, l⟩
      · simp at hCL; rw [← hCL.1]; exact h
      · simp at hCL
    rcases hi with hi | hi <;> subst i
  · -- VSmallF, the frames of `r`
    refine seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr' hval
      (fun Lc' c R' h => clField_of_vsmallF hC0 hG0 hTV r hrT Lc' c R' h) ?_
    rw [hoq, hv0]
    intro s y hsy g hg
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, -⟩ := hsy
    rw [← hX1e]; exact (hDom τ0 hC0).2 g hg
  · -- VSmallF, the frame of `q`
    refine hfrq ?_
    rw [hy0, hvq]
    intro s y hsy g hg
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, -⟩ := hsy
    rw [comps_eq_nil_of_lev (fun q hq => lev_lt_of_summand hs'ot hq)] at hg; simp at hg
  · -- FrameOT, the frames of `r`
    refine seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr' hval
      (fun Lc' c R' h => hTO r hrT Lc' c R' h) ?_
    show isOT (psi (τ0.v r) (spArg (τ0.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o))) z) = true
    rw [← o_cl_eq hC0 hG0 hrT]; exact hG0.ot_o r hrT
  · -- FrameOT, the frame of `q`
    refine hfrq ?_
    show isOT (psi (σ.v q) (spArg (σ.v q) z (sumN ([] : List T))) z) = true
    rw [spArg_nil, hvq]
    exact isOT_psi_zz hs'ot
  · -- FrameClosed, the frames of `r`
    refine seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr' hval
      (fun Lc' c R' h => clField_QFCo hG0 hTC r hrT Lc' c R' h) ⟨hGN.ot_o q hqN, ?_⟩
    have hot := hGN.ot_o q hqN
    rw [hoq] at hot ⊢
    intro s y hsy ht
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, rfl, -⟩ := hsy
    have hst : spArg (τ0.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o)) = X1 := rfl
    rw [hst] at ht ⊢
    rw [hv0] at ht ⊢
    by_cases hX0 : X1 = z
    · -- the child is `ψ_{s′}(Ω_{s′})`
      have hstep : step s' z s' (sh V s' (shIt V s' X1 (n - 2))) z = psi s' z z := by
        rw [hX0, shIt_z, sh_z]; unfold step; rw [if_neg (by simp [lt])]; rfl
      rw [hstep] at hot ⊢
      rw [hX0]
      have hsp : split (psi s' z z) (psi (succ s') z z) = (z, psi s' z z) := by
        simp only [split]
        rw [if_pos (show lt (psi s' z z) (psi (succ s') z z) = true from
          psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self _)))]
      have hH : H s' (psi s' z z) = psi s' (psi s' z z) z := by
        rw [H_eq hot, hsp]; simp [hs'def]
      rw [hH]
      exact frameDom_first (le_of_lt hVs') (X := z) (by rw [lev_psi, app_z_right])
    · obtain ⟨hin, hEn⟩ := hX1n hX0
      rw [hin] at hot ⊢
      rw [hin] at ht
      refine frameDom_of_kind hot
        (seed_kind hVot hs'ot hVs' hX1ot (isOT_shIt hVot hs'ot hVs' hX1ot (n - 2)) hBhi hFx hEn ht.1) ?_
      intro u hu g hg
      rcases (hDom τ0 hC0).1 hX0 u hu g hg with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
  · -- FrameClosed, the frame of `q`
    refine hfrq ⟨hGN.ot_o _ hxN, ?_⟩
    rw [hy0, hvq]
    intro s y hsy _
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, -⟩ := hsy
    exact frameDom_self (fun u _ => by rw [spArg_nil]; rfl)

end Ytosk.G
