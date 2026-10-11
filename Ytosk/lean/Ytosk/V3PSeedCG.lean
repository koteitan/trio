/-
**t = 2・C（q ≠ r、q − 1 が q へ上げ、q は r で数えられない）の種の列 r と q の枠の PH3cG・FC3（closure、2026-10-12）。**

N = M[n] で CL_N(r) = CL_{M.take x}(r) ++ [q]、CL_N(q) = [x′]（t2 の `C_frame`）。
- r の q より前の枠は M.take x の枠。
- r の q の枠: 状態 X₁（M.take x での r の引数）、子 o_N(q) = ψ_{s′}(σ^{n−1} X₁)（s′ = v_N(q) = qnS、
  σ = σ_{V,s′}）。sv と同じく SeedExt を段の帰納法で運び（t2 の残り `T2SeedCRes.rw`）、種類は `seed_kind`。
  要るのは名前つきの残り `T2SeedCFix`（Fix(X₁) と加数 ≥ Ω_{s′+1}）。
- q の枠は最初の枠だけ。FC3 は v_N(x′) = v_N(q) = s′ = V + ω^W の最後の加数 ω^W ≠ 1 から。
-/
import Ytosk.V3PSeedQNG
import Ytosk.V3T2SeedC

namespace Ytosk.G

open T

set_option linter.unusedSectionVars false

/-- **The residual of the C seed state**: `X₁` is fixed by `σ = σ_{V, s′}` or a G3 cut of its image at level
`s′`, and its summands are at least `Ω_{s′+1}`. -/
structure T2SeedCFix (M : Mat) (ρ : Valn) (r L q : Nat) : Prop where
  fix : ∀ τ, Cons (M.take (r + L)) τ →
    sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) = t2X1 M r L τ ∨
      t2X1 M r L τ ∈ cutsNSG (qnS M ρ r L q) (sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ))
  hi : ∀ τ, Cons (M.take (r + L)) τ → AllGeT (psi (succ (qnS M ρ r L q)) z z) (t2X1 M r L τ)

/-- `last (V + ω^W) ≠ 1` for `s′ = qnS`. -/
theorem qnS_last_ne_one {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) (r L q : Nat) :
    last (qnS M ρ r L q) ≠ one := by
  have hlW : ∀ u ∈ ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q),
      isOT u = true := by
    intro u hu; obtain ⟨d, _, rfl⟩ := List.mem_map.mp hu; exact isOT_bumpTerm I.good q d
  have hWne : sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q)) ≠ z := by
    intro h0
    have hle := le_foldl_sf (((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))
      one rfl hlW
    have : sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q)) =
        (((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q)).foldl
          (fun a b => sf (add a b)) one := rfl
    rw [← this, h0] at hle
    exact absurd hle (not_le_of_gt (T.z_lt_psi z z z))
  obtain ⟨s0, y0, hW⟩ := omega_psi_form (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
    (bumpTerm M ρ q)))
  have hne1 := omega_ne_one hWne
  rw [hW] at hne1
  unfold qnS; rw [hW]
  obtain ⟨P0, hP0, _⟩ := add_eq_app_prefix (ρ.v r) (psi s0 y0 z)
  rw [hP0, last_app P0 (by simp)]
  exact hne1

open Classical in
/-- **PH3cG and FC3 at the frames of the seeds `r` and `q` of `M[n]`** (C case). -/
theorem seed_frames_C {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hRes : T2SeedCRes M ρ r L q) (hFix : T2SeedCFix M ρ r L q)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : Rk (M.take (r + L)) rk0)
    (hT : FrameOT (M.take (r + L)) τ0 ∧ PH3cG (M.take (r + L)) τ0 ∧ FC3 (M.take (r + L)) τ0) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ∀ i, (i = r ∨ i = q) → ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat),
        CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) i =
          Lc' ++ c :: R' →
        QPHs (σ.v i) (Lc'.map σ.o) (σ.o c) ∧ QF3s (σ.v i) (Lc'.map σ.o) (σ.o c) := by
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
  have hQT1 := clField_qT2P hC0 hT.1 hT.2.1 r hrT
  have hQT2 := clField_qT2F hC0 hT.1 hT.2.2 r hrT
  intro n hn hGlow σ hCN hGN i hi Lc' c R' hCL
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
  -- the data of the frames, with the argument of `r` in `P = M[n − 1]` equal to `σ^{n−2} X₁`
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
  -- the levels below `n` are standard
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
  have hBhi := hFix.hi τ0 hC0
  have hFx := hFix.fix τ0 hC0
  -- the inner step is `σ Y` when `X₁ ≠ 0`
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
  rcases hi with hi | hi
  · -- the frames of `r`
    rw [hi] at hCL ⊢
    refine ⟨seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN (by rw [hvr, hv0]) hval
        (fun Lc' c R' h => (hQT1 Lc' c R' h).2) ?_ Lc' c R' hCL,
      seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN (by rw [hvr, hv0]) hval
        (fun Lc' c R' h => (hQT2 Lc' c R' h).2) ?_ Lc' c R' hCL⟩
    · rw [hoq]
      intro s y c0 hc ht hBz
      have hst : spArg (τ0.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o)) = X1 := rfl
      rw [hst] at ht hBz ⊢
      have hEn := hE hBz (n - 2) (by omega)
      rw [hinner (n - 2) (by omega) hBz hEn] at hc
      simp only [psi.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exact seed_kind hVot hs'ot hVs' hX1ot (isOT_shIt hVot hs'ot hVs' hX1ot (n - 2)) hBhi hFx hEn ht.1
    · rw [hoq]
      intro s y c0 hc ht hL hhi
      have hLc0 : CL (M.take (r + L)) r = [] := List.map_eq_nil_iff.mp hL
      have hX0 : X1 = z := by rw [hX1e, hLc0]; rfl
      rw [hX0, shIt_z, sh_z] at hc
      have hstep : step s' z s' z z = psi s' z z := by
        unfold step; rw [if_neg (by simp [lt])]; rfl
      rw [hstep] at hc
      simp only [psi.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exfalso; apply hhi
      simp only [split]
      rw [if_pos (show lt (psi s' z z) (psi (succ s') z z) = true from psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self _)))]
  · -- the frame of `q`: only `x′`, the first frame
    rw [hi] at hCL ⊢
    rw [hCLNq] at hCL
    have hc : c = r + L ∧ Lc' = [] := by
      rcases Lc' with _ | ⟨a, l⟩
      · simp at hCL; exact ⟨hCL.1.symm, rfl⟩
      · simp at hCL
    obtain ⟨rfl, rfl⟩ := hc
    have hxN : r + L < (TRIO.gexp M r L d0 d1 n).length := by
      have := TRIO.gexp_length (d0 := d0) (d1 := d1) (n := n) hlen
      have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
      omega
    obtain ⟨y0, hy0⟩ := o_psi_sub hCN hxN
    rw [sf_ot (hGN.ot_v _ hxN), hvx] at hy0
    refine ⟨fun s y c0 _ _ hB => absurd (spArg_nil _) (by simpa using hB), fun s y c0 hc _ _ _ => ?_⟩
    rw [hy0] at hc
    simp only [psi.injEq] at hc
    obtain ⟨rfl, _, _⟩ := hc
    rw [hvq]
    exact ⟨fun _ => ⟨ne_of_gt (lt_of_le_of_lt (z_le V) hVs'), qnS_last_ne_one I r L q⟩, fun h => absurd rfl h⟩

end Ytosk.G
