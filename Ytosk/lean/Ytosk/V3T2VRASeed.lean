/-
**t = 2 の種の列の枠の VSmallRAll（T2VRASeed、qr・qn、2026-10-17、t2）。**

t1 の骨組み V3T2VRA の残り `T2VRASeed` を、qr と qn の場合で示す（sv・C は名前つきの残り）。
- 段: N = M[n] で種 r の段は M の r の段に入る（`pathLv_r`）。r の親 k は種の列でないので FrameShape で、
  N で枠 (k, r) が書き換えるなら M でも書き換える（`rw_frame_of_shape`、o_N(r) は M より下）。k より上は
  t1 の残り `T2VRAPre`。
- 枠: r の最後の枠より前は M の枠そのもの（M の VSmallRAll）。最後の枠の子の添字は qr で V + 1（段 u ≤ V での
  成分は z か V の成分）、qn で s′ = v_N(q)（名前つきの残り `T2VRAQNDom`、M の段での s′ の成分の上限）。
  q の枠は子の添字が v_N(q) 自身なので自明。
-/
import Ytosk.V3T2SeedFrV2
import Ytosk.V3T2VRA

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **A rewriting frame of `N` at a parent with `FrameShape`** is a rewriting frame of `M` with the same
parent value, the same values before the child, and the same subscript. -/
theorem rw_frame_of_shape {M N : Mat} {ρ σ : Valn} {k : Nat} (hC : Cons M ρ) (hCN : Cons N σ)
    (hS : FrameShape M N ρ σ k) {Lc : List Nat} {c : Nat} {R : List Nat} (hCL : CL N k = Lc ++ c :: R)
    {s y : T} (hc : σ.o c = psi s y z)
    (ht : lt (spArg (σ.v k) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v k) z z) (psi s y z) = true) :
    ∃ y', CL M k = Lc ++ c :: R ∧ ρ.v k = σ.v k ∧ Lc.map ρ.o = Lc.map σ.o ∧ ρ.o c = psi s y' z ∧
      (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v k) z z) (psi s y' z) = true) := by
  rcases hS with ⟨hv, hcl, hsame⟩ | ⟨hv, Lc0, c0, hclM, hclN, hsame, hl, _, hchv, _⟩ | ⟨hN, _⟩
  · rw [hcl] at hCL
    have hmem : ∀ d ∈ Lc ++ [c], d ∈ CL M k := fun d hd => by
      rw [hCL]
      rcases List.mem_append.mp hd with h | h
      · exact List.mem_append_left _ h
      · simp at h; rw [h]; simp
    have hLc : Lc.map ρ.o = Lc.map σ.o :=
      List.map_congr_left (fun d hd => (hsame d (hmem d (List.mem_append_left _ hd))).symm)
    have hcc : ρ.o c = σ.o c := (hsame c (hmem c (by simp))).symm
    refine ⟨y, hCL, hv.symm, hLc, by rw [hcc, hc], ?_⟩
    rw [hLc, ← hv]
    exact ht
  · have hCLM : CL M k = Lc ++ c :: R := by rw [hclM, ← hclN, hCL]
    by_cases hR : R = []
    · subst hR
      rw [hclN] at hCL
      obtain ⟨h1, h2⟩ := List.append_inj' hCL rfl
      simp only [List.cons.injEq, and_true] at h2
      subst Lc0 c0
      have hLc : Lc.map ρ.o = Lc.map σ.o := List.map_congr_left (fun d hd => (hsame d hd).symm)
      -- the subscript is unchanged: otherwise the new child is `ψ_{v′}(0)` and does not rewrite
      have hvc : σ.v c ≠ ρ.v c → False := by
        intro hne
        have := hchv hne
        rw [hc] at this
        simp only [psi.injEq] at this
        rw [this.2.1] at ht
        exact T.not_lt_z _ ht.1
      have hveq : σ.v c = ρ.v c := by by_contra h; exact hvc h
      have hcM : c < M.length := (mem_children (cl_mem_children (show c ∈ CL M k by rw [hclM]; simp))).2
      have hcN : c < N.length := (mem_children (cl_mem_children (show c ∈ CL N k by rw [hclN]; simp))).2
      obtain ⟨y0, hy0⟩ := o_psi_sub hC hcM
      obtain ⟨y1, hy1⟩ := o_psi_sub hCN hcN
      rw [hc] at hy1
      simp only [psi.injEq] at hy1
      rw [← hveq, ← hy1.1] at hy0
      have hl1 := hl.1
      rw [hc, hy0] at hl1
      have hyy : y < y0 := by
        rcases psi_lt_psi_z_iff.mp hl1 with h | ⟨_, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact h
      refine ⟨y0, hCLM, hv.symm, hLc, hy0, ?_⟩
      rw [hLc, ← hv]
      exact ⟨lt_trans' ht.1 hyy, lt_trans' ht.2 (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hyy⟩))⟩
    · have hdl : (Lc ++ c :: R).dropLast = Lc0 := by rw [← hCL, hclN]; simp
      rw [List.dropLast_append_of_ne_nil (by simp)] at hdl
      have hLs : ∀ d ∈ Lc, d ∈ Lc0 := fun d hd => by rw [← hdl]; exact List.mem_append_left _ hd
      have hcs : c ∈ Lc0 := by
        rw [← hdl]
        apply List.mem_append_right
        obtain ⟨r0, rs, rfl⟩ := List.exists_cons_of_ne_nil hR
        simp
      have hLc : Lc.map ρ.o = Lc.map σ.o := List.map_congr_left (fun d hd => (hsame d (hLs d hd)).symm)
      refine ⟨y, hCLM, hv.symm, hLc, by rw [← hsame c hcs, hc], ?_⟩
      rw [hLc, ← hv]
      exact ht
  · rw [hN] at hCL; simp at hCL

/-- **The path levels of a column whose parent has `FrameShape`**: the frame to the parent rewrites in `M` too,
and the levels above the parent are `M`'s by `hup`. -/
theorem pathLv_of_shape {M N : Mat} {ρ σ : Valn} (hC : Cons M ρ) (hCN : Cons N σ) {c : Nat}
    (hS : ∀ k, par N 0 c = some k → FrameShape M N ρ σ k)
    (hup : ∀ k u, par N 0 c = some k → PathLvAll N σ k u → PathLvAll M ρ k u) :
    ∀ u, PathLvAll N σ c u → PathLvAll M ρ c u := by
  intro u h
  have hpar : ∀ {k : Nat} {Lc R : List Nat}, CL N k = Lc ++ c :: R → par N 0 c = some k := by
    intro k Lc R hcl
    exact (mem_children_iff.mp (cl_mem_children (show c ∈ CL N k by rw [hcl]; simp))).2
  cases h with
  | top hcl hsy ht =>
    obtain ⟨y', hclM, hv, hLc, hy', ht'⟩ := rw_frame_of_shape hC hCN (hS _ (hpar hcl)) hcl hsy ht
    rw [← hv]
    exact PathLvAll.top hclM hy' ht'
  | step hcl hsy ht hk =>
    obtain ⟨y', hclM, hv, hLc, hy', ht'⟩ := rw_frame_of_shape hC hCN (hS _ (hpar hcl)) hcl hsy ht
    exact PathLvAll.step hclM hy' ht' (hup _ u (hpar hcl) hk)

/-- **The frames of a seed column with the same frames as `M` before the last child**: the levels are `M`'s
(`hlev`), the frames before the last are `M`'s, and the last frame is given (`hlast`). -/
theorem vra_lift {M N : Mat} {ρ σ : Valn} {i x x' : Nat} {Lc : List Nat}
    (hVM : VSmallRAll M ρ) (hCLM : CL M i = Lc ++ [x]) (hCLN : CL N i = Lc ++ [x']) (hvr : σ.v i = ρ.v i)
    (hLc : ∀ d ∈ Lc, σ.o d = ρ.o d) (hlev : ∀ u, LevAt N σ i u → LevAt M ρ i u)
    (hlast : ∀ u, LevAt M ρ i u → QVRAt (ρ.v i) (Lc.map ρ.o) (σ.o x') u) :
    ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat), CL N i = Lc' ++ c :: R' →
      ∀ u, LevAt N σ i u → QVRAt (σ.v i) (Lc'.map σ.o) (σ.o c) u := by
  intro Lc' c R' h u hu
  have hu' := hlev u hu
  rw [hCLN] at h
  rw [hvr]
  by_cases hR : R' = []
  · subst hR
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at h2
    subst h1; subst h2
    rw [List.map_congr_left hLc]; exact hlast u hu'
  · have hdl : (Lc' ++ c :: R').dropLast = Lc := by rw [← h]; simp
    rw [List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hR] at hdl
    have hLs : ∀ d ∈ Lc', d ∈ Lc := fun d hd => by rw [← hdl]; exact List.mem_append_left _ hd
    have hcs : c ∈ Lc := by rw [← hdl]; simp
    have hclM : CL M i = Lc' ++ c :: (R'.dropLast ++ [x]) := by rw [hCLM, ← hdl]; simp
    rw [List.map_congr_left (fun d hd => hLc d (hLs d hd)), hLc c hcs]
    exact (vsmallRAll_iff.mp hVM) i Lc' c _ hclM u hu'

/-- **A frame whose child subscript is the parent's own value**: `QVRAt` at every level. -/
theorem qVRAt_self {a cv u : T} {Lv : List T} (hcv : ∃ y, cv = psi a y z) : QVRAt a Lv cv u := by
  intro s y hsy _ _ _ g hg
  obtain ⟨y0, hy0⟩ := hcv
  rw [hy0] at hsy
  simp only [psi.injEq] at hsy
  rw [← hsy.1] at hg
  exact Or.inr (Or.inr ⟨g, hg, le_refl _⟩)

/-- **The residual of the qn seed frame for `VSmallRAll`**: at the levels of `r` in `M` (at most `V`), the
components of `s′ = v_N(q)` are below `Ω_{s′}`, below `B`, or below a component of `V`. -/
def T2VRAQNDom (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop :=
  ∀ u, LevAt M ρ r u → ¬ lt (ρ.v r) u = true → ∀ g ∈ comps u (qnS M ρ r L q),
    g ≤ psi (qnS M ρ r L q) z z ∨ g ≤ t2B (ρ.v r) ρ Lc ∨ ∃ d ∈ comps u (ρ.v r), g ≤ d

/-- **The residual of the sv and C seed frames of `r` for `VSmallRAll`** (the frames before the last are those of
`M.take x`). -/
def T2VRASeedSVC (M : Mat) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
    ((par M 0 (r + L) = some r ∧ upg M (r + L - 1) = some (r + L)) ∨
      (∃ q, par M 0 (r + L) = some q ∧ q ≠ r ∧ ¬ ∃ Lc, CL M r = Lc ++ [q])) →
    ∀ n, 2 ≤ n → ∀ σ, Cons (G2 M r L n) σ → Good3 (G2 M r L n) σ →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL (G2 M r L n) r = Lc ++ c :: R →
        ∀ u, LevAt (G2 M r L n) σ r u → QVRAt (σ.v r) (Lc.map σ.o) (σ.o c) u

open Classical in
/-- **T2VRASeed** (`VSmallRAll` at the seed frames of `M[n]`) for qr and qn, with the residuals `T2VRAQNDom`
and `T2VRASeedSVC` (sv, C). The levels of `r` are those of `M` (`pathLv_of_shape`, `T2VRAPre`). -/
theorem t2VRASeed_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hVM : VSmallRAll M ρ) (hRes : G.T2SeedPRes M ρ) (hPre : T2VRAPre M ρ)
    (hQN : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc)
    (hSVC : T2VRASeedSVC M) : T2VRASeed M := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hGall := good3_expand_t2 hM hS I R hz h2 (t2BelowXE_of hB hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
  have hlen1 : 1 ≤ M.length := by
    rcases hM0 : M with _ | _
    · rw [hM0] at hz; exact absurd rfl hz
    · simp
  have hRk1 : Rk (M.take (M.length - 1)) rk :=
    rk_take (by omega) I.rank (counted_take_last (M := M) hlen1 I.r0p I.z2 I.sd I.z1 I.uat)
  have hC1 := cons_of_rk hRk1
  set τ0 := rhsIt (M.take (M.length - 1)) (rkBound (M.take (M.length - 1)) rk) with hτ0
  intro r L hlen hr n hn σ hCN hGN i hsc Lc c R' hCL u hu
  have hx : M.length - 1 = r + L := by omega
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = G2 M r L m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, hx]; exact hr)
    rw [h2, hx] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hGlow : ∀ m, 1 ≤ m → m < n → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ :=
    fun m hm _ τ hτ => by rw [← hexp m] at hτ ⊢; exact hGall m hm τ hτ
  have hBS := t2BelowXS_of hB hM hS I R hz h2 hlen hr n hn hGlow σ hCN
    (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩)
  have hC0 : Cons (M.take (r + L)) τ0 := by rw [← hx]; exact hC1
  have hR0 : Rk (M.take (r + L)) rk := by rw [← hx]; exact hRk1
  -- the columns before `r` are not seeds
  have hns : ∀ k, k < r → ¬ T2SeedCol M r L k := by
    intro k hk hsk
    rcases hsk with (⟨_, hkr⟩ | ⟨q, hq, hqr, hpq⟩) | ⟨q, hq, hqr, hkq⟩
    · omega
    · rw [par0_q_t2 hM hS I hlen hr hq hqr] at hpq; cases hpq; omega
    · have := par_lt M 0 q r (par0_q_t2 hM hS I hlen hr hq hqr); omega
  -- the levels of `r` in `N` are levels of `M`
  have hlev : σ.v r = ρ.v r → ∀ u, LevAt (G2 M r L n) σ r u → LevAt M ρ r u := by
    intro hvr u hu
    rcases hu with hu | hu
    · exact Or.inl (by rw [hu, hvr])
    · right
      refine pathLv_of_shape I.cons hCN (c := r) (fun k hk => ?_) (fun k u hk hku => ?_) u hu
      · have hkr : k < r := par_lt _ 0 r k hk
        exact (hBS k (by omega)).2.2.2.1 (hns k hkr)
      · have hkr : k < r := par_lt _ 0 r k hk
        exact hPre r L hlen hr n hn σ hCN hGN k (by omega) (hns k hkr) u hku
  by_cases hqr : par M 0 (r + L) = some r
  · -- q = r: the seed is `r`
    have hir : i = r := by
      rcases hsc with (⟨_, h⟩ | ⟨q, hq, hqr', _⟩) | ⟨q, hq, hqr', _⟩
      · exact h
      · rw [hqr] at hq; cases hq; exact absurd rfl hqr'
      · rw [hqr] at hq; cases hq; exact absurd rfl hqr'
    subst i
    by_cases hux : upg M (r + L - 1) = some (r + L)
    · exact hSVC r L hlen hr (Or.inl ⟨hqr, hux⟩) n hn σ hCN hGN Lc c R' hCL u hu
    · have hXu : ∀ j, upg M j ≠ some (r + L) := by
        intro j hj
        have := G.upg_last_eq hlen hj
        rw [this] at hj; exact hux hj
      obtain ⟨Lc0, hLc0⟩ := G.cl_qr I.z2 hlen hr hqr hXu
      obtain ⟨Y, hox, _, hCLN, hvr, hLc⟩ :=
        seed_last_qr hM hS I R hz h2 hlen hr hqr hXu hLc0 (hRes.qr r L hlen hr hqr hXu Lc0 hLc0) hC0 ⟨rk, hR0⟩
          n hn hGlow σ hCN
      refine vra_lift hVM hLc0 hCLN hvr hLc (hlev hvr) (fun u _ => ?_) Lc c R' hCL u hu
      rw [hox]
      intro s y hsy _ _ _ g hg
      simp only [psi.injEq] at hsy
      obtain ⟨rfl, -⟩ := hsy
      rcases comps_succ_sub u g hg with h | h
      · left; rw [h]; exact z_le _
      · exact Or.inr (Or.inr ⟨g, h, le_refl _⟩)
  · -- q ≠ r
    obtain ⟨q, hq⟩ : ∃ q, par M 0 (r + L) = some q :=
      par0_some_of hrx (anc0_e0_lt (anc0_of_par M 2 r (r + L) hr) (by omega))
    have hqr' : q ≠ r := fun h => hqr (by rw [hq, h])
    have hir : i = r ∨ i = q := by
      rcases hsc with (⟨h, _⟩ | ⟨q', hq', _, hpq⟩) | ⟨q', hq', _, h⟩
      · exact absurd h hqr
      · rw [hq] at hq'; cases hq'
        rw [par0_q_t2 hM hS I hlen hr hq hqr'] at hpq; cases hpq; exact Or.inl rfl
      · rw [hq] at hq'; cases hq'; exact Or.inr h
    by_cases hcl : ∃ Lc0, CL M r = Lc0 ++ [q]
    · obtain ⟨Lc0, hLc0⟩ := hcl
      obtain ⟨ft, hCLN, hCLNq, hvr, hLc, hvx, hvq, hoq, _, _⟩ :=
        seed_last_qn hM hS I R hz h2 hlen hr hq hqr' hLc0 (hRes.qn r L q hlen hr hq hqr' Lc0 hLc0) hC0
          ⟨rk, hR0⟩ n hn hGlow σ hCN
      rcases hir with hir | hir <;> subst i
      · refine vra_lift hVM hLc0 hCLN hvr hLc (hlev hvr) (fun u hu' => ?_) Lc c R' hCL u hu
        rw [hoq]
        intro s y hsy _ _ hu2 g hg
        simp only [psi.injEq] at hsy
        obtain ⟨rfl, -⟩ := hsy
        exact hQN r L q hlen hr hq hqr' Lc0 hLc0 u hu' hu2 g hg
      · -- the frame of `q`: its only child has the subscript `v_N(q)`
        rw [hCLNq] at hCL
        have hc : c = r + L ∧ Lc = [] := by
          rcases Lc with _ | ⟨a, l⟩
          · simp at hCL; exact ⟨hCL.1.symm, rfl⟩
          · simp at hCL
        obtain ⟨rfl, rfl⟩ := hc
        have hxN : r + L < (G2 M r L n).length := by
          rw [TRIO.gexp_length hlen]
          have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
          omega
        obtain ⟨y0, hy0⟩ := o_psi_sub hCN hxN
        rw [sf_ot (hGN.ot_v _ hxN), hvx, ← hvq] at hy0
        exact qVRAt_self ⟨y0, hy0⟩
    · rcases hir with hir | hir <;> subst i
      · exact hSVC r L hlen hr (Or.inr ⟨q, hq, hqr', hcl⟩) n hn σ hCN hGN Lc c R' hCL u hu
      · -- the frame of `q` in the C case: as in qn
        obtain ⟨hCR, hBig⟩ := hRes.C r L q hlen hr hq hqr' hcl
        have hFix := G.t2SeedCFix_of hM hS I R hlen hr hq hqr' hcl hCR hBig
        obtain ⟨_, _, _, _, _, hvx, hvq, _, hCLNq, _⟩ :=
          G.seed_last_C hM hS I R hz h2 hlen hr hq hqr' hcl hCR hFix hC0 hR0 n hn hGlow σ hCN hGN
        rw [hCLNq] at hCL
        have hc : c = r + L ∧ Lc = [] := by
          rcases Lc with _ | ⟨a, l⟩
          · simp at hCL; exact ⟨hCL.1.symm, rfl⟩
          · simp at hCL
        obtain ⟨rfl, rfl⟩ := hc
        have hxN : r + L < (G2 M r L n).length := by
          rw [TRIO.gexp_length hlen]
          have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
          omega
        obtain ⟨y0, hy0⟩ := o_psi_sub hCN hxN
        rw [sf_ot (hGN.ot_v _ hxN), hvx, ← hvq] at hy0
        exact qVRAt_self ⟨y0, hy0⟩

/-- **The top-level form** of `T2VRASeed` (t1's `t2VRAV2_of` argument `hSeedG`). -/
theorem t2VRASeedG_of (hB : T2BelowXResV2) (hPR : T2SeedPResV2)
    (hPreG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAPre M ρ)
    (hQNG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
        par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc)
    (hSVCG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeedSVC M) :
    ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeed M :=
  fun M ρ rk C hz h2 => t2VRASeed_of (hB M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 C.I.vra
    (hPR M ρ rk C hz h2) (hPreG M ρ rk C hz h2) (hQNG M ρ rk C hz h2) (hSVCG M ρ rk C hz h2)

end Ytosk
