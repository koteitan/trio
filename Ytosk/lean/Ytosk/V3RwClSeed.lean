/-
**RwClosed の種の枠（t = 2、2026-10-17、t0）。**

closure の種の枠の証明（V3PSeedQRG・QNG・SVG・CG）の前半（N での r・q の数える子と値）を写し、最後の枠の結論を
RwClosed の枠の性質 `QRC`（書き換えて B < hi(y) で B が hi(y) の先頭部分でないなら ClosedA）にした。
- qr: 最後の枠は書き換えない（n = 2）か、y = B + ψ(…)（B が先頭部分）で前提が立たない。前の枠は M の枠。
- qn: r の最後の枠は y = B + Ω_{f t} で前提が立たない。q の枠は最初の枠（状態 0）。前の枠は M の枠。
- sv・C: 最後の枠の状態は X₁（M.take x での r の引数）。名前つきの残り `T2X1Cl`（X₁ は ClosedA）。前の枠は
  M.take x の枠。q の枠（C）は最初の枠。
-/
import Ytosk.V3RwClT2
import Ytosk.V3PSeedAllG

namespace Ytosk.G

open T

set_option linter.unusedSectionVars false

open Classical in
/-- **RwClosed at the frames of the seed `r` of `M[n]`** (`t = 2`, `q = r`, no upgrade into `x`), from
PH3cG・FC3 of `M` and t2 の残り `T2SeedQRRes` (σB is `tame_sigmaB_std`). -/
theorem seed_frames_qr_RC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) (hRes : T2SeedQRRes M ρ r L Lc)
    {τ0 : Valn} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : ∃ rk0, Rk (M.take (r + L)) rk0)
    (hRw : RwClosed M ρ) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat),
        CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r =
          Lc' ++ c :: R' →
        QRC (σ.v r) (Lc'.map σ.o) (σ.o c) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set V := ρ.v r with hVdef
  set B := t2B V ρ Lc with hBdef
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
  obtain ⟨hBc, hBot, _⟩ := qr_M_side I hlen hrx hCLM
  intro n hn hGlow σ hCN Lc' c R' hCL
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  -- the valuation of `P = M[n − 1]` and the child of the last frame
  obtain ⟨Y, hYl⟩ : ∃ Y, σ.o (r + L) = psi (succ V) Y z ∧
      ((n = 2 ∧ ¬ B < Y) ∨ (3 ≤ n ∧ Y = sh V (succ V) (seqZ V B (t2W1 (M.take (r + L)) V τ0 r) (n - 3)))) ∧
      CL (TRIO.gexp M r L d0 d1 n) r = Lc ++ [r + L] ∧ σ.v r = V ∧ ∀ d ∈ Lc, σ.o d = ρ.o d := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn2 : n = 2 := by omega
      subst hn2
      have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
      have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hC0
      have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := hGlow 1 (le_refl 1) (by omega) τ0 hCP
      obtain ⟨rk0, hRk0⟩ := hR0
      have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hRk0
      obtain ⟨hCLN, hvr, hLc, hox⟩ :=
        seed_frame_data_qr hM hS I R hz h2 hlen hr hq hXu hCLM (le_refl 2) hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hox
      rw [show (2 - 1 : Nat) = 1 from rfl, hP1] at hox
      exact ⟨_, hox, Or.inl ⟨rfl, hRes.w1 τ0 hC0⟩, hCLN, hvr, hLc⟩
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      obtain ⟨hCLN, hvr, hLc, hox⟩ :=
        seed_frame_data_qr hM hS I R hz h2 hlen hr hq hXu hCLM hn hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hox
      have hval := seed_r_value_qr hM hS I R hz h2 hlen hr hq hXu hCLM hRes hC0 ⟨_, hR0.choose_spec⟩ (n - 1)
        (by omega) (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP
      have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
      have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hform := o_cl_eq hCP hGP hrP
      rw [hval] at hform
      simp only [psi.injEq] at hform
      have h21 := hform.2.1
      rw [← hform.1] at h21
      rw [← hform.1, ← h21, show n - 1 - 2 = n - 3 by omega] at hox
      exact ⟨_, hox, Or.inr ⟨hn3, rfl⟩, hCLN, hvr, hLc⟩
  obtain ⟨hox, hcase, hCLN, hvr, hLc⟩ := hYl
  have hσB := tame_sigmaB_std hM hS I hlen hr hq hXu hCLM
  refine seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => rwClosed_iff.mp hRw r hrM Lc' c R' h) ?_
    Lc' c R' hCL
  rw [hox]
  intro s y hc ht _ hnp
  simp only [psi.injEq] at hc
  obtain ⟨rfl, rfl, -⟩ := hc
  rcases hcase with ⟨_, hnr⟩ | ⟨_, hY⟩
  · exact absurd ht.1 hnr
  · exfalso; apply hnp
    have h1 := split_all_ge (sh_seqZ_allGe (B := B) (W1 := t2W1 (M.take (r + L)) V τ0 r) hVot hσB hBc hRes.ks (n - 3))
    have h2 := sh_seqZ (B := B) (W1 := t2W1 (M.take (r + L)) V τ0 r) hVot hσB hBc hRes.ks (n - 3)
    rw [hY, h1, h2]
    exact ⟨_, rfl⟩

open Classical in
/-- **PH3cG and FC3 at the frames of the seeds `r` and `q` of `M[n]`** (`q ≠ r` counted at `r`), from PH3cG・FC3
of `M`, t2 の残り `T2SeedQNRes`, and `T2SeedQNFC`. -/
theorem seed_frames_qn_RC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) (hRes : T2SeedQNRes M ρ r L q Lc)
    (hFC : T2SeedQNFC M ρ r L q Lc)
    {τ0 : Valn} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : ∃ rk0, Rk (M.take (r + L)) rk0)
    (hRw : RwClosed M ρ) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ∀ i, (i = r ∨ i = q) → ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat),
        CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) i =
          Lc' ++ c :: R' →
        QRC (σ.v i) (Lc'.map σ.o) (σ.o c) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set V := ρ.v r with hVdef
  set B := t2B V ρ Lc with hBdef
  set s' := qnS M ρ r L q with hs'def
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hpq : par M 0 q = some r := (mem_children_iff.mp (cl_mem_children hqcl)).2
  have hrq : r < q := par_lt M 0 _ _ hpq
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
  have hv0 := v_take_of_untopped I hlen (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hC0
  obtain ⟨t1, ht1, hch⟩ := hRes.base τ0 hC0
  intro n hn hGlow σ hCN hGN i hi Lc' c R' hCL
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  have hvq : σ.v q = s' := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  -- the argument of `r` in `P = M[n − 1]` is `B + Ω_{t_{n−2}}`
  obtain ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩ : CL (TRIO.gexp M r L d0 d1 n) r = Lc ++ [q] ∧
      CL (TRIO.gexp M r L d0 d1 n) q = [r + L] ∧ σ.v r = V ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧
      σ.v (r + L) = s' ∧
      σ.o q = psi s' (step s' z s' (sh V s' (app B (psi (tqN V s' t1 (n - 2)) z z))) z) z := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn2 : n = 2 := by omega
      subst hn2
      have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hC0
      have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := hGlow 1 (le_refl 1) (by omega) τ0 hCP
      obtain ⟨rk0, hRk0⟩ := hR0
      have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show (2 - 1 : Nat) = 1 from rfl, hP1]; exact hRk0
      obtain ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩ :=
        seed_frame_data_qn hM hS I R hz h2 hlen hr hq hqr hCLM (le_refl 2) hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hCLNq hoq
      rw [show (2 - 1 : Nat) = 1 from rfl, hP1, ht1, hv0] at hoq
      rw [hvq, qnS_vxs] at hvx
      rw [hvq, hvx, spArg_nil] at hoq
      exact ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      obtain ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩ :=
        seed_frame_data_qn hM hS I R hz h2 hlen hr hq hqr hCLM hn hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hCLNq hoq
      have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
      have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hqP : q < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hval := seed_r_value_qn hM hS I R hz h2 hlen hr hq hqr hCLM hRes hC0 hR0 hv0 ht1
        (fun k => ⟨(hch k).1, (hch k).2.1⟩) (n - 1) (by omega)
        (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP (hGP.ot_o q hqP) (cl_vals hCP hGP hrP).2
      have hform := o_cl_eq hCP hGP hrP
      rw [hval] at hform
      simp only [psi.injEq] at hform
      have h21 := hform.2.1
      rw [← hform.1] at h21
      rw [← hform.1, ← h21, show n - 1 - 1 = n - 2 by omega] at hoq
      rw [hvq, qnS_vxs] at hvx
      rw [hvq, hvx, spArg_nil] at hoq
      exact ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩
  -- the child of `r`'s last frame
  set t := tqN V s' t1 (n - 2) with htdef
  have hat : V < t := (hch (n - 2)).1
  have hts : ¬ shf V s' t < succ s' := (hch (n - 2)).2.1
  have hσB := hRes.σB
  have hBc := hRes.Bc
  have hhigh : ∀ g ∈ summands (app B (psi (shf V s' t) z z)), ¬ g < psi (succ s') z z := by
    intro g hg
    rw [summands_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hBc g hg
    · simp [summands] at hg; rw [hg]
      intro hlt
      rw [psi_lt_psi_z_iff] at hlt
      rcases hlt with h | ⟨_, h⟩
      · exact hts h
      · exact T.not_lt_z _ h
  have hinner : step s' z s' (sh V s' (app B (psi t z z))) z = app B (psi (shf V s' t) z z) := by
    rw [sh_app, hσB, sh_psi_gt hat, sh_z]
    have hne : app B (psi (shf V s' t) z z) ≠ z := by
      intro h; cases hB : B with
      | z => rw [hB] at h; simp at h
      | psi _ _ _ => rw [hB] at h; simp at h
    have hzlt : z < app B (psi (shf V s' t) z z) := by
      cases h : app B (psi (shf V s' t) z z) with
      | z => exact absurd h hne
      | psi _ _ _ => exact T.z_lt_psi _ _ _
    unfold step
    rw [if_pos ⟨hzlt, psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hzlt⟩)⟩]
    exact H_of_high hs'ot hhigh
  rw [hinner] at hoq
  rcases hi with hi | hi
  · rw [hi] at hCL ⊢
    refine seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => rwClosed_iff.mp hRw r hrM Lc' c R' h) ?_
      Lc' c R' hCL
    rw [hoq]
    intro s y hc _ _ hnp
    simp only [psi.injEq] at hc
    obtain ⟨rfl, rfl, -⟩ := hc
    exfalso; apply hnp
    rw [split_all_ge hhigh]
    exact ⟨_, rfl⟩
  · rw [hi] at hCL ⊢
    rw [hCLNq] at hCL
    have hc : c = r + L ∧ Lc' = [] := by
      rcases Lc' with _ | ⟨a, l⟩
      · simp at hCL; exact ⟨hCL.1.symm, rfl⟩
      · simp at hCL
    obtain ⟨rfl, rfl⟩ := hc
    intro s y _ _ _ _ u _ g hg
    simp [sumN, spArg, comps] at hg

open Classical in
/-- **PH3cG and FC3 at the frames of the seed `r` of `M[n]`** (sv), from PH3cG・FC3・FrameOT of `M.take x`,
t2 の残り `T2SeedSVRes`, and the residual `T2SeedSVFix`. -/
theorem seed_frames_sv_RC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (hRes : T2SeedSVRes M ρ r L)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : Rk (M.take (r + L)) rk0)
    (hRwT : RwClosed (M.take (r + L)) τ0)
    (hX1cl : ∀ k, QRC (τ0.v r) ((CL (M.take (r + L)) r).map τ0.o)
      (psi (succ (ρ.v r)) (sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ0) k)) z)) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
      ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat),
        CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r =
          Lc' ++ c :: R' →
        QRC (σ.v r) (Lc'.map σ.o) (σ.o c) := by
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
  intro n hn hGlow σ hCN hdecN Lc' c R' hCL
  have hG0 : Good3 (M.take (r + L)) τ0 := by
    have := hGlow 1 (le_refl 1) (by omega) τ0 (by rw [hP1]; exact hC0)
    rw [hP1] at this; exact this
  have hX1ot : isOT X1 = true := by
    have := hG0.ot_o r hrT
    rw [o_cl_eq hC0 hG0 hrT] at this
    rw [hX1def]; exact isOT_arg this
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  -- the child of the last frame: `σ^{n−1} X₁`
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
  refine seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr hval
      (fun Lc' c R' h => rwClosed_iff.mp hRwT r hrT Lc' c R' h) ?_ Lc' c R' hCL
  rw [hox]; exact hX1cl (n - 2)

open Classical in
/-- **PH3cG and FC3 at the frames of the seeds `r` and `q` of `M[n]`** (C case). -/
theorem seed_frames_C_RC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hRes : T2SeedCRes M ρ r L q)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : Rk (M.take (r + L)) rk0)
    (hRwT : RwClosed (M.take (r + L)) τ0)
    (hX1cl : ∀ k, QRC (τ0.v r) ((CL (M.take (r + L)) r).map τ0.o)
      (psi (qnS M ρ r L q) (step (qnS M ρ r L q) z (qnS M ρ r L q)
        (sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ0) k)) z) z)) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ∀ i, (i = r ∨ i = q) → ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat),
        CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) i =
          Lc' ++ c :: R' →
        QRC (σ.v i) (Lc'.map σ.o) (σ.o c) := by
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
  rcases hi with hi | hi
  · rw [hi] at hCL ⊢
    refine seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN (by rw [hvr, hv0]) hval
        (fun Lc' c R' h => rwClosed_iff.mp hRwT r hrT Lc' c R' h) ?_ Lc' c R' hCL
    rw [hoq]; exact hX1cl (n - 2)
  · rw [hi] at hCL ⊢
    rw [hCLNq] at hCL
    have hc : c = r + L ∧ Lc' = [] := by
      rcases Lc' with _ | ⟨a, l⟩
      · simp at hCL; exact ⟨hCL.1.symm, rfl⟩
      · simp at hCL
    obtain ⟨rfl, rfl⟩ := hc
    intro s y _ _ _ _ u _ g hg
    simp [sumN, spArg, comps] at hg

/-- **Residual: the last seed frame of `r`** in the sv and C cases (state `X₁`, the argument of `r` in `M.take x`):
`QRC` at the new last child `ψ_{V′}(σ^{k+1} X₁)` (sv, `V′ = V + 1`) or `ψ_{s′}(step s′ 0 s′ (σ^{k+1} X₁))` (C,
`s′ = qnS`). The unconditional `ClosedA (v r) X₁` is false (Cprime: 22 matrices); the premise of `QRC` does
not hold there. -/
def T2X1Cl (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
    (par M 0 (r + L) = some r → upg M (r + L - 1) = some (r + L) → QRC (τ.v r) ((CL (M.take (r + L)) r).map τ.o)
      (psi (succ (ρ.v r)) (sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k)) z)) ∧
    (∀ q, par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → QRC (τ.v r) ((CL (M.take (r + L)) r).map τ.o)
      (psi (qnS M ρ r L q) (step (qnS M ρ r L q) z (qnS M ρ r L q)
        (sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)) z) z))

/-- **RwClosed at the seed frames of every `M[n]`** (`t = 2`). -/
theorem seed_frames_RC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hRw : RwClosed M ρ)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → RwClosed (M.take (M.length - 1)) τ)
    (hX1 : T2X1Cl M ρ) (hRes : T2SeedPRes M ρ) :
    T2SeedFrames QRC M := by
  have hRk1 : Rk (M.take (M.length - 1)) rk := by
    have hlen1 : 1 ≤ M.length := by
      rcases hM0 : M with _ | _
      · rw [hM0] at hz; exact absurd rfl hz
      · simp
    exact rk_take (by omega) I.rank (counted_take_last (M := M) hlen1 I.r0p I.z2 I.sd I.z1 I.uat)
  have hC1 := cons_of_rk hRk1
  set τ0 := rhsIt (M.take (M.length - 1)) (rkBound (M.take (M.length - 1)) rk) with hτ0
  have hx : ∀ r L, r + L + 1 = M.length → M.length - 1 = r + L := fun r L h => by omega
  refine t2_seed_frames_of (Q := QRC) hM hS I ?_ ?_ ?_ ?_
  · intro r L hlen hr hq hXu Lc hLc n hn hlow σ hσ _ Lc' c R' hcl
    rw [hx r L hlen] at hC1 hRk1
    exact seed_frames_qr_RC hM hS I R hz h2 hlen hr hq hXu hLc (hRes.qr r L hlen hr hq hXu Lc hLc) hC1
      ⟨rk, hRk1⟩ hRw n hn hlow σ hσ Lc' c R' hcl
  · intro r L hlen hr hq hux n hn hlow σ hσ hG Lc' c R' hcl
    have hT' := hT τ0 hC1
    rw [hx r L hlen] at hC1 hRk1 hT'
    have hSV := hRes.sv r L hlen hr hq hux
    have hrN : r < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n).length := by
      have hc : c ∈ children _ r := cl_mem_children (by rw [hcl]; simp)
      have := mem_children hc; omega
    have hdec : ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n)
        r).map σ.o).Pairwise (fun a b => b ≤ a) := by
      rw [← cvals_eq_map hσ hG]; exact hG.dec r hrN
    exact seed_frames_sv_RC hM hS I R hz h2 hlen hr hq hux hSV hC1 hRk1 hT' (fun k => (hX1 r L hlen hr τ0 hC1 k).1 hq hux)
      n hn hlow σ hσ hdec Lc' c R' hcl
  · intro r L q hlen hr hq hqr Lc hLc i hi n hn hlow σ hσ hG Lc' c R' hcl
    rw [hx r L hlen] at hC1 hRk1
    have hQN := hRes.qn r L q hlen hr hq hqr Lc hLc
    have hFC := t2SeedQNFC_holds hM hS I R hlen hr hq hqr hLc
    exact seed_frames_qn_RC hM hS I R hz h2 hlen hr hq hqr hLc hQN hFC hC1 ⟨rk, hRk1⟩ hRw n hn hlow σ hσ hG
      i hi Lc' c R' hcl
  · intro r L q hlen hr hq hqr hncl i hi n hn hlow σ hσ hG Lc' c R' hcl
    have hT' := hT τ0 hC1
    rw [hx r L hlen] at hC1 hRk1 hT'
    obtain ⟨hCR, _⟩ := hRes.C r L q hlen hr hq hqr hncl
    exact seed_frames_C_RC hM hS I R hz h2 hlen hr hq hqr hncl hCR hC1 hRk1 hT' (fun k => (hX1 r L hlen hr τ0 hC1 k).2 q hq hqr hncl)
      n hn hlow σ hσ hG i hi Lc' c R' hcl

/-- **RwClosed of every `M[n]`** (`t = 2`) with the seed frames reduced to `T2X1Cl` and the seed residuals. -/
theorem rwClosed_expand_t2S (hCl : ClSh) (hB : T2BelowXRes) {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hRM : RwClosed M ρ)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → RwClosed (M.take (M.length - 1)) τ)
    (hX1 : T2X1Cl M ρ) (hRes : T2SeedPRes M ρ) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → RwClosed (expand M n) σ :=
  rwClosed_expand_t2 hCl hB hM hS I R hz h2 hRM hT (seed_frames_RC hM hS I R hRM hz h2 hT hX1 hRes)

end Ytosk.G
