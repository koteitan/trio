/- QPHs/QF3s seed producers on the consistent V3 context. -/
import Ytosk.V3SeedFOC2
import Ytosk.V3T2CopyV3

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

structure QRRel (M : Mat) (ρ : Valn) (r L : Nat) (Lc : List Nat) : Prop where
  ks : ∀ k, addN (ρ.v r) k < ρ.v (r + L)
  w1 : ∀ τ, Cons (M.take (r + L)) τ → ¬ t2B (ρ.v r) ρ Lc < t2W1 (M.take (r + L)) (ρ.v r) τ r

structure QNRel (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop where
  σB : sh (ρ.v r) (qnS M ρ r L q) (t2B (ρ.v r) ρ Lc) = t2B (ρ.v r) ρ Lc
  Bc : ∀ g ∈ summands (t2B (ρ.v r) ρ Lc), ¬ g < psi (succ (qnS M ρ r L q)) z z
  base : ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ∧
    ∀ k, ρ.v r < tqN (ρ.v r) (qnS M ρ r L q) t1 k ∧
      ¬ shf (ρ.v r) (qnS M ρ r L q) (tqN (ρ.v r) (qnS M ρ r L q) t1 k) < succ (qnS M ρ r L q)

structure SVRel (M : Mat) (ρ : Valn) (r L : Nat) : Prop where
  rw : ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
    step (ρ.v r) (t2X1 M r L τ) (succ (ρ.v r))
      (sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k)) z =
    sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k)

structure CRel (M : Mat) (ρ : Valn) (r L q : Nat) : Prop where
  decP : ∀ τ, Cons (M.take (r + L)) τ → ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] →
    ∃ s y, τ.o c0 = psi s y z ∧ qnS M ρ r L q < s
  un : upg M (r + L - 1) = none
  vqP : ∀ τ, Cons (M.take (r + L)) τ → τ.v q = qnS M ρ r L q
  rw : ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
    step (ρ.v r) (t2X1 M r L τ) (qnS M ρ r L q) (step (qnS M ρ r L q) z (qnS M ρ r L q)
      (sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)) z) z =
    sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)

theorem o_r_level_qrV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L])
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    (hks1 : succ (ρ.v r) < ρ.v (r + L)) :
    σ.o r = psi (ρ.v r) (step (ρ.v r) (spArg (ρ.v r) z (sumN (Lc.map ρ.o))) (succ (ρ.v r))
      (sh (ρP.v r) (succ (ρ.v r)) (spArg (ρP.v r) z (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) (n - 1)) r).map ρP.o)))) z) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
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
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hxbr : col M (r + L) ≠ bump M r := fun h => by
    have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hIU : ∀ c, c < r + L → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_N2 (d1 := d1) hlen hL0 hq hd0e hn hXu hxbr he2r hc]
    exact htM
  have hxcN : Counted N r (r + L) := by
    have hx2 := (entry_xprime (d1 := d1) hlen hL0 hq hd0e (by omega) hn).1
    rw [← hN] at hx2
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col _ (r + L) = (_, _, 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hCLN : CL N r = Lc ++ [r + L] := by
    rw [CL_N2 hlen hL0 hq hd0e hn hXu hxbr he2r hIU hxcN hrx, hCLM]
  -- `D = DepS M {o(r)}` misses the counted children of `r` and `v(r)`
  have hoff := t2_off hlen hL0 hq hd0e hn hXu hxbr hrb he2r hIU I.cons hCN hRN
  have hnoD : ∀ b i, DepS M (fun b i => b = true ∧ i = r) b i → i < M.length → rk true r ≤ rk b i := by
    intro b i hD hi
    obtain ⟨b', i', ⟨rfl, rfl⟩, hle⟩ := depS_rk_ex I.rank hD hi
    exact hle
  have hrM : r < M.length := by omega
  have hvr : σ.v r = ρ.v r := (hoff r hrx).2 (fun hD => by
    have h1 := hnoD false r hD hrM
    have h2' := (I.rank r hrM).1
    omega)
  have hLc : ∀ d ∈ Lc, d < r + L ∧ σ.o d = ρ.o d := by
    intro d hd
    have hdCL : d ∈ CL M r := by rw [hCLM]; simp [hd]
    have hdc := cl_mem_children hdCL
    have hcnt : Counted M r d := by simpa using (List.mem_filter.mp hdCL).2
    have hdx : d < r + L := by
      have hsort := cl_sorted M r
      rw [hCLM] at hsort
      exact (List.pairwise_append.mp hsort).2.2 d hd (r + L) (by simp)
    refine ⟨hdx, (hoff d hdx).1 (fun hD => ?_)⟩
    have h1 := hnoD true d hD (by omega)
    have h2' := (I.rank r hrM).2.1 d hdc hcnt.1 hcnt.2
    omega
  -- the copy root `x′`
  have hCR := t2CopyResV3 hM hS I hz h2 r L hlen hr
  have hm : n - 1 + 1 = n := by omega
  have hBEP : BumpE2 P := by rw [hP, ← hexp (n - 1)]; exact (sInvX_expand hX (n - 1)).loc.2.2.1
  obtain ⟨hKV, hB', hV', hVV⟩ := hCR n hn σ ρP hCN hCP hGP
  have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP
  have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hX.r0p hX.loc.1
  have hF := copy_facts_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP hCN hCP hGP hRP hK hKV hRK hB' hV' hVV
  have hox := o_copy_root hCN hCP hGP hF hrP hxN hV' hVV rfl
  -- `v(x′) = V + 1`
  have hvx : σ.v (r + L) = succ (ρ.v r) := by
    have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
    rcases vx_eq hlen hL0 hA hq hd0e hn hd1e he2r h1lt hrb hr1 (fun h => absurd rfl h) I.be hJ hX.r0p I.uat hUN
      I.cons I.good hCN hRN with h | ⟨h, _⟩
    · rw [h, add_one_eq_succ (I.good.ot_v r hrM)]
    · exact absurd rfl h
  rw [hvx] at hox
  -- the frame of `r` in `N`
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hrM
  rw [hCLM] at hsM hpM
  simp only [List.map_append, List.map_singleton] at hsM hpM
  have hxM : r + L < M.length := by omega
  have hoxM : ρ.o (r + L) = psi (ρ.v (r + L)) z z := by
    rw [o_cl_eq I.cons I.good hxM]
    have : CL M (r + L) = [] := by
      unfold CL; rw [children_last_nil hlen]; rfl
    rw [this]; rfl
  have hVot := I.good.ot_v r hrM
  have hshOT : isOT (psi (succ (ρ.v r)) (sh (ρP.v r) (succ (ρ.v r))
      (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o)))) z) = true := by
    have hPo : isOT (psi (ρP.v r) (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o))) z) = true := by
      rw [← o_cl_eq hCP hGP hrP]; exact hGP.ot_o r hrP
    have := isOT_shTop (V' := succ (ρ.v r)) (hGP.ot_v r hrP) (by rw [← hvx]; exact hV') (by rw [← hvx]; exact hVV)
      hPo (le_refl _)
    rwa [shf_self] at this
  have hsN : ∀ c ∈ CL N r, Single (σ.o c) := by
    intro c hc
    rw [hCLN] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [(hLc c hc).2]; exact hsM _ (List.mem_append_left _ (List.mem_map_of_mem hc))
    · simp at hc; rw [hc, hox]; exact ⟨hshOT, _, _, rfl⟩
  have hpN : ((CL N r).map σ.o).Pairwise (fun a b => b ≤ a) := by
    rw [hCLN, List.map_append, List.map_singleton, List.map_congr_left (fun d hd => (hLc d hd).2)]
    have hp1 := List.pairwise_append.mp hpM
    refine List.pairwise_append.mpr ⟨hp1.1, by simp, fun t ht b hb => ?_⟩
    simp at hb; rw [hb, hox]
    refine le_trans (le_of_lt ?_) (hp1.2.2 t ht (ρ.o (r + L)) (by simp))
    rw [hoxM, psi_lt_psi_z_iff]; left; exact hks1
  have hform := o_last_form hCN hrN (by rw [hvr]; exact hVot) hCLN hsN hpN hox
  rw [hform, hvr, List.map_congr_left (fun d hd => (hLc d hd).2)]

theorem seed_r_value_qrV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) (hRes : QRRel M ρ r L Lc)
    {τ0 : Valn} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : ∃ rk0, Rk (M.take (r + L)) rk0) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
        σ.o r = psi (ρ.v r) (seqZ (ρ.v r) (t2B (ρ.v r) ρ Lc) (t2W1 (M.take (r + L)) (ρ.v r) τ0 r) (n - 2)) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set V := ρ.v r with hVdef
  set B := t2B V ρ Lc with hBdef
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  have hxM : r + L < M.length := by omega
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
  -- the M side: the summands of `B` are at least `Ω_s`
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hrM
  rw [hCLM] at hsM hpM
  simp only [List.map_append, List.map_singleton] at hsM hpM
  have hoxM : ρ.o (r + L) = psi (ρ.v (r + L)) z z := by
    rw [o_cl_eq I.cons I.good hxM]
    have : CL M (r + L) = [] := by
      unfold CL; rw [children_last_nil hlen]; rfl
    rw [this]; rfl
  have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht))
    (List.pairwise_append.mp hpM).1
  have hBc : ∀ q ∈ summands B, psi (ρ.v (r + L)) z z ≤ q := by
    apply spArg_summands_ge ⟨_, _, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq; rw [← hoxM]
      exact (List.pairwise_append.mp hpM).2.2 q hq _ (by simp)
    · simp [summands]
  have hBot : isOT B = true := by
    rw [hBdef]; unfold t2B
    exact isOT_arg (I.fo r hrM Lc (r + L) [] (by rw [hCLM]))
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ihs =>
  intro hGlow σ hCN
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  have hks1 : succ V < ρ.v (r + L) := by rw [succ_eq_addN_one]; exact hRes.ks 1
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · -- `n = 2`: the base `P = M.take x`
    have hn2 : n = 2 := by omega
    subst hn2
    have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
    have hCP : Cons (TRIO.gexp M r L d0 d1 1) τ0 := by rw [hP1]; exact hC0
    have hGP : Good3 (TRIO.gexp M r L d0 d1 1) τ0 := hGlow 1 (le_refl 1) (by omega) τ0 hCP
    obtain ⟨rk0, hRk0⟩ := hR0
    have hRP : Rk (TRIO.gexp M r L d0 d1 1) rk0 := by rw [hP1]; exact hRk0
    have h := o_r_level_qrV3 hM hS I Ctx hz h2 hlen hr hq hXu hCLM (le_refl 2) hCN hRN hCP hGP hRP hks1
    rw [← hd0def, ← hd1def] at h
    rw [show (2 - 1 : Nat) = 1 from rfl, hP1] at h
    rw [h]
    show psi V (step V B (succ V) (t2W1 (M.take (r + L)) V τ0 r) z) z = psi V (seqZ V B _ 0) z
    rw [step_app_leaf hBot (hRes.w1 τ0 hC0)]
    · rfl
    · intro hBz
      have hl : last B ∈ summands B := last_mem_summands hBz
      refine le_trans (le_of_lt ?_) (hBc _ hl)
      rw [psi_lt_psi_z_iff]; left; exact hks1
  · -- `n ≥ 3`: from `M[n − 1]`
    obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
    have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
    have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
    have hP := ihs (n - 1) (by omega) (by omega) (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP
    have h := o_r_level_qrV3 hM hS I Ctx hz h2 hlen hr hq hXu hCLM hn hCN hRN hCP hGP hRP hks1
    have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
    have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
      have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
      omega
    have hform := o_cl_eq hCP hGP hrP
    rw [hP] at hform
    simp only [psi.injEq] at hform
    have h21 := hform.2.1
    rw [← hform.1] at h21
    rw [← hd0def, ← hd1def] at h
    rw [h, ← hform.1, ← h21]
    show psi V (step V B (succ V) (sh V (succ V) (seqZ V B _ (n - 1 - 2))) z) z = psi V (seqZ V B _ (n - 2)) z
    rw [show n - 2 = (n - 1 - 2) + 1 by omega]
    rfl

theorem qn_frameV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q])
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = Lc ++ [q] ∧
    (∀ d ∈ Lc, σ.o d = ρ.o d) ∧ σ.v r = ρ.v r ∧
    σ.v (r + L) = add (ρ.v r) (last (σ.v q)) ∧
    σ.o q = psi (σ.v q) (step (σ.v q) z (σ.v (r + L)) (sh (ρP.v r) (σ.v (r + L)) (spArg (ρP.v r) z
        (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1))
          r).map ρP.o)))) z) z ∧
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) q = [r + L] := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hqc := cl_mem_children hqcl
  have hpq : par M 0 q = some r := (mem_children_iff.mp hqc).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  obtain ⟨qp, rfl⟩ : ∃ qp, q = r + qp := ⟨q - r, by omega⟩
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hqcnt : Counted M r (r + qp) := by simpa using (List.mem_filter.mp hqcl).2
  have hqx : r + qp < r + L := par_lt M 0 _ _ hq
  have hqp : qp < L := by omega
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
  obtain ⟨Txb, Tqb, _, Tclq, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq
  have hqb : ∀ i, par M 0 (r + qp) = some i → col M (r + qp) ≠ bump M i := by
    intro i hi; rw [hpq] at hi; cases hi; exact Tqb
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hm1 : 1 ≤ n := by omega
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hqN : r + qp < N.length := by omega
  have hrM : r < M.length := by omega
  have hqM : r + qp < M.length := by omega
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
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hcolN : ∀ i, i < r + L → col N i = col M i := fun i hi => col_gexp_pre hlen hm1 hi
  have hbN : ∀ c, c < r + L → bump N c = bump M c := fun c hc => by
    unfold bump; rw [entry_gexp_pre hlen hm1 0 hc, entry_gexp_pre hlen hm1 1 hc]
  have hchN : ∀ i, i < r + L → children N i = children M i :=
    fun i hi => children_N2Q hlen hL0 hA hq hqp hd0e (by omega) hn hi
  have hIUt : ∀ c, c < r + L → c ≠ r + qp → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc hcq htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_eq_of (hchN c hc) (fun d hd => hcolN d (by
      have := (mem_children hd).2
      by_contra h'
      have hdx : d = r + L := by omega
      have := (mem_children_iff.mp hd).2; rw [hdx, hq] at this; exact hcq (Option.some.inj this).symm))
      (hbN c hc)]
    exact htM
  have hcntN : ∀ i c, i < r + L → c < r + L → c ≠ r + qp → (Counted N i c ↔ Counted M i c) :=
    fun i c hi hc hcq => counted_NQ hlen hL0 hA hq hqp hd0e hn Txb hIUt hi hc hcq
  -- `x′` counts at `q`, `q` counts at `r`
  have hx2N : entry N 2 (r + L) = 0 := by
    rw [(entry_xprimeQ hlen hL0 hA hq hqp hd0e (by omega) hn).1, he2r]
  have hxcnt : Counted N (r + qp) (r + L) := by
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col N (r + L) = (entry N 0 (r + qp) + 1, entry N 1 (r + qp), 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hq⟩
  have hsplitq := children_split_x hlen hxq
  have hCLNq : CL N (r + qp) = [r + L] := by
    unfold CL
    rw [hchN _ hqx, hsplitq, List.filter_append]
    have h1 : List.filter (fun c => decide (Counted N (r + qp) c))
        (List.filter (fun d => decide (d < r + L)) (children M (r + qp))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hcn
      have hc' := List.mem_filter.mp hc
      have hcx : c < r + L := by simpa using hc'.2
      have hcq : c ≠ r + qp := by have := (mem_children hc'.1).1; omega
      have hcntM : Counted M (r + qp) c := (hcntN _ c hqx hcx hcq).mp (by simpa using hcn)
      have hin : c ∈ CL M (r + qp) := by unfold CL; exact List.mem_filter.mpr ⟨hc'.1, by simpa using hcntM⟩
      rw [Tclq] at hin; simp at hin
    rw [h1]; simp [hxcnt]
  have hqcntN : Counted N r (r + qp) := by
    refine ⟨by rw [hcolN _ hqx, hbN r (by omega)]; exact hqcnt.1, fun ⟨_, ht⟩ => ?_⟩
    unfold topped at ht
    rw [hchN _ hqx, hsplitq] at ht
    simp at ht
    exact hxcnt.1 ht
  have hCLN : CL N r = Lc ++ [r + qp] := by
    rw [← hCLM]; unfold CL
    rw [hchN r (by omega)]
    apply List.filter_congr
    intro c hc
    by_cases hcq : c = r + qp
    · rw [hcq]; simp [hqcntN, hqcnt]
    · have hcx : c < r + L := by
        have hcl := (mem_children hc).2
        by_contra h'
        have hcx' : c = r + L := by omega
        rw [hcx'] at hc
        have := (mem_children_iff.mp hc).2; rw [hq] at this
        have := Option.some.inj this; omega
      simp only [decide_eq_decide]
      exact hcntN r c (by omega) hcx hcq
  -- `N` agrees with `M` outside `D = DepS M {v(q), o(r)}`
  have hnu : upg M (r + L - 1) ≠ some (r + L) := fun h =>
    upg_not_x hlen hA hq Txb I.be h (le_refl _) (by omega)
  have hupgN : ∀ i, i < r + L → upg N i = upg M i := fun i hi =>
    upg_NQ hlen hL0 hA hq hqp hd0e hn he2r hnu hi
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hq] at h'; exact (Option.some.inj h').symm
  have hbjN : ∀ i j, i < r + L → j ∈ children N i → r + L ≤ j → col N j ≠ bump N i := by
    intro i j hi hj hjx hb
    have hjl := (mem_children hj).2
    rw [hlN] at hjl
    rcases par0_tail2Q hlen hL0 hA hq hqp hd0e (by omega) hjx hjl with ⟨hjx', _⟩ | ⟨p', hp', hp'1, _⟩
    · rw [hjx'] at hb
      have := e2_of_col (show col N (r + L) = (entry N 0 i + 1, entry N 1 i, 1) from hb)
      omega
    · rw [(mem_children_iff.mp hj).2] at hp'; cases hp'; omega
  have hoff := t2_off_gen (S := SQ (r + qp) r) (bnd := r + L) I.cons hCN hRN (by omega) (by rw [hlN]; omega)
    (fun i hi _ => hchN i hi) (DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (Or.inr (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i hqi hb => by have h' := (mem_children_iff.mp hqi).2; rw [hpq] at h'; cases h'; exact Tqb hb)
    (fun y i hi => entry_gexp_pre hlen (by omega) y hi) (fun i hi => par_gexp_pre hlen (by omega) 1 hi)
    (fun i hi _ => hupgN i hi)
    (fun i c hi hd hc hcx => hcntN i c hi hcx (by
      intro hcq; apply hd; apply DepS.seed; right; refine ⟨rfl, ?_⟩
      have h' := (mem_children_iff.mp hc).2; rw [hcq, hpq] at h'; exact (Option.some.inj h').symm))
    (fun i c hi hc hcx => by
      obtain ⟨_, rfl⟩ := hxc i c hc hcx
      exact DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i k hi hk hkx => (upg_not_x hlen hA hq Txb I.be hk hkx hi).elim)
    hbjN
    (fun i j hi hj hjx _ => by
      obtain ⟨_, rfl⟩ := hxc i j hj hjx
      exact DepS.seed (Or.inl ⟨rfl, rfl⟩))
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc j k hk hkx
      have h' := (mem_children_iff.mp hj).2; rw [hpq] at h'; cases h'
      exact absurd hjb Tqb)
  have htq : topped M (r + qp) = true := by
    unfold topped; rw [hsplitq]; simp [Txb]
  have hinv : ∀ {b i}, DepS M (SQ (r + qp) r) b i → i < M.length → Anc0 M (r + qp) i ∨ rk true r ≤ rk b i :=
    fun h hi => depS_SQ_inv I.rank hpq Tqb hqcnt.2 htq he2r h hi
  have hvr : σ.v r = ρ.v r := (hoff r (by omega)).2 (fun hD => by
    rcases hinv hD hrM with hAq | hle
    · have := hAq.le; omega
    · have := (I.rank r hrM).1; omega)
  have hLc : ∀ d ∈ Lc, σ.o d = ρ.o d := by
    intro d hd
    have hdCL : d ∈ CL M r := by rw [hCLM]; simp [hd]
    have hdc := cl_mem_children hdCL
    have hcnt : Counted M r d := by simpa using (List.mem_filter.mp hdCL).2
    have hdq : d < r + qp := by
      have hsort := cl_sorted M r
      rw [hCLM] at hsort
      exact (List.pairwise_append.mp hsort).2.2 d hd (r + qp) (by simp)
    refine (hoff d (by omega)).1 (fun hD => ?_)
    rcases hinv hD (by omega) with hAq | hle
    · have := hAq.le; omega
    · have := (I.rank r hrM).2.1 d hdc hcnt.1 hcnt.2; omega
  -- the copy root `x′`
  have hCR := t2CopyResV3 hM hS I hz h2 r L hlen hr
  have hBEP : BumpE2 P := by rw [hP, ← hexp (n - 1)]; exact (sInvX_expand hX (n - 1)).loc.2.2.1
  obtain ⟨hKV, hB', hV', hVV⟩ := hCR n hn σ ρP hCN hCP hGP
  have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP
  have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hX.r0p hX.loc.1
  have hF := copy_facts_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP hCN hCP hGP hRP hK hKV hRK hB' hV' hVV
  have hox := o_copy_root hCN hCP hGP hF hrP hxN hV' hVV rfl
  -- `v(x′) = a + last(v_N(q))`
  have hvq := vq_N hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 (by omega) Txb I.be I.uat hUN I.cons I.good hCN hRN
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hvx : σ.v (r + L) = add (ρ.v r) (last (σ.v (r + qp))) := by
    rw [(hCN (r + L) hxN).2]; unfold vRhs
    have he1 : entry N 1 (r + L) ≠ 0 := by
      have := entry1_xN hlen hL0 hA hq hd0e hn hd1e
      rw [← hN] at this; rw [this]; omega
    rw [if_neg he1, if_pos hx2N]
    have hp1 := par1_xN hlen hL0 hA hq hd0e hn hd1e
    rw [hr1, ← hN] at hp1
    have hu := upg_N_x_q hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 (by omega) Txb hJ hX.r0p I.be
    rw [← hN] at hu
    rw [hp1, hu]
    show sf (add (σ.v r) (last (σ.v (r + qp)))) = _
    rw [hvr, sf_ot (isOT_add hVot (isOT_last hvq.1))]
  -- the frame of `q`: only `x′`
  have hPo : isOT (psi (ρP.v r) (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o))) z) = true := by
    rw [← o_cl_eq hCP hGP hrP]; exact hGP.ot_o r hrP
  have hxOT : isOT (psi (σ.v (r + L)) (sh (ρP.v r) (σ.v (r + L))
      (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o)))) z) = true := by
    have := isOT_shTop (V' := σ.v (r + L)) (hGP.ot_v r hrP) hV' hVV hPo (le_refl _)
    rwa [shf_self] at this
  have hoq := o_last_form (Lc := []) hCN hqN hvq.1 (by rw [hCLNq]; rfl)
    (fun c hc => by rw [hCLNq] at hc; simp at hc; rw [hc, hox]; exact ⟨hxOT, _, _, rfl⟩)
    (by rw [hCLNq]; simp) hox
  exact ⟨hCLN, hLc, hvr, hvx, by rw [hoq]; rfl, hCLNq⟩

theorem o_r_level_qnV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q])
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    (hqOT : isOT (σ.o q) = true)
    (hdecN : ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
      σ.o).Pairwise (fun a b => b ≤ a)) :
    σ.v (r + L) = add (ρ.v r) (last (σ.v q)) ∧
    σ.o r = psi (ρ.v r) (step (ρ.v r) (spArg (ρ.v r) z (sumN (Lc.map ρ.o))) (σ.v q)
      (step (σ.v q) z (σ.v (r + L)) (sh (ρP.v r) (σ.v (r + L)) (spArg (ρP.v r) z
        (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1))
          r).map ρP.o)))) z) z) z := by
  obtain ⟨hCLN, hLc, hvr, hvx, hoq, _⟩ :=
    qn_frameV3 hM hS I Ctx hz h2 hlen hr hq hqr hCLM hn hCN hRN hCP hGP hRP
  refine ⟨hvx, ?_⟩
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hrM : r < M.length := by omega
  have hrN : r < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n).length := by
    have := TRIO.gexp_length (M := M) (j0 := r) (Lb := L) (d0 := entry M 0 (r + L) - entry M 0 r)
      (d1 := entry M 1 (r + L) - entry M 1 r) (n := n) hlen
    have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
    omega
  have hsN : ∀ c ∈ CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r,
      Single (σ.o c) := by
    intro c hc
    rw [hCLN] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [hLc c hc]
      exact single_o I.cons I.good (mem_children (cl_mem_children (show c ∈ CL M r by rw [hCLM]; simp [hc]))).2
    · simp at hc; rw [hc]; exact ⟨hqOT, _, _, hoq⟩
  have hor := o_last_form hCN hrN (by rw [hvr]; exact I.good.ot_v r hrM) hCLN hsN hdecN hoq
  rw [hor, hvr, List.map_congr_left hLc]

theorem seed_r_value_qnV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) (hRes : QNRel M ρ r L q Lc)
    {τ0 : Valn} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : ∃ rk0, Rk (M.take (r + L)) rk0)
    (hv0 : τ0.v r = ρ.v r) {t1 : T}
    (ht1 : spArg (τ0.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z))
    (hch : ∀ k, ρ.v r < tqN (ρ.v r) (qnS M ρ r L q) t1 k ∧
      ¬ shf (ρ.v r) (qnS M ρ r L q) (tqN (ρ.v r) (qnS M ρ r L q) t1 k) < succ (qnS M ρ r L q)) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      isOT (σ.o q) = true →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
        σ.o r = psi (ρ.v r) (app (t2B (ρ.v r) ρ Lc)
          (psi (tqN (ρ.v r) (qnS M ρ r L q) t1 (n - 1)) z z)) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set V := ρ.v r with hVdef
  set B := t2B V ρ Lc with hBdef
  set s' := qnS M ρ r L q with hs'def
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hpq : par M 0 q = some r := (mem_children_iff.mp (cl_mem_children hqcl)).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
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
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ihs =>
  intro hGlow σ hCN hqOT hdecN
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  have hvq : σ.v q = s' := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  -- one level from `M[n − 1]`
  have key : ∀ (ρP : Valn) (rkP : Bool → Nat → Nat), Cons (TRIO.gexp M r L d0 d1 (n - 1)) ρP →
      Good3 (TRIO.gexp M r L d0 d1 (n - 1)) ρP → Rk (TRIO.gexp M r L d0 d1 (n - 1)) rkP → ρP.v r = V →
      spArg (ρP.v r) z (sumN ((CL (TRIO.gexp M r L d0 d1 (n - 1)) r).map ρP.o)) =
        app B (psi (tqN V s' t1 (n - 2)) z z) →
      σ.o r = psi V (app B (psi (tqN V s' t1 (n - 1)) z z)) z := by
    intro ρP rkP hCP hGP hRP hvP hXP
    obtain ⟨hvx, hor⟩ := o_r_level_qnV3 hM hS I Ctx hz h2 hlen hr hq hqr hCLM hn hCN hRN hCP hGP hRP hqOT hdecN
    have hvx' : σ.v (r + L) = s' := by rw [hvx, hvq]; exact qnS_vxs M ρ r L q
    rw [hor, hvx', hvq, hXP, hvP]
    obtain ⟨hat, hts⟩ := hch (n - 2)
    rw [show n - 1 = (n - 2) + 1 by omega]
    exact congrArg (fun X => psi V X z) (qn_step (qnS_ot I (by omega) L q) (qnS_gt M ρ r L q) hRes.σB hRes.Bc hat hts)
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · -- `n = 2`: the base `P = M.take x`
    have hn2 : n = 2 := by omega
    subst hn2
    have hP1 : TRIO.gexp M r L d0 d1 (2 - 1) = M.take (r + L) := gexp_one_gen hlen
    have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [hP1]; exact hC0
    have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := hGlow 1 (le_refl 1) (by omega) τ0 hCP
    obtain ⟨rk0, hRk0⟩ := hR0
    have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [hP1]; exact hRk0
    exact key τ0 rk0 hCP hGP hRP hv0 (by rw [hP1]; exact ht1)
  · -- `n ≥ 3`: from `M[n − 1]`
    obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
    have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
    have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
    have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
    have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
    have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by omega
    have hqP : q < (TRIO.gexp M r L d0 d1 (n - 1)).length := by omega
    have hP := ihs (n - 1) (by omega) (by omega) (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP
      (hGP.ot_o q hqP) (by rw [← cvals_eq_mapC hCP]; exact hGP.dec r hrP)
    have hform := o_cl_eq hCP hGP hrP
    rw [hP] at hform
    simp only [psi.injEq] at hform
    refine key _ rkP hCP hGP hRP hform.1.symm ?_
    rw [← hform.2.1, show n - 1 - 1 = n - 2 by omega]

theorem sv_frameV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (htP : topped (M.take (r + L)) r = false)
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hG0 : Good3 (M.take (r + L)) τ0)
    (hR0 : Rk (M.take (r + L)) rk0) :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r =
      CL (M.take (r + L)) r ++ [r + L] ∧
    (∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d) ∧ σ.v r = τ0.v r ∧
    σ.o (r + L) = psi (succ (ρ.v r)) (sh (ρP.v r) (succ (ρ.v r)) (spArg (ρP.v r) z (sumN ((CL (TRIO.gexp M r L
        (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) r).map ρP.o)))) z ∧
    isOT (σ.o (r + L)) = true := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨hcntN, hcntP⟩ := sv_cnt hM hS I hz h2 hlen hr hq hux htP hn
  have hag := sv_agree hM hS I hz h2 hlen hr hq hux htP hn hCN hC0 hR0
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
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
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hrM : r < M.length := by omega
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hrT : r < (M.take (r + L)).length := by omega
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  -- the counted children of `r` in `N`
  have hxcN : Counted N r (r + L) := by
    have hx2 := (entry_xprime (d1 := d1) hlen hL0 hq hd0e (by omega) hn).1
    rw [← hN] at hx2
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col _ (r + L) = (_, _, 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hxrc : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have hCLN : CL N r = CL (M.take (r + L)) r ++ [r + L] := by
    unfold CL
    rw [children_N2 hlen hL0 hq hd0e (by omega) hn hrx, children_take]
    conv_lhs => rw [children_split_x hlen hxrc, List.filter_append]
    rw [show List.filter (fun c => decide (Counted N r c)) [r + L] = [r + L] by simp [hxcN]]
    congr 1
    apply List.filter_congr
    intro c hc
    have hcx : c < r + L := by simpa using (List.mem_filter.mp hc).2
    simp only [decide_eq_decide]
    exact (hcntN r c hrx hcx).trans (hcntP r c hrx hcx).symm
  -- the values of the earlier children are those of `M.take x`
  have hval : ∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d := by
    intro d hd
    have hdc := cl_mem_children hd
    have hcnt : Counted (M.take (r + L)) r d := by simpa using (List.mem_filter.mp hd).2
    exact ((hag d (by have := (mem_children hdc).2; omega)).1
      ((hR0 r hrT).2.1 d hdc hcnt.1 hcnt.2)).symm
  have hvr : σ.v r = τ0.v r := ((hag r hrx).2 (hR0 r hrT).1).symm
  -- the copy root `x′`
  have hCR := t2CopyResV3 hM hS I hz h2 r L hlen hr
  have hBEP : BumpE2 P := by rw [hP, ← hexp (n - 1)]; exact (sInvX_expand hX (n - 1)).loc.2.2.1
  obtain ⟨hKV, hB', hV', hVV⟩ := hCR n hn σ ρP hCN hCP hGP
  have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP
  have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hX.r0p hX.loc.1
  have hF := copy_facts_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP hCN hCP hGP hRP hK hKV hRK hB' hV' hVV
  have hox := o_copy_root hCN hCP hGP hF hrP hxN hV' hVV rfl
  have hvx : σ.v (r + L) = succ (ρ.v r) := by
    have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
    rcases vx_eq hlen hL0 hA hq hd0e hn hd1e he2r h1lt hrb hr1 (fun h => absurd rfl h) I.be hJ hX.r0p I.uat hUN
      I.cons I.good hCN hRN with h | ⟨h, _⟩
    · rw [h, add_one_eq_succ (I.good.ot_v r hrM)]
    · exact absurd rfl h
  rw [hvx] at hox
  have hshOT : isOT (psi (succ (ρ.v r)) (sh (ρP.v r) (succ (ρ.v r))
      (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o)))) z) = true := by
    have hPo : isOT (psi (ρP.v r) (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o))) z) = true := by
      rw [← o_cl_eq hCP hGP hrP]; exact hGP.ot_o r hrP
    have := isOT_shTop (V' := succ (ρ.v r)) (hGP.ot_v r hrP) (by rw [← hvx]; exact hV') (by rw [← hvx]; exact hVV)
      hPo (le_refl _)
    rwa [shf_self] at this
  exact ⟨hCLN, hval, hvr, hox, by rw [hox]; exact hshOT⟩

theorem o_r_level_svV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (htP : topped (M.take (r + L)) r = false)
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hG0 : Good3 (M.take (r + L)) τ0)
    (hR0 : Rk (M.take (r + L)) rk0)
    (hdecN : ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
      σ.o).Pairwise (fun a b => b ≤ a)) :
    σ.o r = psi (τ0.v r) (step (τ0.v r) (spArg (τ0.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o)))
      (succ (ρ.v r)) (sh (ρP.v r) (succ (ρ.v r)) (spArg (ρP.v r) z (sumN ((CL (TRIO.gexp M r L
        (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) r).map ρP.o)))) z) z := by
  obtain ⟨hCLN, hval, hvr, hox, hxOT⟩ :=
    sv_frameV3 hM hS I Ctx hz h2 hlen hr hq hux htP hn hCN hRN hCP hGP hRP hC0 hG0 hR0
  have hrN : r < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n).length := by
    have := TRIO.gexp_length (M := M) (j0 := r) (Lb := L) (d0 := entry M 0 (r + L) - entry M 0 r)
      (d1 := entry M 1 (r + L) - entry M 1 r) (n := n) hlen
    have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
    have := par_lt M 0 _ _ hq; omega
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; have := par_lt M 0 _ _ hq; omega
  have hsN : ∀ c ∈ CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r,
      Single (σ.o c) := by
    intro c hc
    rw [hCLN] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [hval c hc]
      exact single_o hC0 hG0 (mem_children (cl_mem_children hc)).2
    · simp at hc; rw [hc, hox]; rw [hox] at hxOT; exact ⟨hxOT, _, _, rfl⟩
  have hform := o_last_form hCN hrN (by rw [hvr]; exact hG0.ot_v r hrT) hCLN hsN hdecN hox
  rw [hform, hvr, List.map_congr_left hval]

theorem seed_r_value_svV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (hRes : SVRel M ρ r L)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : Rk (M.take (r + L)) rk0) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
        σ.o r = psi (ρ.v r) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ0) (n - 1)) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hrx : r < r + L := par_lt M 0 _ _ hq
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
  have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
  have hv0 : τ0.v r = ρ.v r := v_take_of_untopped I hlen (par_lt M 0 _ _ hq) (topP_sv hlen I.z2 I.z1 hr hq hux) hC0
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ihs =>
  intro hGlow σ hCN hdecN
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  have hG0 : Good3 (M.take (r + L)) τ0 := by
    have h := hGlow 1 (le_refl 1) (by omega) τ0 (by rw [hP1]; exact hC0)
    rwa [hP1] at h
  have key : ∀ (ρP : Valn) (rkP : Bool → Nat → Nat), Cons (TRIO.gexp M r L d0 d1 (n - 1)) ρP →
      Good3 (TRIO.gexp M r L d0 d1 (n - 1)) ρP → Rk (TRIO.gexp M r L d0 d1 (n - 1)) rkP → ρP.v r = (ρ.v r) →
      spArg (ρP.v r) z (sumN ((CL (TRIO.gexp M r L d0 d1 (n - 1)) r).map ρP.o)) =
        shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ0) (n - 2) →
      σ.o r = psi (ρ.v r) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ0) (n - 1)) z := by
    intro ρP rkP hCP hGP hRP hvP hXP
    have h := o_r_level_svV3 hM hS I Ctx hz h2 hlen hr hq hux (topP_sv hlen I.z2 I.z1 hr hq hux) hn hCN hRN hCP hGP hRP hC0 hG0 hR0 hdecN
    have hX1 : t2X1 M r L τ0 = spArg (ρ.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o)) := by
      unfold t2X1; rw [hv0]
    rw [h, hXP, hvP, hv0, show n - 1 = (n - 2) + 1 by omega, ← hX1, hRes.rw τ0 hC0 (n - 2)]
    rfl
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have hn2 : n = 2 := by omega
    subst hn2
    have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show 2 - 1 = 1 from rfl, hP1]; exact hC0
    have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show 2 - 1 = 1 from rfl, hP1]; exact hG0
    have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show 2 - 1 = 1 from rfl, hP1]; exact hR0
    exact key τ0 rk0 hCP hGP hRP hv0 (by rw [show 2 - 1 = 1 from rfl, hP1]; rfl)
  · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
    have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
    have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
    have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
    have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
    have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by omega
    have hP := ihs (n - 1) (by omega) (by omega) (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP
      (by rw [← cvals_eq_mapC hCP]; exact hGP.dec r hrP)
    have hform := o_cl_eq hCP hGP hrP
    rw [hP] at hform
    simp only [psi.injEq] at hform
    refine key _ rkP hCP hGP hRP hform.1.symm ?_
    rw [← hform.2.1, show n - 1 - 1 = n - 2 by omega]

theorem C_frameV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    (hqP : ¬ Counted (M.take (r + L)) r q) (hun : upg M (r + L - 1) = none)
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hG0 : Good3 (M.take (r + L)) τ0)
    (hR0 : Rk (M.take (r + L)) rk0) (hv0 : τ0.v r = ρ.v r) (hvq0 : τ0.v q = σ.v q) :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r =
      CL (M.take (r + L)) r ++ [q] ∧
    (∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d) ∧ σ.v r = ρ.v r ∧
    σ.v (r + L) = add (ρ.v r) (last (σ.v q)) ∧
    σ.o q = psi (σ.v q) (step (σ.v q) z (σ.v (r + L)) (sh (ρP.v r) (σ.v (r + L)) (spArg (ρP.v r) z
        (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1))
          r).map ρP.o)))) z) z ∧
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) q = [r + L] := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrx0 : r < r + L := par_lt M 2 _ _ hr
  have hA0 : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have hrq0 : Anc0 M r q := anc0_par hA0 (by have := par_lt M 0 _ _ hq; omega) hq
  obtain ⟨pq, hpq0⟩ := par0_of_anc hrq0 (fun h => hqr h.symm)
  have hrq : r < q := by have := hrq0.le; omega
  obtain ⟨qp, rfl⟩ : ∃ qp, q = r + qp := ⟨q - r, by omega⟩
  have hpq' := hpq0
  obtain ⟨Txb0, Tqb0, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq'
  have hpq : par M 0 (r + qp) = some r := by
    have he0lt' := anc0_e0_lt hA0 (by omega)
    obtain ⟨he2r', h1lt'⟩ := par2_facts hX.z2 (by omega) hr
    have hqb' : ∀ i, par M 0 (r + qp) = some i → col M (r + qp) ≠ bump M i := by
      intro i hi; rw [hpq0] at hi; cases hi; exact Tqb0
    exact qn_par0_q hlen (by omega) hA0 hq (d0 := entry M 0 (r + L) - entry M 0 r) (by omega) (le_refl 2)
      (d1 := entry M 1 (r + L) - entry M 1 r) (by omega) he2r' h1lt' hqb'
      (par1_x_r (by omega) I.z2 I.z1 hr) hqr Txb0 hJ hX.r0p I.be
  rw [hpq] at hpq0; cases hpq0
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hqx : r + qp < r + L := par_lt M 0 _ _ hq
  have hqp : qp < L := by omega
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
  obtain ⟨Txb, Tqb, _, Tclq, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq
  have hqb : ∀ i, par M 0 (r + qp) = some i → col M (r + qp) ≠ bump M i := by
    intro i hi; rw [hpq] at hi; cases hi; exact Tqb
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hm1 : 1 ≤ n := by omega
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hqN : r + qp < N.length := by omega
  have hrM : r < M.length := by omega
  have hqM : r + qp < M.length := by omega
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
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hcolN : ∀ i, i < r + L → col N i = col M i := fun i hi => col_gexp_pre hlen hm1 hi
  have hbN : ∀ c, c < r + L → bump N c = bump M c := fun c hc => by
    unfold bump; rw [entry_gexp_pre hlen hm1 0 hc, entry_gexp_pre hlen hm1 1 hc]
  have hchN : ∀ i, i < r + L → children N i = children M i :=
    fun i hi => children_N2Q hlen hL0 hA hq hqp hd0e (by omega) hn hi
  have hIUt : ∀ c, c < r + L → c ≠ r + qp → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc hcq htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_eq_of (hchN c hc) (fun d hd => hcolN d (by
      have := (mem_children hd).2
      by_contra h'
      have hdx : d = r + L := by omega
      have := (mem_children_iff.mp hd).2; rw [hdx, hq] at this; exact hcq (Option.some.inj this).symm))
      (hbN c hc)]
    exact htM
  have hcntN : ∀ i c, i < r + L → c < r + L → c ≠ r + qp → (Counted N i c ↔ Counted M i c) :=
    fun i c hi hc hcq => counted_NQ hlen hL0 hA hq hqp hd0e hn Txb hIUt hi hc hcq
  -- `x′` counts at `q`, `q` counts at `r`
  have hx2N : entry N 2 (r + L) = 0 := by
    rw [(entry_xprimeQ hlen hL0 hA hq hqp hd0e (by omega) hn).1, he2r]
  have hxcnt : Counted N (r + qp) (r + L) := by
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col N (r + L) = (entry N 0 (r + qp) + 1, entry N 1 (r + qp), 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hq⟩
  have hsplitq := children_split_x hlen hxq
  have hCLNq : CL N (r + qp) = [r + L] := by
    unfold CL
    rw [hchN _ hqx, hsplitq, List.filter_append]
    have h1 : List.filter (fun c => decide (Counted N (r + qp) c))
        (List.filter (fun d => decide (d < r + L)) (children M (r + qp))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hcn
      have hc' := List.mem_filter.mp hc
      have hcx : c < r + L := by simpa using hc'.2
      have hcq : c ≠ r + qp := by have := (mem_children hc'.1).1; omega
      have hcntM : Counted M (r + qp) c := (hcntN _ c hqx hcx hcq).mp (by simpa using hcn)
      have hin : c ∈ CL M (r + qp) := by unfold CL; exact List.mem_filter.mpr ⟨hc'.1, by simpa using hcntM⟩
      rw [Tclq] at hin; simp at hin
    rw [h1]; simp [hxcnt]
  have hqcntN : Counted N r (r + qp) := by
    refine ⟨by rw [hcolN _ hqx, hbN r (by omega)]; exact Tqb, fun ⟨_, ht⟩ => ?_⟩
    unfold topped at ht
    rw [hchN _ hqx, hsplitq] at ht
    simp at ht
    exact hxcnt.1 ht
  have hnu : upg M (r + L - 1) ≠ some (r + L) := by rw [hun]; intro h; cases h
  have hupgN : ∀ i, i < r + L → upg N i = upg M i := fun i hi =>
    upg_NQ hlen hL0 hA hq hqp hd0e hn he2r hnu hi
  -- `M.take x` and `N` before `x`
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hrT : r < (M.take (r + L)).length := by omega
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hq] at h'; exact (Option.some.inj h').symm
  have hcntP : ∀ i c, i < r + L → c < r + L → c ≠ r + qp →
      (Counted (M.take (r + L)) i c ↔ Counted M i c) := by
    intro i c hi hc hcq
    unfold Counted
    have hu' : upg M (r + L - 1) ≠ some c := by rw [hun]; intro h; cases h
    rw [col_take M hc, bump_take M hi, isUpg_take_eq hlen hu' hc,
      topped_take_eq hlen hc (fun h => hcq (hxc c (r + L) h (le_refl _)).2)]
  have hrbP : ∀ i, r ∈ children (M.take (r + L)) i → col (M.take (r + L)) r ≠ bump (M.take (r + L)) i := by
    intro i hi hb
    have hi' : r ∈ children M i := by rw [children_take] at hi; exact (List.mem_filter.mp hi).1
    have hil : i < r := (mem_children hi').1
    rw [col_take M hrx0, bump_take M (by omega)] at hb
    have := e2_of_col (show col M r = (entry M 0 i + 1, entry M 1 i, 1) from hb); omega
  have hag := agree_by_rank (M' := M.take (r + L)) (ρ := σ) (ρ' := τ0)
    (fun b i => rk0 true r ≤ rk0 b i ∨ (b = true ∧ i = r + qp)) hR0
    (by
      intro i hi hE hvi hci
      rw [hlT] at hi
      have hir : i ≠ r := by intro e; rw [e] at hE; exact hE (Or.inl (le_refl _))
      have hiq : i ≠ r + qp := by intro e; exact hE (Or.inr ⟨rfl, e⟩)
      rw [(hC0 i (by rw [hlT]; exact hi)).1, (hCN i (by omega)).1]
      rw [oRhs_congr (ρ₂ := σ) hvi (fun c hc hb hu => hci c hc ⟨hb, hu⟩), ← hT]
      apply oRhs_takeX
      · intro c hc
        rw [hchN i hi] at hc
        by_contra h'
        exact hiq (hxc i c hc (by omega)).2
      · intro c hc
        rw [hchN i hi] at hc
        have hcx : c < r + L := by
          by_contra h'
          exact hiq (hxc i c hc (by omega)).2
        have hcq : c ≠ r + qp := by
          intro e; rw [e] at hc; rw [(mem_children_iff.mp hc).2] at hpq; cases hpq; exact hir rfl
        rw [hT]
        exact (hcntP i c hi hcx hcq).trans (hcntN i c hi hcx hcq).symm)
    (by
      intro i hi hE hp1 hup hbk
      rw [hlT] at hi
      by_cases hiq : i = r + qp
      · rw [hiq]; exact hvq0
      rw [(hC0 i (by rw [hlT]; exact hi)).2, (hCN i (by omega)).2]
      rw [vRhs_congr (ρ₂ := σ) (fun m h1 hm => hp1 m h1 hm) (fun k h1 h2 hk => hup k h1 h2 hk)
        (fun j hj h1 h2 hb k hk => hbk j hj h1 h2 hb k hk), ← hT]
      apply vRhs_takeX hi
      · by_cases hi1 : i + 1 < r + L
        · exact upg_take N hi1
        · have hix : i = r + L - 1 := by omega
          rw [hix, upg_take_last N (by omega) (by omega), hupgN _ (by omega), hun]
      · intro h2'
        rw [hchN i hi]
        refine ⟨fun c hc => ?_, fun j hj hjb c hc => ?_⟩
        · by_contra h'
          exact hiq (hxc i c hc (by omega)).2
        · have hjx : j < r + L := by
            by_contra h'
            exact hiq (hxc i j hj (by omega)).2
          have hjq : j ≠ r + qp := by
            intro e
            rw [e] at hjb hj
            have hpi := (mem_children_iff.mp hj).2
            rw [hpq] at hpi; cases hpi
            rw [hcolN _ hqx, hbN r (by omega)] at hjb
            exact Tqb hjb
          rw [hchN j hjx] at hc
          by_contra h'
          exact hjq (hxc j c hc (by omega)).2)
    (by
      intro i hi hE
      refine ⟨fun h => ?_, fun c hc hcnt h => ?_⟩
      · rcases h with h | ⟨h, _⟩
        · exact hE (Or.inl (le_trans h (le_of_lt (hR0 i hi).1)))
        · cases h
      · rcases h with h | ⟨_, hcq⟩
        · exact hE (Or.inl (le_trans h (le_of_lt ((hR0 i hi).2.1 c hc hcnt.1 hcnt.2))))
        · rw [hcq] at hc
          have hpi := (mem_children_iff.mp hc).2
          rw [par_take M 0 _ (by omega), hpq] at hpi; cases hpi
          exact hE (Or.inl (le_refl _)))
    (by
      intro i hi hE h1
      obtain ⟨hp1, hup, hbk⟩ := (hR0 i hi).2.2 h1
      have hE' : ¬ rk0 true r ≤ rk0 false i := fun h => hE (Or.inl h)
      refine ⟨fun m hm h => ?_, fun h2' k hk h => ?_, fun h2' j hj hjb k hk h => ?_⟩
      · rcases h with h | ⟨h, _⟩
        · exact hE' (le_trans h (le_of_lt (hp1 m hm)))
        · cases h
      · rcases h with h | ⟨h, _⟩
        · exact hE' (le_trans h (le_of_lt (hup h2' k hk)))
        · cases h
      · rcases h with h | ⟨_, hkq⟩
        · exact hE' (le_trans h (le_of_lt (hbk h2' j hj hjb k hk)))
        · rw [hkq] at hk
          have hpj := (mem_children_iff.mp hk).2
          rw [par_take M 0 _ (by omega), hpq] at hpj; cases hpj
          exact hrbP i hj hjb)
  have hval : ∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d := by
    intro d hd
    have hdc := cl_mem_children hd
    have hcnt : Counted (M.take (r + L)) r d := by simpa using (List.mem_filter.mp hd).2
    have hdq : d ≠ r + qp := by intro e; rw [e] at hcnt; exact hqP hcnt
    refine ((hag d (mem_children hdc).2).1 ?_).symm
    rintro (h | ⟨_, h⟩)
    · have := (hR0 r hrT).2.1 d hdc hcnt.1 hcnt.2; omega
    · exact hdq h
  have hvr : σ.v r = ρ.v r := by
    rw [← hv0]
    refine ((hag r hrT).2 ?_).symm
    rintro (h | ⟨h, _⟩)
    · have := (hR0 r hrT).1; omega
    · cases h
  -- the counted children of `r` in `N`
  have hqc : r + qp ∈ children M r := mem_children_iff.mpr ⟨by omega, hpq⟩
  have hqlast : children M r = (children M r).filter (fun d => decide (d < r + qp)) ++ [r + qp] := by
    apply split_last_max _ _ (children_sorted M r) hqc
    intro d hd
    by_contra hlt
    have hdx : d < r + L := by
      have := (mem_children hd).2
      by_contra h'
      have hd' : d = r + L := by omega
      rw [hd'] at hd; have h' := (mem_children_iff.mp hd).2; rw [hq] at h'; have := Option.some.inj h'; omega
    have hAq : Anc0 M (r + qp) (r + L) := Anc0.step hq (Anc0.refl _)
    have hAd : Anc0 M (r + qp) d := anc_between hAq d (by omega) (by omega)
    have hAr := anc0_par hAd (by omega) (mem_children_iff.mp hd).2
    have := hAr.le; omega
  have hCLN : CL N r = CL (M.take (r + L)) r ++ [r + qp] := by
    unfold CL
    have hall : ∀ d ∈ children M r, d < r + L := by
      intro d hd
      by_contra h'
      have := (hxc r d hd (by omega)).2; omega
    rw [hchN r (by omega), children_take, show (children M r).filter (fun d => decide (d < r + L)) = children M r
      from List.filter_eq_self.mpr (fun d hd => by simpa using hall d hd)]
    conv_lhs => rw [hqlast, List.filter_append]
    conv_rhs => rw [hqlast, List.filter_append]
    rw [show List.filter (fun c => decide (Counted N r c)) [r + qp] = [r + qp] by simp [hqcntN],
      show List.filter (fun c => decide (Counted (M.take (r + L)) r c)) [r + qp] = [] by simp [hqP],
      List.append_nil]
    congr 1
    apply List.filter_congr
    intro c hc
    have hc' := List.mem_filter.mp hc
    have hcq : c < r + qp := by simpa using hc'.2
    simp only [decide_eq_decide]
    exact (hcntN r c (by omega) (by omega) (by omega)).trans (hcntP r c (by omega) (by omega) (by omega)).symm
  -- the copy root `x′`
  have hCR := t2CopyResV3 hM hS I hz h2 r L hlen hr
  have hBEP : BumpE2 P := by rw [hP, ← hexp (n - 1)]; exact (sInvX_expand hX (n - 1)).loc.2.2.1
  obtain ⟨hKV, hB', hV', hVV⟩ := hCR n hn σ ρP hCN hCP hGP
  have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP
  have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hX.r0p hX.loc.1
  have hF := copy_facts_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP hCN hCP hGP hRP hK hKV hRK hB' hV' hVV
  have hox := o_copy_root hCN hCP hGP hF hrP hxN hV' hVV rfl
  -- `v(x′) = a + last(v_N(q))`
  have hvq := vq_N hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 (by omega) Txb I.be I.uat hUN I.cons I.good hCN hRN
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hvx : σ.v (r + L) = add (ρ.v r) (last (σ.v (r + qp))) := by
    rw [(hCN (r + L) hxN).2]; unfold vRhs
    have he1 : entry N 1 (r + L) ≠ 0 := by
      have := entry1_xN hlen hL0 hA hq hd0e hn hd1e
      rw [← hN] at this; rw [this]; omega
    rw [if_neg he1, if_pos hx2N]
    have hp1 := par1_xN hlen hL0 hA hq hd0e hn hd1e
    rw [hr1, ← hN] at hp1
    have hu := upg_N_x_q hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 (by omega) Txb hJ hX.r0p I.be
    rw [← hN] at hu
    rw [hp1, hu]
    show sf (add (σ.v r) (last (σ.v (r + qp)))) = _
    rw [hvr, sf_ot (isOT_add hVot (isOT_last hvq.1))]
  -- the frame of `q`: only `x′`
  have hPo : isOT (psi (ρP.v r) (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o))) z) = true := by
    rw [← o_cl_eq hCP hGP hrP]; exact hGP.ot_o r hrP
  have hxOT : isOT (psi (σ.v (r + L)) (sh (ρP.v r) (σ.v (r + L))
      (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o)))) z) = true := by
    have := isOT_shTop (V' := σ.v (r + L)) (hGP.ot_v r hrP) hV' hVV hPo (le_refl _)
    rwa [shf_self] at this
  have hoq := o_last_form (Lc := []) hCN hqN hvq.1 (by rw [hCLNq]; rfl)
    (fun c hc => by rw [hCLNq] at hc; simp at hc; rw [hc, hox]; exact ⟨hxOT, _, _, rfl⟩)
    (by rw [hCLNq]; simp) hox
  -- the frame of `r`
  exact ⟨hCLN, hval, hvr, hvx, by rw [hoq]; rfl, hCLNq⟩

theorem o_r_level_CV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    (hqP : ¬ Counted (M.take (r + L)) r q) (hun : upg M (r + L - 1) = none)
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hG0 : Good3 (M.take (r + L)) τ0)
    (hR0 : Rk (M.take (r + L)) rk0) (hv0 : τ0.v r = ρ.v r) (hvq0 : τ0.v q = σ.v q)
    (hqOT : isOT (σ.o q) = true)
    (hdecN : ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
      σ.o).Pairwise (fun a b => b ≤ a)) :
    σ.v (r + L) = add (ρ.v r) (last (σ.v q)) ∧
    σ.o r = psi (ρ.v r) (step (ρ.v r) (t2X1 M r L τ0) (σ.v q)
      (step (σ.v q) z (σ.v (r + L)) (sh (ρP.v r) (σ.v (r + L)) (spArg (ρP.v r) z
        (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1))
          r).map ρP.o)))) z) z) z := by
  obtain ⟨hCLN, hval, hvr, hvx, hoq, _⟩ :=
    C_frameV3 hM hS I Ctx hz h2 hlen hr hq hqr hqP hun hn hCN hRN hCP hGP hRP hC0 hG0 hR0 hv0 hvq0
  refine ⟨hvx, ?_⟩
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hrN : r < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n).length := by
    have := TRIO.gexp_length (M := M) (j0 := r) (Lb := L) (d0 := entry M 0 (r + L) - entry M 0 r)
      (d1 := entry M 1 (r + L) - entry M 1 r) (n := n) hlen
    have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
    omega
  have hsN : ∀ c ∈ CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r,
      Single (σ.o c) := by
    intro c hc
    rw [hCLN] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [hval c hc]
      exact single_o hC0 hG0 (mem_children (cl_mem_children hc)).2
    · simp at hc; rw [hc]; exact ⟨hqOT, _, _, hoq⟩
  have hor := o_last_form hCN hrN (by rw [hvr]; exact I.good.ot_v r (by omega)) hCLN hsN hdecN hoq
  rw [hor, hvr, List.map_congr_left hval]
  unfold t2X1; rw [hv0]

theorem seed_r_value_CV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q]) (hRes : CRel M ρ r L q)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : Rk (M.take (r + L)) rk0) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      isOT (σ.o q) = true →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
        σ.o r = psi (ρ.v r) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ0) (n - 1)) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hqx : q < r + L := par_lt M 0 _ _ hq
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
  have hP1 : TRIO.gexp M r L d0 d1 1 = M.take (r + L) := gexp_one_gen hlen
  have hv0 : τ0.v r = ρ.v r := v_take_of_untopped I hlen (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hC0
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ihs =>
  intro hGlow σ hCN hqOT hdecN
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  have hG0 : Good3 (M.take (r + L)) τ0 := by
    have h := hGlow 1 (le_refl 1) (by omega) τ0 (by rw [hP1]; exact hC0)
    rwa [hP1] at h
  have hvq : σ.v q = qnS M ρ r L q := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  have hvq0 : τ0.v q = σ.v q := by rw [hvq]; exact hRes.vqP τ0 hC0
  have key : ∀ (ρP : Valn) (rkP : Bool → Nat → Nat), Cons (TRIO.gexp M r L d0 d1 (n - 1)) ρP →
      Good3 (TRIO.gexp M r L d0 d1 (n - 1)) ρP → Rk (TRIO.gexp M r L d0 d1 (n - 1)) rkP → ρP.v r = ρ.v r →
      spArg (ρP.v r) z (sumN ((CL (TRIO.gexp M r L d0 d1 (n - 1)) r).map ρP.o)) =
        shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ0) (n - 2) →
      σ.o r = psi (ρ.v r) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ0) (n - 1)) z := by
    intro ρP rkP hCP hGP hRP hvP hXP
    obtain ⟨hvx, hor⟩ := o_r_level_CV3 hM hS I Ctx hz h2 hlen hr hq hqr (qP_C hM hS I hlen hr hq hqr hncl hRes.un) hRes.un hn hCN hRN hCP hGP hRP
      hC0 hG0 hR0 hv0 hvq0 hqOT hdecN
    have hvx' : σ.v (r + L) = qnS M ρ r L q := by rw [hvx, hvq]; exact qnS_vxs M ρ r L q
    rw [hor, hvx', hvq, hXP, hvP, show n - 1 = (n - 2) + 1 by omega, hRes.rw τ0 hC0 (n - 2)]
    rfl
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have hn2 : n = 2 := by omega
    subst hn2
    have hCP : Cons (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show 2 - 1 = 1 from rfl, hP1]; exact hC0
    have hGP : Good3 (TRIO.gexp M r L d0 d1 (2 - 1)) τ0 := by rw [show 2 - 1 = 1 from rfl, hP1]; exact hG0
    have hRP : Rk (TRIO.gexp M r L d0 d1 (2 - 1)) rk0 := by rw [show 2 - 1 = 1 from rfl, hP1]; exact hR0
    exact key τ0 rk0 hCP hGP hRP hv0 (by rw [show 2 - 1 = 1 from rfl, hP1]; rfl)
  · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
    have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
    have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
    have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
    have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
    have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by omega
    have hqP' : q < (TRIO.gexp M r L d0 d1 (n - 1)).length := by omega
    have hP := ihs (n - 1) (by omega) (by omega) (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP
      (hGP.ot_o q hqP') (by rw [← cvals_eq_mapC hCP]; exact hGP.dec r hrP)
    have hform := o_cl_eq hCP hGP hrP
    rw [hP] at hform
    simp only [psi.injEq] at hform
    refine key _ rkP hCP hGP hRP hform.1.symm ?_
    rw [← hform.2.1, show n - 1 - 1 = n - 2 by omega]

theorem seed_frame_data_qrV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L])
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP) :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = Lc ++ [r + L] ∧
      σ.v r = ρ.v r ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧
      σ.o (r + L) = psi (succ (ρ.v r)) (sh (ρP.v r) (succ (ρ.v r)) (spArg (ρP.v r) z
        (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1))
          r).map ρP.o)))) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
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
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hxbr : col M (r + L) ≠ bump M r := fun h => by
    have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hIU : ∀ c, c < r + L → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_N2 (d1 := d1) hlen hL0 hq hd0e hn hXu hxbr he2r hc]
    exact htM
  have hxcN : Counted N r (r + L) := by
    have hx2 := (entry_xprime (d1 := d1) hlen hL0 hq hd0e (by omega) hn).1
    rw [← hN] at hx2
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col _ (r + L) = (_, _, 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hCLN : CL N r = Lc ++ [r + L] := by
    rw [CL_N2 hlen hL0 hq hd0e hn hXu hxbr he2r hIU hxcN hrx, hCLM]
  -- `D = DepS M {o(r)}` misses the counted children of `r` and `v(r)`
  have hoff := t2_off hlen hL0 hq hd0e hn hXu hxbr hrb he2r hIU I.cons hCN hRN
  have hnoD : ∀ b i, DepS M (fun b i => b = true ∧ i = r) b i → i < M.length → rk true r ≤ rk b i := by
    intro b i hD hi
    obtain ⟨b', i', ⟨rfl, rfl⟩, hle⟩ := depS_rk_ex I.rank hD hi
    exact hle
  have hrM : r < M.length := by omega
  have hvr : σ.v r = ρ.v r := (hoff r hrx).2 (fun hD => by
    have h1 := hnoD false r hD hrM
    have h2' := (I.rank r hrM).1
    omega)
  have hLc : ∀ d ∈ Lc, d < r + L ∧ σ.o d = ρ.o d := by
    intro d hd
    have hdCL : d ∈ CL M r := by rw [hCLM]; simp [hd]
    have hdc := cl_mem_children hdCL
    have hcnt : Counted M r d := by simpa using (List.mem_filter.mp hdCL).2
    have hdx : d < r + L := by
      have hsort := cl_sorted M r
      rw [hCLM] at hsort
      exact (List.pairwise_append.mp hsort).2.2 d hd (r + L) (by simp)
    refine ⟨hdx, (hoff d hdx).1 (fun hD => ?_)⟩
    have h1 := hnoD true d hD (by omega)
    have h2' := (I.rank r hrM).2.1 d hdc hcnt.1 hcnt.2
    omega
  -- the copy root `x′`
  have hCR := t2CopyResV3 hM hS I hz h2 r L hlen hr
  have hm : n - 1 + 1 = n := by omega
  have hBEP : BumpE2 P := by rw [hP, ← hexp (n - 1)]; exact (sInvX_expand hX (n - 1)).loc.2.2.1
  obtain ⟨hKV, hB', hV', hVV⟩ := hCR n hn σ ρP hCN hCP hGP
  have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP
  have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hX.r0p hX.loc.1
  have hF := copy_facts_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP hCN hCP hGP hRP hK hKV hRK hB' hV' hVV
  have hox := o_copy_root hCN hCP hGP hF hrP hxN hV' hVV rfl
  -- `v(x′) = V + 1`
  have hvx : σ.v (r + L) = succ (ρ.v r) := by
    have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
    rcases vx_eq hlen hL0 hA hq hd0e hn hd1e he2r h1lt hrb hr1 (fun h => absurd rfl h) I.be hJ hX.r0p I.uat hUN
      I.cons I.good hCN hRN with h | ⟨h, _⟩
    · rw [h, add_one_eq_succ (I.good.ot_v r hrM)]
    · exact absurd rfl h
  rw [hvx] at hox
  exact ⟨hCLN, hvr, fun d hd => (hLc d hd).2, hox⟩

/-! ## 枠の持ち上げ -/

theorem seed_frame_data_qnV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q])
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP) :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r = Lc ++ [q] ∧
      CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) q = [r + L] ∧
      σ.v r = ρ.v r ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧
      σ.v (r + L) = add (ρ.v r) (last (σ.v q)) ∧
      σ.o q = psi (σ.v q) (step (σ.v q) (spArg (σ.v q) z (sumN ([] : List T))) (σ.v (r + L))
        (sh (ρP.v r) (σ.v (r + L)) (spArg (ρP.v r) z
          (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1))
            r).map ρP.o)))) z) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hqc := cl_mem_children hqcl
  have hpq : par M 0 q = some r := (mem_children_iff.mp hqc).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  obtain ⟨qp, rfl⟩ : ∃ qp, q = r + qp := ⟨q - r, by omega⟩
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hqcnt : Counted M r (r + qp) := by simpa using (List.mem_filter.mp hqcl).2
  have hqx : r + qp < r + L := par_lt M 0 _ _ hq
  have hqp : qp < L := by omega
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
  obtain ⟨Txb, Tqb, _, Tclq, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq
  have hqb : ∀ i, par M 0 (r + qp) = some i → col M (r + qp) ≠ bump M i := by
    intro i hi; rw [hpq] at hi; cases hi; exact Tqb
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hm1 : 1 ≤ n := by omega
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hqN : r + qp < N.length := by omega
  have hrM : r < M.length := by omega
  have hqM : r + qp < M.length := by omega
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
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hT : N.take (r + L) = M.take (r + L) := gexp_take_x hlen (by omega)
  have hcolN : ∀ i, i < r + L → col N i = col M i := fun i hi => col_gexp_pre hlen hm1 hi
  have hbN : ∀ c, c < r + L → bump N c = bump M c := fun c hc => by
    unfold bump; rw [entry_gexp_pre hlen hm1 0 hc, entry_gexp_pre hlen hm1 1 hc]
  have hchN : ∀ i, i < r + L → children N i = children M i :=
    fun i hi => children_N2Q hlen hL0 hA hq hqp hd0e (by omega) hn hi
  have hIUt : ∀ c, c < r + L → c ≠ r + qp → topped M c = true → isUpg N c = isUpg M c := by
    intro c hc hcq htM
    apply isUpg_topped_take (by omega) (by omega) hT I.uat hUN hc _ htM
    rw [topped_eq_of (hchN c hc) (fun d hd => hcolN d (by
      have := (mem_children hd).2
      by_contra h'
      have hdx : d = r + L := by omega
      have := (mem_children_iff.mp hd).2; rw [hdx, hq] at this; exact hcq (Option.some.inj this).symm))
      (hbN c hc)]
    exact htM
  have hcntN : ∀ i c, i < r + L → c < r + L → c ≠ r + qp → (Counted N i c ↔ Counted M i c) :=
    fun i c hi hc hcq => counted_NQ hlen hL0 hA hq hqp hd0e hn Txb hIUt hi hc hcq
  -- `x′` counts at `q`, `q` counts at `r`
  have hx2N : entry N 2 (r + L) = 0 := by
    rw [(entry_xprimeQ hlen hL0 hA hq hqp hd0e (by omega) hn).1, he2r]
  have hxcnt : Counted N (r + qp) (r + L) := by
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col N (r + L) = (entry N 0 (r + qp) + 1, entry N 1 (r + qp), 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hq⟩
  have hsplitq := children_split_x hlen hxq
  have hCLNq : CL N (r + qp) = [r + L] := by
    unfold CL
    rw [hchN _ hqx, hsplitq, List.filter_append]
    have h1 : List.filter (fun c => decide (Counted N (r + qp) c))
        (List.filter (fun d => decide (d < r + L)) (children M (r + qp))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hcn
      have hc' := List.mem_filter.mp hc
      have hcx : c < r + L := by simpa using hc'.2
      have hcq : c ≠ r + qp := by have := (mem_children hc'.1).1; omega
      have hcntM : Counted M (r + qp) c := (hcntN _ c hqx hcx hcq).mp (by simpa using hcn)
      have hin : c ∈ CL M (r + qp) := by unfold CL; exact List.mem_filter.mpr ⟨hc'.1, by simpa using hcntM⟩
      rw [Tclq] at hin; simp at hin
    rw [h1]; simp [hxcnt]
  have hqcntN : Counted N r (r + qp) := by
    refine ⟨by rw [hcolN _ hqx, hbN r (by omega)]; exact hqcnt.1, fun ⟨_, ht⟩ => ?_⟩
    unfold topped at ht
    rw [hchN _ hqx, hsplitq] at ht
    simp at ht
    exact hxcnt.1 ht
  have hCLN : CL N r = Lc ++ [r + qp] := by
    rw [← hCLM]; unfold CL
    rw [hchN r (by omega)]
    apply List.filter_congr
    intro c hc
    by_cases hcq : c = r + qp
    · rw [hcq]; simp [hqcntN, hqcnt]
    · have hcx : c < r + L := by
        have hcl := (mem_children hc).2
        by_contra h'
        have hcx' : c = r + L := by omega
        rw [hcx'] at hc
        have := (mem_children_iff.mp hc).2; rw [hq] at this
        have := Option.some.inj this; omega
      simp only [decide_eq_decide]
      exact hcntN r c (by omega) hcx hcq
  -- `N` agrees with `M` outside `D = DepS M {v(q), o(r)}`
  have hnu : upg M (r + L - 1) ≠ some (r + L) := fun h =>
    upg_not_x hlen hA hq Txb I.be h (le_refl _) (by omega)
  have hupgN : ∀ i, i < r + L → upg N i = upg M i := fun i hi =>
    upg_NQ hlen hL0 hA hq hqp hd0e hn he2r hnu hi
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hq] at h'; exact (Option.some.inj h').symm
  have hbjN : ∀ i j, i < r + L → j ∈ children N i → r + L ≤ j → col N j ≠ bump N i := by
    intro i j hi hj hjx hb
    have hjl := (mem_children hj).2
    rw [hlN] at hjl
    rcases par0_tail2Q hlen hL0 hA hq hqp hd0e (by omega) hjx hjl with ⟨hjx', _⟩ | ⟨p', hp', hp'1, _⟩
    · rw [hjx'] at hb
      have := e2_of_col (show col N (r + L) = (entry N 0 i + 1, entry N 1 i, 1) from hb)
      omega
    · rw [(mem_children_iff.mp hj).2] at hp'; cases hp'; omega
  have hoff := t2_off_gen (S := SQ (r + qp) r) (bnd := r + L) I.cons hCN hRN (by omega) (by rw [hlN]; omega)
    (fun i hi _ => hchN i hi) (DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (Or.inr (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i hqi hb => by have h' := (mem_children_iff.mp hqi).2; rw [hpq] at h'; cases h'; exact Tqb hb)
    (fun y i hi => entry_gexp_pre hlen (by omega) y hi) (fun i hi => par_gexp_pre hlen (by omega) 1 hi)
    (fun i hi _ => hupgN i hi)
    (fun i c hi hd hc hcx => hcntN i c hi hcx (by
      intro hcq; apply hd; apply DepS.seed; right; refine ⟨rfl, ?_⟩
      have h' := (mem_children_iff.mp hc).2; rw [hcq, hpq] at h'; exact (Option.some.inj h').symm))
    (fun i c hi hc hcx => by
      obtain ⟨_, rfl⟩ := hxc i c hc hcx
      exact DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i k hi hk hkx => (upg_not_x hlen hA hq Txb I.be hk hkx hi).elim)
    hbjN
    (fun i j hi hj hjx _ => by
      obtain ⟨_, rfl⟩ := hxc i j hj hjx
      exact DepS.seed (Or.inl ⟨rfl, rfl⟩))
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc j k hk hkx
      have h' := (mem_children_iff.mp hj).2; rw [hpq] at h'; cases h'
      exact absurd hjb Tqb)
  have htq : topped M (r + qp) = true := by
    unfold topped; rw [hsplitq]; simp [Txb]
  have hinv : ∀ {b i}, DepS M (SQ (r + qp) r) b i → i < M.length → Anc0 M (r + qp) i ∨ rk true r ≤ rk b i :=
    fun h hi => depS_SQ_inv I.rank hpq Tqb hqcnt.2 htq he2r h hi
  have hvr : σ.v r = ρ.v r := (hoff r (by omega)).2 (fun hD => by
    rcases hinv hD hrM with hAq | hle
    · have := hAq.le; omega
    · have := (I.rank r hrM).1; omega)
  have hLc : ∀ d ∈ Lc, σ.o d = ρ.o d := by
    intro d hd
    have hdCL : d ∈ CL M r := by rw [hCLM]; simp [hd]
    have hdc := cl_mem_children hdCL
    have hcnt : Counted M r d := by simpa using (List.mem_filter.mp hdCL).2
    have hdq : d < r + qp := by
      have hsort := cl_sorted M r
      rw [hCLM] at hsort
      exact (List.pairwise_append.mp hsort).2.2 d hd (r + qp) (by simp)
    refine (hoff d (by omega)).1 (fun hD => ?_)
    rcases hinv hD (by omega) with hAq | hle
    · have := hAq.le; omega
    · have := (I.rank r hrM).2.1 d hdc hcnt.1 hcnt.2; omega
  -- the copy root `x′`
  have hCR := t2CopyResV3 hM hS I hz h2 r L hlen hr
  have hBEP : BumpE2 P := by rw [hP, ← hexp (n - 1)]; exact (sInvX_expand hX (n - 1)).loc.2.2.1
  obtain ⟨hKV, hB', hV', hVV⟩ := hCR n hn σ ρP hCN hCP hGP
  have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP
  have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hX.r0p hX.loc.1
  have hF := copy_facts_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP hCN hCP hGP hRP hK hKV hRK hB' hV' hVV
  have hox := o_copy_root hCN hCP hGP hF hrP hxN hV' hVV rfl
  -- `v(x′) = a + last(v_N(q))`
  have hvq := vq_N hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 (by omega) Txb I.be I.uat hUN I.cons I.good hCN hRN
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hvx : σ.v (r + L) = add (ρ.v r) (last (σ.v (r + qp))) := by
    rw [(hCN (r + L) hxN).2]; unfold vRhs
    have he1 : entry N 1 (r + L) ≠ 0 := by
      have := entry1_xN hlen hL0 hA hq hd0e hn hd1e
      rw [← hN] at this; rw [this]; omega
    rw [if_neg he1, if_pos hx2N]
    have hp1 := par1_xN hlen hL0 hA hq hd0e hn hd1e
    rw [hr1, ← hN] at hp1
    have hu := upg_N_x_q hlen hL0 hA hq hd0e hn hd1e he2r h1lt hqb hr1 (by omega) Txb hJ hX.r0p I.be
    rw [← hN] at hu
    rw [hp1, hu]
    show sf (add (σ.v r) (last (σ.v (r + qp)))) = _
    rw [hvr, sf_ot (isOT_add hVot (isOT_last hvq.1))]
  -- the frame of `q`: only `x′`
  have hPo : isOT (psi (ρP.v r) (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o))) z) = true := by
    rw [← o_cl_eq hCP hGP hrP]; exact hGP.ot_o r hrP
  have hxOT : isOT (psi (σ.v (r + L)) (sh (ρP.v r) (σ.v (r + L))
      (spArg (ρP.v r) z (sumN ((CL P r).map ρP.o)))) z) = true := by
    have := isOT_shTop (V' := σ.v (r + L)) (hGP.ot_v r hrP) hV' hVV hPo (le_refl _)
    rwa [shf_self] at this
  have hoq := o_last_form (Lc := []) hCN hqN hvq.1 (by rw [hCLNq]; rfl)
    (fun c hc => by rw [hCLNq] at hc; simp at hc; rw [hc, hox]; exact ⟨hxOT, _, _, rfl⟩)
    (by rw [hCLNq]; simp) hox
  exact ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩

theorem seed_frame_data_svV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (htP : topped (M.take (r + L)) r = false)
    {n : Nat} (hn : 2 ≤ n) {σ ρP : Valn} {rkN rkP : Bool → Nat → Nat}
    (hCN : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ)
    (hRN : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) rkN)
    (hCP : Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hGP : Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) ρP)
    (hRP : Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1)) rkP)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hG0 : Good3 (M.take (r + L)) τ0)
    (hR0 : Rk (M.take (r + L)) rk0) :
    CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r =
        CL (M.take (r + L)) r ++ [r + L] ∧
      σ.v r = τ0.v r ∧ (∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d) ∧
      σ.o (r + L) = psi (succ (ρ.v r)) (sh (ρP.v r) (succ (ρ.v r)) (spArg (ρP.v r) z
        (sumN ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) (n - 1))
          r).map ρP.o)))) z := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨hcntN, hcntP⟩ := sv_cnt hM hS I hz h2 hlen hr hq hux htP hn
  have hag := sv_agree hM hS I hz h2 hlen hr hq hux htP hn hCN hC0 hR0
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  set N := TRIO.gexp M r L d0 d1 n with hN
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hd1 : 0 < d1 := by omega
  have hd1e : entry M 1 (r + L) = entry M 1 r + d1 := by omega
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
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
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
  have hxN : r + L < N.length := by omega
  have hrP : r < P.length := by omega
  have hrN : r < N.length := by omega
  have hrM : r < M.length := by omega
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hrT : r < (M.take (r + L)).length := by omega
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  have hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p := fun p _ h => by
    have := e2_of_col (show col M r = (entry M 0 p + 1, entry M 1 p, 1) from h); omega
  -- the counted children of `r` in `N`
  have hxcN : Counted N r (r + L) := by
    have hx2 := (entry_xprime (d1 := d1) hlen hL0 hq hd0e (by omega) hn).1
    rw [← hN] at hx2
    refine ⟨fun h => ?_, fun ⟨hiu, _⟩ => ?_⟩
    · have := e2_of_col (show col _ (r + L) = (_, _, 1) from h); omega
    · unfold isUpg at hiu
      obtain ⟨k0, _, hk0⟩ := List.any_eq_true.mp hiu
      have := upg_target_e2 (of_decide_eq_true hk0); omega
  have hxrc : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have hCLN : CL N r = CL (M.take (r + L)) r ++ [r + L] := by
    unfold CL
    rw [children_N2 hlen hL0 hq hd0e (by omega) hn hrx, children_take]
    conv_lhs => rw [children_split_x hlen hxrc, List.filter_append]
    rw [show List.filter (fun c => decide (Counted N r c)) [r + L] = [r + L] by simp [hxcN]]
    congr 1
    apply List.filter_congr
    intro c hc
    have hcx : c < r + L := by simpa using (List.mem_filter.mp hc).2
    simp only [decide_eq_decide]
    exact (hcntN r c hrx hcx).trans (hcntP r c hrx hcx).symm
  -- the values of the earlier children are those of `M.take x`
  have hval : ∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d := by
    intro d hd
    have hdc := cl_mem_children hd
    have hcnt : Counted (M.take (r + L)) r d := by simpa using (List.mem_filter.mp hd).2
    exact ((hag d (by have := (mem_children hdc).2; omega)).1
      ((hR0 r hrT).2.1 d hdc hcnt.1 hcnt.2)).symm
  have hvr : σ.v r = τ0.v r := ((hag r hrx).2 (hR0 r hrT).1).symm
  -- the copy root `x′`
  have hCR := t2CopyResV3 hM hS I hz h2 r L hlen hr
  have hBEP : BumpE2 P := by rw [hP, ← hexp (n - 1)]; exact (sInvX_expand hX (n - 1)).loc.2.2.1
  obtain ⟨hKV, hB', hV', hVV⟩ := hCR n hn σ ρP hCN hCP hGP
  have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP
  have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hX.r0p hX.loc.1
  have hF := copy_facts_gexp hlen hL0 hA hd0e hn hd0 hd1 hgx he2r hBEP hCN hCP hGP hRP hK hKV hRK hB' hV' hVV
  have hox := o_copy_root hCN hCP hGP hF hrP hxN hV' hVV rfl
  have hvx : σ.v (r + L) = succ (ρ.v r) := by
    have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) I.z2 I.z1 hr
    rcases vx_eq hlen hL0 hA hq hd0e hn hd1e he2r h1lt hrb hr1 (fun h => absurd rfl h) I.be hJ hX.r0p I.uat hUN
      I.cons I.good hCN hRN with h | ⟨h, _⟩
    · rw [h, add_one_eq_succ (I.good.ot_v r hrM)]
    · exact absurd rfl h
  rw [hvx] at hox
  exact ⟨hCLN, hvr, hval, hox⟩

theorem qn_take_t1V3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hCLM : CL M r = [q])
    {τ : Valn} (hτ : Cons (M.take (r + L)) τ) {t1 : T}
    (ht1 : spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = psi t1 z z) :
    ∃ ωT, t1 = add (ρ.v r) ωT ∧ isOT ωT = true ∧ (∃ a b, ωT = psi a b z) ∧
      ωT ≤ omega (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hpq : par M 0 q = some r := (mem_children_iff.mp (cl_mem_children hqcl)).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hL0 : 0 < L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, Tqb, _, TCLq, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb Tqb TCLq
  have hqb : ∀ a, par M 0 q = some a → col M q ≠ bump M a := by
    intro a ha; rw [hpq] at ha; cases ha; exact Tqb
  have hr1 : par M 1 (r + L) = some r := par1_x_r (by omega) hX.z2 hX.loc.2.1 hr
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have he1q : entry M 1 (r + L) = entry M 1 q :=
    e1_of_col (show col M (r + L) = (entry M 0 q + 1, entry M 1 q, 1) from Txb)
  have he2q : entry M 2 q = 1 := I.be q (r + L) hxq Txb
  have he0lt := anc0_e0_lt hA (by omega)
  have hpar1q : par M 1 q = some r :=
    par1_q (n := 2) (d0 := entry M 0 (r + L) - entry M 0 r) (d1 := entry M 1 (r + L) - entry M 1 r)
      hlen hL0 hA hq (by omega) (le_refl 2) (by omega) he2r h1lt hqb hr1 hqr Txb
  -- the drop
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := (Ctx.drop (by omega)).1
  have J1 := Ctx.pre (M.length - 1) (by omega) (by omega)
  have hG1 := good3_congr J1.good (agree_of_cons J1.cons hC1 J1.rank)
  have hpre : ∀ i, i < M.length - 1 → ∃ Tl, CL M i = CL (M.take (M.length - 1)) i ++ Tl :=
    fun i hi => cl_prefix hx1 I.r0p I.z2 I.sd I.z1 I.uat hi
  have hfr := fun i (hi : i < M.length - 1) (h : CL (M.take (M.length - 1)) i = [] ++ q :: []) =>
    (frame_take hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hi h).1
  rw [show M.length - 1 = r + L by omega] at hRk1 hC1 hdrop hG1 hpre hfr
  set ρ' := rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rk) with hρ'
  have hTlen : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hag := agree_of_cons hτ hC1 hRk1
  -- `CL_T(q) = []`, `CL_T(r) = [q]`
  obtain ⟨Tl, hTl⟩ := hpre q hqx
  rw [TCLq] at hTl
  have hCLTq : CL (M.take (r + L)) q = [] := (List.append_eq_nil_iff.mp hTl.symm).1
  obtain ⟨Tl', hTl'⟩ := hpre r (by omega)
  rw [hCLM] at hTl'
  have hCLTr : CL (M.take (r + L)) r = [q] := by
    rcases hc : CL (M.take (r + L)) r with _ | ⟨a, l⟩
    · rw [hc] at ht1; exact absurd ht1 (by simp [sumN, spArg])
    · rw [hc] at hTl'
      simp only [List.cons_append, List.cons.injEq] at hTl'
      obtain ⟨rfl, hl⟩ := hTl'
      rw [(List.append_eq_nil_iff.mp hl.symm).1]
  -- `o_T(q) = Ω_{v_T(q)}`, so `t1 = v_T(q)`
  have hqT : q < (M.take (r + L)).length := by omega
  have hoq : ρ'.o q = psi (ρ'.v q) z z := by
    rw [o_cl_eq hC1 hG1 hqT, hCLTq]; rfl
  rw [hCLTr, List.map_singleton, (hag q hqT).1, hoq, sumN_single (by rw [← hoq]; exact hG1.ot_o q hqT),
    spArg_cons] at ht1
  have hst : step (τ.v r) z (ρ'.v q) z z = psi (ρ'.v q) z z := by
    unfold step; rw [if_neg (fun h => T.not_lt_z _ h.1)]; rfl
  rw [hst] at ht1
  have ht1q : t1 = ρ'.v q := by
    have : psi (ρ'.v q) z z = psi t1 z z := ht1
    simp only [psi.injEq] at this; exact this.1.symm
  -- `v_T(q)`
  have hvr : ρ'.v r = ρ.v r := hfr r (by omega) (by rw [hCLTr]; rfl)
  set Lq := (children M q).filter (fun d => decide (d < r + L)) with hLq
  have hbT : ∀ j ∈ Lq, bumpTerm (M.take (r + L)) ρ' q j ≤ bumpTerm M ρ q j := by
    intro j hjL
    have hjq : j ∈ children M q := (List.mem_filter.mp hjL).1
    have hjx : j < r + L := by simpa using (List.mem_filter.mp hjL).2
    have hpj : par M 0 j = some q := (mem_children_iff.mp hjq).2
    unfold bumpTerm
    rw [col_take M hjx, bump_take M hqx]
    split
    · have hch : children (M.take (r + L)) j = children M j := by
        rw [children_take, List.filter_eq_self]
        intro c hc
        simpa using kid_lt_x hpj hq hjx (mem_children_iff.mp hc).2
      rw [hch]
      have hcx : ∀ c ∈ children M j, c < r + L := fun c hc => kid_lt_x hpj hq hjx (mem_children_iff.mp hc).2
      apply omega_le_omega
      · exact isOT_sumN _ (fun t ht => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact hG1.ot_o c (by have := hcx c hc; omega))
      · exact isOT_sumN _ (fun t ht => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact I.good.ot_o c (mem_children hc).2)
      · apply sumN_le2 (forall₂_map_le _ (fun c hc => po_le (hdrop c (hcx c hc)).1))
        · intro t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact hG1.ot_o c (by have := hcx c hc; omega)
        · intro t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; exact I.good.ot_o c (mem_children hc).2
    · exact le_refl _
  have hOT1 : ∀ t ∈ one :: Lq.map (bumpTerm (M.take (r + L)) ρ' q), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG1 q j
  have hOT2 : ∀ t ∈ one :: Lq.map (bumpTerm M ρ q), isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm I.good q j
  have hvq : ρ'.v q = add (ρ.v r) (omega (sumN (one :: Lq.map (bumpTerm (M.take (r + L)) ρ' q)))) := by
    rw [(hC1 q hqT).2]; unfold vRhs
    rw [entry_take M 1 hqx, entry_take M 2 hqx, if_neg (by omega), if_neg (by omega), par_take M 1 q hqx,
      hpar1q, children_take]
    show sf (add (ρ'.v r) _) = _
    rw [hvr, sf_ot (isOT_add (I.good.ot_v r (by omega)) (isOT_omega (isOT_sumN _ hOT1)))]
  refine ⟨omega (sumN (one :: Lq.map (bumpTerm (M.take (r + L)) ρ' q))), by rw [ht1q, hvq],
    isOT_omega (isOT_sumN _ hOT1), omega_psi_form _, ?_⟩
  apply omega_le_omega (isOT_sumN _ hOT1) (isOT_sumN _ hOT2)
  exact sumN_le2 (List.Forall₂.cons (le_refl _) (forall₂_map_le Lq hbT)) hOT1 hOT2

theorem t2SeedQNFC_holdsV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) :
    T2SeedQNFC M ρ r L q Lc := by
  intro hLc0 τ hτ t1 ht1 k
  subst hLc0
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have ht1' : spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = psi t1 z z := by
    rw [ht1]; rfl
  obtain ⟨ωT, ht1e, hωTot, ⟨a1, b1, hωTf⟩, hωT⟩ :=
    qn_take_t1V3 hM hS I Ctx hlen hr hq hqr (by simpa using hCLM) hτ ht1'
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hpq : par M 0 q = some r := (mem_children_iff.mp (cl_mem_children hqcl)).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, _, _, _, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb
  set V := ρ.v r with hVdef
  have hWot : isOT (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
      (bumpTerm M ρ q))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm I.good q j
  set ω := omega (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
      (bumpTerm M ρ q))) with hωdef
  have hωot : isOT ω = true := isOT_omega hWot
  obtain ⟨a, b, hωf⟩ := omega_psi_form (sumN (one :: ((children M q).filter
    (fun d => decide (d < r + L))).map (bumpTerm M ρ q)))
  rw [← hωdef] at hωf
  have hV : isOT V = true := I.good.ot_v r hrM
  have hs'ot : isOT (add V ω) = true := isOT_add hV hωot
  have hVs : V < add V ω := qnS_gt M ρ r L q
  have hlast : last (add V ω) = ω := by
    obtain ⟨P, hP, _⟩ := add_eq_app_prefix V ω
    rw [hP, last_app P (by rw [hωf]; simp), hωf]; rfl
  have hωlast : last ω = ω := by rw [hωf]; rfl
  have hωlev : ¬ V < lev ω := qn_omega_lev hX hJ I.cons I.good I.rank (by omega) hr hq hpq Txb
  have hωTlev : ¬ V < lev ωT := fun h => hωlev (lt_of_lt_of_le h (lev_le_of_le hωT))
  have hshω : sh V (add V ω) ω = ω := sh_fix hωot hωlev
  have hshωT : sh V (add V ω) ωT = ωT := sh_fix hωTot hωTlev
  have hsubV : ∀ Y, sub (add V Y) V = Y := fun Y => by
    rw [sub_add_dist Y hV hV (le_refl _), sub_self_T]; rfl
  have hheadT : head ωT ≤ ω := by rw [hωTf]; show psi a1 b1 z ≤ ω; rw [← hωTf]; exact hωT
  have key : ∀ k, ∃ X, X ≠ z ∧ isOT X = true ∧ head X ≤ ω ∧
      tqN V (add V ω) t1 (k + 1) = app (add V ω) X := by
    intro k
    induction k with
    | zero =>
      refine ⟨ωT, by rw [hωTf]; simp, hωTot, hheadT, ?_⟩
      show add (add V ω) (sh V (add V ω) (sub t1 V)) = _
      rw [ht1e, hsubV, hshωT]
      exact add_eq_app_of_last hs'ot (by rw [hlast]; exact hheadT)
    | succ k ih =>
      obtain ⟨X, _, hXot, hXh, hXe⟩ := ih
      have hXsh := isOT_sh hV hs'ot hVs hXot
      have hX' : head (sh V (add V ω) X) ≤ ω := by
        rw [head_sh]
        exact le_of_le_of_eq (sh_le_sh hV hs'ot (le_of_lt hVs) (isOT_headT hXot) hωot hXh) hshω
      have happ : add ω (sh V (add V ω) X) = app ω (sh V (add V ω) X) :=
        add_eq_app_of_last hωot (by rw [hωlast]; exact hX')
      have hhd : head (app ω (sh V (add V ω) X)) = ω := by rw [hωf]; rfl
      refine ⟨app ω (sh V (add V ω) X), by rw [hωf]; simp [app], by rw [← happ]; exact isOT_add hωot hXsh,
        by rw [hhd], ?_⟩
      show add (add V ω) (sh V (add V ω) (sub (tqN V (add V ω) t1 (k + 1)) V)) = _
      rw [hXe, ← add_eq_app_of_last hs'ot (by rw [hlast]; exact hXh),
        sub_add_dist X hV hs'ot (le_of_lt hVs), hsubV, add_eq_app_of_last hωot (by rw [hωlast]; exact hXh),
        sh_app, hshω]
      exact add_eq_app_of_last hs'ot (by rw [hlast, hhd])
  obtain ⟨X, hX0, _, _, hXe⟩ := key k
  exact ⟨X, hX0, hXe⟩

theorem t2SeedSVFix_holdsV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L)) : T2SeedSVFix M ρ r L := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrx : r < r + L := par_lt M 0 _ _ hq
  -- the drop and `M.take x`
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := (Ctx.drop (by omega)).1
  have J1 := Ctx.pre (M.length - 1) (by omega) (by omega)
  have hG1 := good3_congr J1.good (agree_of_cons J1.cons hC1 J1.rank)
  rw [show M.length - 1 = r + L by omega] at hRk1 hC1 hG1
  have hTS : M.take (r + L) ≠ SRO := ne_SRO_of_rk hRk1
  obtain ⟨hXT, hJT⟩ := sInvXJ_std (std_take hM (r + L) (by omega)) hTS
  have core : ∀ τ, Cons (M.take (r + L)) τ →
      (sh (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) = t2X1 M r L τ ∨
        t2X1 M r L τ ∈ cutsNSG (succ (ρ.v r)) (sh (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ))) ∧
      AllGeT (psi (succ (succ (ρ.v r))) z z) (t2X1 M r L τ) := by
    intro τ hτ
    have hG : Good3 (M.take (r + L)) τ := good3_congr hG1 (agree_of_cons hC1 hτ hRk1)
    have hvr : τ.v r = ρ.v r := v_take_of_untopped I hlen hrx (topP_sv hlen I.z2 I.z1 hr hq hux) hτ
    rw [← hvr]
    unfold t2X1
    have hTlen : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
    have hrT : r < (M.take (r + L)).length := by omega
    set V := τ.v r with hVdef
    have hVo : isOT V = true := hG.ot_v r hrT
    have hV'o : isOT (succ V) = true := isOT_succ hVo
    have hVV : V < succ V := lt_succ_self V
    obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
    have he2x : entry M 2 (r + L) = 1 := by
      obtain ⟨_, _, _, he2', _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
      have h' : entry M 2 r < entry M 2 (r + L) := he2'
      have := hX.z2 (r + L); omega
    -- the children of `r`
    have hkid : ∀ d ∈ CL (M.take (r + L)) r, succ V < τ.v d ∧ (sh V (succ V) (τ.o d) = τ.o d ∨
        (ChgX M (r + L) true d ∧ τ.o d ∈ cutsHG (succ V) (sh V (succ V) (τ.o d)))) := by
      intro d hd
      have hdc := cl_mem_children hd
      have hdT := (mem_children hdc).2
      have hdx : d < r + L := by omega
      have hpdT : par (M.take (r + L)) 0 d = some r := (mem_children_iff.mp hdc).2
      have hpd : par M 0 d = some r := by rwa [par_take M 0 d hdx] at hpdT
      have hrd := par_lt M 0 d r hpd
      refine ⟨?_, ?_⟩
      · have hcol := t_child_col hX hq (by omega) he2x h1lt (mem_children_iff.mpr ⟨by omega, hpd⟩) (le_of_lt hdx)
        have hcx := t_col_x hX hq (by omega) he2x h1lt
        have he1 : entry (M.take (r + L)) 1 d = entry M 1 r + 1 := by
          rw [entry_take M 1 hdx]; have : entry M 1 d = (col M d).2.1 := rfl; rw [this, hcol, hcx]
        have he2 : entry (M.take (r + L)) 2 d = 1 := by
          rw [entry_take M 2 hdx]; have : entry M 2 d = (col M d).2.2 := rfl; rw [this, hcol, hcx]
        have hm : par (M.take (r + L)) 1 d = some r := by
          rw [par_take M 1 d hdx]; apply par1_of_child hpd
          rw [entry_take M 1 hdx] at he1; omega
        have hWot : isOT (sumN (one :: (children (M.take (r + L)) d).map (bumpTerm (M.take (r + L)) τ d))) = true := by
          apply isOT_sumN
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · rfl
          · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm hG d j
        have hvd : τ.v d = add V (omega (sumN (one :: (children (M.take (r + L)) d).map
            (bumpTerm (M.take (r + L)) τ d)))) := by
          rw [(hτ d hdT).2]; unfold vRhs; rw [if_neg (by omega), if_neg (by omega), hm]
          exact sf_ot (isOT_add hVo (isOT_omega hWot))
        obtain ⟨s', y', hsy⟩ := omega_psi_form (sumN (one :: (children (M.take (r + L)) d).map
          (bumpTerm (M.take (r + L)) τ d)))
        rw [hvd, ← t_add_succ hVo (omega_psi_form _) (bumpOmega_ne_one hτ hG d), hsy]
        exact lt_add_principal s' y' _
      · have hT : TVis (M.take (r + L)) τ r (r + L) d := ⟨hrd, hdx, fun p hp hpd' hne => by
          have := (anc0_par hpd' hne hpdT).le; omega⟩
        exact (sv_main hX hJ I hlen hr hq hux hXT hJT hτ hG hRk1 (rkT := rk) (rk true d) d hT).1 le_rfl
    obtain ⟨hsing, hdec⟩ := cl_vals hτ hG hrT
    have hlevS : ∀ q ∈ summands (sumN ((CL (M.take (r + L)) r).map τ.o)), succ V < lev q := by
      intro q hq
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (summands_sumN_sub hsing q hq)
      have hdT := (mem_children (cl_mem_children hd)).2
      obtain ⟨y, hy⟩ := o_psi_sub hτ hdT
      rw [hy, lev_psi, sf_ot (hG.ot_v d hdT)]; exact (hkid d hd).1
    have hSo := isOT_sumN _ (fun t ht => (hsing t ht).1)
    have hall : AllGeT (psi (succ (succ V)) z z) (spArg V z (sumN ((CL (M.take (r + L)) r).map τ.o))) := by
      intro q hq hlt
      have hge := spArg_summands_ge (a := V) (c := psi (succ (succ V)) z z) ⟨_, _, rfl⟩
        (sumN ((CL (M.take (r + L)) r).map τ.o)) z hSo (fun q hq => by
          obtain ⟨a, b, rfl⟩ := mem_summands_form hq
          have := hlevS _ hq; simp only [lev_psi] at this
          exact psi_le_psi_z (succ_le_of_lt this)) (by simp [summands]) q hq
      exact absurd hlt (not_lt.mpr hge)
    refine ⟨?_, hall⟩
    rcases (CL (M.take (r + L)) r).eq_nil_or_concat with hnil | ⟨L', d0, hLd⟩
    · left; rw [hnil]; show sh V (succ V) z = z; exact sh_z
    rw [List.concat_eq_append] at hLd
    have hd0m : d0 ∈ CL (M.take (r + L)) r := by rw [hLd]; simp
    have hfixL : ∀ d ∈ L', sh V (succ V) (τ.o d) = τ.o d := by
      intro d hd
      rcases (hkid d (by rw [hLd]; simp [hd])).2 with h | ⟨hch, _⟩
      · exact h
      · exfalso
        have hsorted : (CL (M.take (r + L)) r).Pairwise (· < ·) :=
          List.Pairwise.filter _ (children_sorted _ r)
        rw [hLd] at hsorted
        have hdd0 : d < d0 := (List.pairwise_append.mp hsorted).2.2 d hd d0 (by simp)
        have hdcT : d ∈ children (M.take (r + L)) r := cl_mem_children (by rw [hLd]; simp [hd])
        exact chg_last hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hdcT hch d0 (cl_mem_children hd0m) hdd0
          (of_decide_eq_true (List.mem_filter.mp hd0m).2)
    have hLo : ∀ u ∈ L'.map τ.o, isOT u = true := by
      intro u hu; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
      exact hG.ot_o d (mem_children (cl_mem_children (by rw [hLd]; simp [hd]))).2
    have hd0T := (mem_children (cl_mem_children hd0m)).2
    have hd0o := hG.ot_o d0 hd0T
    have hS : sumN ((CL (M.take (r + L)) r).map τ.o) = app (sumN (L'.map τ.o)) (τ.o d0) := by
      rw [hLd, List.map_append, List.map_singleton]
      rw [hLd, List.map_append, List.map_singleton] at hsing hdec
      rw [sumN_append_dec hsing hdec, sumN_singleton (hsing _ (by simp))]
    have hPfix : sh V (succ V) (sumN (L'.map τ.o)) = sumN (L'.map τ.o) := by
      rw [sh_sumN hVo hV'o hVV hLo, List.map_map]
      congr 1
      apply List.map_congr_left
      intro d hd; exact hfixL d hd
    have hPo := isOT_sumN _ hLo
    have hlevP : ∀ q ∈ summands (sumN (L'.map τ.o)), succ V < lev q := by
      intro q hq; apply hlevS; rw [hS, summands_app]; exact List.mem_append_left _ hq
    have hB : spArg (succ V) z (sumN (L'.map τ.o)) = spArg V z (sumN (L'.map τ.o)) :=
      spArg_level (fun q hq => ⟨hlevP q hq, lt_trans hVV (hlevP q hq)⟩)
    have hBf : sh V (succ V) (spArg V z (sumN (L'.map τ.o))) = spArg V z (sumN (L'.map τ.o)) := by
      have := sh_spArg hVo hV'o hVV hVo (le_refl V) (b := z) rfl hPo
        (Or.inr (fun q hq => ne_of_gt (lt_trans hVV (hlevP q hq))))
      rw [shf_self, sh_z, hPfix, hB] at this
      exact this.symm
    have hBo : isOT (spArg V z (sumN (L'.map τ.o))) = true := isOT_spArg _ _ _ rfl hPo
    obtain ⟨u, y, hu⟩ := o_psi_form hτ hd0T
    obtain ⟨u', y', hu'⟩ := sh_single (V := V) (V' := succ V) u y
    have hSo' : isOT (app (sumN (L'.map τ.o)) (psi u y z)) = true := by rw [← hu, ← hS]; exact hSo
    have hlevS' : ∀ q ∈ summands (app (sumN (L'.map τ.o)) (psi u y z)), succ V < lev q := by
      rw [← hu, ← hS]; exact hlevS
    have hσX : sh V (succ V) (spArg V z (app (sumN (L'.map τ.o)) (psi u y z))) =
        spArg (succ V) z (app (sumN (L'.map τ.o)) (psi u' y' z)) := by
      have := sh_spArg hVo hV'o hVV hVo (le_refl V) (b := z) rfl hSo'
        (Or.inr (fun q hq => ne_of_gt (lt_trans hVV (hlevS' q hq))))
      rw [shf_self, sh_z, sh_app, hPfix, hu'] at this
      exact this.symm
    have hY : spArg V z (app (sumN (L'.map τ.o)) (psi u y z)) =
        step V (spArg V z (sumN (L'.map τ.o))) u y z := by
      rw [spArg_app, spArg_cons]; rfl
    have hY' : spArg (succ V) z (app (sumN (L'.map τ.o)) (psi u' y' z)) =
        step (succ V) (spArg V z (sumN (L'.map τ.o))) u' y' z := by
      rw [spArg_app, hB, spArg_cons]; rfl
    rw [hS, hu]
    rw [hS, hu] at hall
    rcases (hkid d0 hd0m).2 with hf0 | ⟨_, hcut0⟩
    · left
      rw [hσX]
      rw [hu, hu'] at hf0
      rw [hf0]
      exact spArg_level (fun q hq => ⟨hlevS' q hq, lt_trans hVV (hlevS' q hq)⟩)
    · right
      rw [hσX]
      apply hg_to_nsg _ hall
      rw [hY, hY']
      have hu0 : succ V < u := by
        have := (hkid d0 hd0m).1
        obtain ⟨yy, hyy⟩ := o_psi_sub hτ hd0T
        rw [hyy, sf_ot (hG.ot_v d0 hd0T)] at hu
        simp only [psi.injEq] at hu
        rw [← hu.1]; exact this
      have hVu : V < u := lt_trans hVV hu0
      have huo : isOT u = true := by rw [hu] at hd0o; exact isOT_sub hd0o
      have hu'u : u ≤ u' := by
        rw [sh_psi_gt hVu, sh_z] at hu'
        simp only [psi.injEq] at hu'
        rw [← hu'.1]; exact le_shf_self hVo hV'o (le_of_lt hVV) huo (le_of_lt hVu)
      exact G.step_cut hVo hV'o hVV (a := V) (a' := succ V) (u := u) (y := y) (u' := u') (y' := y') hBo hBf
        (by rw [← hu]; exact hd0o) hu' (by rw [hu, hu'] at hcut0; exact hcut0)
        ⟨fun _ => psi_lt_psi_z_iff.mpr (Or.inl (lt_of_lt_of_le hu0 hu'u)),
          fun _ => psi_lt_psi_z_iff.mpr (Or.inl hVu)⟩
  exact ⟨fun τ hτ => (core τ hτ).1, fun τ hτ => (core τ hτ).2⟩

theorem t2SeedCFix_ofV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hRes : CRel M ρ r L q) (hBig : T2SeedCBig M ρ r L q) : T2SeedCFix M ρ r L q := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hpq := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 q r hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hrx : r < r + L := by omega
  have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
  have hpq' : par M 0 (r + (q - r)) = some r := by rw [show r + (q - r) = q by omega]; exact hpq
  obtain ⟨Txb, _, _, TCLq, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
  rw [show r + (q - r) = q by omega] at Txb TCLq
  have hqnc := qP_C hM hS I hlen hr hq hqr hncl hRes.un
  -- the drop and `M.take x`
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdrop := (Ctx.drop (by omega)).1
  have J1 := Ctx.pre (M.length - 1) (by omega) (by omega)
  have hG1 := good3_congr J1.good (agree_of_cons J1.cons hC1 J1.rank)
  rw [show M.length - 1 = r + L by omega] at hRk1 hC1 hG1
  have hTS : M.take (r + L) ≠ SRO := ne_SRO_of_rk hRk1
  obtain ⟨hXT, hJT⟩ := sInvXJ_std (std_take hM (r + L) (by omega)) hTS
  have core : ∀ τ, Cons (M.take (r + L)) τ →
      (sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) = t2X1 M r L τ ∨
        t2X1 M r L τ ∈ cutsNSG (qnS M ρ r L q) (sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ))) ∧
      AllGeT (psi (succ (qnS M ρ r L q)) z z) (t2X1 M r L τ) := by
    intro τ hτ
    have hG : Good3 (M.take (r + L)) τ := good3_congr hG1 (agree_of_cons hC1 hτ hRk1)
    have hvr : τ.v r = ρ.v r := v_take_of_untopped I hlen hrx (topP_C hM hS I hlen hr hq hqr) hτ
    have hvq := hRes.vqP τ hτ
    set V' := qnS M ρ r L q with hV'def
    have hWot : isOT (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
        (bumpTerm M ρ q))) = true := by
      apply isOT_sumN
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact isOT_one
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm I.good q j
    have hV'eq : V' = add (τ.v r) (omega (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
        (bumpTerm M ρ q)))) := by rw [hvr]; rfl
    rw [← hvr]
    unfold t2X1
    have hTlen : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
    have hrT : r < (M.take (r + L)).length := by omega
    set V := τ.v r with hVdef
    have hVo : isOT V = true := hG.ot_v r hrT
    have hV'o : isOT V' = true := by rw [hV'eq]; exact isOT_add hVo (isOT_omega hWot)
    have hVV : V < V' := by
      obtain ⟨a, b, hab⟩ := omega_psi_form (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
        (bumpTerm M ρ q)))
      rw [hV'eq, hab]; exact lt_add_principal a b V
    -- children of `r` before `q` are above `s′`
    have hbig : ∀ d ∈ children (M.take (r + L)) r, d < q → V' < τ.v d := by
      intro d hd hdq
      by_cases hcnt : Counted (M.take (r + L)) r d
      · have hdCL : d ∈ CL (M.take (r + L)) r := List.mem_filter.mpr ⟨hd, decide_eq_true hcnt⟩
        obtain ⟨hsing, hdec⟩ := cl_vals hτ hG hrT
        rcases (CL (M.take (r + L)) r).eq_nil_or_concat with hnil | ⟨Lc, c0, hLc⟩
        · rw [hnil] at hdCL; simp at hdCL
        rw [List.concat_eq_append] at hLc
        obtain ⟨s, y, hc0, hs⟩ := hRes.decP τ hτ Lc c0 hLc
        have hc0T : c0 < (M.take (r + L)).length :=
          (mem_children (cl_mem_children (show c0 ∈ CL (M.take (r + L)) r by rw [hLc]; simp))).2
        have hdT := (mem_children hd).2
        have hvc0 : τ.v c0 = s := by
          rw [o_cl_eq hτ hG hc0T] at hc0; simp only [psi.injEq] at hc0; exact hc0.1
        have hle : τ.o c0 ≤ τ.o d := by
          rw [hLc] at hdCL hdec
          rcases List.mem_append.mp hdCL with h | h
          · have := (List.pairwise_append.mp (List.pairwise_map.mp hdec)).2.2 d h c0 (by simp)
            exact this
          · simp at h; rw [h]
        have hl := lev_le_of_le hle
        rw [o_cl_eq hτ hG hc0T, o_cl_eq hτ hG hdT] at hl
        simp only [lev_psi] at hl
        rw [hvc0] at hl
        exact lt_of_lt_of_le hs hl
      · exact hBig.big τ hτ d hd hdq hcnt
    -- the children of `r`
    have hkid : ∀ d ∈ CL (M.take (r + L)) r, V' < τ.v d ∧ (sh V V' (τ.o d) = τ.o d ∨
        (ChgX M (r + L) true d ∧ τ.o d ∈ cutsHG V' (sh V V' (τ.o d)))) := by
      intro d hd
      have hdc := cl_mem_children hd
      have hdT := (mem_children hdc).2
      have hdx : d < r + L := by omega
      have hpdT : par (M.take (r + L)) 0 d = some r := (mem_children_iff.mp hdc).2
      have hpd : par M 0 d = some r := by rwa [par_take M 0 d hdx] at hpdT
      have hrd := par_lt M 0 d r hpd
      have hdq : d < q := by
        rcases lt_trichotomy d q with h | h | h
        · exact h
        · exfalso; rw [h] at hd; exact hqnc (of_decide_eq_true (List.mem_filter.mp hd).2)
        · exfalso
          have hAqd : Anc0 M q d := anc_between (anc0_of_par M 0 q (r + L) hq) d (le_of_lt h) (le_of_lt hdx)
          have := (anc0_par hAqd (by omega) hpd).le; omega
      have hcntd : Counted (M.take (r + L)) r d := of_decide_eq_true (List.mem_filter.mp hd).2
      refine ⟨hbig d hdc hdq, ?_⟩
      · have hT : TVis (M.take (r + L)) τ r (r + L) d := ⟨hrd, hdx, fun p hp hpd' hne => by
          have := (anc0_par hpd' hne hpdT).le; omega⟩
        exact (c_main hX hJ I hlen hr hq hqr hpq Txb TCLq hXT hJT hτ hG hRk1 (rkT := rk) hV'eq
          (omega_psi_form _) (isOT_omega hWot) hvq hbig (rk true d) d hT
          (fun p hp => by rw [hpdT] at hp; cases hp; exact hcntd.1)).1 le_rfl
    obtain ⟨hsing, hdec⟩ := cl_vals hτ hG hrT
    have hlevS : ∀ q ∈ summands (sumN ((CL (M.take (r + L)) r).map τ.o)), V' < lev q := by
      intro q hq
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (summands_sumN_sub hsing q hq)
      have hdT := (mem_children (cl_mem_children hd)).2
      obtain ⟨y, hy⟩ := o_psi_sub hτ hdT
      rw [hy, lev_psi, sf_ot (hG.ot_v d hdT)]; exact (hkid d hd).1
    have hSo := isOT_sumN _ (fun t ht => (hsing t ht).1)
    have hall : AllGeT (psi (succ V') z z) (spArg V z (sumN ((CL (M.take (r + L)) r).map τ.o))) := by
      intro q hq hlt
      have hge := spArg_summands_ge (a := V) (c := psi (succ V') z z) ⟨_, _, rfl⟩
        (sumN ((CL (M.take (r + L)) r).map τ.o)) z hSo (fun q hq => by
          obtain ⟨a, b, rfl⟩ := mem_summands_form hq
          have := hlevS _ hq; simp only [lev_psi] at this
          exact psi_le_psi_z (succ_le_of_lt this)) (by simp [summands]) q hq
      exact absurd hlt (not_lt.mpr hge)
    refine ⟨?_, hall⟩
    rcases (CL (M.take (r + L)) r).eq_nil_or_concat with hnil | ⟨L', d0, hLd⟩
    · left; rw [hnil]; show sh V V' z = z; exact sh_z
    rw [List.concat_eq_append] at hLd
    have hd0m : d0 ∈ CL (M.take (r + L)) r := by rw [hLd]; simp
    have hfixL : ∀ d ∈ L', sh V V' (τ.o d) = τ.o d := by
      intro d hd
      rcases (hkid d (by rw [hLd]; simp [hd])).2 with h | ⟨hch, _⟩
      · exact h
      · exfalso
        have hsorted : (CL (M.take (r + L)) r).Pairwise (· < ·) :=
          List.Pairwise.filter _ (children_sorted _ r)
        rw [hLd] at hsorted
        have hdd0 : d < d0 := (List.pairwise_append.mp hsorted).2.2 d hd d0 (by simp)
        have hdcT : d ∈ children (M.take (r + L)) r := cl_mem_children (by rw [hLd]; simp [hd])
        exact chg_last hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hdcT hch d0 (cl_mem_children hd0m) hdd0
          (of_decide_eq_true (List.mem_filter.mp hd0m).2)
    have hLo : ∀ u ∈ L'.map τ.o, isOT u = true := by
      intro u hu; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
      exact hG.ot_o d (mem_children (cl_mem_children (by rw [hLd]; simp [hd]))).2
    have hd0T := (mem_children (cl_mem_children hd0m)).2
    have hd0o := hG.ot_o d0 hd0T
    have hS : sumN ((CL (M.take (r + L)) r).map τ.o) = app (sumN (L'.map τ.o)) (τ.o d0) := by
      rw [hLd, List.map_append, List.map_singleton]
      rw [hLd, List.map_append, List.map_singleton] at hsing hdec
      rw [sumN_append_dec hsing hdec, sumN_singleton (hsing _ (by simp))]
    have hPfix : sh V V' (sumN (L'.map τ.o)) = sumN (L'.map τ.o) := by
      rw [sh_sumN hVo hV'o hVV hLo, List.map_map]
      congr 1
      apply List.map_congr_left
      intro d hd; exact hfixL d hd
    have hPo := isOT_sumN _ hLo
    have hlevP : ∀ q ∈ summands (sumN (L'.map τ.o)), V' < lev q := by
      intro q hq; apply hlevS; rw [hS, summands_app]; exact List.mem_append_left _ hq
    have hB : spArg V' z (sumN (L'.map τ.o)) = spArg V z (sumN (L'.map τ.o)) :=
      spArg_level (fun q hq => ⟨hlevP q hq, lt_trans hVV (hlevP q hq)⟩)
    have hBf : sh V V' (spArg V z (sumN (L'.map τ.o))) = spArg V z (sumN (L'.map τ.o)) := by
      have := sh_spArg hVo hV'o hVV hVo (le_refl V) (b := z) rfl hPo
        (Or.inr (fun q hq => ne_of_gt (lt_trans hVV (hlevP q hq))))
      rw [shf_self, sh_z, hPfix, hB] at this
      exact this.symm
    have hBo : isOT (spArg V z (sumN (L'.map τ.o))) = true := isOT_spArg _ _ _ rfl hPo
    obtain ⟨u, y, hu⟩ := o_psi_form hτ hd0T
    obtain ⟨u', y', hu'⟩ := sh_single (V := V) (V' := V') u y
    have hSo' : isOT (app (sumN (L'.map τ.o)) (psi u y z)) = true := by rw [← hu, ← hS]; exact hSo
    have hlevS' : ∀ q ∈ summands (app (sumN (L'.map τ.o)) (psi u y z)), V' < lev q := by
      rw [← hu, ← hS]; exact hlevS
    have hσX : sh V V' (spArg V z (app (sumN (L'.map τ.o)) (psi u y z))) =
        spArg V' z (app (sumN (L'.map τ.o)) (psi u' y' z)) := by
      have := sh_spArg hVo hV'o hVV hVo (le_refl V) (b := z) rfl hSo'
        (Or.inr (fun q hq => ne_of_gt (lt_trans hVV (hlevS' q hq))))
      rw [shf_self, sh_z, sh_app, hPfix, hu'] at this
      exact this.symm
    have hY : spArg V z (app (sumN (L'.map τ.o)) (psi u y z)) =
        step V (spArg V z (sumN (L'.map τ.o))) u y z := by
      rw [spArg_app, spArg_cons]; rfl
    have hY' : spArg V' z (app (sumN (L'.map τ.o)) (psi u' y' z)) =
        step V' (spArg V z (sumN (L'.map τ.o))) u' y' z := by
      rw [spArg_app, hB, spArg_cons]; rfl
    rw [hS, hu]
    rw [hS, hu] at hall
    rcases (hkid d0 hd0m).2 with hf0 | ⟨_, hcut0⟩
    · left
      rw [hσX]
      rw [hu, hu'] at hf0
      rw [hf0]
      exact spArg_level (fun q hq => ⟨hlevS' q hq, lt_trans hVV (hlevS' q hq)⟩)
    · right
      rw [hσX]
      apply hg_to_nsg _ hall
      rw [hY, hY']
      have hu0 : V' < u := by
        have := (hkid d0 hd0m).1
        obtain ⟨yy, hyy⟩ := o_psi_sub hτ hd0T
        rw [hyy, sf_ot (hG.ot_v d0 hd0T)] at hu
        simp only [psi.injEq] at hu
        rw [← hu.1]; exact this
      have hVu : V < u := lt_trans hVV hu0
      have huo : isOT u = true := by rw [hu] at hd0o; exact isOT_sub hd0o
      have hu'u : u ≤ u' := by
        rw [sh_psi_gt hVu, sh_z] at hu'
        simp only [psi.injEq] at hu'
        rw [← hu'.1]; exact le_shf_self hVo hV'o (le_of_lt hVV) huo (le_of_lt hVu)
      exact G.step_cut hVo hV'o hVV (a := V) (a' := V') (u := u) (y := y) (u' := u') (y' := y') hBo hBf
        (by rw [← hu]; exact hd0o) hu' (by rw [hu, hu'] at hcut0; exact hcut0)
        ⟨fun _ => psi_lt_psi_z_iff.mpr (Or.inl (lt_of_lt_of_le hu0 hu'u)),
          fun _ => psi_lt_psi_z_iff.mpr (Or.inl hVu)⟩
  exact ⟨fun τ hτ => (core τ hτ).1, fun τ hτ => (core τ hτ).2⟩

theorem seed_frames_qrV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) (hRes : QRRel M ρ r L Lc)
    {τ0 : Valn} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : ∃ rk0, Rk (M.take (r + L)) rk0)
    (hP : PH3cG M ρ) (hF : FC3 M ρ) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat),
        CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r =
          Lc' ++ c :: R' →
        QPHs (σ.v r) (Lc'.map σ.o) (σ.o c) ∧ QF3s (σ.v r) (Lc'.map σ.o) (σ.o c) := by
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
  have hQM1 := clField_qT2P I.cons I.fo hP r hrM
  have hQM2 := clField_qT2F I.cons I.fo hF r hrM
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
        seed_frame_data_qrV3 hM hS I Ctx hz h2 hlen hr hq hXu hCLM (le_refl 2) hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hox
      rw [show (2 - 1 : Nat) = 1 from rfl, hP1] at hox
      exact ⟨_, hox, Or.inl ⟨rfl, hRes.w1 τ0 hC0⟩, hCLN, hvr, hLc⟩
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      obtain ⟨hCLN, hvr, hLc, hox⟩ :=
        seed_frame_data_qrV3 hM hS I Ctx hz h2 hlen hr hq hXu hCLM hn hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hox
      have hval := seed_r_value_qrV3 hM hS I Ctx hz h2 hlen hr hq hXu hCLM hRes hC0 ⟨_, hR0.choose_spec⟩ (n - 1)
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
  refine ⟨seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => (hQM1 Lc' c R' h).2) ?_ Lc' c R' hCL,
    seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => (hQM2 Lc' c R' h).2) ?_ Lc' c R' hCL⟩
  · -- PH3cG at the last frame
    rw [hox]
    intro s y c0 hc ht hBz
    simp only [psi.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    rcases hcase with ⟨_, hnr⟩ | ⟨hn3, hY⟩
    · exact absurd ht.1 hnr
    · rw [hY]
      exact seed_last_kind hVot hσB hBc hRes.ks (n - 3)
  · -- FC3 at the last frame
    rw [hox]
    intro s y c0 hc ht hL _
    simp only [psi.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    rcases hcase with ⟨_, hnr⟩ | ⟨hn3, hY⟩
    · exact absurd ht.1 hnr
    · rw [hY]
      have hLc0 : Lc = [] := List.map_eq_nil_iff.mp hL
      exact seed_last_fc3 hVot hσB hBc hRes.ks (n - 3) (by rw [hLc0]; rfl)

theorem seed_frames_qnV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) (hRes : QNRel M ρ r L q Lc)
    (hFC : T2SeedQNFC M ρ r L q Lc)
    {τ0 : Valn} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : ∃ rk0, Rk (M.take (r + L)) rk0)
    (hP : PH3cG M ρ) (hF : FC3 M ρ) :
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
  have hQM1 := clField_qT2P I.cons I.fo hP r hrM
  have hQM2 := clField_qT2F I.cons I.fo hF r hrM
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
        seed_frame_data_qnV3 hM hS I Ctx hz h2 hlen hr hq hqr hCLM (le_refl 2) hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hCLNq hoq
      rw [show (2 - 1 : Nat) = 1 from rfl, hP1, ht1, hv0] at hoq
      rw [hvq, qnS_vxs] at hvx
      rw [hvq, hvx, spArg_nil] at hoq
      exact ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      obtain ⟨hCLN, hCLNq, hvr, hLc, hvx, hoq⟩ :=
        seed_frame_data_qnV3 hM hS I Ctx hz h2 hlen hr hq hqr hCLM hn hCN hRN hCP hGP hRP
      rw [← hd0def, ← hd1def] at hCLN hCLNq hoq
      have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
      have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hqP : q < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hval := seed_r_value_qnV3 hM hS I Ctx hz h2 hlen hr hq hqr hCLM hRes hC0 hR0 hv0 ht1
        (fun k => ⟨(hch k).1, (hch k).2⟩) (n - 1) (by omega)
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
  have hts : ¬ shf V s' t < succ s' := (hch (n - 2)).2
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
  · -- the frames of `r`
    rw [hi] at hCL ⊢
    refine ⟨seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => (hQM1 Lc' c R' h).2) ?_ Lc' c R' hCL,
      seed_frames_lift hCLM hCLN hvr hLc (fun Lc' c R' h => (hQM2 Lc' c R' h).2) ?_ Lc' c R' hCL⟩
    · rw [hoq]
      intro s y c0 hc _ _
      simp only [psi.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      rw [split_all_ge hhigh]
      refine Or.inr ⟨fun h => ?_, Or.inl ⟨_, by simp, rfl⟩⟩
      have := app_eq_self_iff h; simp at this
    · rw [hoq]
      intro s y c0 hc _ hL _
      simp only [psi.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      have hLc0 : Lc = [] := List.map_eq_nil_iff.mp hL
      obtain ⟨X, hX0, hXe⟩ := hFC hLc0 τ0 hC0 t1 ht1 (n - 2)
      refine ⟨fun h => absurd h (ne_of_gt hVs'), fun _ => ⟨X, hX0, ?_⟩⟩
      rw [split_all_ge hhigh, show B = z by rw [hBdef, hLc0]; rfl, app_z, lev_psi]
      exact hXe
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
    refine ⟨fun _ => ⟨ne_of_gt (lt_of_le_of_lt (z_le V) hVs'), ?_⟩, fun h => absurd rfl h⟩
    -- `last s′ = ω^W ≠ 1`
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
    rw [hs'def]; unfold qnS; rw [hW]
    obtain ⟨P0, hP0, _⟩ := add_eq_app_prefix (ρ.v r) (psi s0 y0 z)
    rw [hP0, last_app P0 (by simp)]
    exact hne1

theorem seed_frames_svV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (hRes : SVRel M ρ r L) (hFix : T2SeedSVFix M ρ r L)
    {τ0 : Valn} {rk0 : Bool → Nat → Nat} (hC0 : Cons (M.take (r + L)) τ0) (hR0 : Rk (M.take (r + L)) rk0)
    (hT : FrameOT (M.take (r + L)) τ0 ∧ PH3cG (M.take (r + L)) τ0 ∧ FC3 (M.take (r + L)) τ0) :
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
        QPHs (σ.v r) (Lc'.map σ.o) (σ.o c) ∧ QF3s (σ.v r) (Lc'.map σ.o) (σ.o c) := by
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
  have hQT1 := clField_qT2P hC0 hT.1 hT.2.1 r hrT
  have hQT2 := clField_qT2F hC0 hT.1 hT.2.2 r hrT
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
        seed_frame_data_svV3 hM hS I Ctx hz h2 hlen hr hq hux (topP_sv hlen I.z2 I.z1 hr hq hux) (le_refl 2) hCN hRN hCP hGP hRP hC0 hG0 hR0
      rw [← hd0def, ← hd1def] at hCLN hox
      rw [show (2 - 1 : Nat) = 1 from rfl, hP1, hvP, ← hX1e] at hox
      exact ⟨hox, hCLN, hvr, hval⟩
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      obtain ⟨hCLN, hvr, hval, hox⟩ :=
        seed_frame_data_svV3 hM hS I Ctx hz h2 hlen hr hq hux (topP_sv hlen I.z2 I.z1 hr hq hux) hn hCN hRN hCP hGP hRP hC0 hG0 hR0
      rw [← hd0def, ← hd1def] at hCLN hox
      have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
      have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hval' := seed_r_value_svV3 hM hS I Ctx hz h2 hlen hr hq hux hRes hC0 hR0 (n - 1) (by omega)
        (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP (cl_vals hCP hGP hrP).2
      have hform := o_cl_eq hCP hGP hrP
      rw [hval'] at hform
      simp only [psi.injEq] at hform
      have h21 := hform.2.1
      rw [← hform.1] at h21
      rw [← hform.1, ← h21, show n - 1 - 1 = n - 2 by omega] at hox
      exact ⟨hox, hCLN, hvr, hval⟩
  -- the levels below `n` are standard
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
      have hv := seed_r_value_svV3 hM hS I Ctx hz h2 hlen hr hq hux hRes hC0 hR0 (j + 1) (by omega)
        (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCj (cl_vals hCj hGj hrj).2
      have := hGj.ot_o r hrj
      rw [hv, show j + 1 - 1 = j by omega] at this
      exact this
  have hBhi := hFix.hi τ0 hC0
  have hFx := hFix.fix τ0 hC0
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
  refine ⟨seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr hval
      (fun Lc' c R' h => (hQT1 Lc' c R' h).2) ?_ Lc' c R' hCL,
    seed_frames_liftE (G := M.take (r + L)) (E := []) (by simp) hCLN hvr hval
      (fun Lc' c R' h => (hQT2 Lc' c R' h).2) ?_ Lc' c R' hCL⟩
  · -- PH3cG at the last frame
    rw [hox]
    intro s y c0 hc ht _
    simp only [psi.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    have hst : spArg (τ0.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o)) = X1 := rfl
    rw [hst] at ht ⊢
    exact seed_kind hVot hV' hVV hX1ot (isOT_shIt hVot hV' hVV hX1ot (n - 2)) hBhi hFx (hE (n - 2) (by omega)) ht.1
  · -- FC3 at the last frame: the state is `0` and nothing rewrites
    rw [hox]
    intro s y c0 hc ht hL _
    simp only [psi.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    have hLc0 : CL (M.take (r + L)) r = [] := List.map_eq_nil_iff.mp hL
    have hX0 : X1 = z := by rw [hX1e, hLc0]; rfl
    have hst : spArg (τ0.v r) z (sumN ((CL (M.take (r + L)) r).map τ0.o)) = X1 := rfl
    rw [hst, hX0, shIt_z, sh_z] at ht
    exact absurd ht.1 (lt_irrefl' _)

theorem seed_frames_CV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hRes : CRel M ρ r L q) (hFix : T2SeedCFix M ρ r L q)
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
      obtain ⟨hCLN, hval, hvr, hvx, hoq, hCLNq⟩ := C_frameV3 hM hS I Ctx hz h2 hlen hr hq hqr (qP_C hM hS I hlen hr hq hqr hncl hRes.un) hRes.un
        (le_refl 2) hCN hRN hCP hGP hRP hC0 hG0 hR0 hv0 hvq0
      rw [← hd0def, ← hd1def] at hCLN hoq hCLNq
      rw [hvq, qnS_vxs] at hvx
      rw [show (2 - 1 : Nat) = 1 from rfl, hP1, hv0, hvq, hvx, ← hX1e] at hoq
      exact ⟨hCLN, hval, hvr, hvx, hoq, hCLNq⟩
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP : Cons (TRIO.gexp M r L d0 d1 (n - 1)) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      obtain ⟨hCLN, hval, hvr, hvx, hoq, hCLNq⟩ := C_frameV3 hM hS I Ctx hz h2 hlen hr hq hqr (qP_C hM hS I hlen hr hq hqr hncl hRes.un) hRes.un
        hn hCN hRN hCP hGP hRP hC0 hG0 hR0 hv0 hvq0
      rw [← hd0def, ← hd1def] at hCLN hoq hCLNq
      have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
      have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hqP : q < (TRIO.gexp M r L d0 d1 (n - 1)).length := by
        have : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
        omega
      have hval' := seed_r_value_CV3 hM hS I Ctx hz h2 hlen hr hq hqr hncl hRes hC0 hR0 (n - 1) (by omega)
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
      have hv := seed_r_value_CV3 hM hS I Ctx hz h2 hlen hr hq hqr hncl hRes hC0 hR0 (j + 1) (by omega)
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

end Ytosk.V3Main.SeedPF
