/-
**3 行・t = 2・q ≠ r（q が r の最後の数える子）: 種 r = P_0(q) の ◁（SeedL）を M と M.take x だけの性質から。**

n の強い帰納法で、M[n] の r の値は ψ_V(B + Ω_{t_{n−1}})（`seed_r_value_qn`）。t_0 = t_1′ は M.take x での r の
最後の子の添字、t_{k+1} = σ_{V, s′}(t_k)、s′ = v_N(q)（`qnS`、どの段でも同じ）。各段は `qn_step`（V3T2SeedQNL）。
o_M(r) = ψ_V(B + Ω_s)（s = v(q)、CL(q) = []）。ψ_V(B + Ω_t) ◁ ψ_V(B + Ω_s) は seed_frame_lhd を s′ := t で使う。
残り `T2SeedQNRes` は M と M.take x だけの性質。
-/
import Ytosk.V3T2SeedQNL
import Ytosk.V3ExpT2BD

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- **`V + last(s′) = s′`** for `s′ = V + ω^{…}` (`ω^·` is a single summand). -/
theorem qnS_vxs (M : Mat) (ρ : Valn) (r L q : Nat) : add (ρ.v r) (last (qnS M ρ r L q)) = qnS M ρ r L q := by
  unfold qnS
  obtain ⟨s, y, hW⟩ := omega_psi_form (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
    (bumpTerm M ρ q)))
  rw [hW]
  obtain ⟨P, hP, _⟩ := add_eq_app_prefix (ρ.v r) (psi s y z)
  rw [hP, last_app P (by simp), show last (psi s y z) = psi s y z from rfl, hP]

/-- `s′` is standard. -/
theorem qnS_ot {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) {r : Nat} (hr : r < M.length)
    (L q : Nat) : isOT (qnS M ρ r L q) = true := by
  unfold qnS
  refine isOT_add (I.good.ot_v r hr) (isOT_omega (isOT_sumN _ ?_))
  intro t ht
  simp only [List.mem_cons, List.mem_map] at ht
  rcases ht with rfl | ⟨d, _, rfl⟩
  · rfl
  · exact isOT_bumpTerm I.good q d

/-- `V < s′`. -/
theorem qnS_gt (M : Mat) (ρ : Valn) (r L q : Nat) : ρ.v r < qnS M ρ r L q := by
  unfold qnS
  obtain ⟨s, y, hW⟩ := omega_psi_form (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map
    (bumpTerm M ρ q)))
  rw [hW]; exact lt_add_principal s y _

/-- **The residual of the seed `r`** (`t = 2`, `q ≠ r`, `q` the last counted child of `r`):
properties of `M` and `M.take x`. -/
structure T2SeedQNRes (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop where
  σB : sh (ρ.v r) (qnS M ρ r L q) (t2B (ρ.v r) ρ Lc) = t2B (ρ.v r) ρ Lc
  Bc : ∀ g ∈ summands (t2B (ρ.v r) ρ Lc), ¬ g < psi (succ (qnS M ρ r L q)) z z
  base : ∀ τ, Cons (M.take (r + L)) τ → τ.v r = ρ.v r ∧ ∃ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ∧
    ∀ k, ρ.v r < tqN (ρ.v r) (qnS M ρ r L q) t1 k ∧
      ¬ shf (ρ.v r) (qnS M ρ r L q) (tqN (ρ.v r) (qnS M ρ r L q) t1 k) < succ (qnS M ρ r L q) ∧
      (1 ≤ k → tqN (ρ.v r) (qnS M ρ r L q) t1 k < ρ.v q ∧
        (tqN (ρ.v r) (qnS M ρ r L q) t1 k = ρ.v q ∨ Lhd z (tqN (ρ.v r) (qnS M ρ r L q) t1 k) (ρ.v q)))

/-- **The seed `r` of `M` itself** with a leaf as last counted child: `o_M(r) = ψ_V(B + Ω_s)`. -/
theorem leaf_M_side {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r c : Nat} {s : T} (hrM : r < M.length) {Lc : List Nat} (hCLM : CL M r = Lc ++ [c])
    (hoc : ρ.o c = psi s z z) :
    (∀ g ∈ summands (t2B (ρ.v r) ρ Lc), psi s z z ≤ g) ∧ isOT (t2B (ρ.v r) ρ Lc) = true ∧
      ρ.o r = psi (ρ.v r) (app (t2B (ρ.v r) ρ Lc) (psi s z z)) z := by
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hrM
  have hsM' := hsM
  have hpM' := hpM
  rw [hCLM] at hsM hpM
  simp only [List.map_append, List.map_singleton] at hsM hpM
  have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht))
    (List.pairwise_append.mp hpM).1
  have hBc : ∀ g ∈ summands (t2B (ρ.v r) ρ Lc), psi s z z ≤ g := by
    apply spArg_summands_ge ⟨_, _, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro g hg; rw [← hoc]
      exact (List.pairwise_append.mp hpM).2.2 g hg _ (by simp)
    · simp [summands]
  have hBot : isOT (t2B (ρ.v r) ρ Lc) = true := isOT_arg (I.fo r hrM Lc c [] (by rw [hCLM]))
  refine ⟨hBc, hBot, ?_⟩
  rw [o_last_form I.cons hrM hVot hCLM (fun c hc => hsM' _ (List.mem_map_of_mem hc)) hpM' hoc]
  congr 1
  apply step_app_leaf hBot (T.not_lt_z _)
  intro hBz
  exact hBc _ (last_mem_summands hBz)

/-- **The value of the seed `r` in every `M[n]`** (`n ≥ 2`, `q ≠ r`): `ψ_V(B + Ω_{t_{n−1}})`. -/
theorem seed_r_value_qn {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) (hRes : T2SeedQNRes M ρ r L q Lc)
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
    obtain ⟨hvx, hor⟩ := o_r_level_qn hM hS I R hz h2 hlen hr hq hqr hCLM hn hCN hRN hCP hGP hRP hqOT hdecN
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

/-- **SeedL for `q ≠ r`** (`q` the last counted child of `r`): `o_N(r) ◁ o_M(r)` for every `M[n]` (`n ≥ 2`). -/
theorem seedL_qn {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) (hRes : T2SeedQNRes M ρ r L q Lc) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      isOT (σ.o q) = true →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
        Lhd z (σ.o r) (ρ.o r) := by
  intro n hn hGlow σ hCN hqOT hdecN
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hrM : r < M.length := by omega
  have hqcl : q ∈ CL M r := by rw [hCLM]; simp
  have hpq : par M 0 q = some r := (mem_children_iff.mp (cl_mem_children hqcl)).2
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqx : q < r + L := par_lt M 0 _ _ hq
  -- `CL M q = []`, so `o_M(q) = Ω_{v(q)}`
  obtain ⟨qp, rfl⟩ : ∃ qp, q = r + qp := ⟨q - r, by omega⟩
  obtain ⟨_, _, _, Tclq, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq
  have hoq : ρ.o (r + qp) = psi (ρ.v (r + qp)) z z := by
    rw [o_cl_eq I.cons I.good (show r + qp < M.length by omega), Tclq]; rfl
  obtain ⟨_, _, hoM⟩ := leaf_M_side I hrM hCLM hoq
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  obtain ⟨hv0, t1, ht1, hch⟩ := hRes.base _ hC0
  rw [seed_r_value_qn hM hS I R hz h2 hlen hr hq hqr hCLM hRes hC0 ⟨rk, hRk1⟩ hv0 ht1
    (fun k => ⟨(hch k).1, (hch k).2.1⟩) n hn hGlow σ hCN hqOT hdecN, hoM]
  obtain ⟨hat, _, hlast⟩ := hch (n - 1)
  obtain ⟨hts, hlhd⟩ := hlast (by omega)
  apply seed_frame_lhd (s' := tqN (ρ.v r) (qnS M ρ r L (r + qp)) t1 (n - 1)) hat (le_refl _)
    (app_lt_app_left _ (psi_lt_psi_z_iff.mpr (Or.inl hts))) hlhd
  intro u hu g hg
  have htu : ¬ tqN (ρ.v r) (qnS M ρ r L (r + qp)) t1 (n - 1) < u := fun h =>
    hu (lt_trans' hat h)
  rw [comps_app, comps_psi_z_of_ge htu] at hg
  simp only [comps, List.nil_append, List.mem_append, List.mem_cons] at hg
  rcases hg with hg | rfl | hg
  · exact Or.inr ⟨g, by simp [hg], le_refl _⟩
  · exact Or.inl (z_le _)
  · exact Or.inr ⟨g, by simp [hg], le_refl _⟩

end Ytosk
