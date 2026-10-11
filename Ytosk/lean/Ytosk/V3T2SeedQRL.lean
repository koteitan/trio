/-
**3 行・t = 2・q = r（x への上げなし）: 種 r の ◁（SeedL）を M だけの性質から。**

n の強い帰納法で、M[n] の r の値は ψ_V(seqZ V B W_1 (n − 2))（o_r_level_qr）。W_1 は M.take x の r の引数の
σ_{v′(r), V+1} 像。seqZ_lhd で ψ_V(seqZ …) ◁ ψ_V(B + Ω_s) = o_M(r)。
残り `T2SeedQRRes` は M と M.take x だけの性質: σ(B) = B、V + k < s、V + 1 ◁ s、¬ B < W_1、閉じた形の成分の押さえ。
-/
import Ytosk.V3T2SeedQR

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- The state before `x` at `r`. -/
def t2B (V : T) (ρ : Valn) (Lc : List Nat) : T := spArg V z (sumN (Lc.map ρ.o))

/-- The base `W₁ = σ_{v′(r), V+1}(arg of o′(r))` from a valuation `τ` of `M.take x`. -/
def t2W1 (P : Mat) (V : T) (τ : Valn) (r : Nat) : T :=
  sh (τ.v r) (succ V) (spArg (τ.v r) z (sumN ((CL P r).map τ.o)))

/-- **The residual of the seed `r`** (`t = 2`, `q = r`, no upgrade into `x`): properties of `M` and `M.take x`. -/
structure T2SeedQRRes (M : Mat) (ρ : Valn) (r L : Nat) (Lc : List Nat) : Prop where
  σB : sh (ρ.v r) (succ (ρ.v r)) (t2B (ρ.v r) ρ Lc) = t2B (ρ.v r) ρ Lc
  ks : ∀ k, addN (ρ.v r) k < ρ.v (r + L)
  vs : succ (ρ.v r) = ρ.v (r + L) ∨ Lhd z (succ (ρ.v r)) (ρ.v (r + L))
  w1 : ∀ τ, Cons (M.take (r + L)) τ → ¬ t2B (ρ.v r) ρ Lc < t2W1 (M.take (r + L)) (ρ.v r) τ r
  dom : ∀ τ, Cons (M.take (r + L)) τ → ∀ k u, ¬ lt (ρ.v r) u = true →
    ∀ g ∈ comps u (app (t2B (ρ.v r) ρ Lc)
      (psi (addN (ρ.v r) (k + 1)) (shN (ρ.v r) k (t2W1 (M.take (r + L)) (ρ.v r) τ r)) z)),
      g ≤ app (t2B (ρ.v r) ρ Lc)
        (psi (addN (ρ.v r) (k + 1)) (shN (ρ.v r) k (t2W1 (M.take (r + L)) (ρ.v r) τ r)) z) ∨
      ∃ d ∈ comps u (t2B (ρ.v r) ρ Lc) ++ comps u (ρ.v r) ++ comps u (succ (ρ.v r)), g ≤ d

/-- `step` with the leaf `Ω_s` (or any child below the last summand of `B`) just appends. -/
theorem step_app_leaf {a B s y : T} (hB : isOT B = true) (hnr : ¬ B < y)
    (hlast : B ≠ z → psi s y z ≤ last B) : step a B s y z = app B (psi s y z) := by
  unfold step
  rw [if_neg (fun h => hnr h.1)]
  by_cases hBz : B = z
  · subst hBz; rfl
  · exact add_eq_app_of_last hB (by simpa [head] using hlast hBz)

/-- **The value of the seed `r` in every `M[n]`** (`n ≥ 2`): `ψ_V(seqZ V B W₁ (n − 2))`. -/
theorem seed_r_value_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) (hRes : T2SeedQRRes M ρ r L Lc)
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
    have h := o_r_level_qr hM hS I R hz h2 hlen hr hq hXu hCLM (le_refl 2) hCN hRN hCP hGP hRP hks1
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
    have h := o_r_level_qr hM hS I R hz h2 hlen hr hq hXu hCLM hn hCN hRN hCP hGP hRP hks1
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

/-- **The seed `r` of `M` itself**: `o_M(r) = ψ_V(B + Ω_s)`, the summands of `B` are at least `Ω_s`. -/
theorem qr_M_side {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hrx : r < r + L)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) :
    (∀ q ∈ summands (t2B (ρ.v r) ρ Lc), psi (ρ.v (r + L)) z z ≤ q) ∧ isOT (t2B (ρ.v r) ρ Lc) = true ∧
      ρ.o r = psi (ρ.v r) (app (t2B (ρ.v r) ρ Lc) (psi (ρ.v (r + L)) z z)) z := by
  have hrM : r < M.length := by omega
  have hxM : r + L < M.length := by omega
  have hVot : isOT (ρ.v r) = true := I.good.ot_v r hrM
  obtain ⟨hsM, hpM⟩ := cl_vals I.cons I.good hrM
  have hsM' := hsM
  have hpM' := hpM
  rw [hCLM] at hsM hpM
  simp only [List.map_append, List.map_singleton] at hsM hpM
  have hoxM : ρ.o (r + L) = psi (ρ.v (r + L)) z z := by
    rw [o_cl_eq I.cons I.good hxM]
    have : CL M (r + L) = [] := by
      unfold CL; rw [children_last_nil hlen]; rfl
    rw [this]; rfl
  have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht))
    (List.pairwise_append.mp hpM).1
  have hBc : ∀ q ∈ summands (t2B (ρ.v r) ρ Lc), psi (ρ.v (r + L)) z z ≤ q := by
    apply spArg_summands_ge ⟨_, _, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
    · rw [hLs.2]; intro q hq; rw [← hoxM]
      exact (List.pairwise_append.mp hpM).2.2 q hq _ (by simp)
    · simp [summands]
  have hBot : isOT (t2B (ρ.v r) ρ Lc) = true := isOT_arg (I.fo r hrM Lc (r + L) [] (by rw [hCLM]))
  refine ⟨hBc, hBot, ?_⟩
  rw [o_last_form I.cons hrM hVot hCLM (fun c hc => hsM' _ (List.mem_map_of_mem hc))
    hpM' hoxM]
  congr 1
  apply step_app_leaf hBot (T.not_lt_z _)
  intro hBz
  exact hBc _ (last_mem_summands hBz)

/-- **SeedL for `q = r` without an upgrade into `x`**: `o_N(r) ◁ o_M(r)` for every `M[n]` (`n ≥ 2`). -/
theorem seedL_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) (hRes : T2SeedQRRes M ρ r L Lc) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
        Lhd z (σ.o r) (ρ.o r) := by
  intro n hn hGlow σ hCN
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hrM : r < M.length := by omega
  obtain ⟨hBc, hBot, hoM⟩ := qr_M_side I hlen hrx hCLM
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  rw [seed_r_value_qr hM hS I R hz h2 hlen hr hq hXu hCLM hRes hC0 ⟨rk, hRk1⟩ n hn hGlow σ hCN, hoM]
  exact seqZ_lhd (I.good.ot_v r hrM) hRes.σB hBc hRes.ks hRes.vs (hRes.dom _ hC0) (n - 2)

end Ytosk
