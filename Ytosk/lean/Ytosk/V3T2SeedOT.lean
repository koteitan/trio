/-
**3 行・t = 2: 種 r と q（q ≠ r）の o の標準形を、閉じた形の標準形（M と M.take x だけの残り）から。**

各場合の o_{M[n]}(r)・o_{M[n]}(q) は閉じた形（seed_r_value_*）なので、その標準形を残り `T2Seed*OT` にする。
- qr: ψ_V(seqZ k)。qn: ψ_V(B + Ω_{t_k})、ψ_{s′}(B + Ω_{t_k})。sv: ψ_V(σ^k X₁)。C: ψ_V(σ^k X₁)、ψ_{s′}(step(0, s′, σ^{k+1} X₁))。
q の値は前の段の r の引数から（qn_frame・C_frame）。
-/
import Ytosk.V3T2SeedC
import Ytosk.V3InvW

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- The frame of `q` in one level of the `q ≠ r` seed: `step_{s′}(0, s′, σ(B + Ω_t)) = B + Ω_{σ t}`. -/
theorem qn_inner {a B s' t : T} (hs' : isOT s' = true) (hσB : sh a s' B = B)
    (hBc : ∀ g ∈ summands B, ¬ g < psi (succ s') z z) (hat : a < t)
    (hts : ¬ shf a s' t < succ s') :
    step s' z s' (sh a s' (app B (psi t z z))) z = app B (psi (shf a s' t) z z) := by
  rw [sh_app, hσB, sh_psi_gt hat, sh_z]
  have hhigh : ∀ g ∈ summands (app B (psi (shf a s' t) z z)), ¬ g < psi (succ s') z z := by
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
  have hzlt : z < app B (psi (shf a s' t) z z) := by
    cases B with
    | z => exact T.z_lt_psi _ _ _
    | psi _ _ _ => exact T.z_lt_psi _ _ _
  unfold step
  rw [if_pos ⟨hzlt, psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hzlt⟩)⟩]
  exact H_of_high hs' hhigh

/-- **The standard form of the closed forms, `q = r` without an upgrade into `x`.** -/
def T2SeedQROT (M : Mat) (ρ : Valn) (r L : Nat) (Lc : List Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
    isOT (psi (ρ.v r) (seqZ (ρ.v r) (t2B (ρ.v r) ρ Lc) (t2W1 (M.take (r + L)) (ρ.v r) τ r) k) z) = true

/-- **The standard form of the closed forms, `q ≠ r` with `q` the last counted child.** -/
def T2SeedQNOT (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) →
    ∀ k, 1 ≤ k →
      isOT (psi (ρ.v r) (app (t2B (ρ.v r) ρ Lc) (psi (tqN (ρ.v r) (qnS M ρ r L q) t1 k) z z)) z) = true ∧
      isOT (psi (qnS M ρ r L q) (app (t2B (ρ.v r) ρ Lc) (psi (tqN (ρ.v r) (qnS M ρ r L q) t1 k) z z)) z) = true

/-- **The standard form of the closed forms, sv.** -/
def T2SeedSVOT (M : Mat) (ρ : Valn) (r L : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k →
    isOT (psi (ρ.v r) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) z) = true

/-- **The standard form of the closed forms, C.** -/
def T2SeedCOT (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ →
    (∀ k, 1 ≤ k → isOT (psi (ρ.v r) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k) z) = true) ∧
    (∀ k, isOT (psi (qnS M ρ r L q) (step (qnS M ρ r L q) z (qnS M ρ r L q)
      (sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)) z) z) = true)

/-- **The seed `r` is standard** (`q = r` without an upgrade into `x`). -/
theorem seed_ot_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hXu : ∀ i, upg M i ≠ some (r + L))
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [r + L]) (hRes : T2SeedQRRes M ρ r L Lc)
    (hOT : T2SeedQROT M ρ r L Lc) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
        isOT (σ.o r) = true := by
  intro n hn hGlow σ hCN
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  rw [seed_r_value_qr hM hS I R hz h2 hlen hr hq hXu hCLM hRes hC0 ⟨rk, hRk1⟩ n hn hGlow σ hCN]
  exact hOT _ hC0 (n - 2)

/-- **The seed `r` is standard** (sv). -/
theorem seed_ot_sv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (hRes : T2SeedSVRes M ρ r L) (hOT : T2SeedSVOT M ρ r L) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
        isOT (σ.o r) = true := by
  intro n hn hGlow σ hCN hdecN
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  rw [seed_r_value_sv hM hS I R hz h2 hlen hr hq hux hRes hC0 hRk1 n hn hGlow σ hCN hdecN]
  exact hOT _ hC0 (n - 1) (by omega)

/-- **The seeds `q` and `r` are standard** (`q ≠ r`, `q` the last counted child of `r`). -/
theorem seed_ot_qn {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {Lc : List Nat} (hCLM : CL M r = Lc ++ [q]) (hRes : T2SeedQNRes M ρ r L q Lc)
    (hOT : T2SeedQNOT M ρ r L q Lc) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
        isOT (σ.o q) = true ∧ isOT (σ.o r) = true := by
  intro n hn hGlow σ hCN hdecN
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
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  have hv0 := v_take_of_untopped I hlen (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hC0
  obtain ⟨t1, ht1, hch⟩ := hRes.base _ hC0
  set V := ρ.v r with hVdef
  set B := t2B V ρ Lc with hBdef
  set s' := qnS M ρ r L q with hs'def
  -- the previous level: `ρ_P.v r = V` and the argument of `r` is `B + Ω_{t_{n−2}}`
  have hprev : ∃ (ρP : Valn) (rkP : Bool → Nat → Nat), Cons (TRIO.gexp M r L d0 d1 (n - 1)) ρP ∧
      Good3 (TRIO.gexp M r L d0 d1 (n - 1)) ρP ∧ Rk (TRIO.gexp M r L d0 d1 (n - 1)) rkP ∧ ρP.v r = V ∧
      spArg (ρP.v r) z (sumN ((CL (TRIO.gexp M r L d0 d1 (n - 1)) r).map ρP.o)) =
        app B (psi (tqN V s' t1 (n - 2)) z z) := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn2 : n = 2 := by omega
      subst hn2
      refine ⟨_, rk, by rw [show 2 - 1 = 1 from rfl, hP1]; exact hC0, ?_, by rw [show 2 - 1 = 1 from rfl, hP1]; exact hRk1,
        hv0, by rw [show 2 - 1 = 1 from rfl, hP1]; exact ht1⟩
      have h := hGlow 1 (le_refl 1) (by omega) _ (by rw [hP1]; exact hC0)
      exact h
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
      have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
      have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by omega
      have hqP : q < (TRIO.gexp M r L d0 d1 (n - 1)).length := by omega
      have hP := seed_r_value_qn hM hS I R hz h2 hlen hr hq hqr hCLM hRes hC0 ⟨rk, hRk1⟩ hv0 ht1
        (fun k => ⟨(hch k).1, (hch k).2.1⟩) (n - 1) (by omega)
        (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP (hGP.ot_o q hqP)
        (by rw [← cvals_eq_mapC hCP]; exact hGP.dec r hrP)
      have hform := o_cl_eq hCP hGP hrP
      rw [hP] at hform
      simp only [psi.injEq] at hform
      refine ⟨_, rkP, hCP, hGP, hRP, hform.1.symm, ?_⟩
      rw [← hform.2.1, show n - 1 - 1 = n - 2 by omega]
  obtain ⟨ρP, rkP, hCP, hGP, hRP, hvP, hXP⟩ := hprev
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  obtain ⟨_, _, _, hvx, hoq, _⟩ := qn_frame hM hS I R hz h2 hlen hr hq hqr hCLM hn hCN hRN hCP hGP hRP
  have hvq : σ.v q = s' := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  have hvx' : σ.v (r + L) = s' := by rw [hvx, hvq]; exact qnS_vxs M ρ r L q
  obtain ⟨hat, hts, _⟩ := hch (n - 2)
  have hoq' : σ.o q = psi s' (app B (psi (tqN V s' t1 (n - 1)) z z)) z := by
    rw [hoq, hvx', hvq, hXP, hvP, qn_inner (qnS_ot I (by omega) L q) hRes.σB hRes.Bc hat hts,
      show n - 1 = (n - 2) + 1 by omega]
    rfl
  have hqOT : isOT (σ.o q) = true := by rw [hoq']; exact (hOT _ hC0 t1 ht1 (n - 1) (by omega)).2
  refine ⟨hqOT, ?_⟩
  rw [seed_r_value_qn hM hS I R hz h2 hlen hr hq hqr hCLM hRes hC0 ⟨rk, hRk1⟩ hv0 ht1
    (fun k => ⟨(hch k).1, (hch k).2.1⟩) n hn hGlow σ hCN hqOT hdecN]
  exact (hOT _ hC0 t1 ht1 (n - 1) (by omega)).1

/-- **The seeds `q` and `r` are standard** (C case). -/
theorem seed_ot_C {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q]) (hRes : T2SeedCRes M ρ r L q)
    (hOT : T2SeedCOT M ρ r L q) :
    ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
        σ.o).Pairwise (fun a b => b ≤ a) →
        isOT (σ.o q) = true ∧ isOT (σ.o r) = true := by
  intro n hn hGlow σ hCN hdecN
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
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  have hG0 : Good3 (M.take (r + L)) (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rk)) := by
    have h := hGlow 1 (le_refl 1) (by omega) _ (by rw [hP1]; exact hC0)
    rwa [hP1] at h
  have hv0 := v_take_of_untopped I hlen (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hC0
  set V := ρ.v r with hVdef
  set s' := qnS M ρ r L q with hs'def
  set X1 := t2X1 M r L (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rk)) with hX1def
  have hprev : ∃ (ρP : Valn) (rkP : Bool → Nat → Nat), Cons (TRIO.gexp M r L d0 d1 (n - 1)) ρP ∧
      Good3 (TRIO.gexp M r L d0 d1 (n - 1)) ρP ∧ Rk (TRIO.gexp M r L d0 d1 (n - 1)) rkP ∧ ρP.v r = V ∧
      spArg (ρP.v r) z (sumN ((CL (TRIO.gexp M r L d0 d1 (n - 1)) r).map ρP.o)) = shIt V s' X1 (n - 2) := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn2 : n = 2 := by omega
      subst hn2
      refine ⟨_, rk, by rw [show 2 - 1 = 1 from rfl, hP1]; exact hC0,
        by rw [show 2 - 1 = 1 from rfl, hP1]; exact hG0, by rw [show 2 - 1 = 1 from rfl, hP1]; exact hRk1,
        hv0, by rw [show 2 - 1 = 1 from rfl, hP1]; rfl⟩
    · obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
      have hCP := cons_of_rk hRP
      have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
      have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
      have hn1L : L ≤ (n - 1) * L := Nat.le_mul_of_pos_left L (by omega)
      have hrP : r < (TRIO.gexp M r L d0 d1 (n - 1)).length := by omega
      have hqP : q < (TRIO.gexp M r L d0 d1 (n - 1)).length := by omega
      have hP := seed_r_value_C hM hS I R hz h2 hlen hr hq hqr hncl hRes hC0 hRk1 (n - 1) (by omega)
        (fun m h1 h2' τ hτ => hGlow m h1 (by omega) τ hτ) _ hCP (hGP.ot_o q hqP)
        (by rw [← cvals_eq_mapC hCP]; exact hGP.dec r hrP)
      have hform := o_cl_eq hCP hGP hrP
      rw [hP] at hform
      simp only [psi.injEq] at hform
      refine ⟨_, rkP, hCP, hGP, hRP, hform.1.symm, ?_⟩
      rw [← hform.2.1, show n - 1 - 1 = n - 2 by omega]
  obtain ⟨ρP, rkP, hCP, hGP, hRP, hvP, hXP⟩ := hprev
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  have hvq : σ.v q = s' := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
  have hvq0 : (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rk)).v q = σ.v q := by
    rw [hvq]; exact hRes.vqP _ hC0
  obtain ⟨_, _, _, hvx, hoq, _⟩ := C_frame hM hS I R hz h2 hlen hr hq hqr (qP_C hM hS I hlen hr hq hqr hncl hRes.un) hRes.un hn hCN hRN hCP hGP hRP
    hC0 hG0 hRk1 hv0 hvq0
  have hvx' : σ.v (r + L) = s' := by rw [hvx, hvq]; exact qnS_vxs M ρ r L q
  have hqOT : isOT (σ.o q) = true := by
    rw [hoq, hvx', hvq, hXP, hvP]; exact (hOT _ hC0).2 (n - 2)
  refine ⟨hqOT, ?_⟩
  rw [seed_r_value_C hM hS I R hz h2 hlen hr hq hqr hncl hRes hC0 hRk1 n hn hGlow σ hCN hqOT hdecN]
  exact (hOT _ hC0).1 (n - 1) (by omega)

end Ytosk
