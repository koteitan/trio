/-
**WfInvC1: a weaker qn path clause for the seed `r` (2026-10-31).**

`WfScout.T2SeedQNBaseR` asks, at every path level `u ≤ V` of `r`, that the components of `t₁` and of
`s′ = qnS` are below `X₁ = B + Ω_{t₁}`. The `s′` half is false (WfReM2: a component of `s′` is above `X₁`).

What the consumers use:
- `T2SeedQNCl` (via `qn_closed_tqN`) only at `k ≥ 1`, where `X_k = B + Ω_{t_k}` and `s′ < t_k` (`lt_shf`);
- `T2VRAQNDom0` (`Lc = []`, `B = 0`): `g ≤ Ω_{s′}`.

So the weaker clause asks, for the components of `s′`, only `g < B + Ω_{s′}` (`X₁ ≤ B + Ω_{s′}` since `t₁ ≤ s′`).
- `qn_closed_tqN_W`: the closedness of `t_k` (`k ≥ 1`) from the `t₁` half (below `X₁`) and the weaker `s′` half.
- `t2SeedQNCl_of_W`: `T2SeedQNCl` from it.
- `t2VRAQNDom0_of_W`: `T2VRAQNDom0` from it.
-/
import Ytosk.WfScoutSeedCl
import Ytosk.V3T2SeedQNK

namespace Ytosk.WfInvC

open T

set_option linter.unusedSectionVars false

/-- **One `σ` step keeps the closedness of `t`, with the components of `V′` below `B + Ω_{V′}`.** -/
theorem qn_closed_step_W {Lv : T → Prop} {V V' B t : T} (hV : isOT V = true) (hV' : isOT V' = true)
    (hVV : V < V') (hσB : sh V V' B = B) (hVt : V < t) (hot : isOT (app B (psi t z z)) = true)
    (hcl : ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u t, g < app B (psi t z z))
    (hclS : ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u V', g < app B (psi V' z z)) :
    isOT (app B (psi (shf V V' t) z z)) = true ∧ V < shf V V' t ∧
      ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u (shf V V' t), g < app B (psi (shf V V' t) z z) := by
  have hσ : sh V V' (app B (psi t z z)) = app B (psi (shf V V' t) z z) := by
    rw [sh_app, hσB, sh_psi_gt hVt, sh_z]
  have hle : app B (psi t z z) ≤ app B (psi (shf V V' t) z z) :=
    hσ ▸ le_sh hV hV' (le_of_lt hVV) hot
  have hot' : isOT (app B (psi (shf V V' t) z z)) = true := hσ ▸ isOT_sh hV hV' hVV hot
  have ht : isOT t = true := isOT_sub (isOT_app_right hot)
  have hV't : V' < shf V V' t := lt_shf hV hV' (le_of_lt hVV) ht hVt
  have hSX : app B (psi V' z z) < app B (psi (shf V V' t) z z) :=
    app_lt_app_left B (psi_lt_psi_z_iff.mpr (Or.inl hV't))
  refine ⟨hot', lt_trans hVV hV't, fun u hu hVu g hg => ?_⟩
  change g ∈ comps u (add V' (sh V V' (sub t V))) at hg
  obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix V' (sh V V' (sub t V))
  rw [hP, comps_app, List.mem_append] at hg
  rcases hg with hg | hg
  · exact lt_trans (hclS u hu hVu g (comps_sub_of_summands u hPs g hg)) hSX
  · rcases comps_sh_low hVu _ _ (Nat.le_refl _) g hg with ⟨g0, hg0, rfl | rfl⟩ | h
    · exact lt_of_lt_of_le (hcl u hu hVu _ (comps_sub_sub u _ V hg0)) hle
    · rw [← hσ]
      exact sh_lt_sh hV hV' (le_of_lt hVV) (isOT_of_mem_comps u (isOT_sub_sfx ht V) hg0) hot
        (hcl u hu hVu _ (comps_sub_sub u _ V hg0))
    · exact lt_trans (hclS u hu hVu g h) hSX

/-- **The qn closed forms at `k`**, from the closedness of `t₁` and the weaker clause on `V′`. -/
theorem qn_closed_tqN_W0 {Lv : T → Prop} {V V' B t1 : T} (hV : isOT V = true) (hV' : isOT V' = true)
    (hVV : V < V') (hσB : sh V V' B = B) (hVt : V < t1) (hot : isOT (app B (psi t1 z z)) = true)
    (hcl : ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u t1, g < app B (psi t1 z z))
    (hclS : ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u V', g < app B (psi V' z z)) :
    ∀ k, isOT (app B (psi (tqN V V' t1 k) z z)) = true ∧ V < tqN V V' t1 k ∧
      ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u (tqN V V' t1 k), g < app B (psi (tqN V V' t1 k) z z)
  | 0 => ⟨hot, hVt, hcl⟩
  | k + 1 => by
    obtain ⟨hk, hVk, hclk⟩ := qn_closed_tqN_W0 hV hV' hVV hσB hVt hot hcl hclS k
    exact qn_closed_step_W hV hV' hVV hσB hVk hk hclk hclS

/-- **The qn closed forms at `k ≥ 1` with the components of `V′`** (the conclusion of `qn_closed_tqN` there). -/
theorem qn_closed_tqN_W {Lv : T → Prop} {V V' B t1 : T} (hV : isOT V = true) (hV' : isOT V' = true)
    (hVV : V < V') (hσB : sh V V' B = B) (hVt : V < t1) (hot : isOT (app B (psi t1 z z)) = true)
    (hcl : ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u t1, g < app B (psi t1 z z))
    (hclS : ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u V', g < app B (psi V' z z)) :
    ∀ k, 1 ≤ k → isOT (app B (psi (tqN V V' t1 k) z z)) = true ∧ V < tqN V V' t1 k ∧
      ∀ u, Lv u → ¬ V < u → ∀ g ∈ comps u (tqN V V' t1 k) ++ comps u V', g < app B (psi (tqN V V' t1 k) z z) := by
  intro k hk
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hk0, hVk0, -⟩ := qn_closed_tqN_W0 hV hV' hVV hσB hVt hot hcl hclS k'
  obtain ⟨h1, h2, h3⟩ := qn_closed_tqN_W0 hV hV' hVV hσB hVt hot hcl hclS (k' + 1)
  have ht : isOT (tqN V V' t1 k') = true := isOT_sub (isOT_app_right hk0)
  have hV't : V' < tqN V V' t1 (k' + 1) := lt_shf hV hV' (le_of_lt hVV) ht hVk0
  have hSX : app B (psi V' z z) < app B (psi (tqN V V' t1 (k' + 1)) z z) :=
    app_lt_app_left B (psi_lt_psi_z_iff.mpr (Or.inl hV't))
  refine ⟨h1, h2, fun u hu hVu g hg => ?_⟩
  rcases List.mem_append.mp hg with hg | hg
  · exact h3 u hu hVu g hg
  · exact lt_trans (hclS u hu hVu g hg) hSX

/-- **The weaker qn base (residual form)**: as `WfScout.T2SeedQNBaseR`, but the components of `s′` at the path levels
only below `B + Ω_{s′}`. -/
def T2SeedQNBaseRW (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) →
      (∀ g ∈ comps (ρ.v r) (qnS M ρ r L q), g < app (t2B (ρ.v r) ρ Lc) (psi t1 z z)) ∧
      ∀ u, PathLvAll M ρ r u → ¬ lt (ρ.v r) u = true →
        (∀ g ∈ comps u t1, g < app (t2B (ρ.v r) ρ Lc) (psi t1 z z)) ∧
        ∀ g ∈ comps u (qnS M ρ r L q), g < app (t2B (ρ.v r) ρ Lc) (psi (qnS M ρ r L q) z z)

/-- **The weaker qn base (full form)**: `T2SeedQNBase` with the weaker path clause. -/
def T2SeedQNBaseW (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ t1,
    spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) →
    isOT (psi (ρ.v r) (app (t2B (ρ.v r) ρ Lc) (psi t1 z z)) z) = true ∧
      (∀ g ∈ comps (ρ.v r) (qnS M ρ r L q), g < app (t2B (ρ.v r) ρ Lc) (psi t1 z z)) ∧
      (Lc = [] → t1 ≤ qnS M ρ r L q) ∧
      ∀ u, PathLvAll M ρ r u → ¬ lt (ρ.v r) u = true →
        (∀ g ∈ comps u t1, g < app (t2B (ρ.v r) ρ Lc) (psi t1 z z)) ∧
        ∀ g ∈ comps u (qnS M ρ r L q), g < app (t2B (ρ.v r) ρ Lc) (psi (qnS M ρ r L q) z z)

/-- **The old base gives the weaker one** when `t₁ ≤ s′` (then `X₁ ≤ B + Ω_{s′}`). -/
theorem base_W_of_base {M : Mat} {ρ : Valn} {r L q : Nat} {Lc : List Nat}
    (ht : ∀ τ, Cons (M.take (r + L)) τ → ∀ t1,
      spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) →
        t1 ≤ qnS M ρ r L q)
    (h : T2SeedQNBase M ρ r L q Lc) : T2SeedQNBaseW M ρ r L q Lc := by
  intro τ hτ t1 hsp
  obtain ⟨h0, h1, h2, h3⟩ := h τ hτ t1 hsp
  have hle : app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ≤ app (t2B (ρ.v r) ρ Lc) (psi (qnS M ρ r L q) z z) := by
    rcases (le_iff _ _).mp (ht τ hτ t1 hsp) with h5 | h5
    · exact le_of_lt (app_lt_app_left _ (psi_lt_psi_z_iff.mpr (Or.inl h5)))
    · rw [h5]
  refine ⟨h0, h1, h2, fun u hu hVu => ⟨fun g hg => h3 u hu hVu g (List.mem_append_left _ hg),
    fun g hg => lt_of_lt_of_le (h3 u hu hVu g (List.mem_append_right _ hg)) hle⟩⟩

/-- **`T2SeedQNCl` from the weaker base.** -/
theorem t2SeedQNCl_of_W {M : Mat} {ρ : Valn} {r L q : Nat} {Lc : List Nat} (hV : isOT (ρ.v r) = true)
    (hs : isOT (qnS M ρ r L q) = true) (hσB : sh (ρ.v r) (qnS M ρ r L q) (t2B (ρ.v r) ρ Lc) = t2B (ρ.v r) ρ Lc)
    (hVt' : ∀ τ, Cons (M.take (r + L)) τ → ∀ t1,
      spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) → ρ.v r < t1)
    (h : T2SeedQNBaseW M ρ r L q Lc) : T2SeedQNCl M ρ r L q Lc := by
  intro τ hτ t1 ht1 k hk u hu hVu g hg
  have hVt := hVt' τ hτ t1 ht1
  obtain ⟨hot, -, -, hcl⟩ := h τ hτ t1 ht1
  exact Or.inl ((qn_closed_tqN_W (Lv := PathLvAll M ρ r) hV hs (qnS_gt M ρ r L q) hσB hVt (isOT_arg hot)
    (fun u hu hVu => (hcl u hu hVu).1) (fun u hu hVu => (hcl u hu hVu).2) k hk).2.2 u hu.toAll hVu g
    (List.mem_append_left _ hg))

/-- **`T2VRAQNDom0` from the weaker base** (`Lc = []`, `B = 0`): the components of `s′` at the level `V` are below
`X₁ = Ω_{t₁} ≤ Ω_{s′}`, and at the path levels below `Ω_{s′}`. -/
theorem t2VRAQNDom0_of_W {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) {r L q : Nat}
    (hlen : r + L + 1 = M.length) (h : T2SeedQNBaseW M ρ r L q [])
    (hP : ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
      spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ []) (psi t1 z z)) :
    T2VRAQNDom0 M ρ r L q := by
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hC0 := cons_of_rk (rk_take (by omega) I.rank hcnt)
  obtain ⟨t1, ht1⟩ := hP _ hC0
  obtain ⟨-, hcV, hts, hcl⟩ := h _ hC0 t1 ht1
  have hB : app (t2B (ρ.v r) ρ []) (psi t1 z z) = psi t1 z z := rfl
  have hBS : app (t2B (ρ.v r) ρ []) (psi (qnS M ρ r L q) z z) = psi (qnS M ρ r L q) z z := rfl
  have hle : psi t1 z z ≤ psi (qnS M ρ r L q) z z := by
    rcases (le_iff _ _).mp (hts rfl) with h5 | h5
    · exact psi_le_psi_of (Or.inl h5)
    · rw [h5]
  intro u hu hVu g hg
  left
  rcases hu with rfl | hu
  · have := hcV g hg; rw [hB] at this; exact le_trans (le_of_lt this) hle
  · have := (hcl u hu hVu).2 g hg; rw [hBS] at this; exact le_of_lt this

end Ytosk.WfInvC
