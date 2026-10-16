/-
**t = 2 の種の残り（続き、2026-10-16、t2）: sv の rw を厳しい増加 1 つに。**

- `summands_spArg_ge`: 状態と並びの加数がどれも Ω_w 以上なら、spArg の結果の加数も Ω_w 以上
  （書き換えは H、H の加数は ψ_s(y) 以上。足すだけなら加数は元のもの）。
- `summands_sh_ge`: V < w のとき σ_{V,V′} は Ω_w 以上の加数を Ω_w 以上に移す（f(s) ≥ s）。
- sv: M.take x の r の子はどれも v > V + 1 なので、X₁ の加数は Ω_{V+2} 以上。σ^k X₁ も同じなので
  H(V + 1, σ^{k+1} X₁) = σ^{k+1} X₁。よって `T2SeedSVRes.rw` は X₁ < σ(X₁)（`T2SVStrict`）だけから出る。
-/
import Ytosk.V3T2SeedRes

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem isOT_head_of_psi {s y c : T} (h : isOT (psi s y c) = true) : isOT (psi s y z) = true := by
  obtain ⟨h1, h2, _, _, h5⟩ := isOT_psi_iff.mp h
  exact isOT_psi_iff.mpr ⟨h1, h2, rfl, z_le _, h5⟩

/-- `spArg` keeps a lower bound `Ω_w` on the summands. -/
theorem summands_spArg_ge {a w : T} : ∀ (S b : T), isOT S = true → (∀ q ∈ summands b, ¬ q < Om w) →
    (∀ q ∈ summands S, ¬ q < Om w) → ∀ q ∈ summands (spArg a b S), ¬ q < Om w
  | z, b, _, hb, _ => by simpa [spArg] using hb
  | psi s y c, b, hS, hb, hSq => by
    rw [spArg_cons]
    have hsy : ¬ psi s y z < Om w := hSq _ (by simp [summands])
    have hst : ∀ q ∈ summands (step a b s y c), ¬ q < Om w := by
      unfold step
      split
      · intro q hq hlt
        exact hsy (lt_of_le_of_lt (H_summands_ge (isOT_head_of_psi hS) q hq) hlt)
      · obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix b (psi s y z)
        rw [hP]
        intro q hq
        rw [summands_app, List.mem_append] at hq
        rcases hq with hq | hq
        · exact hb q (hPs q hq)
        · simp [summands] at hq; rw [hq]; exact hsy
    exact summands_spArg_ge c _ (isOT_rest hS) hst (fun q hq => hSq q (by simp [summands, hq]))

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

/-- `σ_{V,V′}` keeps a lower bound `Ω_w` (`V < w`) on the summands. -/
theorem summands_sh_ge {w : T} (hVw : V < w) : ∀ X, isOT X = true → (∀ q ∈ summands X, ¬ q < Om w) →
    ∀ q ∈ summands (sh V V' X), ¬ q < Om w
  | z, _, _ => by simp [summands]
  | psi s y c, hX, hq0 => by
    rw [sh_psi_app, summands_app, List.forall_mem_append]
    have hsy : ¬ psi s y z < Om w := hq0 _ (by simp [summands])
    have hws : ¬ s < w := fun h => hsy (psi_lt_psi_z_iff.mpr (Or.inl h))
    have hVs : V < s := by
      rcases lt_trichotomy' s w with h | h | h
      · exact absurd h hws
      · rw [h]; exact hVw
      · exact lt_trans hVw h
    have hsot : isOT s = true := isOT_sub hX
    have hfs : s ≤ shf V V' s := le_shf_self hV hV' (le_of_lt hVV) hsot (le_of_lt hVs)
    refine ⟨?_, summands_sh_ge hVw c (isOT_rest hX) (fun q hq => hq0 q (by simp [summands, hq]))⟩
    rw [sh_psi_gt hVs, sh_z]
    intro q hq hlt
    simp only [summands, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    rcases psi_lt_psi_z_iff.mp hlt with h | ⟨_, h⟩
    · rcases (le_iff _ _).mp hfs with h' | h'
      · exact hws (lt_trans h' h)
      · rw [← h'] at h; exact hws h
    · exact not_lt_z _ h

/-- The iterate `σ^k` keeps the standard form, does not decrease, and keeps the bound. -/
theorem shIt_facts {w : T} (hVw : V < w) {X : T} (hX : isOT X = true)
    (hq : ∀ q ∈ summands X, ¬ q < Om w) : ∀ k, isOT (shIt V V' X k) = true ∧ X ≤ shIt V V' X k ∧
      ∀ q ∈ summands (shIt V V' X k), ¬ q < Om w
  | 0 => ⟨hX, le_refl _, hq⟩
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := shIt_facts hVw hX hq k
    exact ⟨isOT_sh hV hV' hVV h1, le_trans h2 (le_sh hV hV' (le_of_lt hVV) h1),
      summands_sh_ge hV hV' hVV hVw _ h1 h3⟩

end

/-- **The strict increase** that `T2SeedSVRes.rw` needs: `X₁ < σ_{V,V+1}(X₁)`. -/
def T2SVStrict (M : Mat) (ρ : Valn) (r L : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → t2X1 M r L τ < sh (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ)

/-- **`T2SeedSVRes.rw` from `T2SVStrict`.** -/
theorem sv_rw_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L))
    (hSt : T2SVStrict M ρ r L) :
    ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
      step (ρ.v r) (t2X1 M r L τ) (succ (ρ.v r))
        (sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k)) z =
      sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) := by
  intro τ hτ k
  obtain ⟨hG, hvr, hch⟩ := sv_children_ctx hM hS I R hlen hr hq hux hτ
  have hrT : r < (M.take (r + L)).length := by
    have := par_lt M 0 _ _ hq; rw [List.length_take]; omega
  have hV : isOT (ρ.v r) = true := I.good.ot_v r (by omega)
  have hV' : isOT (succ (ρ.v r)) = true := isOT_succ hV
  have hVV : ρ.v r < succ (ρ.v r) := lt_succ_self _
  have hVw : ρ.v r < succ (succ (ρ.v r)) := lt_trans hVV (lt_succ_self _)
  -- `X₁` is standard and its summands are at least `Ω_{V+2}`
  have hX1 : isOT (t2X1 M r L τ) = true := by
    have := hG.ot_o r hrT
    rw [o_cl_eq hτ hG hrT] at this
    exact isOT_arg this
  have hq1 : ∀ q ∈ summands (t2X1 M r L τ), ¬ q < Om (succ (succ (ρ.v r))) := by
    unfold t2X1
    have hsing : ∀ t ∈ (CL (M.take (r + L)) r).map τ.o, Single t := by
      intro t ht
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
      exact single_o hτ hG (mem_children (cl_mem_children hd)).2
    apply summands_spArg_ge _ z (isOT_sumN _ (fun t ht => (hsing t ht).1)) (by simp [summands])
    intro q hq hlt
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (summands_sumN_sub hsing q hq)
    have hdc := cl_mem_children hd
    have hdT := (mem_children hdc).2
    have hlt' := hch d hdc
    obtain ⟨y, hy⟩ := o_psi_sub hτ hdT
    rw [sf_ot (hG.ot_v d hdT)] at hy
    rw [hy, Om] at hlt
    rcases psi_lt_psi_z_iff.mp hlt with h | ⟨_, h⟩
    · exact lt_irrefl' _ (lt_of_lt_of_le h (succ_le_of_lt hlt'))
    · exact not_lt_z _ h
  obtain ⟨hk1, hk2, hk3⟩ := shIt_facts hV hV' hVV hVw hX1 hq1 (k + 1)
  have hY : shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) (k + 1) =
      sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) := rfl
  rw [hY] at hk1 hk2 hk3
  have hlt : t2X1 M r L τ < sh (ρ.v r) (succ (ρ.v r)) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) := by
    obtain ⟨_, hk2', _⟩ := shIt_facts hV hV' hVV hVw hX1 hq1 k
    exact lt_of_lt_of_le (hSt τ hτ) (sh_le_sh hV hV' (le_of_lt hVV) hX1 (shIt_facts hV hV' hVV hVw hX1 hq1 k).1 hk2')
  unfold step
  rw [if_pos ⟨hlt, psi_lt_psi_z_iff.mpr (Or.inl hVV)⟩]
  exact H_of_high hV' (fun q hq h => hk3 q hq h)

end Ytosk
