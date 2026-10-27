/-
**上げ先が祖先の列の成分の支配 HUAC（2026-10-26、lead）。**

列 n が祖先 k へ上げる（k < n）とき、v(P₁ n) のどの成分も v(n) の成分か 0 以下（`HUAC`、標準形全体の残り）。
上げの定義から P₁(n) = P₁(k)・v(n) = v(k) なので、上げ先の bump 型の列 k での吸収の成分版。18 集合・約 800 万件で例外 0
（上げ先が n + 1 では偽）。

Bad2 で x − 1 が祖先へ上げると、M.take x では上げを失い v′(x − 1) = V′ + 1、o′(x − 1) = ψ_{V′+1}(0)
（V′ = v(P₁(x − 1))）。T0BadSeedsH7 の (1)（r = x − 1）と (2)（r の子が x − 1 だけ）の弱い場合はこの形で、
成分の支配は HUAC そのもの（`t0BadSeedsH7_of`）。残りはその外の場合だけの `T0BadSeedsH8`。
-/
import Ytosk.V3T0BadCnt

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Residual: the components of `v(P₁ n)` are bounded by those of `v(n)` when `n` upgrades to an ancestor.** -/
def HUAC : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ → ∀ n k, upg N n = some k → k < n →
    ∀ u, Dom (comps u (vOpt σ (par N 1 n))) (comps u (σ.v n) ++ [z])

theorem comps_summand_subH (u : T) : ∀ {W q : T}, q ∈ summands W → ∀ g ∈ comps u q, g ∈ comps u W
  | z, _, h, _, _ => by simp [summands] at h
  | psi a b c, q, hq, g, hg => by
    simp only [summands, List.mem_cons] at hq
    simp only [comps, List.mem_append]
    rcases hq with rfl | hq
    · simp only [comps, List.mem_append] at hg
      rcases hg with hg | hg
      · exact Or.inl hg
      · simp at hg
    · exact Or.inr (comps_summand_subH u hq g hg)

/-- The components of `V + X` are those of `V` or of `X`. -/
theorem comps_add_sub (u V X : T) : ∀ g ∈ comps u (add V X), g ∈ comps u V ∨ g ∈ comps u X := by
  intro g hg
  obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix V X
  rw [hP, comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨t, ht, hgt⟩ := comps_sub_summands u P g hg
    exact Or.inl (comps_summand_subH u (hPs t ht) g hgt)
  · exact Or.inr hg

theorem comps_one_eq {u g : T} (h : g ∈ comps u one) : g = z := by
  simp only [one, comps] at h
  split_ifs at h <;> simp_all

/-- The components of `ψ_a(0)` are `0` and those of `a`. -/
theorem comps_psi_zz {u a g : T} (h : g ∈ comps u (psi a z z)) : g = z ∨ g ∈ comps u a := by
  simp only [comps] at h
  split_ifs at h with h'
  · simp at h
  · simp at h
    exact h

/-- **The lost upgrade**: the components of `V′ + 1` are `0` or bounded by those of `w`, when `V′`'s are. -/
theorem dom_add_one {V' w : T} (hH : ∀ u, Dom (comps u V') (comps u w ++ [z])) :
    ∀ u, ∀ e ∈ comps u (add V' one), e = z ∨ ∃ d ∈ comps u w, e ≤ d := by
  intro u e he
  rcases comps_add_sub u V' one e he with he | he
  · obtain ⟨d, hd, hed⟩ := hH u e he
    rcases List.mem_append.mp hd with hd | hd
    · exact Or.inr ⟨d, hd, hed⟩
    · rw [List.mem_singleton] at hd; subst hd
      rcases (le_iff _ _).mp hed with h | h
      · exact absurd h (T.not_lt_z _)
      · exact Or.inl h
  · exact Or.inl (comps_one_eq he)

/-- `ω^{ψ_a(0)} = ψ_a(0)` for `a ≠ 0`. -/
theorem omega_psi_zz {a : T} (ha : a ≠ z) (hot : isOT (psi a z z) = true) : omega (psi a z z) = psi a z z := by
  have hE : ¬ psi a z z < E0 := by
    intro h
    unfold E0 at h
    rw [T.psi_lt_psi] at h
    rcases h with h | ⟨h1, _⟩ | ⟨h1, _, _⟩
    · exact T.not_lt_z _ h
    · exact ha h1
    · exact ha h1
  rw [omega_big' hot hE]
  simp [hiOf, loOf, split, app]

/-- A column with no children has `o = ψ_v(0)`. -/
theorem o_nochild {N : Mat} {σ : Valn} (hC : Cons N σ) {i : Nat} (hi : i < N.length) (hch : children N i = [])
    (hot : isOT (σ.v i) = true) : σ.o i = psi (σ.v i) z z := by
  rw [(hC i hi).1]; unfold oRhs; rw [hch]
  exact sf_ot (isOT_psi_zz hot)

/-- **The lost upgrade in `M.take x`**: `x − 1 = r` with `r + 1 = x`, `r` upgrades: `v′(r) = V′ + 1` and
`o′(r) = ψ_{V′+1}(0)` (`V′ = v(P₁ r)`). -/
theorem lost_upg_take {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3V2 M ρ rk) {r x k : Nat} (hx : x + 1 = M.length) (hr : r + 1 = x) (hu : upg M r = some k) :
    (drop1 M x rk).v r = add (vOpt ρ (par M 1 r)) one ∧
      (drop1 M x rk).o r = psi (add (vOpt ρ (par M 1 r)) one) z z := by
  have S := sInv_std hM hS
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  rw [show M.length - 1 = x by omega] at hcnt
  have hRk1 : Rk (M.take x) rk := rk_take (by omega) I.rank hcnt
  have hC1 : Cons (M.take x) (drop1 M x rk) := cons_of_rk hRk1
  obtain ⟨h1r, h2r⟩ := upg_e12 hu
  have h2r' : entry M 2 r = 0 := by have := S.z2 r; omega
  have hVot : isOT (add (vOpt ρ (par M 1 r)) one) = true :=
    isOT_add (vOpt_ot I.good (by omega)) isOT_one
  have hv : (drop1 M x rk).v r = add (vOpt ρ (par M 1 r)) one := by
    rw [v_last_take hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 hr h1r h2r', sf_ot hVot]
  refine ⟨hv, ?_⟩
  have hlT : (M.take x).length = x := by rw [List.length_take]; omega
  rw [o_nochild hC1 (by omega) (children_last (by omega)) (by rw [hv]; exact hVot), hv]

/-- **An upgrade target's row-0 parent is its row-1 parent**: if `n` upgrades to `k` then `P₀(k) = P₁(k) = P₁(n)`
(`col k = (e0 m + 1, …)` with `m` a row-0 ancestor of `k`). -/
theorem upg_target_par0 {M : Mat} (hR0 : R0P M) {n k : Nat} (h : upg M n = some k) :
    ∃ m, par M 1 n = some m ∧ par M 0 k = some m := by
  obtain ⟨m, hm, hmk, hcol, _⟩ := upg_spec h
  refine ⟨m, hm, ?_⟩
  have hA : Anc0 M m k := anc0_of_par M 1 m k hmk
  have hmk' : m ≠ k := by have := par_lt M 1 k m hmk; omega
  have he0k : entry M 0 k = entry M 0 m + 1 := by
    have := congrArg (fun c : Nat × Nat × Nat => c.1) hcol
    simpa [col_eq_entries] using this
  cases hp : par M 0 k with
  | none =>
    exfalso
    cases hA with
    | refl => exact hmk' rfl
    | step h' _ => rw [hp] at h'; cases h'
  | some p =>
    have hAp : Anc0 M m p := anc0_par hA hmk' hp
    have he0p := hR0 k p hp
    by_cases hmp : m = p
    · rw [hmp]
    · have := anc0_e0_lt hAp hmp; omega

/-- **Residual: `T0BadSeedsH7` outside the lost upgrade** (2026-10-26): field (1) when not `r = x − 1` upgrading to an
ancestor, field (2) when the children of `r` in `M.take x` are not just `x − 1` upgrading to an ancestor. In those
excluded cases the weak disjunct holds by `HUAC` (`t0BadSeedsH7_of`); outside them the strong disjunct holds on the
sets (b2grow1・b2grow2・graftBb2St: field (1) `Lhd` 2708 cases, field (2) `⊴` 2973 cases). Field (3) only when `r − 1`
is not the row-0 parent `g` of `r` (b2grow2: 56 cases; for `r − 1 = g` an upgrade `r − 1 → r` would make `g = P₁(r − 1)`,
`upg_target_par0`). -/
def T0BadSeedsH8 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (¬ (L = 1 ∧ ∃ k, upg M r = some k ∧ k < r) →
      ∀ g pp, par M 0 r = some g → par M 0 g = some pp → entry M 1 pp ≠ 0 → entry M 2 pp ≠ 0 →
      col M g = bump M pp →
      Lhd z ((drop1 M (r + L) rk).o r) (ρ.o r) ∨
        ∀ w', (drop1 M (r + L) rk).o r = psi w' z z →
          ∀ u, ¬ w' < u → ∀ e ∈ comps u w', ∃ d ∈ z :: comps u (ρ.v r), e ≤ d) ∧
    (∀ g, par M 0 r = some g → r ≠ r + L - 1 → col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 →
      ¬ (children (M.take (r + L)) r = [r + L - 1] ∧ ∃ k, upg M (r + L - 1) = some k ∧ k < r + L - 1) →
      LhdE (omega (sumN ((children (M.take (r + L)) r).map (drop1 M (r + L) rk).o)))
          (omega (sumN ((children (M.take (r + L)) r).map ρ.o))) ∨
        ∀ s b', omega (sumN ((children (M.take (r + L)) r).map ρ.o)) = psi s b' z →
          ∀ u, ∀ e ∈ comps u (omega (sumN ((children (M.take (r + L)) r).map (drop1 M (r + L) rk).o))),
            ∃ d ∈ z :: b' :: (comps u b' ++ comps u s), e ≤ d) ∧
    (∀ g, par M 0 r = some g → r ≠ r + L - 1 → r - 1 ≠ g → Counted M g r → topped (M.take (r + L)) r = true →
      upg M (r - 1) ≠ some r)

theorem t0BadSeedsH7_of (hU : HUAC) (h8 : T0BadSeedsH8) : T0BadSeedsH7 := by
  intro M ρ rk hM hS hB I r L hlen hL hp he1
  obtain ⟨h1, h2, h3⟩ := h8 M ρ rk hM hS hB I r L hlen hL hp he1
  refine ⟨fun g pp hg hpp h1p h2p hgb => ?_, fun g hg hrx hrb h1g h2g => ?_,
    fun g hg hrx hcnt htop hu => ?_⟩
  rotate_left 2
  · by_cases hrg : r - 1 = g
    · obtain ⟨m, hm, hm0⟩ := upg_target_par0 (sInv_std hM hS).r0p hu
      rw [hg] at hm0; cases hm0
      rw [← hrg] at hm
      have := par_lt M 1 _ _ hm; omega
    · exact h3 g hg hrx hrg hcnt htop hu
  · by_cases hs : L = 1 ∧ ∃ k, upg M r = some k ∧ k < r
    · obtain ⟨hL1, k, hk, hkr⟩ := hs
      subst hL1
      right
      intro w' hw' u _ e he
      obtain ⟨_, ho⟩ := lost_upg_take hM hS I (x := r + 1) (by omega) rfl hk
      rw [ho] at hw'
      simp only [psi.injEq] at hw'
      rw [← hw'.1] at he
      rcases dom_add_one (hU M ρ rk hM hS I.cons I.rank I.good r k hk hkr) u e he with h | ⟨d, hd, hed⟩
      · exact ⟨z, List.mem_cons_self .., by rw [h]⟩
      · exact ⟨d, List.mem_cons_of_mem _ hd, hed⟩
    · exact h1 hs g pp hg hpp h1p h2p hgb
  · by_cases hs : children (M.take (r + L)) r = [r + L - 1] ∧ ∃ k, upg M (r + L - 1) = some k ∧ k < r + L - 1
    · obtain ⟨hch, k, hk, hkx⟩ := hs
      right
      have S := sInv_std hM hS
      obtain ⟨hv', ho'⟩ := lost_upg_take hM hS I (x := r + L) (r := r + L - 1) (by omega) (by omega) hk
      -- `x − 1` has no children in `M` (`x` is a child of `r ≠ x − 1`)
      have hchM : children M (r + L - 1) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro c hc
        have hcl := mem_children hc
        have hcx : c = r + L := by omega
        have hpc := (mem_children_iff.mp hc).2
        rw [hcx, hp] at hpc
        exact hrx (Option.some.inj hpc)
      have hvot : isOT (ρ.v (r + L - 1)) = true := I.good.ot_v _ (by omega)
      have hoM := o_nochild I.cons (by omega) hchM hvot
      have hVot : isOT (add (vOpt ρ (par M 1 (r + L - 1))) one) = true :=
        isOT_add (vOpt_ot I.good (by omega)) isOT_one
      have hw0 : add (vOpt ρ (par M 1 (r + L - 1))) one ≠ z := by
        intro h
        have := congrArg last h
        rw [show one = psi z z z from rfl, last_add_W ⟨z, z, rfl⟩] at this
        cases this
      have hvz : ρ.v (r + L - 1) ≠ z := v_ne_z_of_e1 I.cons (by omega) (upg_e12 hk).1
      rw [hch]
      simp only [List.map_cons, List.map_nil]
      rw [sumN_singleton (single_o I.cons I.good (by omega)), hoM, omega_psi_zz hvz (isOT_psi_zz hvot)]
      intro s b' hsb u e he
      simp only [psi.injEq] at hsb
      obtain ⟨rfl, rfl, -⟩ := hsb
      rw [sumN_singleton ⟨by rw [ho']; exact isOT_psi_zz hVot, _, _, ho'⟩, ho',
        omega_psi_zz hw0 (isOT_psi_zz hVot)] at he
      rcases comps_psi_zz he with h | he
      · exact ⟨z, List.mem_cons_self .., by rw [h]⟩
      rcases dom_add_one (hU M ρ rk hM hS I.cons I.rank I.good (r + L - 1) k hk hkx) u e he with h | ⟨d, hd, hed⟩
      · exact ⟨z, List.mem_cons_self .., by rw [h]⟩
      · exact ⟨d, by simp [hd], hed⟩
    · exact h2 g hg hrx hrb h1g h2g hs

end Ytosk
