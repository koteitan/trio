/-
**ClosedA を σ で運ぶ（2026-10-17、t0）。**

`ClSh`（V3RwClT2）は項だけの主張としては偽: V = Ω_2、V′ = Ω_3 + ψ_1(ψ_1(ψ_0(Ω_{Ω_5})))、a = Ω_2 + ψ_1(Ω_2)、
B = ψ_a(Ω_{Ω_2+1}) で ClosedA a B だが、σB の段 0 の成分 Ω_{Ω_5}（f(Ω_2 + 1) = V′ + 1 の中の V′ の成分）は
σB より大きく、f(a) = Ω_3 + ψ_1(Ω_2) の成分のどれよりも大きい。

ここでは V, V′, a についての支配の条件 `SubstDom` を仮定して示す（`closedA_sh`）。
- (1) a の段 pullLev（u′ ≤ V なら u′、そうでなければ V < a なら V + 1、a = V なら V）の成分 d（d ≠ 0）は σ d が f(a) の段 u′ の成分で押さえられる。
- (2) V′ の段 u′ の成分は f(a) の段 u′ の成分で押さえられる（a = V なら f(a) = V′ で自明）。
証明は V3SubstLev の `comps_sh_pull` で σB の成分を B の成分に引き戻す。
-/
import Ytosk.V3SubstLev
import Ytosk.V3RwClT2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The pull-back level: `u′` if `u′ ≤ V`; otherwise `V + 1` if `V < a`, else `V`. -/
def pullLev (V a u' : T) : T := if u' ≤ V then u' else (if V < a then succ V else V)

/-- **The domination condition** of `V, V′, a` for carrying `ClosedA` through `σ = sh V V′`. -/
def SubstDom (V V' a : T) : Prop :=
  (∀ u', ¬ lt (shf V V' a) u' = true → ∀ d ∈ comps (pullLev V a u') a,
    d = z ∨ ∃ d' ∈ comps u' (shf V V' a), sh V V' d ≤ d') ∧
  (∀ u', ¬ lt (shf V V' a) u' = true → ∀ g ∈ comps u' V', ∃ d' ∈ comps u' (shf V V' a), g ≤ d')

theorem pullLev_le {V a u' : T} (hVa : V ≤ a) : pullLev V a u' ≤ a := by
  unfold pullLev
  by_cases h : u' ≤ V
  · rw [if_pos h]; exact le_trans h hVa
  · rw [if_neg h]
    by_cases h' : V < a
    · rw [if_pos h']; exact succ_le_of_lt h'
    · rw [if_neg h']; exact hVa

/-- **`ClosedA` moves with `σ`** under `SubstDom`. -/
theorem closedA_sh {V V' a B : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V ≤ V')
    (ha : isOT a = true) (hVa : V ≤ a) (hB : isOT B = true) (hD : SubstDom V V' a) (hc : ClosedA a B) :
    ClosedA (shf V V' a) (sh V V' B) := by
  intro u' hu' g' hg'
  have hua : ¬ lt a (pullLev V a u') = true := fun h =>
    absurd (show a < _ from h) (not_lt.mpr (pullLev_le hVa))
  have hw1 : V ≤ (if V < a then succ V else V) := by
    by_cases h : V < a
    · rw [if_pos h]; exact le_of_lt (lt_succ_self V)
    · rw [if_neg h]
  have hw2 : (if V < a then succ V else V) ≤ succ V := by
    by_cases h : V < a
    · rw [if_pos h]
    · rw [if_neg h]; exact le_of_lt (lt_succ_self V)
  rcases comps_sh_pull V V' u' _ hw1 hw2 hg' with ⟨g, hg, rfl⟩ | ⟨g, hg, e⟩ | ⟨q, hq, hgq⟩
  · have hgo := isOT_of_mem_comps _ hB hg
    rcases hc _ hua g hg with h | ⟨d, hd, hgd⟩
    · exact Or.inl (sh_le_sh hV hV' hVV hgo hB h)
    · rcases hD.1 u' hu' d hd with rfl | ⟨d', hd', h'⟩
      · left
        have : g = z := le_antisymm hgd (z_le _)
        subst this; rw [sh_z]; exact z_le _
      · exact Or.inr ⟨d', hd', le_trans (sh_le_sh hV hV' hVV hgo (isOT_of_mem_comps _ ha hd) hgd) h'⟩
  · subst e
    rcases hc _ hua g' hg with h | ⟨d, hd, hgd⟩
    · exact Or.inl (le_trans h (le_sh hV hV' hVV hB))
    · rcases hD.1 u' hu' d hd with rfl | ⟨d', hd', h'⟩
      · exact Or.inl (le_trans hgd (z_le _))
      · exact Or.inr ⟨d', hd', le_trans hgd (le_trans (le_sh hV hV' hVV (isOT_of_mem_comps _ ha hd)) h')⟩
  · obtain ⟨d', hd', h'⟩ := hD.2 u' hu' g' (comps_of_mem_summands hq hgq)
    exact Or.inr ⟨d', hd', h'⟩

/-- **When `a = V`** the second condition is free (`f(V) = V′`). -/
theorem substDom_self {V V' : T}
    (h1 : ∀ u', ¬ lt V' u' = true → ∀ d ∈ comps (if u' ≤ V then u' else V) V,
      d = z ∨ ∃ d' ∈ comps u' V', sh V V' d ≤ d') : SubstDom V V' V := by
  refine ⟨?_, ?_⟩
  · rw [shf_self]
    intro u' hu' d hd
    apply h1 u' hu' d
    unfold pullLev at hd
    by_cases h : u' ≤ V
    · rw [if_pos h] at hd ⊢; exact hd
    · rw [if_neg h, if_neg (lt_irrefl' V)] at hd; rw [if_neg h]; exact hd
  · rw [shf_self]; intro u' _ g hg; exact ⟨g, hg, le_refl _⟩

end Ytosk
