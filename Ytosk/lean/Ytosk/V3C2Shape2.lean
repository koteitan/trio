/-
**t = 2, C2, shape 2 with a path of length 1 (2026-11-06, in progress).**

In C2 the last counted child `c₀` of `r` has a counted child; in 170 of the 174 measured frames `w = q − 1` is the last
counted child of `c₀` and a leaf, `e2 w = 0`, `upg w = q`.  Step 1: the closure of the calls whose equations differ
between `M` and `N = M[n]` (the subtree of `q`, `o(r)`) is the subtree of `q`, the calls of rank at least `o(r)`, and
`v(w)`, `o(w)`, `o(c₀)` (`depS_C2_inv`, with the template `depS_SQ_inv`).
-/
import Ytosk.V3CanonBump

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The seeds: the subtree of `q` and `o(r)`. -/
def SC2 (M : Mat) (q r : Nat) : Bool → Nat → Prop := fun b i => Anc0 M q i ∨ (b = true ∧ i = r)

theorem depS_C2_inv {M : Mat} {rk : Bool → Nat → Nat} (hR : Rk M rk) {q r c0 w : Nat}
    (hpq : par M 0 q = some r) (hqb : col M q ≠ bump M r) (he2r : entry M 2 r = 0)
    (hpc0 : par M 0 c0 = some r) (hc0b : col M c0 ≠ bump M r)
    (hpw : par M 0 w = some c0) (hwq : w + 1 = q) (hwleaf : children M w = []) (he2w : entry M 2 w = 0) :
    ∀ {b i}, DepS M (SC2 M q r) b i → i < M.length →
      Anc0 M q i ∨ rk true r ≤ rk b i ∨ (b = false ∧ i = w) ∨ (b = true ∧ (i = w ∨ i = c0)) := by
  intro b i h
  induction h with
  | @seed b i hs =>
    intro _
    rcases hs with hA | ⟨rfl, rfl⟩
    · exact Or.inl hA
    · exact Or.inr (Or.inl (le_refl _))
  | @ochild i c hc hcb hcu _ ih =>
    intro hi
    have hrk := (hR _ hi).2.1 _ hc hcb hcu
    have hpc := (mem_children_iff.mp hc).2
    rcases ih (mem_children hc).2 with hA | hle | ⟨h1, _⟩ | ⟨_, hcw | hcc⟩
    · by_cases hcq : c = q
      · subst hcq
        have : i = r := by rw [hpc] at hpq; exact Option.some.inj hpq
        subst this; exact Or.inr (Or.inl (le_refl _))
      · exact Or.inl (anc0_par hA (Ne.symm hcq) hpc)
    · exact Or.inr (Or.inl (by omega))
    · cases h1
    · subst hcw
      have : i = c0 := by rw [hpc] at hpw; exact Option.some.inj hpw
      subst this; exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩))
    · subst hcc
      have : i = r := by rw [hpc] at hpc0; exact Option.some.inj hpc0
      subst this; exact Or.inr (Or.inl (le_refl _))
  | @ov i _ ih =>
    intro hi
    have := (hR _ hi).1
    rcases ih hi with hA | hle | ⟨_, hiw⟩ | ⟨h1, _⟩
    · exact Or.inl hA
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl hiw⟩))
    · cases h1
  | @vpar i m h1 hm _ ih =>
    intro hi
    have hrk := ((hR _ hi).2.2 h1).1 _ hm
    rcases ih (by have := par_lt _ 1 _ _ hm; omega) with hA | hle | ⟨_, hmw⟩ | ⟨h2, _⟩
    · exact Or.inl (Anc0.trans hA (anc0_of_par M 1 m i hm))
    · exact Or.inr (Or.inl (by omega))
    · exfalso
      subst hmw
      have hAi := anc0_of_par M 1 m i hm
      have hne : m ≠ i := by have := par_lt M 1 i m hm; omega
      obtain ⟨c, hcw, hAc⟩ := anc0_child hAi hne
      have hcM : c ∈ children M m := mem_children_iff.mpr ⟨by have := hAc.le; omega, hcw⟩
      rw [hwleaf] at hcM; simp at hcM
    · cases h2
  | @vupg i k h1 h2 hk _ ih =>
    intro hi
    have hrk := ((hR _ hi).2.2 h1).2.1 h2 _ hk
    rcases ih (upg_lt hi hk) with hA | hle | ⟨_, hkw⟩ | ⟨h3, _⟩
    · obtain ⟨_, _, _, _, hcase⟩ := upg_spec hk
      rcases hcase with hk1 | ⟨hAk, _⟩
      · by_cases hkq : k = q
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
        · have hqk := hA.le
          exact Or.inl (anc_between hA i (by omega) (by omega))
      · exact Or.inl (Anc0.trans hA hAk)
    · exact Or.inr (Or.inl (by omega))
    · exfalso
      subst hkw
      have := upg_target_e2 hk; omega
    · cases h3
  | @vbump i j k h1 h2 hj hjb hk _ ih =>
    intro hi
    have hrk := ((hR _ hi).2.2 h1).2.2 h2 _ hj hjb _ hk
    have hkl := (mem_children hk).2
    have hpk := (mem_children_iff.mp hk).2
    have hpj := (mem_children_iff.mp hj).2
    rcases ih hkl with hA | hle | ⟨h3, _⟩ | ⟨_, hkw | hkc⟩
    · by_cases hkq : k = q
      · subst hkq
        have hjr : j = r := by rw [hpk] at hpq; exact Option.some.inj hpq
        subst hjr
        exfalso
        have := e2_of_col (show col M j = (entry M 0 i + 1, entry M 1 i, 1) from hjb); omega
      · have hAj : Anc0 M q j := anc0_par hA (Ne.symm hkq) hpk
        by_cases hjq : j = q
        · subst hjq
          have hir : i = r := by rw [hpj] at hpq; exact Option.some.inj hpq
          subst hir
          exact absurd hjb hqb
        · exact Or.inl (anc0_par hAj (Ne.symm hjq) hpj)
    · exact Or.inr (Or.inl (by omega))
    · cases h3
    · subst hkw
      have hjc : j = c0 := by rw [hpk] at hpw; exact Option.some.inj hpw
      subst hjc
      have hir : i = r := by rw [hpj] at hpc0; exact Option.some.inj hpc0
      subst hir
      exact absurd hjb hc0b
    · subst hkc
      have hjr : j = r := by rw [hpk] at hpc0; exact Option.some.inj hpc0
      subst hjr
      exfalso
      have := e2_of_col (show col M j = (entry M 0 i + 1, entry M 1 i, 1) from hjb); omega

#print axioms depS_C2_inv

end Ytosk.V3Main.SeedPF
