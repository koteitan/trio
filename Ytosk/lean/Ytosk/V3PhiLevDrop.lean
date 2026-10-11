/-
**LevLeafInv ∧ PrefLast を 1 列落としで運ぶ。**

- PrefLast: どの列 j と、j より前に行 1 の子を持つ列 p についても、v(p) は添字 v(P_1 j)・v(P_1 (P_0 j)) の
  部分項を持たない（5 集合で計 7000 万組、例外 0）。「各接頭辞の最後の列」の事実を M の値で書いたもの。
- 1 列落としで新しく出る後続の葉は、上げを失った x − 1（PrefLast の j = x − 1）か、唯一の数える子 x を
  失った P_0 x（PrefLast の j = x、2 番目の項）だけ。後者は明示的な仮定 LostKids（数える子をすべて失う列は
  P_0 x、5 集合で 52 万件、例外 0）。
-/
import Ytosk.V3PhiLevLink

namespace Ytosk

open T

theorem subT_size : ∀ {w t : T}, SubT w t → size w ≤ size t
  | _, _, .refl _ => Nat.le_refl _
  | _, _, .sub h => le_of_lt (lt_of_le_of_lt (subT_size h) (size_sub_lt _ _ _))
  | _, _, .arg h => le_of_lt (lt_of_le_of_lt (subT_size h) (size_arg_lt _ _ _))
  | _, _, .rest h => le_of_lt (lt_of_le_of_lt (subT_size h) (size_rest_lt _ _ _))

/-- **No subterm of `V` has subscript `V`.** -/
theorem levFree_self (V : T) : LevFree V V := by
  intro a b c h ha
  subst ha
  have := subT_size h
  have := size_sub_lt a b c
  omega

/-- **The prefix-last condition.** -/
def PrefLast (M : Mat) (ρ : Valn) : Prop :=
  ∀ j c p, j < M.length → c < j → par M 1 c = some p →
    (∀ q, par M 1 j = some q → ρ.v q ≠ z → LevFree (ρ.v q) (ρ.v p)) ∧
    (∀ i q, par M 0 j = some i → par M 1 i = some q → ρ.v q ≠ z → LevFree (ρ.v q) (ρ.v p))

section
variable {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
include hC hG

/-- **A successor `v` is `v(P_1) + 1`** (row 2 zero, no upgrade). -/
theorem v_succ_form {i : Nat} (hi : i < M.length) {μ : T} (hμ : ρ.v i = succ μ) :
    entry M 1 i ≠ 0 ∧ entry M 2 i = 0 ∧ upg M i = none ∧ μ = vOpt ρ (par M 1 i) := by
  have hv := (hC i hi).2
  unfold vRhs at hv
  by_cases h1 : entry M 1 i = 0
  · rw [if_pos h1] at hv; rw [hv] at hμ; exact absurd hμ.symm (succ_ne_z μ)
  rw [if_neg h1] at hv
  have hV0 : isOT (vOpt ρ (par M 1 i)) = true := by
    cases hp : par M 1 i with
    | none => rfl
    | some m => exact hG.ot_v m (by have := par_lt M 1 i m hp; omega)
  by_cases h2 : entry M 2 i = 0
  · rw [if_pos h2] at hv
    cases hu : upg M i with
    | none =>
      rw [hu] at hv; simp only at hv
      rw [sf_ot (isOT_add hV0 rfl)] at hv
      rw [hv] at hμ
      exact ⟨h1, h2, rfl, (succ_of_add_single ⟨z, z, rfl⟩ hμ).2⟩
    | some k =>
      rw [hu] at hv; simp only at hv
      rw [upg_target_last hC hG hi hu] at hv
      have hW : isOT (bumpW M ρ k) = true := isOT_bumpOmega hC hG k
      rw [sf_ot (isOT_add hV0 hW)] at hv
      rw [hv] at hμ
      exact absurd (succ_of_add_single (omega_psi_form _) hμ).1 (bumpOmega_ne_one hC hG k)
  · rw [if_neg h2] at hv
    rw [sf_ot (isOT_add hV0 (isOT_bumpOmega hC hG i))] at hv
    rw [hv] at hμ
    exact absurd (succ_of_add_single (omega_psi_form _) hμ).1 (bumpOmega_ne_one hC hG i)

end

/-! ## 1 列落とし -/

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB

/-- **The lost-kids hypothesis**: a column that loses all its counted children is the parent of `x`. -/
def LostKids (M : Mat) (x : Nat) (ρ ρ' : Valn) : Prop :=
  ∀ i, i < x → cvals (M.take x) ρ' i = [] → cvals M ρ i ≠ [] → par M 0 x = some i

theorem prefLast_take {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hR' : Rk (M.take x) rk') (hP : PrefLast M ρ) :
    PrefLast (M.take x) ρ' := by
  have hlen : (M.take x).length = x := by rw [List.length_take]; omega
  have hv := fun {c p : Nat} (hc : c < x) (hp : par M 1 c = some p) =>
    v_take_of_par1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hR' hc hp
  intro j c p hj hcj hp
  rw [hlen] at hj
  rw [par_take M 1 c (by omega)] at hp
  rw [hv (by omega) hp]
  refine ⟨fun q hq hne => ?_, fun i q hi hq hne => ?_⟩
  · rw [par_take M 1 j hj] at hq
    rw [hv hj hq] at hne ⊢
    exact (hP j c p (by omega) hcj hp).1 q hq hne
  · rw [par_take M 0 j hj] at hi
    have hij := par_lt M 0 j i hi
    rw [par_take M 1 i (by omega)] at hq
    rw [hv (by omega) hq] at hne ⊢
    exact (hP j c p (by omega) hcj hp).2 i q hi hq hne

/-- **LevLeafInv passes to `M.take x`**, given PrefLast and the lost-kids hypothesis. -/
theorem levLeaf_take {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hG' : Good3 (M.take x) ρ') (hR' : Rk (M.take x) rk')
    (hL : LevLeafInv M ρ) (hP : PrefLast M ρ) (hK : LostKids M x ρ ρ') : LevLeafInv (M.take x) ρ' := by
  have hlen : (M.take x).length = x := by rw [List.length_take]; omega
  have hv := fun {c p : Nat} (hc : c < x) (hp : par M 1 c = some p) =>
    v_take_of_par1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hR' hc hp
  intro c p i μ hc hp hi hcv hvi hμ
  rw [hlen] at hc hi
  rw [par_take M 1 c hc] at hp
  rw [hv hc hp]
  obtain ⟨h1, h2, hu', hμq⟩ := v_succ_form hC' hG' (by rw [hlen]; exact hi) hvi
  rw [entry_take M 1 hi] at h1
  rw [entry_take M 2 hi] at h2
  rw [par_take M 1 i hi] at hμq
  cases hq : par M 1 i with
  | none => rw [hq] at hμq; exact absurd hμq hμ
  | some q =>
    rw [hq] at hμq
    simp only [vOpt] at hμq
    rw [hv hi hq] at hμq
    subst hμq
    by_cases hix : i + 1 < x
    · -- the upgrade is unchanged, so `v(i) = v(q) + 1` in `M` too
      rw [upg_take M hix] at hu'
      have hvM : ρ.v i = succ (ρ.v q) := by
        have hvi' := (hC i (by omega)).2
        unfold vRhs at hvi'
        rw [if_neg h1, if_pos h2, hu', hq] at hvi'
        simp only [vOpt] at hvi'
        rw [hvi', sf_ot (isOT_add (hG.ot_v q (by have := par_lt M 1 i q hq; omega)) rfl), add_one_eq_app]
        rfl
      by_cases hcvM : cvals M ρ i = []
      · exact hL c p i _ (by omega) hp (by omega) hcvM hvM hμ
      · have hpx := hK i hi hcv hcvM
        exact (hP x c p (by omega) (by omega) hp).2 i q hpx hq hμ
    · -- `i = x − 1`
      have hix' : i = x - 1 := by omega
      by_cases hcx : c < x - 1
      · exact (hP (x - 1) c p (by omega) hcx hp).1 q (by rw [← hix']; exact hq) hμ
      · have hce : c = x - 1 := by omega
        rw [hce, ← hix', hq] at hp
        cases hp
        exact levFree_self _

end

end Ytosk
