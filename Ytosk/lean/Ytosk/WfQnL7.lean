/-
**WfQnL7 (2026-11-01): root decrease for the generalized t = 1, q ≠ r engine (step 4).**
- `root_N_any`: `root_N_t1` (V3Root) for any valuation `σ` of `N = M[n]` that keeps the roots before the root `Rt`
  of `x` and puts a single term below `o(Rt)` at `Rt`.
- `root_N_E3`: with (E1) off `DepXB M B` (`WfQnL5.E1_M`), the roots before `Rt` keep their value (they are outside
  `D`); at `Rt` the old glue value `fsD(o(Rt), ζ)` is used when `Rt ∉ DepXB M B`, and (E3) when `Rt ∈ DepXB M B`.
-/
import Ytosk.WfQnL5
import Ytosk.V3Root

namespace Ytosk.WfQnL7
open T Ytosk Ytosk.WfQnE3

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **The value of `M[n]` drops**, for any valuation that keeps the earlier roots and drops at `Rt`. -/
theorem root_N_any {ρ σ : Valn} {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0))
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hpre : ∀ c ∈ roots M, c < Rt → σ.o c = ρ.o c)
    (hsR : Single (σ.o Rt)) (hlt : σ.o Rt < ρ.o Rt) :
    isOT (root (TRIO.gexp M r L d0 0 n) σ) = true ∧ root (TRIO.gexp M r L d0 0 n) σ < root M ρ := by
  have hsplit := roots_split hlen hRA hR0
  set pre := (roots M).filter (fun c => decide (c < Rt)) with hpre'
  have hpre_lt : ∀ c ∈ pre, c < Rt := by
    intro c hc; rw [hpre', List.mem_filter] at hc; simpa using hc.2
  have hpre_mem : ∀ c ∈ pre, c ∈ roots M := by
    intro c hc; rw [hpre', List.mem_filter] at hc; exact hc.1
  have hglue : (roots M).map σ.o = pre.map ρ.o ++ [σ.o Rt] := by
    rw [hsplit, List.map_append, List.map_singleton]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact hpre c (hpre_mem c hc) (hpre_lt c hc)
  have hMl : (roots M).map ρ.o = pre.map ρ.o ++ [ρ.o Rt] := by
    rw [hsplit, List.map_append, List.map_singleton]
  rw [hMl] at hpM
  have hsl : ∀ t ∈ pre.map ρ.o ++ [ρ.o Rt], Single t := by
    intro t ht
    rw [← hMl] at ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    exact hsM i hi
  have hsl' : ∀ t ∈ pre.map ρ.o ++ [σ.o Rt], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsl t (List.mem_append_left _ ht)
    · rw [List.mem_singleton] at ht; subst ht; exact hsR
  have hpl' : (pre.map ρ.o ++ [σ.o Rt]).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_append] at hpM ⊢
    refine ⟨hpM.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    exact le_trans (le_of_lt hlt) (hpM.2.2 a ha _ (List.mem_singleton_self _))
  have hrootN : root (TRIO.gexp M r L d0 0 n) σ = sumN (pre.map ρ.o ++ [σ.o Rt]) := by
    rw [root_eq_roots, roots_N_t1 hlen hL hA hd0e hn, hglue]
    · intro i hi
      rw [roots_N_t1 hlen hL hA hd0e hn] at hi
      have : σ.o i ∈ (roots M).map σ.o := List.mem_map.mpr ⟨i, hi, rfl⟩
      rw [hglue] at this
      exact hsl' _ this
    · rw [roots_N_t1 hlen hL hA hd0e hn, hglue]; exact hpl'
  have hrootM : root M ρ = sumN (pre.map ρ.o ++ [ρ.o Rt]) := by
    rw [root_eq_roots hsM (by rw [hMl]; exact hpM), hMl]
  rw [hrootN, hrootM]
  refine ⟨(sumN_dec _ hsl' hpl').1, ?_⟩
  rw [sumN_snoc_dec hsl' hpl', sumN_snoc_dec hsl hpM]
  exact app_lt_app_left _ hlt

/-- **Root decrease from (E1) and (E3).** `hE1o` is the `o` half of `WfQnL5.E1_M`; `hE3` is (E3) at the root
(only used when the root lies in the closure of the bad calls). -/
theorem root_N_E3 {ρ ρP σ : Valn} {Z : Nat → T} {B : Nat → Prop} {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hB : ∀ i, B i → DepX M (r + L) false i)
    (hE1o : ∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M B true i) →
      σ.o i = (glueZ M (r + L) ρ (shiftV ρP L) Z).o i)
    (hsR : Single (fsD (ρ.o Rt) (Z Rt))) (hlt : fsD (ρ.o Rt) (Z Rt) < ρ.o Rt)
    (hE3 : DepXB M B true Rt → Single (σ.o Rt) ∧ σ.o Rt < ρ.o Rt) :
    isOT (root (TRIO.gexp M r L d0 0 n) σ) = true ∧ root (TRIO.gexp M r L d0 0 n) σ < root M ρ := by
  have hlN := len_N (d0 := d0) hlen hn
  have hR0e : entry M 0 Rt = 0 := by unfold entry; unfold col at hR0; rw [hR0]; rfl
  have hRx : Rt < r + L := by
    rcases Nat.eq_or_lt_of_le hRA.le with h | h
    · exfalso
      have h1 : entry M 0 (r + L) ≠ 0 := by
        have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
      rw [h] at hR0e; exact h1 hR0e
    · exact h
  have hpre : ∀ c ∈ roots M, c < Rt → σ.o c = ρ.o c := by
    intro c _ hc
    have hnd : ¬ DepX M (r + L) true c := by
      intro hd
      have := depX_ge (by omega) hR0e hRA.le hRlast hd
      omega
    rw [hE1o c (by omega) (fun h => hnd (DepXB.sub hB h.2)), glueZ_o_lt ρ _ Z (by omega) hnd]
  by_cases hb : DepXB M B true Rt
  · exact root_N_any hlen hL hA hd0e hn hRA hR0 hsM hpM hpre (hE3 hb).1 (hE3 hb).2
  · have hσR : σ.o Rt = fsD (ρ.o Rt) (Z Rt) := by
      rw [hE1o Rt (by omega) (fun h => hb h.2), glueZ_o_dep ρ _ Z hRx hRd]
    rw [← hσR] at hsR hlt
    exact root_N_any hlen hL hA hd0e hn hRA hR0 hsM hpM hpre hsR hlt

end

end Ytosk.WfQnL7
