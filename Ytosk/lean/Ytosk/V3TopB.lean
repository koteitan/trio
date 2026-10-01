/-
**最上位の仮定から接頭辞の分（`Res3.chain`）を外す。**

標準形の接頭辞はまた標準形（`std_take`）。そこで最上位の仮定を「すべての評価について」述べる形 `HInvA` に
替えると、`Res3.chain`（接頭辞 `M.take (j + 1) → M.take j` の落とす補題の残り）は、接頭辞にそれ自身の
`Res3.drop` を当てて出る。接頭辞の順位は `M` の順位をそのまま使う（`counted_take_last`）。
-/
import Ytosk.V3Top
import Ytosk.V3ExpOne
import Ytosk.TwoRowZ

namespace Ytosk

open T

/-- `Res3` without `chain`. -/
structure Res3A (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  drop : DropRes M (M.length - 1) ρ (drop1 M (M.length - 1) rk)
  seed : ∀ r, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    lt (sf ((drop1 M (M.length - 1) rk).v r)) (ρ.v r) = true →
    ∀ u g, g ∈ comps u ((drop1 M (M.length - 1) rk).o r) → g < (drop1 M (M.length - 1) rk).o r
  t0 : ∀ r L, r + L + 1 = M.length → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ s' y', (drop1 M (r + L) rk).o r = psi s' y' z → s' ≠ ρ.v r → ∀ g Lc,
      par M 0 r = some g → CL M g = Lc ++ [r] → ∀ s y, ρ.o r = psi s y z →
      lt (spArg (ρ.v g) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true →
      VSmallV s') ∧
    (∀ g, par M 0 r = some g → col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 →
      sumN ((children (M.take (r + L)) r).map (drop1 M (r + L) rk).o) =
        sumN ((children (M.take (r + L)) r).map ρ.o)) ∧
    (∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → VSmallNewN M r ρ σ)

/-- **The top hypothesis, for every valuation**: every nonempty standard matrix other than SRO has a
ranking, and every valuation and ranking of it satisfy `Inv3` and `Res3A`. -/
def HInvA : Prop :=
  ∀ M, Std M → M ≠ SRO → M ≠ [] →
    (∃ rk, Rk M rk) ∧ ∀ ρ rk, Cons M ρ → Rk M rk → Inv3 M ρ rk ∧ Res3A M ρ rk

/-- The ranking of `M` ranks every prefix. -/
theorem rk_take_all {M : Mat} {rk : Bool → Nat → Nat} (hR : Rk M rk)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAB : UAB M) :
    ∀ j, j ≤ M.length → Rk (M.take j) rk := by
  have hUATt := fun k => UAT_take hR0 hZ2 hSD hZ1 hUAB k
  have key : ∀ m j, M.length - j ≤ m → j ≤ M.length → Rk (M.take j) rk := by
    intro m
    induction m with
    | zero =>
      intro j hm hj
      rw [show j = M.length by omega, List.take_length]; exact hR
    | succ m ih =>
      intro j hm hj
      rcases Nat.eq_or_lt_of_le hj with hjx | hjx
      · rw [hjx, List.take_length]; exact hR
      · have hN := ih (j + 1) (by omega) hjx
        have hlj : (M.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
        have hcnt := counted_take_last (M := M.take (j + 1)) (by rw [hlj]; omega)
          (R0P_take hR0 _) (Z2_take hZ2 _) (SibDec_take hSD _) (Z1C_take hZ1 _) (hUATt _)
        rw [hlj, show j + 1 - 1 = j by omega] at hcnt
        have := rk_take (by rw [hlj]; omega) hN hcnt
        rwa [take_take_succ] at this
  exact fun j hj => key (M.length - j) j (Nat.le_refl _) hj

theorem drop1_take_succ (M : Mat) (j : Nat) (rk : Bool → Nat → Nat) :
    drop1 (M.take (j + 1)) j rk = drop1 M j rk := by
  unfold drop1; rw [take_take_succ]

/-- **`HInvA` gives the old top hypothesis**, with `chain` from the prefixes. -/
theorem hInv_of_A (h : HInvA) :
    ∀ M, Std M → M ≠ SRO → M ≠ [] → ∃ ρ rk, Inv3 M ρ rk ∧ Res3 M ρ rk := by
  intro M hM hS hE
  obtain ⟨⟨rk, hR⟩, hall⟩ := h M hM hS hE
  have hC := cons_of_rk hR
  obtain ⟨I, RA⟩ := hall _ rk hC hR
  have hRk := rk_take_all hR I.r0p I.z2 I.sd I.z1 I.uab
  refine ⟨_, rk, I, ⟨RA.drop, ?_, RA.seed, ?_⟩⟩
  rotate_left
  · -- `t0`: the values of `M[n]` are those of a standard matrix
    intro r L hlen hp he1
    obtain ⟨hVr, hG', hVN⟩ := RA.t0 r L hlen hp he1
    refine ⟨hVr, hG', ?_⟩
    intro n hn2 σ hCN
    have hL : 0 < L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · subst h0; have := par_lt M 0 _ r hp; omega
      · exact h0
    have he2 : entry M 2 (r + L) = 0 := I.r12 _ he1
    have hRN := rk_N0 hlen hL hp (show 1 ≤ n by omega) I.r0p I.z2 he2 hn2 hR
    have hlN : (TRIO.gexp M r L 0 0 n).length = r + n * L := lenN0 hlen (show 1 ≤ n by omega)
    have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
        TRIO.entry M 2 (M.length - 1) = 0) := by
      rw [show M.length - 1 = r + L by omega, ← entry_eq, ← entry_eq, ← entry_eq, I.r0p _ _ hp]
      omega
    have hs0 : TRIO.srow M (M.length - 1) = 0 := by
      unfold TRIO.srow
      rw [show M.length - 1 = r + L by omega, ← entry_eq, ← entry_eq, he1, he2]; rfl
    have hexp := expand_eq_gexp_t0 M n (by omega) hzT
      (by rw [hs0, show M.length - 1 = r + L by omega]; exact hp) hs0
    rw [show M.length - 1 - r = L by omega] at hexp
    have hSN : Std (TRIO.gexp M r L 0 0 n) := hexp ▸ Std.exp n hM
    have hEN : TRIO.gexp M r L 0 0 n ≠ [] := by
      intro he; rw [he] at hlN; simp at hlN
      have : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
      omega
    have hSRN : TRIO.gexp M r L 0 0 n ≠ SRO := by
      intro he; rw [he] at hRN; exact not_val_SRO _ (val_of_rk hRN)
    have IN := ((h _ hSN hSRN hEN).2 σ _ hCN hRN).1
    exact ⟨IN.good, hVN n hn2 σ hCN, IN.rootS, IN.rootP⟩
  intro j hj
  have hlj : (M.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
  have hRj := hRk (j + 1) (by omega)
  have hSj : Std (M.take (j + 1)) := std_take hM (j + 1) (by omega)
  have hEj : M.take (j + 1) ≠ [] := by
    intro he; rw [he] at hlj; simp at hlj
  have hSRj : M.take (j + 1) ≠ SRO := by
    intro he; rw [he] at hRj; exact not_val_SRO _ (val_of_rk hRj)
  have hD := ((h _ hSj hSRj hEj).2 _ rk (cons_of_rk hRj) hRj).2.drop
  rw [hlj, show j + 1 - 1 = j by omega, drop1_take_succ] at hD
  exact hD

/-- **Termination of the 3-row BMS from SRO**, with the top hypothesis stated for every valuation and
without the prefix drops. -/
theorem trio_terminatesA (hInv : HInvA)
    (hT2 : ∀ M ρ rk, Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n) :
    WellFounded Step' :=
  trio_terminates (hInv_of_A hInv) hT2

end Ytosk
