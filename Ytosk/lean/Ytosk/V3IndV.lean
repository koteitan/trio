/-
**帰納法の仮定を値の部分だけにする。**

SRO 以外の標準形は構造の不変条件 `SInv` を満たす（`sInv_std`、V3InvExpand）。したがって `Inv3` の構造の
10 項目は帰納法で運ぶ必要がなく、各段の仕事は値の部分 `Inv3V`（評価・順位・値の不変条件）と `Res3A` だけ。
-/
import Ytosk.V3Ind
import Ytosk.V3InvExpand

namespace Ytosk

open T

/-- The value part of `Inv3`. -/
structure Inv3V (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  cons : Cons M ρ
  good : Good3 M ρ
  rank : Rk M rk
  vs : VSmallF M ρ
  fc : FrameClosed M ρ
  fo : FrameOT M ρ
  kd : BumpKidsDec M ρ
  td : BumpTermDec M ρ
  ad : AbsD M ρ
  au : AbsU M ρ
  tp1 : TP1 M ρ
  tplo : TPLo M ρ
  tp1w : TP1W M ρ
  tplow : TPLoW M ρ
  auw : AbsUW M ρ
  adw : AbsDW M ρ
  trig : TrigOm M ρ
  tplon : TPLoN M ρ
  adn : AbsDN M ρ
  rootS : ∀ i ∈ roots M, Single (ρ.o i)
  rootP : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)

theorem Inv3.ofV {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (V : Inv3V M ρ rk) :
    Inv3 M ρ rk :=
  ⟨S.r0p, S.z2, S.sibDec, S.z1c, S.uat, S.uab, S.r12, S.bumpE2, S.r01, S.e00, V.cons, V.good, V.rank,
    V.vs, V.fc, V.fo, V.kd, V.td, V.ad, V.au, V.tp1, V.tplo, V.tp1w, V.tplow, V.auw, V.adw, V.trig,
    V.tplon, V.adn, V.rootS, V.rootP⟩

/-- **Termination from the value parts of the induction.** The structural invariants of every standard
matrix other than SRO are `sInv_std`. -/
theorem trio_terminates_indV
    (hBase : ∀ n, expand SRO n ≠ [] → ∃ ρ rk, Inv3V (expand SRO n) ρ rk ∧ Res3A (expand SRO n) ρ rk)
    (hTake : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      ∀ j, j < M.length → M.take j ≠ SRO → M.take j ≠ [] →
        ∃ ρ' rk', Inv3V (M.take j) ρ' rk' ∧ Res3A (M.take j) ρ' rk')
    (hExp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN)
    (hT2 : HInvE → ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n) :
    WellFounded Step' := by
  have hSRO : ∀ n, expand SRO n ≠ SRO := by
    intro n h
    have := congrArg List.length h
    rw [expand_SRO_length] at this
    simp [SRO] at this
    omega
  apply trio_terminates_ind _ _ _ hT2
  · intro n hE
    obtain ⟨ρ, rk, V, R⟩ := hBase n hE
    exact ⟨ρ, rk, Inv3.ofV (sInv_std (Std.exp n Std.sro) (hSRO n)) V, R⟩
  · intro M ρ rk hM hS hE I R j hj hjS hjE
    obtain ⟨ρ', rk', V, R'⟩ := hTake M ρ rk hM hS hE I R j hj hjS hjE
    exact ⟨ρ', rk', Inv3.ofV (sInv_std (std_take hM j (by omega)) hjS) V, R'⟩
  · intro M ρ rk hM hS hE I R hz n hn hNS hNE
    obtain ⟨ρN, rkN, V, R'⟩ := hExp M ρ rk hM hS hE I R hz n hn hNS hNE
    exact ⟨ρN, rkN, Inv3.ofV (sInv_std (Std.exp n hM) hNS) V, R'⟩

/-- **The prefix step from the one-column drop.** -/
theorem hTake_of_last
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk') :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      ∀ j, j < M.length → M.take j ≠ SRO → M.take j ≠ [] →
        ∃ ρ' rk', Inv3V (M.take j) ρ' rk' ∧ Res3A (M.take j) ρ' rk' := by
  -- drop one column at a time, from `M.take (k + 1)` to `M.take k`
  have key : ∀ m M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      ∀ j, 1 ≤ j → j < M.length → M.length - j ≤ m →
        ∃ ρ' rk', Inv3V (M.take j) ρ' rk' ∧ Res3A (M.take j) ρ' rk' := by
    intro m
    induction m with
    | zero => intro M ρ rk _ _ _ _ j _ hj hm; omega
    | succ m ih =>
      intro M ρ rk hM hS I R j hj1 hj hm
      obtain ⟨ρ1, rk1, V1, R1⟩ := hLast M ρ rk hM hS (by omega) I R
      by_cases hjx : j = M.length - 1
      · subst hjx; exact ⟨ρ1, rk1, V1, R1⟩
      have hM1 : Std (M.take (M.length - 1)) := std_take hM _ (by omega)
      have hS1 : M.take (M.length - 1) ≠ SRO := ne_SRO_of_rk V1.rank
      have I1 := Inv3.ofV (sInv_std hM1 hS1) V1
      have hl1 : (M.take (M.length - 1)).length = M.length - 1 := by rw [List.length_take]; omega
      obtain ⟨ρ', rk', V', R'⟩ := ih _ ρ1 rk1 hM1 hS1 I1 R1 j hj1 (by omega) (by omega)
      rw [List.take_take, Nat.min_eq_left (by omega)] at V' R'
      exact ⟨ρ', rk', V', R'⟩
  intro M ρ rk hM hS _ I R j hj _ hjE
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; exact absurd List.take_zero hjE
    · exact h0
  exact key _ M ρ rk hM hS I R j hj1 hj (le_refl _)

/-- **The final form of the top theorem**: the remaining work is the base SRO[n], the one-column drop,
the expansions with `n ≥ 2`, and the descent for `t = 2`, each producing only the value part. -/
theorem trio_terminates_final
    (hBase : ∀ n, expand SRO n ≠ [] → ∃ ρ rk, Inv3V (expand SRO n) ρ rk ∧ Res3A (expand SRO n) ρ rk)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hExp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN)
    (hT2 : HInvE → ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n) :
    WellFounded Step' :=
  trio_terminates_indV hBase (hTake_of_last hLast) hExp hT2

end Ytosk
