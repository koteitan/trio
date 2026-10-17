/-
**帰納法の仮定を値の部分だけにする。**

SRO 以外の標準形は構造の不変条件 `SInv` を満たす（`sInv_std`、V3InvExpand）。したがって `Inv3` の構造の
10 項目は帰納法で運ぶ必要がなく、各段の仕事は値の部分 `Inv3V`（評価・順位・値の不変条件）と `Res3A` だけ。
-/
import Ytosk.V3Ind
import Ytosk.V3InvExpand
import Ytosk.V3InvDerive

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
  tp1 : TP1C M ρ
  tplo : TPLo M ρ
  tp1w : TP1WC M ρ
  tplow : TPLoW M ρ
  auw : AbsUW M ρ
  adw : AbsDW M ρ
  trig : TrigOmC M ρ
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
theorem trio_terminates_indV (hU0 : OldUpgAbs)
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
  apply (trio_terminates_ind hU0) _ _ _ hT2
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
theorem trio_terminates_final (hU0 : OldUpgAbs)
    (hBase : ∀ n, expand SRO n ≠ [] → ∃ ρ rk, Inv3V (expand SRO n) ρ rk ∧ Res3A (expand SRO n) ρ rk)
    (hLast : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk')
    (hExp : ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN)
    (hT2 : HInvE → ∀ M ρ rk, Std M → Inv3 M ρ rk → Res3 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ n, DropsAt M ρ n) :
    WellFounded Step' :=
  (trio_terminates_indV hU0) hBase (hTake_of_last hLast) hExp hT2

/-- **The one-column drop from its residual**: the drop lemma (`drop_pres` through `valInv_drop1`) gives the
valuation `drop1 M x rk` of `M.take x` with `Cons`, `Rk`, `Good3`, `VSmallF`, `FrameClosed`, `FrameOT`,
`BumpKidsDec`, `BumpTermDec`, `rootS`, and `rootP` when `x` is not a root. The residual is the other 11
value fields, `rootP` when `x` is a root, and `Res3A` of `M.take x`. -/
theorem hLast_of
    (hRest : ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      let x := M.length - 1
      let σ := drop1 M x rk
      AbsD (M.take x) σ ∧ AbsU (M.take x) σ ∧ TP1C (M.take x) σ ∧ TPLo (M.take x) σ ∧
      TP1WC (M.take x) σ ∧ TPLoW (M.take x) σ ∧ AbsUW (M.take x) σ ∧ AbsDW (M.take x) σ ∧
      TrigOmC (M.take x) σ ∧ TPLoN (M.take x) σ ∧ AbsDN (M.take x) σ ∧
      (entry M 0 x = 0 → RootP (M.take x) σ) ∧ Res3A (M.take x) σ rk) :
    ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3 M ρ rk → Res3A M ρ rk →
      ∃ ρ' rk', Inv3V (M.take (M.length - 1)) ρ' rk' ∧ Res3A (M.take (M.length - 1)) ρ' rk' := by
  intro M ρ rk hM hS hl I R
  obtain ⟨had, hau, htp1, htplo, htp1w, htplow, hauw, hadw, htrig, htplon, hadn, hrp, R'⟩ :=
    hRest M ρ rk hM hS hl I R
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hVI : ValInv M ρ := ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩
  have V := valInv_drop1 hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank hVI R.drop
  have hRP : RootP (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) := by
    by_cases h0 : entry M 0 (M.length - 1) = 0
    · exact hrp h0
    · exact rootP_drop1 hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r01 I.r12 I.e00 h0 I.cons I.rank hVI R.drop
        I.rootP
  exact ⟨_, rk, ⟨hC1, V.g, hRk1, V.vs, V.fc, V.fo, V.kd, V.td, had, hau, htp1, htplo, htp1w, htplow,
    hauw, hadw, htrig, htplon, hadn, rootS_of_good hC1 V.g, hRP⟩, R'⟩

/-- **An expansion of a standard matrix is not SRO** (SRO breaks `UAB`, which `SInvX` gives after an
expansion; and `SRO[n]` has length `1 + 3n`). -/
theorem expand_ne_SRO {M : Mat} (hM : Std M) (n : Nat) : expand M n ≠ SRO := by
  intro h
  rcases sInvX_std' hM with rfl | hX
  · have := congrArg List.length h
    rw [expand_SRO_length] at this
    simp [SRO] at this
    omega
  · have := (sInvX_expand hX n).toSInv.uab
    rw [h] at this
    exact sro_not_uab this

/-- **The valuation of `M[n]` from `HInvE`** (for the cases whose engine does not build one). -/
theorem inv_expand_of_E (h : HInvE) {M : Mat} (hM : Std M) {n : Nat} (hE : expand M n ≠ []) :
    ∃ σ rk, Inv3 (expand M n) σ rk ∧ Res3A (expand M n) σ rk :=
  h _ (Std.exp n hM) (expand_ne_SRO hM n) hE

end Ytosk
