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

end Ytosk
