/-
**t = 2 のエンジンが読む欄だけの束 `Inv3W`・`Res3W`（2026-10-16、t2）。**

t = 2 の展開のエンジン（V3ExpT2*・V3T2*・V3PSeed*・V3PT2*・V3QNFC・V3SVFix・V3CFix・V3CBig・V3Tame）は、
`Inv3` のうち構造の欄と Cons・Good3・Rk・VSmallF・FrameClosed・FrameOT・BumpKidsDec・BumpTermDec・
rootS・rootP しか読まない。`Res3A` からは落とす補題の残り `drop` だけを読む。
偽の欄（AbsD・AbsU・TPLo・AbsUW・TrigOmC）を含む `Inv3` の代わりに、この束で受ける。
`Inv3.toW`・`Res3A.toW` で旧い形から、Inv3V2 からは V3ExpT2Inv2 の `Inv3W.ofV2` で作る。
-/
import Ytosk.V3TopB
import Ytosk.V3InvExpand

namespace Ytosk

open T

/-- **The fields of `Inv3` that the `t = 2` engine reads.** -/
structure Inv3W (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  r0p : R0P M
  z2 : Z2 M
  sd : SibDec M
  z1 : Z1C M
  uat : UAT M
  uab : UAB M
  r12 : R12 M
  be : BumpE2 M
  r01 : R01 M
  e00 : entry M 0 0 = 0
  cons : Cons M ρ
  good : Good3 M ρ
  rank : Rk M rk
  vs : VSmallF M ρ
  fc : FrameClosed M ρ
  fo : FrameOT M ρ
  kd : BumpKidsDec M ρ
  td : BumpTermDec M ρ
  rootS : ∀ i ∈ roots M, Single (ρ.o i)
  rootP : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)

/-- **The field of `Res3A` that the `t = 2` engine reads**: the drop residual of `M → M.take x`. -/
structure Res3W (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  drop : DropRes M (M.length - 1) ρ (drop1 M (M.length - 1) rk)

theorem Inv3.toW {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) : Inv3W M ρ rk :=
  ⟨I.r0p, I.z2, I.sd, I.z1, I.uat, I.uab, I.r12, I.be, I.r01, I.e00, I.cons, I.good, I.rank, I.vs, I.fc,
    I.fo, I.kd, I.td, I.rootS, I.rootP⟩

theorem Res3A.toW {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (R : Res3A M ρ rk) : Res3W M ρ rk :=
  ⟨R.drop⟩

theorem Res3.toW {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (R : Res3 M ρ rk) : Res3W M ρ rk :=
  ⟨R.drop⟩


/-- The structural part of `Inv3W`. -/
theorem Inv3W.toS {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) : SInv M :=
  ⟨I.r0p, I.z2, I.sd, I.z1, I.uat, I.uab, I.r12, I.be, I.r01, I.e00⟩

/-- `Inv3W` from the structural invariants and the value fields. -/
theorem Inv3W.mk' {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ)
    (hG : Good3 M ρ) (hR : Rk M rk) (hV : VSmallF M ρ) (hFC : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hS : ∀ i ∈ roots M, Single (ρ.o i))
    (hP : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a)) : Inv3W M ρ rk :=
  ⟨S.r0p, S.z2, S.sibDec, S.z1c, S.uat, S.uab, S.r12, S.bumpE2, S.r01, S.e00, hC, hG, hR, hV, hFC, hFO,
    hKD, hTD, hS, hP⟩

end Ytosk
