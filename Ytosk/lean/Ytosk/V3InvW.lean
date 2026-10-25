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

/-- **The grafted bad shape** (2026-10-24): the column `x − 1` (`x` the last column) has an upgrade target, its
parent `p` is the bump child of `g`, and either the strong absorption at `x − 1` fails while `x` lies under `g` or has
row 2 ≠ 0, or `x` is the child of `x − 1` with row 1 ≠ 0 and `BumpAbsC` fails. On standard matrices of this shape the frame fields
`TPLoW`・`AbsDW` and the drop fields `BumpWeakSrc`・`UpgAbsXW0`・`BumpAbsC` can fail (grafted sets graftA・graftB,
desc); outside it they hold. (The same day it was narrowed twice from "upgrade target ∧ bump parent": when `x` lies
above `g` the fields hold with `NBParX` in place of `NBPar` in `UpgAbsXW0`; at `t = 2` the engines need
`NBPar M (x − 1)` only when the strong absorption fails; under `g` with the strong absorption the fields fail only
when `x` is the child of `x − 1` with row 1 ≠ 0; after `TPLoWs`・`AbsDWs` replaced `TPLoW`・`AbsDW` only `BumpAbsC`
fails there.) -/
def Bad2 (M : Mat) : Prop :=
  (∃ k, upg M (M.length - 2) = some k) ∧
    ∃ p g, par M 0 (M.length - 2) = some p ∧ par M 0 p = some g ∧ col M p = bump M g ∧
      (((Anc0 M g (M.length - 1) ∨ entry M 2 (M.length - 1) ≠ 0) ∧
          ∃ ρ, Cons M ρ ∧ ¬ UpgAbsX M (M.length - 1) ρ) ∨
        (par M 0 (M.length - 1) = some (M.length - 2) ∧ entry M 1 (M.length - 1) ≠ 0 ∧
          ∃ ρ, Cons M ρ ∧ ¬ BumpAbsC M (M.length - 1) ρ))

/-- **What the `t = 2` engine reads of the drop** (2026-10-25): the conclusion of the drop lemma, and outside `Bad2` the
old drop residual (`DropRes`, false on `Bad2`). -/
structure Res3W (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  hdrop : ∀ i, i < M.length - 1 →
    PO ρ (drop1 M (M.length - 1) rk) i ∧ PV M ρ (drop1 M (M.length - 1) rk) i
  old : ¬ Bad2 M → DropRes M (M.length - 1) ρ (drop1 M (M.length - 1) rk)
  /-- `BumpAbsC` when the parent of `x` is not a bump child (what `t2_absWN_take` reads). -/
  ab : XParNB M (M.length - 1) → BumpAbsC M (M.length - 1) ρ

theorem Inv3.toW {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) : Inv3W M ρ rk :=
  ⟨I.r0p, I.z2, I.sd, I.z1, I.uat, I.uab, I.r12, I.be, I.r01, I.e00, I.cons, I.good, I.rank, I.vs, I.fc,
    I.fo, I.kd, I.td, I.rootS, I.rootP⟩

/-- `Res3W` from the old drop residual (the drop lemma `drop_all`). -/
theorem Res3W.ofDrop {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) (hE : M ≠ [])
    (hD : DropRes M (M.length - 1) ρ (drop1 M (M.length - 1) rk)) : Res3W M ρ rk := by
  have hl : 1 ≤ M.length := List.length_pos_of_ne_nil hE
  have hx1 : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) hl I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  exact ⟨drop_all hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs hD.vst
    I.fc I.fo hD.argT
    (bump_drop hx1 I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td hD.ab hD.ws)
    hD.ua, fun _ => hD, fun _ => hD.ab⟩


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
