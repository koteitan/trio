/-
**1 列落としの根の真の減少（x の形によらない）と RootBadV2T2（2026-10-25）。**

`path_strict`（V3RootPath）を x の根から使う。x の根の部分木は x で終わるので、`hend`・`htr` は自明。
これで `RootBadV2T2`（Bad2 で x の行 2 ≠ 0 かつ x が上がり先か bump 子）は落とす補題の結論から出る。
-/
import Ytosk.V3RootPath
import Ytosk.V3GlobV2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The strict descent of the root at the one-column drop**, from the conclusion of the drop lemma alone, for any
last column. -/
theorem root_drop_any {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (hl : 2 ≤ M.length) (I : Inv3V2 M ρ rk)
    (hdrop : ∀ i, i < M.length - 1 → PO ρ (drop1 M (M.length - 1) rk) i ∧ PV M ρ (drop1 M (M.length - 1) rk) i) :
    root (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) < root M ρ := by
  have S := sInv_std hM hS
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  refine (root_take_lt hx S.r01 S.r12 S.e00 I.cons I.good (fun i hi => (hdrop i hi).1.2.1)
    (fun i hi => (hdrop i hi).1.le) ?_).2
  intro R hR hRA _
  exact path_strict hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 hdrop S.r12 S.bumpE2
    (M.length - 1 - R) R (M.length - 1) (Nat.le_refl _) (le_refl _) hRA
    (fun h => absurd h (lt_irrefl _)) (fun h => absurd h (lt_irrefl _))
    (fun t _ htx => not_anc_out (by omega) (by have := htx.le; omega))
    (fun e he hxe => by have := (mem_children he).2; omega) hR

/-- **`RootBadV2T2` holds**, from `HDropU`. -/
theorem rootBadV2T2_holds (hDU : HDropU) : RootBadV2T2 := by
  intro M ρ rk hM hS hl _ I _ _
  exact root_drop_any hM hS hl I (hdrop_of_U hDU hM hS hl I)

end Ytosk
