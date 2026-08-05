/-
Infcex.lean: ⛔ `InfEquip` は **偽** — 2 列の反例。

`InfEquip` は結論に `entry M 2 p ≤ 1`（文脈の行 2 が z<2 断片に収まる）を
含むが、これは `argOK M`（行 0 が正）からも `CtxOK M v z` からも出ない。

反例: `M = [(1,0,2),(2,0,0)]`, `p = 0`, 根 `(v,z) = (0,0)`。
* `argOK M`（両列とも深さ > 0）、窓条件 `entry M 0 0 = 1 < 2 = entry M 0 1`
* `CtxOK M 0 0`: 接頭辞は `[]` と `[(1,0,2)]` のみで、リフトした植えブロックは
  `[(0,t,0)]` と `[(0,t,0),(1,0,2)]`。後者の末尾列は行 1 の祖先を持たない
  （行 1 が増えない）ので UBI により行 2 の親も無く、`oper = Pred`。よって
  `Aop` の節 2 で `W a` に入る。
* しかし `entry M 2 0 = 2 > 1`。

⟹ `InfEquip` を仮定する頂点定理（`TRIO_terminates_of_plant` 系）は**空虚**。
-/
import Gamma

namespace TRIO

open Wset
open Classical

/-! ## 単元のリフト -/

theorem lift_single (v z t : ℕ) :
    Lift1 [((0, v, z) : ℕ × ℕ × ℕ)] t = [((0, v + t, z) : ℕ × ℕ × ℕ)] := by
  have hle : le1 [((0, v, z) : ℕ × ℕ × ℕ)] 0 0 :=
    ⟨by simp, by simp, Relation.ReflTransGen.refl⟩
  unfold Lift1
  rw [show [((0, v, z) : ℕ × ℕ × ℕ)].length = 1 from rfl,
    show List.range 1 = [0] from rfl]
  simp only [List.map_cons, List.map_nil, if_pos hle]
  rfl

/-! ## 反例の列 -/

/-- The witness context. -/
def cexM : TrioSeq := [((1, 0, 2) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ)]

/-- The lifted planted prefix of length 1. -/
def cexX (t : ℕ) : TrioSeq := [((0, t, 0) : ℕ × ℕ × ℕ), ((1, 0, 2) : ℕ × ℕ × ℕ)]

/-- Column 1 has no row-1 ancestor: row 1 does not increase. -/
theorem not_le1_cexX (t : ℕ) : ¬ le1 (cexX t) 0 1 := by
  rintro ⟨-, -, hr⟩
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨b, -, hb⟩
  · exact absurd h (by omega)
  · have hblt : b < 1 := hb.2.2.1
    have hb0 : b = 0 := by omega
    subst hb0
    have hlt : entry (cexX t) 1 0 < entry (cexX t) 1 1 := hb.2.2.2.1
    rw [show entry (cexX t) 1 0 = t from rfl,
      show entry (cexX t) 1 1 = 0 from rfl] at hlt
    omega

theorem lift_cexX (t : ℕ) :
    Lift1 [((0, (0 : ℕ), (0 : ℕ)) : ℕ × ℕ × ℕ), ((1, 0, 2) : ℕ × ℕ × ℕ)] t
      = cexX t := by
  have hle0 : le1 (cexX 0) 0 0 :=
    ⟨by simp [cexX], by simp [cexX], Relation.ReflTransGen.refl⟩
  have hle1 : ¬ le1 (cexX 0) 0 1 := not_le1_cexX 0
  show Lift1 (cexX 0) t = cexX t
  unfold Lift1
  rw [show (cexX 0).length = 2 from rfl, show List.range 2 = [0, 1] from rfl]
  simp only [List.map_cons, List.map_nil, if_pos hle0, if_neg hle1]
  rw [show entry (cexX 0) 0 0 = 0 from rfl, show entry (cexX 0) 1 0 = 0 from rfl,
    show entry (cexX 0) 2 0 = 0 from rfl, show entry (cexX 0) 0 1 = 1 from rfl,
    show entry (cexX 0) 1 1 = 0 from rfl, show entry (cexX 0) 2 1 = 2 from rfl,
    Nat.zero_add]
  rfl

/-! ## 2 列の witness は `W a` に入る（末尾列は孤児） -/

theorem cexX_mem_W {a t : ℕ} (ha : 2 * t ≤ a) : cexX t ∈ W a := by
  have hsingle : [((0, t, (0 : ℕ)) : ℕ × ℕ × ℕ)] ∈ W a :=
    W_mono (show 2 * t + 0 ≤ a by omega) (Om_mem_W t 0)
  have hsrow : srow (cexX t) ((cexX t).length - 1) = 2 := by
    show srow (cexX t) 1 = 2
    unfold srow
    rw [if_pos (show 0 < entry (cexX t) 2 1 from by
      rw [show entry (cexX t) 2 1 = 2 from rfl]; omega)]
  have hnp : ¬ hasParent (cexX t) (srow (cexX t) ((cexX t).length - 1))
      ((cexX t).length - 1) := by
    rw [hsrow, show (cexX t).length - 1 = 1 from rfl]
    rintro ⟨j, hj, -⟩
    unfold nextR at hj
    rw [if_neg (by omega), if_neg (by omega)] at hj
    have hjlt : j < 1 := hj.2.2.1
    have hj0 : j = 0 := by omega
    subst hj0
    exact not_le1_cexX t hj.2.2.2.2.1
  refine A1_intro (Or.inr (Or.inl (fun n _ => ?_)))
  have hL : (cexX t).length - 1 ≠ 0 := by
    rw [show (cexX t).length - 1 = 1 from rfl]; omega
  have hz : ¬ (entry (cexX t) 0 ((cexX t).length - 1) = 0 ∧
      entry (cexX t) 1 ((cexX t).length - 1) = 0 ∧
      entry (cexX t) 2 ((cexX t).length - 1) = 0) := by
    rw [show (cexX t).length - 1 = 1 from rfl,
      show entry (cexX t) 0 1 = 1 from rfl]
    rintro ⟨h0, -, -⟩
    omega
  rw [oper_eq_pred_of_noParent n hL hz hnp]
  unfold Pred
  rw [if_neg (show ¬ (cexX t).length ≤ 1 from by
    rw [show (cexX t).length = 2 from rfl]; omega)]
  rw [show (cexX t).dropLast = [((0, t, (0 : ℕ)) : ℕ × ℕ × ℕ)] from rfl]
  exact hsingle

/-! ## 反例の検証 -/

theorem cexM_ctxOK : CtxOK cexM 0 0 := by
  intro k hk a t hva
  have hklt : k < 2 := by
    rw [show cexM.length = 2 from rfl] at hk; exact hk
  match k, hklt with
  | 0, _ =>
      rw [show cexM.take 0 = ([] : TrioSeq) from rfl, lift_single]
      exact W_mono (show 2 * (0 + t) + 0 ≤ a by omega) (Om_mem_W (0 + t) 0)
  | 1, _ =>
      rw [show ((0, (0 : ℕ), (0 : ℕ)) : ℕ × ℕ × ℕ) :: cexM.take 1
        = [((0, (0 : ℕ), (0 : ℕ)) : ℕ × ℕ × ℕ), ((1, 0, 2) : ℕ × ℕ × ℕ)] from rfl,
        lift_cexX]
      exact cexX_mem_W (by omega)

/-- ⛔ **`InfEquip` is false.**  Its `entry M 2 p ≤ 1` conjunct is not implied
by `argOK` (a row-0 condition) nor by the slice equipment. -/
theorem not_infEquip : ¬ InfEquip := by
  intro h
  have hres := (h cexM 0
    (by
      intro p hp
      rw [show cexM = [((1, 0, 2) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ)] from rfl,
        List.mem_cons, List.mem_cons] at hp
      rcases hp with rfl | rfl | hp
      · omega
      · omega
      · exact absurd hp (List.not_mem_nil))
    (show 2 ≤ cexM.length from by rw [show cexM.length = 2 from rfl])
    (show 0 < cexM.length - 1 from by rw [show cexM.length - 1 = 1 from rfl]; omega)
    (by
      intro j hj0 hj1
      rw [show cexM.length - 1 = 1 from rfl] at hj1
      have hj : j = 1 := by omega
      subst hj
      rw [show entry cexM 0 0 = 1 from rfl, show entry cexM 0 1 = 2 from rfl]
      omega)
    0 0 (by omega) cexM_ctxOK).1
  rw [show entry cexM 2 0 = 2 from rfl] at hres
  omega

end TRIO
