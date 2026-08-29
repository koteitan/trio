/-
H12H2.lean: L3 の §163 の前提 `h2` を消費側の `Q` について確かめる。

`h2`（`L105Cap.lean:11588`、逐語）:
    `∀ j, j < Q.length → 0 < entry Q 2 j → hasParent (Q.take (j + 1)) 2 j`

⚠ **`j = 0` を入れると、結論 `hasParent _ 2 0` は常に偽**
（`L53.not_hasParent_zero`、`L53Subst.lean:3308`）。
⟹ **`h2` は `entry Q 2 0 = 0` を含意する。**
⟹ **L3 が捨てたはずの旧前提 `entry Q 2 0 = 0` が、`h2` の `j = 0` の場合として復活している。**
⟹ 消費側の `Q = Lift1 ((0,v,z) :: R.dropLast) t` では `entry Q 2 0 = z` なので、
   **`z = 1` では `h2` は偽**。
-/
import L105Cap

namespace TRIO
namespace H12H2

open Wset
open L105

/-- **★ `h2` は旧前提 `entry Q 2 0 = 0` を含意する**（`j = 0` の場合）。 -/
theorem h2_implies_root_row2_zero {Q : TrioSeq} (hQne : Q ≠ [])
    (h2 : ∀ j, j < Q.length → 0 < entry Q 2 j → hasParent (Q.take (j + 1)) 2 j) :
    entry Q 2 0 = 0 := by
  by_contra hc
  exact L53.not_hasParent_zero (Q.take 1) 2
    (h2 0 (List.length_pos_iff.mpr hQne) (by omega))

/-- **⟹ 消費側の `Q = Lift1 ((0,v,z) :: R.dropLast) t` では `h2` は `z = 0` を強制する。** -/
theorem h2_forces_z_zero {v z t : ℕ} {R : TrioSeq}
    (h2 : ∀ j, j < (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t).length →
      0 < entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) 2 j →
      hasParent ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t).take (j + 1)) 2 j) :
    z = 0 := by
  have hne : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t ≠ [] := by
    intro hc
    have : (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t).length = 0 := by
      rw [hc]; rfl
    rw [Lift1_length] at this
    simp at this
  have hroot := h2_implies_root_row2_zero hne h2
  rw [entry2_Lift1] at hroot
  show z = 0
  have : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 2 0 = z := rfl
  omega


/-! ## 2. ⛔ **`h2` は `j >= 1` に弱めても偽** —— 断片の中の 2 列の反例

`h2` の `j = 0` を外した版

    `h2' : ∀ j, 1 <= j → j < Q.length → 0 < entry Q 2 j → hasParent (Q.take (j+1)) 2 j`

でも救えない。反例:

    **`Q = Lift1 [(0,0,0),(1,0,1)] t = [(0,t,0),(1,0,1)]`**

`Infcex.cexX`（`Infcex.lean:41`）と同じ形だが、**行 2 が 1 なので z<2 断片の中**。

    列 1 は行 2 が 1 > 0。しかし**行 1 が増えない**ので `le1 Q 0 1` が偽
    （`nextrel1` は行 1 の狭義増加を要求）。`nextrel2` は `le1` を要求するので
    **列 1 は行 2 の親を持たない**。
    しかも **`Q ∈ W a`**（末尾列は孤児なので `oper = Pred`、`Aop` の節 2）。

⟹ **`h2` は `hQmem : Q ∈ W a` からも `hQshallow` からも出ない。** -/

/-- 反例の列（`Lift1 [(0,0,0),(1,0,1)] t` に等しい）。 -/
def X (t : ℕ) : TrioSeq := [((0, t, 0) : ℕ × ℕ × ℕ), ((1, 0, 1) : ℕ × ℕ × ℕ)]

/-- 列 1 は行 1 の祖先を持たない（行 1 が増えない）。 -/
theorem not_le1_X (t : ℕ) : ¬ le1 (X t) 0 1 := by
  rintro ⟨-, -, hr⟩
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨b, -, hb⟩
  · exact absurd h (by omega)
  · have hblt : b < 1 := hb.2.2.1
    have hb0 : b = 0 := by omega
    subst hb0
    have hlt : entry (X t) 1 0 < entry (X t) 1 1 := hb.2.2.2.1
    rw [show entry (X t) 1 0 = t from rfl, show entry (X t) 1 1 = 0 from rfl] at hlt
    omega

/-- ⟹ 列 1 は行 2 の親も持たない（`nextrel2` は `le1` を要求する）。 -/
theorem not_hasParent_X (t : ℕ) : ¬ hasParent (X t) 2 1 := by
  rintro ⟨j, hj, -⟩
  unfold nextR at hj
  rw [if_neg (by omega), if_neg (by omega)] at hj
  have hjlt : j < 1 := hj.2.2.1
  have hj0 : j = 0 := by omega
  subst hj0
  exact not_le1_X t hj.2.2.2.2.1

/-- **★ 反例は `Lift1 ((0,v,z) :: R.dropLast) t` の形をしている**
（`v = 0`, `z = 0`, `R.dropLast = [(1,0,1)]`）。 -/
theorem lift_X (t : ℕ) :
    Lift1 (((0, (0 : ℕ), (0 : ℕ)) : ℕ × ℕ × ℕ) :: [((1, 0, 1) : ℕ × ℕ × ℕ)]) t
      = X t := by
  have hle0 : le1 (X 0) 0 0 :=
    ⟨by simp [X], by simp [X], Relation.ReflTransGen.refl⟩
  have hle1 : ¬ le1 (X 0) 0 1 := not_le1_X 0
  show Lift1 (X 0) t = X t
  unfold Lift1
  rw [show (X 0).length = 2 from rfl, show List.range 2 = [0, 1] from rfl]
  simp only [List.map_cons, List.map_nil, if_pos hle0, if_neg hle1]
  rw [show entry (X 0) 0 0 = 0 from rfl, show entry (X 0) 1 0 = 0 from rfl,
    show entry (X 0) 2 0 = 0 from rfl, show entry (X 0) 0 1 = 1 from rfl,
    show entry (X 0) 1 1 = 0 from rfl, show entry (X 0) 2 1 = 1 from rfl,
    Nat.zero_add]
  rfl

/-- **★ 反例は本当に `W a` の中にいる**（`hQmem` を満たす）。 -/
theorem X_mem_W {a t : ℕ} (ha : 2 * t ≤ a) : X t ∈ W a := by
  have hsingle : [((0, t, (0 : ℕ)) : ℕ × ℕ × ℕ)] ∈ W a :=
    W_mono (show 2 * t + 0 ≤ a by omega) (Om_mem_W t 0)
  have hsrow : srow (X t) ((X t).length - 1) = 2 := by
    show srow (X t) 1 = 2
    unfold srow
    rw [if_pos (show 0 < entry (X t) 2 1 from by
      rw [show entry (X t) 2 1 = 1 from rfl]; omega)]
  have hnp : ¬ hasParent (X t) (srow (X t) ((X t).length - 1))
      ((X t).length - 1) := by
    rw [hsrow, show (X t).length - 1 = 1 from rfl]
    exact not_hasParent_X t
  refine A1_intro (Or.inr (Or.inl (fun n _ => ?_)))
  have hL : (X t).length - 1 ≠ 0 := by
    rw [show (X t).length - 1 = 1 from rfl]; omega
  have hz : ¬ (entry (X t) 0 ((X t).length - 1) = 0 ∧
      entry (X t) 1 ((X t).length - 1) = 0 ∧
      entry (X t) 2 ((X t).length - 1) = 0) := by
    rw [show (X t).length - 1 = 1 from rfl, show entry (X t) 0 1 = 1 from rfl]
    rintro ⟨h0, -, -⟩
    omega
  rw [oper_eq_pred_of_noParent n hL hz hnp]
  unfold Pred
  rw [if_neg (show ¬ (X t).length ≤ 1 from by
    rw [show (X t).length = 2 from rfl]; omega)]
  rw [show (X t).dropLast = [((0, t, (0 : ℕ)) : ℕ × ℕ × ℕ)] from rfl]
  exact hsingle

/-- ⛔ **`h2` を `1 <= j` に弱めても偽。** -/
theorem h2_prime_false (t : ℕ) :
    ¬ (∀ j, 1 ≤ j → j < (X t).length → 0 < entry (X t) 2 j →
        hasParent ((X t).take (j + 1)) 2 j) := by
  intro h
  have hx := h 1 (by omega)
    (show (1 : ℕ) < (X t).length from by rw [show (X t).length = 2 from rfl]; omega)
    (show 0 < entry (X t) 2 1 from by rw [show entry (X t) 2 1 = 1 from rfl]; omega)
  rw [show (X t).take (1 + 1) = X t from rfl] at hx
  exact not_hasParent_X t hx

/-- ⛔ **`h2`（`L105Cap.lean:11588`）は `hQmem : Q ∈ W a` と根の浅さからは出ない。**
`Q = X t` は `W a` の中にあり、根が狭義最浅で、しかも `h2`（弱めた版でも）を満たさない。 -/
theorem h2_not_derivable :
    ∃ Q : TrioSeq, (∀ a, 2 * 0 ≤ a → Q ∈ W a) ∧
      (∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) ∧
      ¬ (∀ j, 1 ≤ j → j < Q.length → 0 < entry Q 2 j →
          hasParent (Q.take (j + 1)) 2 j) := by
  refine ⟨X 0, fun a ha => X_mem_W ha, ?_, h2_prime_false 0⟩
  intro l hl0 hll
  rw [show (X 0).length = 2 from rfl] at hll
  have : l = 1 := by omega
  subst this
  rw [show entry (X 0) 0 0 = 0 from rfl, show entry (X 0) 0 1 = 1 from rfl]
  omega


/-! ## 3. ★ **`h2` の残差はちょうど 2 つ** —— 根（`z=1`）と、行 1 の錐の外の列

§248.3 の反例は**錐の外の列**だった。錐の中に限れば `h2` は**既存の緑の補題から無料**:

    `Wset.hasParent_two_of`（`Wset.lean:1858`）
      `b < |M|` → `k < b` → `le1 M k b` → `entry M 2 k < entry M 2 b` → `hasParent M 2 b`

を `M = Q.take (j+1)`, `k = 0`, `b = j` で使うだけ。

⟹ **`h2` を消費側で満たせない原因は、ちょうど次の 2 つに限られる:**

    (i)  **`j = 0`（根）** … `entry Q 2 0 = z`。`z = 1` なら即座に偽
    (ii) **錐の外の行 2 正の列** … `¬ le1 Q 0 j`（ブロッカーの向こう側）

これは `L105Cap.lean` §79.1 が既に書いている「孤児の条件」と同じもの。
⟹ **`h2` は新しい前提ではなく、`hnb`（ブロッカーなし）＋ `z = 0` の言い換え。** -/

/-- ★ **錐の中の列では `h2` は無料**（`hasParent_two_of` そのもの）。 -/
theorem h2_cone {Q : TrioSeq} (hz0 : entry Q 2 0 = 0) :
    ∀ j, 1 ≤ j → j < Q.length → 0 < entry Q 2 j → le1 Q 0 j →
      hasParent (Q.take (j + 1)) 2 j := by
  intro j hj1 hjl hpos hcone
  have hlen : (Q.take (j + 1)).length = j + 1 := by
    rw [List.length_take]; omega
  refine hasParent_two_of (M := Q.take (j + 1)) (b := j) (k := 0)
    (show j < (Q.take (j + 1)).length from by rw [hlen]; omega) (by omega) ?_ ?_
  · exact (le1_take (by omega) (by omega)).mpr hcone
  · rw [entry_take (by omega), entry_take (by omega), hz0]
    omega

/-- ★★ **⟹ `h2` の残差はちょうど「根」と「錐の外」だけ。**
`entry Q 2 0 = 0`（＝ `z = 0`）と「行 2 が正なら錐の中」があれば `h2` は成り立つ。 -/
theorem h2_of_cone {Q : TrioSeq} (hz0 : entry Q 2 0 = 0)
    (hcone : ∀ j, 1 ≤ j → j < Q.length → 0 < entry Q 2 j → le1 Q 0 j) :
    ∀ j, j < Q.length → 0 < entry Q 2 j → hasParent (Q.take (j + 1)) 2 j := by
  intro j hjl hpos
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · exact absurd hz0 (by omega)
  · exact h2_cone hz0 j hj1 hjl hpos (hcone j hj1 hjl hpos)

end H12H2
end TRIO
