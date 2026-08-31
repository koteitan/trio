/-
課題 L6: **`行 2 <= 行 1` は標準形の不変量**（BMS 3 行 `z<2` 断片）。

既にある `Wset.zle1`（`∀ p ∈ M, p.2.2 ≤ 1`）より**真に強い**。理由は 2 つだけ:

* 生成元の z 頭打ち対角 `diagSeqT 0 v = ((j, j, min j 1))` は
  `min j 1 ≤ j` なので満たす。
* 展開 `oper`（`Trio.lean:98`）は**行 0 と行 1 にだけ非負の差分 `k*d0`, `k*d1` を
  足し、行 2 は逐語コピーする**。だから行 1 は増えるだけで行 2 は動かない。
  `Pred` / `take` は柱を落とすだけ。

証明は `Wset.zle1_oper` / `zle1_ST_TS` の写経（同じ 3 つの補題）。

## なぜ効くかもしれないか

`Wset.no_hasParent_two_of_row1_zero`（`Wset.lean:1893`）が言うのは
「**`(x,0,1)` 型の列（行 1 = 0, 行 2 > 0）はどんな文脈でも行 2 の親を持たない**」。
これが 3 行が 2 行より難しい理由の中心にある（`Wset.lean:2694` の doc:
「この非対称性こそ trio が yapss より多くを必要とする理由」）。そして
`GRAFTALL-PLAN.md §4.5` が `Aop` 節 2 の `natDom` ガードを反証した反例
`[(0,0,0),(1,0,1)]` も、まさに `(1,0,1)` を使っている。

**ところが `row2 ≤ row1` の下では `(x,0,1)` は存在しない**（`row2 > 0` なら
`row1 ≥ row2 ≥ 1`）。下の `no_permanent_orphan_of_r21` がそれを言う。

実測（生成器の制約を使わず、BM4 の展開閉包を直に作ったもの）:
対角 `v = 0..5` から `n ∈ {1,2,3}` で 6 段展開した 2479 個で
**`行 2 > 行 1` の柱 0 個 / `(x,0,1)` 型 0 個**。
-/
import Wset

namespace TRIO
namespace L6

open Wset

/-- **行 2 は行 1 を超えない。** `Wset.zle1`（行 2 ≤ 1）より強い。 -/
def r21 (M : TrioSeq) : Prop := ∀ p ∈ M, p.2.2 ≤ p.2.1

/-- 添字で書いた形（`entry` は範囲外で `0` を返すので全射的に書ける）。 -/
theorem r21_entry {M : TrioSeq} (h : r21 M) (j : ℕ) :
    entry M 2 j ≤ entry M 1 j := by
  by_cases hj : j < M.length
  · exact h _ (entry_pair_mem hj)
  · unfold entry
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

/-- 生成元（z 頭打ち対角）は満たす。 -/
theorem r21_diagSeqT (v : ℕ) : r21 (diagSeqT 0 v) := by
  intro p hp
  unfold diagSeqT at hp
  rw [List.mem_map] at hp
  obtain ⟨j, -, rfl⟩ := hp
  dsimp only
  omega

/-- **展開で保たれる。** `oper` は行 1 に非負を足し、行 2 は逐語コピーする。
`Wset.zle1_oper` の写経。 -/
theorem r21_oper {B : TrioSeq} {n : ℕ} (h : r21 B) : r21 (B⟦n⟧) := by
  by_cases hL : B.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]; exact h
  · by_cases hp : hasParent B (srow B (B.length - 1)) (B.length - 1)
    · have hpos : 0 < entry B 0 (B.length - 1) := by
        by_contra hh
        exact no_hasParent_of_row0_zero (by omega) hp
      have hz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
          entry B 2 (B.length - 1) = 0) := by
        rintro ⟨h1, -, -⟩; omega
      rw [oper_gcopies n hL hz hp]
      intro p hp'
      rcases List.mem_append.mp hp' with hmem | hmem
      · exact h p (List.mem_of_mem_take hmem)
      · unfold gcopies at hmem
        rw [List.mem_flatMap] at hmem
        obtain ⟨k, -, hmem2⟩ := hmem
        unfold gcopy at hmem2
        rw [List.mem_map] at hmem2
        obtain ⟨j, hj, rfl⟩ := hmem2
        rw [List.mem_range'] at hj
        have hjlt : j < B.length := by omega
        have := h _ (entry_pair_mem hjlt)
        dsimp only at this ⊢
        omega
    · have hB : B⟦n⟧ = Pred B := by
        by_cases hz : entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0
        · exact oper_eq_pred_of_zero n hL hz
        · exact oper_eq_pred_of_noParent n hL hz hp
      rw [hB]
      unfold Pred
      split
      · exact h
      · exact fun p hp' => h p (List.dropLast_subset _ hp')

/-- **★ `行 2 <= 行 1` は BMS 3 行 `z<2` 標準形の不変量。** -/
theorem r21_ST_TS {M : TrioSeq} (h : ST_TS M) : r21 M := by
  induction h with
  | diag v => exact r21_diagSeqT v
  | oper _ _ ih => exact r21_oper ih

/-- **系: 標準形には「永久孤児」`(x,0,1)` が現れない。**

`Wset.no_hasParent_two_of_row1_zero` が反例に使う形（行 1 = 0 かつ 行 2 > 0）は
`行 2 <= 行 1` と両立しない。`GRAFTALL-PLAN.md §4.5` が `natDom` ガードを
反証した反例 `[(0,0,0),(1,0,1)]` も、これで標準形の外に落ちる。 -/
theorem no_permanent_orphan_of_r21 {M : TrioSeq} (h : r21 M) :
    ∀ p ∈ M, p.2.1 = 0 → p.2.2 = 0 :=
  fun p hp h1 => Nat.le_zero.mp (h1 ▸ h p hp)

theorem no_permanent_orphan_ST_TS {M : TrioSeq} (h : ST_TS M) :
    ∀ p ∈ M, p.2.1 = 0 → p.2.2 = 0 :=
  no_permanent_orphan_of_r21 (r21_ST_TS h)

/-! ### 機構の道具が `r21` を保つか -/

/-- `graft` は行 0 しか動かさないので保つ。 -/
theorem r21_graft {M z : TrioSeq} (hM : r21 M) (hz : r21 z) : r21 (graft M z) := by
  intro p hp
  unfold graft at hp
  rcases List.mem_append.mp hp with hmem | hmem
  · exact hM p (List.dropLast_subset _ hmem)
  · rw [List.mem_map] at hmem
    obtain ⟨q, hq, rfl⟩ := hmem
    exact hz q hq

/-- `Lift1` は行 1 に非負を足すので保つ。 -/
theorem r21_Lift1 {X : TrioSeq} (hX : r21 X) (d : ℕ) : r21 (Lift1 X d) := by
  intro p hp
  unfold Lift1 at hp
  rw [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  have := r21_entry hX i
  dsimp only
  split <;> omega

theorem r21_take {M : TrioSeq} (h : r21 M) (k : ℕ) : r21 (M.take k) :=
  fun p hp => h p (List.take_subset _ _ hp)

theorem r21_drop {M : TrioSeq} (h : r21 M) (k : ℕ) : r21 (M.drop k) :=
  fun p hp => h p (List.drop_subset _ _ hp)

theorem r21_dropLast {M : TrioSeq} (h : r21 M) : r21 M.dropLast :=
  fun p hp => h p (List.dropLast_subset _ hp)

theorem r21_cons {v z : ℕ} {R : TrioSeq} (hz : z ≤ v) (hR : r21 R) :
    r21 (((0, v, z) : ℕ × ℕ × ℕ) :: R) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hz
  · exact hR p hp

end L6
end TRIO

#print axioms TRIO.L6.r21_ST_TS
#print axioms TRIO.L6.no_permanent_orphan_ST_TS
#print axioms TRIO.L6.r21_graft
#print axioms TRIO.L6.r21_Lift1
