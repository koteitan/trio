/-
**展開指数についての単調性**（`ImgClosedT3` を `ImgCofinalT3` に弱めるための道具）。

`ReindexT1_of_block`（`Dbms3.lean:1171`）が `ImgClosedT3` から実際に使うのは
`m := n + 1` **ただ 1 つ**である。だから

    「すべての m で (conv3 A)⟦m⟧ に標準形の逆像がある」（ImgClosedT3）

は要らず、

    「いくらでも大きい m で (conv3 A)⟦m⟧ に標準形の逆像がある」（ImgCofinalT3）

で足りる。差を埋めるのがこの file の 2 つの補題で、どちらも
`oper` の定義（`Trio.lean:98`）が `M.take j0 ++ (List.range n).flatMap g` という
形をしていることだけから出る。`List.range (n+1) = List.range n ++ [n]` なので
`M⟦n+1⟧` は `M⟦n⟧` の**接尾に足しただけ**である。
-/
import Seqlex

namespace TRIO

open Classical

/-- `A ++ (range (n+1)).flatMap g` は `A ++ (range n).flatMap g` の継ぎ足し。 -/
theorem exists_append_flat {α : Type _} (A : List α) (g : ℕ → List α) (n : ℕ) :
    ∃ R, A ++ (List.range (n + 1)).flatMap g = (A ++ (List.range n).flatMap g) ++ R :=
  ⟨g n, by rw [List.range_succ, List.flatMap_append]; simp⟩

/-- `M⟦n+1⟧` は `M⟦n⟧` に何かを継ぎ足したもの。 -/
theorem oper_succ_append (M : TrioSeq) (n : ℕ) : ∃ R, M⟦n + 1⟧ = M⟦n⟧ ++ R := by
  by_cases h1 : M.length - 1 = 0
  · exact ⟨[], by simp [oper, h1]⟩
  by_cases h2 : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0
  · exact ⟨[], by simp [oper, h1, h2]⟩
  by_cases h3 : hasParent M (srow M (M.length - 1)) (M.length - 1)
  · simp only [oper, h1, h2, h3, if_false, if_true, ite_false, ite_true,
      not_true_eq_false, if_neg]
    exact exists_append_flat _ _ _
  · exact ⟨[], by simp [oper, h1, h2, h3]⟩

/-- `j ≤ k` なら `M⟦k⟧` は `M⟦j⟧` に何かを継ぎ足したもの。 -/
theorem oper_le_append {M : TrioSeq} {j k : ℕ} (h : j ≤ k) :
    ∃ R, M⟦k⟧ = M⟦j⟧ ++ R := by
  induction k with
  | zero => exact ⟨[], by simp [Nat.le_zero.mp h]⟩
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · obtain ⟨R, hR⟩ := ih (by omega)
      obtain ⟨S, hS⟩ := oper_succ_append M k
      exact ⟨R ++ S, by rw [hS, hR, List.append_assoc]⟩
    · have : j = k + 1 := by omega
      exact ⟨[], by simp [this]⟩

/-- 展開指数について `seqlex` で単調（等しいか、真に大きい）。 -/
theorem oper_mono_idx {M : TrioSeq} {j k : ℕ} (h : j ≤ k) :
    M⟦j⟧ = M⟦k⟧ ∨ seqlex (M⟦j⟧) (M⟦k⟧) := by
  obtain ⟨R, hR⟩ := oper_le_append (M := M) h
  rcases List.eq_nil_or_concat R with rfl | ⟨R', a, rfl⟩
  · exact Or.inl (by simpa using hR.symm)
  · exact Or.inr (by rw [hR]; exact seqlex_prefix (by simp) _)

end TRIO
