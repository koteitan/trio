/-
**トリオ数列の記法 `p_{a1,a2}(b)+c` と翻訳 `translate`。**

添字は自然数の**対** (a1, a2) — 行 1 と行 2 のラベルの組であり、文字であって
順序数ではない（BMOCF と同じ設計）。順序 `<o` は添字対優先の辞書式:
a1 → a2 → 引数 → 後続和。BMS の列比較（行 0 → 行 1 → 行 2）の項側の対応物。

2 行の形式化 ~/proofs/lean-yapss/git/lean/Term.lean と同じ設計。
-/
import Trio
import Mathlib.Data.List.TakeWhile

namespace TRIO

inductive Three : Type where
  | Z : Three
  | P : ℕ → ℕ → Three → Three → Three
  deriving DecidableEq, Repr, Inhabited

namespace Three

/-! ## 添字対優先の辞書式順序 -/

/-- The subscript-pair-first lexicographic order on `Three`. -/
def olt : Three → Three → Prop
  | Z, Z => False
  | Z, P _ _ _ _ => True
  | P _ _ _ _, Z => False
  | P a1 a2 b c, P e1 e2 f g =>
      a1 < e1 ∨ (a1 = e1 ∧ a2 < e2) ∨ (a1 = e1 ∧ a2 = e2 ∧ olt b f)
        ∨ (a1 = e1 ∧ a2 = e2 ∧ b = f ∧ olt c g)

@[inherit_doc] infix:50 " <o " => olt

/-- `x ≤o y` iff `x <o y ∨ x = y`. -/
def ole (x y : Three) : Prop := x <o y ∨ x = y

@[inherit_doc] infix:50 " ≤o " => ole

@[simp] theorem olt_Z_Z : ¬ (Z <o Z) := fun h => h

@[simp] theorem olt_Z_P (a1 a2 : ℕ) (b c : Three) : Z <o P a1 a2 b c := trivial

@[simp] theorem olt_P_Z (a1 a2 : ℕ) (b c : Three) : ¬ (P a1 a2 b c <o Z) :=
  fun h => h

@[simp] theorem olt_P_P {a1 a2 e1 e2 : ℕ} {b c f g : Three} :
    P a1 a2 b c <o P e1 e2 f g ↔
      a1 < e1 ∨ (a1 = e1 ∧ a2 < e2) ∨ (a1 = e1 ∧ a2 = e2 ∧ b <o f)
        ∨ (a1 = e1 ∧ a2 = e2 ∧ b = f ∧ c <o g) := Iff.rfl

theorem olt_irrefl (x : Three) : ¬ x <o x := by
  induction x with
  | Z => simp
  | P a1 a2 b c ihb ihc => simp [ihb, ihc]

@[simp] theorem not_olt_Z (x : Three) : ¬ x <o Z := by
  cases x <;> simp

theorem olt_trans {x y z : Three} (hxy : x <o y) (hyz : y <o z) : x <o z := by
  induction z generalizing x y with
  | Z => exact absurd hyz (not_olt_Z y)
  | P c1 c2 c3 c4 ih3 ih4 =>
    cases x with
    | Z => simp
    | P a1 a2 a3 a4 =>
      obtain ⟨e1, e2, e3, e4, rfl⟩ : ∃ e1 e2 e3 e4, y = P e1 e2 e3 e4 := by
        cases y with
        | Z => exact absurd hxy (not_olt_Z _)
        | P e1 e2 e3 e4 => exact ⟨e1, e2, e3, e4, rfl⟩
      rw [olt_P_P] at hxy hyz ⊢
      rcases hxy with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, h1⟩ | ⟨rfl, rfl, rfl, h1⟩ <;>
        rcases hyz with h2 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h2⟩ | ⟨rfl, rfl, rfl, h2⟩
      · exact Or.inl (Nat.lt_trans h1 h2)
      · exact Or.inl h1
      · exact Or.inl h1
      · exact Or.inl h1
      · exact Or.inl h2
      · exact Or.inr (Or.inl ⟨rfl, Nat.lt_trans h1 h2⟩)
      · exact Or.inr (Or.inl ⟨rfl, h1⟩)
      · exact Or.inr (Or.inl ⟨rfl, h1⟩)
      · exact Or.inl h2
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ih3 h1 h2⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1⟩))
      · exact Or.inl h2
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, ih4 h1 h2⟩))

theorem olt_ole_trans {x y z : Three} (hxy : x <o y) (hyz : y ≤o z) : x <o z := by
  rcases hyz with h | rfl
  · exact olt_trans hxy h
  · exact hxy

/-- Strict monotonicity of a principal term in its argument. -/
theorem olt_P_b {b1 b2 : Three} (a1 a2 : ℕ) (c1 c2 : Three) (h : b1 <o b2) :
    P a1 a2 b1 c1 <o P a1 a2 b2 c2 := by simp [h]

/-- Strict monotonicity of a principal term in its tail. -/
theorem olt_P_c {c1 c2 : Three} (a1 a2 : ℕ) (b : Three) (h : c1 <o c2) :
    P a1 a2 b c1 <o P a1 a2 b c2 := by simp [h]

/-- Leading subscript pair of a term. -/
def lead : Three → ℕ × ℕ
  | Z => (0, 0)
  | P a1 a2 _ _ => (a1, a2)

@[simp] theorem lead_Z : lead Z = (0, 0) := rfl
@[simp] theorem lead_P (a1 a2 : ℕ) (b c : Three) :
    lead (P a1 a2 b c) = (a1, a2) := rfl

end Three

/-! ## 翻訳 `translate : TrioSeq → Three`

行 0 を森の深さ優先表記として読む: 先頭の列 `(x, y, z)` は主要項
`p_{y,z}(…)` になり、引数は行 0 の値が `> x` である極大な後続ブロック
（子孫）の翻訳、後続和は残り（兄弟以降）の翻訳。 -/

open Three in
def translate : TrioSeq → Three
  | [] => Z
  | p :: rest =>
    P p.2.1 p.2.2 (translate (rest.takeWhile fun q => p.1 < q.1))
                  (translate (rest.dropWhile fun q => p.1 < q.1))
  termination_by M => M.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

open Three

theorem lead_translate (M : TrioSeq) :
    lead (translate M) = match M with | [] => (0, 0) | p :: _ => (p.2.1, p.2.2) := by
  cases M <;> simp [translate]

end TRIO
