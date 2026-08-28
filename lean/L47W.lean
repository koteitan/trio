/-
課題 L47: `W` の**除去則**（R1 の (W1) / (W3)）。

`W u` の所属を**壊す**向きの補題が Lean に無かった（`A1_intro` は作る向きだけ）。
`A1 u : Aset W u (W u) = W u` を逆向きに使えば 1 行で出る。

## (W3) が本命な理由（R1-NOTES）

`Aop` の節 3 は `∀ z ∈ W m, based z → graft M z ∈ X` という**無限量化**なので、
帰納の仮定として使えなかった。`z := []` を代入すると

    [] ∈ W m（節 1）／ based []（`based_nil`）／ graft M [] = M.dropLast（`graft_nil`）

なので **`M.dropLast ∈ X` の 1 本に落ちる**。

## ⚠ ただし `WSnoc` の証明には**そのままでは届かない**（課題 L47 の判定）

`WSnoc` の目標 `C ++ [p] ∈ W u` は、`domT` が末尾の孤児を要求するので
**節 2 一本**に絞れる（下の `wsnoc_clause2` がその内容）。ところが

    (C ++ [p])⟦n⟧ = C ++ （`p` の親から後ろの `C` の接尾辞のコピー）^n

なので、**`WSnoc` は「親から後ろの接尾辞を繰り返しても `W u` から出ない」**、
すなわち**置換閉包の特別な場合**である。`oper_append_gen` の局所化は
`2 ≤ |P|` を要求するので `P = [p]` には当たらない。
(W3) の `dropLast` は 1 列しか落とさないが `C ++ [p]` は
`C.dropLast ++ [C.getLast] ++ [p]` で 2 列足すので、長さの帰納は**循環する**。
-/
import Wtower2

namespace TRIO
namespace L47

open Wset

/-- **(W3) `W` の除去則**（R1-NOTES の (W3)。Lean に無かった）。

`M ∈ W u` かつ `2 ≤ |M|` なら、節 1 は潰れるので節 2 か節 3。
節 3 のときは `z := []` を代入して `M.dropLast ∈ W u` を得る。 -/
theorem W3 {u : ℕ} {M : TrioSeq} (hM : M ∈ W u) (hlen : 2 ≤ M.length) :
    (∀ n : ℕ, 1 ≤ n → M⟦n⟧ ∈ W u) ∨ M.dropLast ∈ W u := by
  have h : Aop W u (W u) M := by
    have : M ∈ Aset W u (W u) := by rw [A1 u]; exact hM
    exact this
  rcases h with ⟨h1, -⟩ | h2 | ⟨m, -, -, hgr⟩
  · omega
  · exact Or.inl h2
  · have h9 := hgr [] (W_nil m) based_nil
    rw [graft_nil] at h9
    exact Or.inr h9

/-- **(W2) 節 3 ならば `M.dropLast ∈ X`**（`W3` の中で使っている形を単独で）。 -/
theorem W2 {u : ℕ} {M : TrioSeq} {X : Set TrioSeq}
    (h : ∃ m : ℕ, m < u ∧ domT M m ∧ ∀ z ∈ W m, based z → graft M z ∈ X) :
    M.dropLast ∈ X := by
  obtain ⟨m, -, -, hgr⟩ := h
  have h9 := hgr [] (W_nil m) based_nil
  rwa [graft_nil] at h9

/-- **`W` の展開（除去の向き）**。`A1_intro` の逆。 -/
theorem W_elim {u : ℕ} {M : TrioSeq} (hM : M ∈ W u) : Aop W u (W u) M := by
  have : M ∈ Aset W u (W u) := by rw [A1 u]; exact hM
  exact this

/-- **★ `WSnoc` は「節 2 一本」に絞れる**（課題 L47 の (2) の答え）。

`domT M m` の第 2 連言は `¬ hasParent M (srow M (|M|-1)) (|M|-1)` で、
`WSnoc` の仮定はまさにその否定（`|C ++ [p]| - 1 = |C|`）。だから節 3 は使えない。
`C ≠ []` より `2 ≤ |C ++ [p]|` なので節 1 も使えない。 -/
theorem wsnoc_clause2 {u : ℕ} {C : TrioSeq} {p : ℕ × ℕ × ℕ} (hCne : C ≠ [])
    (hpar : hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length)
    (h : ∀ n : ℕ, 1 ≤ n → (C ++ [p])⟦n⟧ ∈ W u) : C ++ [p] ∈ W u := by
  exact A1_intro (Or.inr (Or.inl h))

/-- 逆に、`C ++ [p] ∈ W u` なら**必ず**節 2 が成り立つ（節 1 と節 3 が塞がるので）。
⟹ **`WSnoc` は節 2 と同値**。 -/
theorem wsnoc_clause2_iff {u : ℕ} {C : TrioSeq} {p : ℕ × ℕ × ℕ} (hCne : C ≠ [])
    (hpar : hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length) :
    C ++ [p] ∈ W u ↔ ∀ n : ℕ, 1 ≤ n → (C ++ [p])⟦n⟧ ∈ W u := by
  refine ⟨fun hM => ?_, wsnoc_clause2 hCne hpar⟩
  have hlen : (C ++ [p]).length - 1 = C.length := by
    rw [List.length_append]
    simp
  rcases W_elim hM with ⟨h1, -⟩ | h2 | ⟨m, -, hdom, -⟩
  · exfalso
    rw [List.length_append, List.length_singleton] at h1
    exact hCne (List.eq_nil_of_length_eq_zero (by omega))
  · exact h2
  · exact absurd (hlen ▸ hpar) (hlen ▸ hdom.2)

end L47
end TRIO
