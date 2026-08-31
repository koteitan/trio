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

/-! ## 課題 L48: `(TOW)` の 2 つの還元（R1 の結果を Lean に） -/

@[simp] theorem shTower_nil (e n : ℕ) : shTower ([] : TrioSeq) e n = [] := by
  simp [shTower, shiftr01]

/-- `shiftr01` は行 2 を動かさないので、塔も行 2 ≡ 0 のまま。 -/
theorem shTower_zeroRow2 {Q : TrioSeq} (hz : ∀ p ∈ Q, p.2.2 = 0) (e n : ℕ) :
    ∀ p ∈ shTower Q e n, p.2.2 = 0 := by
  intro p hp
  rw [shTower] at hp
  simp only [List.mem_flatMap, List.mem_range] at hp
  obtain ⟨k, -, hpk⟩ := hp
  rw [shiftr01] at hpk
  simp only [List.mem_map] at hpk
  obtain ⟨q, hq, hqp⟩ := hpk
  rw [← hqp]
  exact hz q hq

/-- `n ≥ 1` の塔は `Q` を接頭辞に持つ（`k = 0` の写しは持ち上げ 0）。 -/
theorem shTower_prefix (Q : TrioSeq) (e : ℕ) :
    ∀ n, 1 ≤ n → ∃ R, shTower Q e n = Q ++ R := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        exact ⟨[], by rw [shTower_one]; simp⟩
      · obtain ⟨R, hR⟩ := ih hn
        exact ⟨R ++ shiftr01 (n * e) 0 Q, by rw [shTower_succ, hR, List.append_assoc]⟩

theorem lev_zero_append {A R : TrioSeq} (hne : A ≠ []) : lev (A ++ R) 0 = lev A 0 := by
  cases A with
  | nil => exact absurd rfl hne
  | cons a t => simp [lev, entry]

/-- `n ≥ 1` の塔の根のレベルは `Q` の根のレベル。 -/
theorem lev_shTower {Q : TrioSeq} (hne : Q ≠ []) (e : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    lev (shTower Q e n) 0 = lev Q 0 := by
  obtain ⟨R, hR⟩ := shTower_prefix Q e n hn
  rw [hR, lev_zero_append hne]

/-- **★ (a) `(TOW)` は行 2 ≡ 0 の `Q` では定理**（課題 L48）。
**側条件（根が最浅）を 1 度も使わない。** -/
theorem shiftTowerClosed_of_zeroRow2 {u e n : ℕ} {Q : TrioSeq}
    (hQ : Q ∈ W u) (hz : ∀ p ∈ Q, p.2.2 = 0) : shTower Q e n ∈ W u := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [shTower_zero]
    exact W_nil u
  by_cases hQne : Q = []
  · subst hQne
    rw [shTower_nil]
    exact W_nil u
  rw [mem_Wself_iff]
  refine ⟨zeroRow2_mem_Wself (shTower_zeroRow2 hz e n), ?_⟩
  rw [lev_shTower hQne e hn]
  exact lev_root_le_of_mem_W hQ hQne

/-- **★ (b) 一般の `(TOW)` は段の添字 `u` の要らない文に還元できる**（課題 L48）。

`Q ∈ W u` から `lev Q 0 ≤ u` が出て、`n ≥ 1` なら結論側の `lev 0` も同じなので
`u` が消える。 -/
theorem shiftTowerClosed_iff_wself :
    ShiftTowerClosed ↔
      ∀ (e n : ℕ) (Q : TrioSeq), Q ∈ Wself → (∀ p ∈ Q, entry Q 0 0 ≤ p.1) →
        shTower Q e n ∈ Wself := by
  constructor
  · intro h e n Q hQ hs
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [shTower_zero]
      exact show ([] : TrioSeq) ∈ W (lev ([] : TrioSeq) 0) from W_nil _
    by_cases hQne : Q = []
    · subst hQne
      rw [shTower_nil]
      exact show ([] : TrioSeq) ∈ W (lev ([] : TrioSeq) 0) from W_nil _
    have h9 := h (lev Q 0) e n Q hQ hs
    show shTower Q e n ∈ W (lev (shTower Q e n) 0)
    rw [lev_shTower hQne e hn]
    exact h9
  · intro h u e n Q hQ hs
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [shTower_zero]
      exact W_nil u
    by_cases hQne : Q = []
    · subst hQne
      rw [shTower_nil]
      exact W_nil u
    obtain ⟨hself, hlev⟩ := (mem_Wself_iff u Q).mp hQ
    rw [mem_Wself_iff]
    refine ⟨h e n Q hself hs, ?_⟩
    rw [lev_shTower hQne e hn]
    exact hlev

/-- **★ (c) `(TOW)` の `e = 0` は既に定理**（`Wset.W_flatMap_copies`、課題 L48）。

`shTower Q 0 n = (range n).flatMap (fun _ => Q)` なので、持ち上げの無い塔は
`W_add`（`rsum`）だけで積める。**`rsum` が通るのは写しが上昇しないから**である。

⟹ **`(TOW)` の難しさは丸ごと `e ≥ 1`（上昇）にある。** -/
theorem shiftTowerClosed_e_zero {u n : ℕ} {Q : TrioSeq} (hQ : Q ∈ W u)
    (hQr : ∀ p ∈ Q, entry Q 0 0 ≤ p.1) : shTower Q 0 n ∈ W u := by
  have h : shTower Q 0 n = (List.range n).flatMap fun _ => Q := by
    unfold shTower
    simp
  rw [h]
  exact W_flatMap_copies hQ hQr n

/-! ## 課題 L50: `diagSeqT 0 v ∈ Wself` は**定理そのもの**（同値）

`ST_TS` は**対角と `oper` だけ**で生成される（`Trio.lean`）:

    inductive ST_TS : TrioSeq → Prop where
      | diag (v : ℕ) : ST_TS (diagSeqT 0 v)
      | oper {M n} : ST_TS M → 1 ≤ n → ST_TS (M⟦n⟧)

そして `oper_closed`（`Wset.lean:2103`、**証明ずみ**）は `W u` を `oper` で閉じる
（段は上がらない）。⟹ **対角が全部 `Wself` に入れば、標準形は全部 `W` に入る。** -/

/-- **★ 対角が `Wself` なら、すべての標準形にある段が付く**（課題 L50）。 -/
theorem exists_stage_of_ST_TS (h : ∀ v : ℕ, diagSeqT 0 v ∈ Wself)
    {M : TrioSeq} (hM : ST_TS M) : ∃ u, M ∈ W u := by
  induction hM with
  | diag v => exact ⟨lev (diagSeqT 0 v) 0, h v⟩
  | oper hM' hn ih =>
      obtain ⟨u, hu⟩ := ih
      exact ⟨u, oper_closed hu hn⟩

/-- **★★ `diagSeqT 0 v ∈ Wself`（∀v）⟹ すべての標準形が `Wself`**（課題 L50）。

⟹ **`diagSeqT 0 v ∈ Wself` は 3 行 (z<2) の停止性と同値**である
（逆向きは `ST_TS.diag` から自明）。**最小形ではあるが、近道ではない。** -/
theorem mem_Wself_of_diag (h : ∀ v : ℕ, diagSeqT 0 v ∈ Wself)
    {M : TrioSeq} (hM : ST_TS M) (hne : M ≠ []) : M ∈ Wself := by
  obtain ⟨u, hu⟩ := exists_stage_of_ST_TS h hM
  exact W_root_stage hu hne

end L47
end TRIO
