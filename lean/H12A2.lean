/-
H12A2.lean: `L105.MTowerClosedRow2` を「`Q` の側で `A2'` を回す」形に分解する。

`Wset.A2'`（`Wset.lean:251`）を

    Y := { Q | ∀ d e n, （根が狭義最浅）→ （行 2 に非零）→ mTower Q d e n ∈ W u }

に当てる。`Aop` の 3 節のうち

    節 1（`|M| <= 1 ∧ lev M 0 = 0`）… **空虚に真**（`lev M 0 = 0` は `entry M 2 0 = 0` を含み、
      `|M| <= 1` なので `Y` の前提「行 2 に非零がある」が偽になる）
    節 3（graft）… `|M| >= 2` なら `Wchar.aop_clause3_to_clause2` で節 2 に吸収。
      **`|M| = 1` は吸収できない**（あの補題は `2 <= M.length` を要求する）ので別に残る
    節 2（展開）… 仮定に残す

⚠ team-lead の読み「節 1 は空虚」は**正しかった**（下の `clause1_vacuous` で証明した）。
⚠ ただし **`|M| = 1` の節 3 は節 1 と重ならない**（節 1 は `lev M 0 = 0`、
  節 3 は `domT M m` すなわち `lev M 0 = m+1 >= 1` を要求するので**両立しない**）。
  ⟹ **仮定は 2 本必要**: `hcl2`（節 2）と `hone`（`|M| = 1` の節 3）。
-/
import L105Cap

namespace TRIO
namespace H12A2

open Wset
open L105

/-- `A2'` を回す先の集合。`u` は外で固定する。 -/
def Y (u : ℕ) : Set TrioSeq :=
  {Q | ∀ d e n : ℕ,
      (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
      (∃ p ∈ Q, 0 < p.2.2) →
      mTower Q d e n ∈ W u}

/-- **★ 節 1 は空虚に真**（team-lead の読みの検証）。
`lev M 0 = 0` は `entry M 2 0 = 0` を含み、`|M| <= 1` なので
`M` の要素は高々 1 つ、それは第 0 列。⟹ 行 2 に非零は無い。 -/
theorem clause1_vacuous {u : ℕ} {M : TrioSeq}
    (h : M.length ≤ 1 ∧ lev M 0 = 0) : M ∈ Y u := by
  intro d e n _ hz2
  exfalso
  obtain ⟨hlen, hlev⟩ := h
  obtain ⟨p, hp, hppos⟩ := hz2
  -- `M` は長さ <= 1 で `p ∈ M` なので `M = [p]`
  have hM1 : M.length = 1 := by
    rcases Nat.eq_zero_or_pos M.length with h0 | h1
    · exact absurd (List.eq_nil_of_length_eq_zero h0 ▸ hp) (by simp)
    · omega
  have hp0 : M.getD 0 ((0, 0, 0) : ℕ × ℕ × ℕ) = p := by
    match M, hM1 with
    | [q], _ =>
        have : p = q := by simpa using hp
        simp [this]
  have h2 : entry M 2 0 = p.2.2 := by
    show (M.getD 0 ((0, 0, 0) : ℕ × ℕ × ℕ)).2.2 = p.2.2
    rw [hp0]
  unfold lev at hlev
  omega

/-- **節 3 は `|M| >= 2` では節 2 に吸収される**（`Wchar.aop_clause3_to_clause2`）。 -/
theorem clause3_to_clause2 {u : ℕ} {M : TrioSeq} (hM2 : 2 ≤ M.length)
    (h : ∃ m : ℕ, m < u ∧ domT M m ∧ ∀ z ∈ W m, based z → graft M z ∈ Y u) :
    ∀ n, 1 ≤ n → M⟦n⟧ ∈ Y u := by
  obtain ⟨m, -, hd, hop⟩ := h
  exact aop_clause3_to_clause2 hM2 hd hop

/-- **★★ 骨組み**: `Aop` の 3 節を落として、残るのは 2 本の仮定だけ。

    `hcl2` … 節 2（展開）から目標を出す
    `hone` … `|M| = 1` の節 3（節 1 と両立しないので別に要る） -/
theorem mTowerClosedRow2_of_clause2
    (hcl2 : ∀ (u : ℕ) (M : TrioSeq),
      (∀ n, 1 ≤ n → M⟦n⟧ ∈ Y u) → M ∈ Y u)
    (hone : ∀ (u : ℕ) (M : TrioSeq), M.length = 1 →
      (∃ m : ℕ, m < u ∧ domT M m) → M ∈ Y u) :
    MTowerClosedRow2 := by
  intro u d e n Q hQ hs hz2
  have hsub : W u ⊆ Y u := by
    refine A2' ?_
    intro M hA
    rcases hA with h1 | h2 | h3
    · exact clause1_vacuous h1
    · exact hcl2 u M h2
    · rcases Nat.lt_or_ge M.length 2 with hsm | hbig
      · -- `|M| <= 1`: 節 3 は `domT` を要求する
        rcases Nat.eq_zero_or_pos M.length with h0 | hpos
        · -- `M = []` は `domT` を持てない
          exfalso
          obtain ⟨m, -, hd, -⟩ := h3
          rw [List.eq_nil_of_length_eq_zero h0] at hd
          exact not_domT_nil m hd
        · obtain ⟨m, hm, hd, -⟩ := h3
          exact hone u M (by omega) ⟨m, hm, hd⟩
      · exact hcl2 u M (clause3_to_clause2 hbig h3)
  exact hsub hQ d e n hs hz2

/-! ## `hone` を落とす —— `|M| = 1` では塔の行 2 が定数なので全部孤児 -/

theorem constRow2_shiftr01 {Q : TrioSeq} {z d0 d1 : ℕ} (h : ∀ p ∈ Q, p.2.2 = z) :
    ∀ p ∈ shiftr01 d0 d1 Q, p.2.2 = z := by
  intro p hp
  unfold shiftr01 at hp
  rw [List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact h q hq

theorem constRow2_Lift1 {X : TrioSeq} {z d : ℕ} (h : ∀ p ∈ X, p.2.2 = z) :
    ∀ p ∈ Lift1 X d, p.2.2 = z := by
  intro p hp
  unfold Lift1 at hp
  rw [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  rw [List.mem_range] at hi
  show entry X 2 i = z
  exact h _ (entry_pair_mem hi)

theorem constRow2_mTower {Q : TrioSeq} {z : ℕ} (h : ∀ p ∈ Q, p.2.2 = z) (d e n : ℕ) :
    ∀ p ∈ mTower Q d e n, p.2.2 = z := by
  intro p hp
  unfold mTower at hp
  rw [List.mem_flatMap] at hp
  obtain ⟨k, -, hk⟩ := hp
  exact constRow2_Lift1 (constRow2_shiftr01 h) p hk

/-- 定数の行 2 は `entry` の言葉でも読める。 -/
theorem entry2_of_constRow2 {X : TrioSeq} {z j : ℕ} (h : ∀ p ∈ X, p.2.2 = z)
    (hj : j < X.length) : entry X 2 j = z :=
  h _ (entry_pair_mem hj)

/-- **★ `hone` は無料**: `|M| = 1` で行 2 に非零があれば、塔の行 2 は定数で正
⟹ どの列も行 2 の親を持たず `oper` は `Pred` ⟹ `n` の帰納で落ちる。 -/
theorem hone_holds : ∀ (u : ℕ) (M : TrioSeq), M.length = 1 →
    (∃ m : ℕ, m < u ∧ domT M m) → M ∈ Y u := by
  rintro u M hM1 ⟨m, hm, hd⟩ d e n hs hz2
  -- `M` は単元。行 2 の値を `z` と置く
  set z : ℕ := entry M 2 0 with hzdef
  have hMne : M ≠ [] := by
    intro hc; rw [hc] at hM1; simp at hM1
  have hconstM : ∀ p ∈ M, p.2.2 = z := by
    intro p hp
    match M, hM1 with
    | [q], _ =>
        have : p = q := by simpa using hp
        rw [this, hzdef]
        show q.2.2 = (([q] : TrioSeq).getD 0 ((0,0,0) : ℕ × ℕ × ℕ)).2.2
        simp
  -- 行 2 に非零がある ⟹ `z > 0`
  have hzpos : 0 < z := by
    obtain ⟨p, hp, hppos⟩ := hz2
    rw [hconstM p hp] at hppos
    exact hppos
  -- `M ∈ W u`（`domT` の `lev = m+1 <= u`）
  have hMW : M ∈ W u := by
    have hlev : lev M 0 = m + 1 := by
      have := hd.1
      rwa [hM1] at this
    have hle : lev M 0 ≤ u := by omega
    match M, hM1 with
    | [q], _ =>
        have : q = (q.1, q.2.1, q.2.2) := rfl
        rw [this]
        refine mem_iff_lev_le.mpr ?_
        have : lev [q] 0 = 2 * q.2.1 + q.2.2 := rfl
        omega
  -- `n` の帰納
  clear hz2 hs
  induction n with
  | zero => rw [mTower_zero]; exact W_nil u
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · rw [mTower_one]; exact hMW
      · -- 長さ >= 2 なので `oper` は `Pred`
        have hlen : (mTower M d e (n + 1)).length = n + 1 := by
          rw [mTower_length, hM1]; omega
        have hconstT : ∀ p ∈ mTower M d e (n + 1), p.2.2 = z :=
          constRow2_mTower hconstM d e (n + 1)
        have hlast : entry (mTower M d e (n + 1)) 2
            ((mTower M d e (n + 1)).length - 1) = z :=
          entry2_of_constRow2 hconstT (by omega)
        have hsr : srow (mTower M d e (n + 1))
            ((mTower M d e (n + 1)).length - 1) = 2 := by
          unfold srow
          rw [if_pos (by rw [hlast]; exact hzpos)]
        have hnp : ¬ hasParent (mTower M d e (n + 1))
            (srow (mTower M d e (n + 1)) ((mTower M d e (n + 1)).length - 1))
            ((mTower M d e (n + 1)).length - 1) := by
          rw [hsr]
          exact not_hasParent_two_of_row2_const hconstT (by omega)
        refine mem_of_oper_mem (fun k hk => ?_)
        rw [oper_eq_pred_of_noParent k (by omega)
          (by intro hc; rw [hlast] at hc; omega) hnp]
        unfold Pred
        rw [if_neg (by omega), mTower_dropLast_of_single hM1]
        exact ih

/-- **★★★★★ 目標の形**: 仮定は **`hcl2`（節 2）1 本**。
節 1 は空虚（`clause1_vacuous`）、節 3 は `|M| >= 2` で節 2 に吸収
（`clause3_to_clause2`）、`|M| = 1` の節 3 は無料（`hone_holds`）、
`|M| = 0` の節 3 は `not_domT_nil` で潰れる。 -/
theorem mTowerClosedRow2_of_clause2'
    (hcl2 : ∀ (u : ℕ) (M : TrioSeq),
      (∀ n, 1 ≤ n → M⟦n⟧ ∈ Y u) → M ∈ Y u) :
    MTowerClosedRow2 :=
  mTowerClosedRow2_of_clause2 hcl2 hone_holds

/-! ## `d = 0` の枝は無料（`e = 0` 側の退化）

`mTower Q 0 0 n` は `Q` の**同一コピー** `n` 個の連結なので、
`Wset.W_flatMap_copies`（`:2552`、既存）がそのまま効く。
（`d = 0` は塔の場面では起きない —— `d = entry R 0 (|R|-1)` で `argOK R` から `d >= 1` ——
　が、`MTowerClosedRow2` は `∀ d` なので命題としては入る。） -/

theorem shiftr01_zero_zero (Q : TrioSeq) : shiftr01 0 0 Q = Q := by
  unfold shiftr01
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  simp

theorem mTower_zero_zero (Q : TrioSeq) (n : ℕ) :
    mTower Q 0 0 n = (List.range n).flatMap fun _ => Q := by
  unfold mTower
  refine List.flatMap_congr ?_
  intro k _
  simp only [Nat.zero_mul, Lift1_zero, shiftr01_zero_zero]

/-- **★ `d = 0` の枝は無料**（同一コピーの連結）。 -/
theorem mTower_d0_mem {u : ℕ} {Q : TrioSeq} (hQ : Q ∈ W u)
    (hs : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) (n : ℕ) :
    mTower Q 0 0 n ∈ W u := by
  rw [mTower_zero_zero]
  refine W_flatMap_copies hQ ?_ n
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp
  -- `Wtower2.shiftTowerClosedS_of_closed` と同じ書き換え
  have hval : entry Q 0 j = Q[j].1 := by
    unfold entry
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · exact le_of_eq hval
  · exact le_of_lt (by rw [← hval]; exact hs j hjpos hj)

end H12A2
end TRIO
