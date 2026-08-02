/-
Cofinality.lean: トリオ数列の Bachmann 共終性（基本列は標準形の中で共終）
への還元機構。

目標: `SeqlexCofinality : seqlex N M → ∃ n ≥ 1, sle N (M⟦n⟧)`（標準形上）。
`olt_ST_iff_seqlex` により translate 側の共終性
`tr N <o tr M → ∃ n, tr N ≤o tr (M⟦n⟧)` が従う（probe: 15038 対 0 失敗、
crux レベル 28010 対 0 失敗）。この章は yapss Cofinality.lean の 3 行版。
-/
import Invariant

namespace TRIO

open Three
open Classical

/-! ## Part 0 — `seqlex` の配管 -/

theorem collt_trans {p q r : ℕ × ℕ × ℕ} (h1 : collt p q) (h2 : collt q r) :
    collt p r := by
  unfold collt at *
  omega

/-- `seqlex` is transitive. -/
theorem seqlex_trans : ∀ {A B C : TrioSeq}, seqlex A B → seqlex B C →
    seqlex A C := by
  intro A
  induction A with
  | nil =>
    intro B C _ h2
    rcases C with _ | ⟨c, C'⟩
    · rcases B with _ | ⟨b, B'⟩
      · exact absurd h2 (by simp)
      · exact absurd h2 (by simp)
    · simp
  | cons a A' ih =>
    intro B C h1 h2
    rcases B with _ | ⟨b, B'⟩
    · exact absurd h1 (by simp)
    rcases C with _ | ⟨c, C'⟩
    · exact absurd h2 (by simp)
    rw [seqlex_cons_cons] at h1 h2 ⊢
    rcases h1 with p1 | ⟨rfl, s1⟩ <;> rcases h2 with p2 | ⟨rfl, s2⟩
    · exact Or.inl (collt_trans p1 p2)
    · exact Or.inl p1
    · exact Or.inl p2
    · exact Or.inr ⟨rfl, ih s1 s2⟩

/-- `≤` version of `seqlex`. -/
def sle (M N : TrioSeq) : Prop := M = N ∨ seqlex M N

theorem sle_refl (M : TrioSeq) : sle M M := Or.inl rfl

theorem seqlex_sle_trans {A B C : TrioSeq} (h1 : seqlex A B) (h2 : sle B C) :
    seqlex A C := by
  rcases h2 with rfl | h2
  · exact h1
  · exact seqlex_trans h1 h2

theorem sle_trans {A B C : TrioSeq} (h1 : sle A B) (h2 : sle B C) :
    sle A C := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (seqlex_sle_trans h1 h2)

/-- `seqlex` is monotone under extending the *larger* side on the right. -/
theorem seqlex_append_mono : ∀ {A B : TrioSeq}, seqlex A B → ∀ (C : TrioSeq),
    seqlex A (B ++ C) := by
  intro A
  induction A with
  | nil =>
    intro B h C
    rcases B with _ | ⟨b, B'⟩
    · exact absurd h (by simp)
    · simp
  | cons a A' ih =>
    intro B h C
    rcases B with _ | ⟨b, B'⟩
    · exact absurd h (by simp)
    · rw [seqlex_cons_cons] at h
      rcases h with hp | ⟨rfl, hs⟩
      · exact Or.inl hp
      · exact Or.inr ⟨rfl, ih hs C⟩

/-- `sle` version of `seqlex_append_mono`. -/
theorem sle_append_mono {A B : TrioSeq} (h : sle A B) (C : TrioSeq) :
    sle A (B ++ C) := by
  rcases h with rfl | h
  · rcases C with _ | ⟨c, C'⟩
    · exact Or.inl (by simp)
    · exact Or.inr (seqlex_prefix (by simp) A)
  · exact Or.inr (seqlex_append_mono h C)

/-- **Snoc case analysis.**  A sequence below `D ++ [lp]` either stays `≤ D`,
or extends `D` by a first column strictly below `lp`. -/
theorem seqlex_snoc_cases : ∀ {D : TrioSeq} {lp : ℕ × ℕ × ℕ} {N : TrioSeq},
    seqlex N (D ++ [lp]) →
    sle N D ∨ ∃ q S, N = D ++ q :: S ∧ collt q lp := by
  intro D
  induction D with
  | nil =>
    intro lp N h
    rcases N with _ | ⟨q, S⟩
    · exact Or.inl (sle_refl _)
    · rw [List.nil_append, seqlex_cons_cons] at h
      rcases h with h | ⟨rfl, h⟩
      · exact Or.inr ⟨q, S, rfl, h⟩
      · exact absurd h (by cases S <;> simp)
  | cons d D' ih =>
    intro lp N h
    rcases N with _ | ⟨q, S⟩
    · exact Or.inl (Or.inr (by simp))
    rw [List.cons_append, seqlex_cons_cons] at h
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl (Or.inr (Or.inl h))
    · rcases ih h with hle | ⟨q', S', rfl, hq'⟩
      · refine Or.inl ?_
        rcases hle with rfl | hle
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨rfl, hle⟩)
      · exact Or.inr ⟨q', S', by simp, hq'⟩

/-! ## Part 1 — 共終性の `seqlex` 形への還元 -/

/-- The `seqlex` form of trio Bachmann cofinality. -/
def SeqlexCofinality : Prop :=
  ∀ {M N : TrioSeq}, ST_TS M → ST_TS N → seqlex N M →
    ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧)

theorem ts_cofinality_of_seqlex (H : SeqlexCofinality)
    {M N : TrioSeq} (hM : ST_TS M) (hN : ST_TS N)
    (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) := by
  have hne : N ≠ M := by
    rintro rfl
    exact olt_irrefl _ h
  have hsl : seqlex N M := (olt_ST_iff_seqlex hN hM hne).1 h
  obtain ⟨n, hn, hres⟩ := H hM hN hsl
  refine ⟨n, hn, ?_⟩
  rcases hres with rfl | hlt
  · exact Or.inr rfl
  · by_cases he : N = M⟦n⟧
    · exact Or.inr (by rw [he])
    · exact Or.inl ((olt_ST_iff_seqlex hN (ST_TS.oper hM hn) he).2 hlt)

/-! ## Part 2 — `oper` の退化枝 -/

/-- **Branch `self`**: `M` has length `≤ 1`, so `M⟦n⟧ = M`. -/
theorem seqlex_cof_short {M N : TrioSeq} (hL : M.length - 1 = 0)
    (h : seqlex N M) : ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) :=
  ⟨1, le_rfl, by rw [oper_eq_self_of_short 1 hL]; exact Or.inr h⟩

theorem dropLast_snoc_getD {M : TrioSeq} (hne : M ≠ []) :
    M.dropLast ++ [M.getD (M.length - 1) (0, 0, 0)] = M := by
  conv_rhs => rw [← List.dropLast_append_getLast hne]
  congr 1
  rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by
      have := List.length_pos_iff.2 hne
      omega)]
  rfl

/-- **Branch `zero`**: the last column is `(0,0,0)`, so `M⟦n⟧ = M.dropLast`.
Nothing squeezes strictly between `M.dropLast` and `M` because `(0,0,0)` is
the `collt`-minimum. -/
theorem seqlex_cof_zero {M N : TrioSeq} (hL : 1 < M.length)
    (hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0)
    (h : seqlex N M) : ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) := by
  have hne : M ≠ [] := by
    intro he
    rw [he] at hL
    simp at hL
  have hlpz : M.getD (M.length - 1) (0, 0, 0) = (0, 0, 0) :=
    Prod.ext hz.1 (Prod.ext hz.2.1 hz.2.2)
  have hMsplit : M.dropLast ++ [M.getD (M.length - 1) (0, 0, 0)] = M :=
    dropLast_snoc_getD hne
  have hop : M⟦1⟧ = M.dropLast := by
    rw [oper_eq_pred_of_zero 1 (by omega) hz]
    unfold Pred
    rw [if_neg (by omega)]
  refine ⟨1, le_rfl, ?_⟩
  rw [hop]
  rcases seqlex_snoc_cases (D := M.dropLast) (lp := M.getD (M.length - 1) (0, 0, 0))
      (N := N) (by rw [hMsplit]; exact h) with hle | ⟨q, S, -, hq⟩
  · exact hle
  · rw [hlpz] at hq
    simp [collt] at hq

/-! ## Part 3 — bad 枝の crux への還元 -/

/-- **The bad-branch crux** (to be discharged by the copy-domination
machinery): a standard `N` extending the good prefix `M.dropLast` with a
column strictly below the dropped one is caught by some expansion. -/
def TrioBadCrux : Prop :=
  ∀ {M N : TrioSeq} {q : ℕ × ℕ × ℕ} {S : TrioSeq},
    ST_TS M → ST_TS N → 1 < M.length →
    ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) →
    N = M.dropLast ++ q :: S →
    collt q (M.getD (M.length - 1) (0, 0, 0)) →
    ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧)

/-- The good prefix plus the zeroth copy is exactly `M.dropLast`. -/
theorem take_gcopy_zero {M : TrioSeq} (hL : 1 < M.length)
    (_hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1)) :
    M.take (parent M (srow M (M.length - 1)) (M.length - 1))
      ++ seg M (parent M (srow M (M.length - 1)) (M.length - 1))
        (M.length - 1 - parent M (srow M (M.length - 1)) (M.length - 1))
      = M.dropLast := by
  have j0lt := nextR_index_lt (parent_nextR hp)
  set j0 := parent M (srow M (M.length - 1)) (M.length - 1) with hj0
  have hdl : M.dropLast = M.take (M.length - 1) := List.dropLast_eq_take
  rw [hdl]
  have htk : (M.take (M.length - 1)).take j0 = M.take j0 := by
    rw [List.take_take]
    congr 1
    omega
  conv_rhs => rw [← List.take_append_drop j0 (M.take (M.length - 1))]
  rw [htk]
  congr 1
  rw [drop_seg]
  have hlen : (M.take (M.length - 1)).length = M.length - 1 := by
    rw [List.length_take]
    omega
  rw [hlen]
  unfold seg
  refine List.map_congr_left ?_
  intro j hj
  have hjb := List.mem_range'_1.1 hj
  have e0 : entry (M.take (M.length - 1)) 0 j = entry M 0 j := by
    unfold entry
    rw [getD_take (by omega)]
  have e1 : entry (M.take (M.length - 1)) 1 j = entry M 1 j := by
    unfold entry
    rw [getD_take (by omega)]
  have e2 : entry (M.take (M.length - 1)) 2 j = entry M 2 j := by
    unfold entry
    rw [getD_take (by omega)]
  rw [e0, e1, e2]

/-- **Branch `bad`, modulo the crux.** -/
theorem seqlex_cof_bad (H : TrioBadCrux) {M N : TrioSeq}
    (hM : ST_TS M) (hN : ST_TS N) (L : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (h : seqlex N M) : ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) := by
  have hp := hasParent_last_ST_TS hM (by omega) hz
  have hne : M ≠ [] := by
    intro he
    rw [he] at L
    simp at L
  rcases seqlex_snoc_cases (D := M.dropLast)
      (lp := M.getD (M.length - 1) (0, 0, 0)) (N := N)
      (by rw [dropLast_snoc_getD hne]; exact h) with hle | ⟨q, S, hNeq, hq⟩
  · -- `N` stays within the good part: the first expansion already contains it
    refine ⟨1, le_rfl, ?_⟩
    have hsplit : M⟦1⟧ = M.dropLast := by
      rw [oper_gcopies 1 (by omega) hz hp, gcopies_eq_from,
        show (1 : ℕ) = 0 + 1 from rfl, gcopiesFrom_succ, gcopiesFrom_zero,
        List.append_nil, gcopy_zero, take_gcopy_zero L hz hp]
    rw [hsplit]
    exact hle
  · exact H hM hN L hz hNeq hq

/-- **Trio Bachmann cofinality, modulo the crux.** -/
theorem seqlex_cofinality_of_crux (H : TrioBadCrux) : SeqlexCofinality := by
  intro M N hM hN h
  by_cases hL : M.length - 1 = 0
  · exact seqlex_cof_short hL h
  · by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
        entry M 2 (M.length - 1) = 0
    · exact seqlex_cof_zero (by omega) hz h
    · exact seqlex_cof_bad H hM hN (by omega) hz h

/-- Translate-side cofinality, modulo the crux. -/
theorem ts_cofinality_of_crux (H : TrioBadCrux) {M N : TrioSeq}
    (hM : ST_TS M) (hN : ST_TS N) (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) :=
  ts_cofinality_of_seqlex (seqlex_cofinality_of_crux H) hM hN h

/-! ## Part 4 — 複写支配の道具（splice と分割） -/

/-- **Splice.**  A strictly smaller argument block stays smaller once the
tails are attached, provided the left tail re-opens at or below the block base
while every column of the right block is strictly above it. -/
theorem seqlex_splice : ∀ {A B : TrioSeq}, seqlex A B →
    ∀ {U : TrioSeq}, (U = [] ∨ ∀ x ∈ B, collt (U.headI) x) →
    ∀ (C : TrioSeq), seqlex (A ++ U) (B ++ C) := by
  intro A
  induction A with
  | nil =>
    intro B h U hU C
    rcases B with _ | ⟨b0, B'⟩
    · exact absurd h (by simp)
    · rcases U with _ | ⟨u, U'⟩
      · simp
      · refine Or.inl ?_
        rcases hU with h' | h'
        · exact absurd h' (by simp)
        · simpa using h' b0 (by simp)
  | cons a A' ihA =>
    intro B h U hU C
    rcases B with _ | ⟨b0, B'⟩
    · exact absurd h (by simp)
    · rw [seqlex_cons_cons] at h
      rcases h with hp | ⟨rfl, hs⟩
      · exact Or.inl hp
      · refine Or.inr ⟨rfl, ihA hs ?_ C⟩
        rcases hU with h' | h'
        · exact Or.inl h'
        · exact Or.inr (fun x hx => h' x (List.mem_cons_of_mem _ hx))

/-- The block split at the base level. -/
theorem split_block {v0 : ℕ} {R Y : TrioSeq} (hRgt : ∀ x ∈ R, v0 < x.1)
    (hYhd : Y = [] ∨ ¬ v0 < (Y.headI).1) :
    (R ++ Y).takeWhile (fun q => v0 < q.1) = R ∧
    (R ++ Y).dropWhile (fun q => v0 < q.1) = Y := by
  have hR' : ∀ x ∈ R, (fun q : ℕ × ℕ × ℕ => decide (v0 < q.1)) x = true := by
    intro x hx
    simpa using hRgt x hx
  rcases hYhd with rfl | hY
  · exact ⟨by simpa using List.takeWhile_eq_self_iff.2 hR',
      by simpa using List.dropWhile_eq_nil_iff.2 hR'⟩
  · rcases Y with _ | ⟨y, Y'⟩
    · exact ⟨by simpa using List.takeWhile_eq_self_iff.2 hR',
        by simpa using List.dropWhile_eq_nil_iff.2 hR'⟩
    · simp only [List.headI] at hY
      exact ⟨by rw [takeWhile_append_all hR']; simp [hY],
        by rw [dropWhile_append_all hR']; simp [hY]⟩

end TRIO
