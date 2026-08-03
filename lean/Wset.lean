/-
Wset.lean: 反復帰納的集合 W_u（yapss Wset.lean の trio 移植）。

trio の添字は対 (row1, row2) だが z < 2 なので辞書式順序型は ω：
`lev p = 2 * row1 + row2` で ℕ に符号化でき、yapss の ℕ 添字階層がそのまま動く。
-/
import Core
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Induction

namespace TRIO

open Three

namespace Wset

/-! ## 基本事実 -/

@[simp] theorem translate_nil : translate ([] : TrioSeq) = Z := by
  rw [translate]

/-- `translate` is `Z` only on the empty sequence. -/
theorem translate_eq_Z_iff {M : TrioSeq} : translate M = Z ↔ M = [] := by
  cases M with
  | nil => simp
  | cons p rest => simp [translate]

/-- Nothing but `0` is `<o` the term `p_{0,0}(0) = 1`. -/
theorem eq_Z_of_olt_one {t : Three} (h : t <o P 0 0 Z Z) : t = Z := by
  cases t with
  | Z => rfl
  | P a1 a2 b c =>
      rcases olt_P_P.mp h with h1 | ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, -, h1⟩
      · exact absurd h1 (Nat.not_lt_zero a1)
      · exact absurd h1 (Nat.not_lt_zero a2)
      · exact absurd h1 (not_olt_Z b)
      · exact absurd h1 (not_olt_Z c)

/-- A standard form is nonempty. -/
theorem stts_ne_nil {M : TrioSeq} (hM : ST_TS M) : M ≠ [] := by
  intro h
  have := stps_len_pos hM
  rw [h] at this
  simp at this

/-- A standard form of length `1` is `[(0,0,0)]`. -/
theorem stts_len_one {M : TrioSeq} (hM : ST_TS M) (h : M.length = 1) :
    M = [(0, 0, 0)] := by
  have hh := stps_head hM
  match M, h with
  | [p], _ => simpa [List.headD_cons] using congrArg (fun q => [q]) hh

/-! ## 添字と定義域 -/

/-- The subscript level of a column: `(row1, row2)` in lexicographic order,
encoded in `ℕ` (legitimate because `row2 < 2` on standard forms). -/
def lev (M : TrioSeq) (j : ℕ) : ℕ := 2 * entry M 1 j + entry M 2 j

/-- The last column of `M` is an *orphan* of level `m+1`: it carries subscript
level `m+1 > 0` and has no parent in its own row. -/
def domT (M : TrioSeq) (m : ℕ) : Prop :=
  lev M (M.length - 1) = m + 1 ∧
    ¬ hasParent M (srow M (M.length - 1)) (M.length - 1)

/-- **The level-`m` fundamental sequence `M[z]`**: replace the trailing orphan
by the forest `z`, re-based at the row-0 depth that leaf occupied. -/
def graft (M z : TrioSeq) : TrioSeq :=
  M.dropLast ++ z.map
    (fun p => ((p.1 + entry M 0 (M.length - 1), p.2.1, p.2.2) : ℕ × ℕ × ℕ))

/-- A block is in normalised (depth-`0`-anchored) form. -/
def based (z : TrioSeq) : Prop := entry z 0 0 = 0

@[simp] theorem based_nil : based ([] : TrioSeq) := by simp [based, entry]

@[simp] theorem graft_nil (M : TrioSeq) : graft M [] = M.dropLast := by
  simp [graft]

theorem not_domT_nil (m : ℕ) : ¬ domT ([] : TrioSeq) m := by
  rintro ⟨h, -⟩
  simp [lev, entry] at h

def natDom (M : TrioSeq) : Prop := ∀ m : ℕ, ¬ domT M m

theorem natDom_iff {M : TrioSeq} :
    natDom M ↔ (lev M (M.length - 1) = 0 ∨
      hasParent M (srow M (M.length - 1)) (M.length - 1)) := by
  constructor
  · intro h
    by_cases hz : lev M (M.length - 1) = 0
    · exact Or.inl hz
    · refine Or.inr ?_
      by_contra hp
      obtain ⟨m, hm⟩ : ∃ m, lev M (M.length - 1) = m + 1 :=
        ⟨lev M (M.length - 1) - 1, by omega⟩
      exact h m ⟨hm, hp⟩
  · rintro (hz | hp) m ⟨hw, hnp⟩
    · omega
    · exact hnp hp

theorem oper_eq_graft_nil_of_domT {M : TrioSeq} {m n : ℕ}
    (hL : 1 < M.length) (hd : domT M m) : M⟦n⟧ = graft M [] := by
  obtain ⟨hw, hp⟩ := hd
  have hj1 : M.length - 1 ≠ 0 := by omega
  have hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) := by
    rintro ⟨-, h2, h3⟩
    unfold lev at hw
    omega
  rw [oper_eq_pred_of_noParent (M := M) n hj1 hz hp, graft_nil]
  unfold Pred
  rw [if_neg (by omega)]

/-! ## 最小不動点と W 階層 -/

def lfpS (f : Set TrioSeq → Set TrioSeq) : Set TrioSeq := ⋂₀ {Y | f Y ⊆ Y}

theorem lfpS_lowerbound {f : Set TrioSeq → Set TrioSeq} {Y : Set TrioSeq}
    (h : f Y ⊆ Y) : lfpS f ⊆ Y := fun _ hx => hx Y h

theorem lfpS_unfold_le {f : Set TrioSeq → Set TrioSeq} (hm : Monotone f) :
    f (lfpS f) ⊆ lfpS f := by
  intro x hx Y hY
  exact hY (hm (lfpS_lowerbound hY) hx)

theorem lfpS_unfold_ge {f : Set TrioSeq → Set TrioSeq} (hm : Monotone f) :
    lfpS f ⊆ f (lfpS f) :=
  lfpS_lowerbound (hm (lfpS_unfold_le hm))

theorem lfpS_unfold {f : Set TrioSeq → Set TrioSeq} (hm : Monotone f) :
    f (lfpS f) = lfpS f :=
  Set.Subset.antisymm (lfpS_unfold_le hm) (lfpS_unfold_ge hm)

/-- The operator `A_u`. -/
def Aop (Wfam : ℕ → Set TrioSeq) (u : ℕ) (X : Set TrioSeq) (M : TrioSeq) : Prop :=
  (M.length ≤ 1 ∧ lev M 0 = 0) ∨
  (natDom M ∧ ∀ n : ℕ, 1 ≤ n → M⟦n⟧ ∈ X) ∨
  (∃ m : ℕ, m < u ∧ domT M m ∧ ∀ z ∈ Wfam m, based z → graft M z ∈ X)

def Aset (Wfam : ℕ → Set TrioSeq) (u : ℕ) (X : Set TrioSeq) : Set TrioSeq :=
  {M | Aop Wfam u X M}

theorem Aop_mono_X {Wfam : ℕ → Set TrioSeq} {u : ℕ} {X Y : Set TrioSeq}
    {M : TrioSeq} (h : Aop Wfam u X M) (hXY : X ⊆ Y) : Aop Wfam u Y M := by
  rcases h with h | h | ⟨m, hm, hd, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h.1, fun n hn => hXY (h.2 n hn)⟩)
  · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz hb => hXY (hop z hz hb)⟩)

theorem Aset_mono (Wfam : ℕ → Set TrioSeq) (u : ℕ) : Monotone (Aset Wfam u) := by
  intro X Y hXY M hM
  exact Aop_mono_X (Wfam := Wfam) (u := u) hM hXY

theorem Aop_mono_level {Wfam : ℕ → Set TrioSeq} {u v : ℕ} {X : Set TrioSeq}
    {M : TrioSeq} (le : u ≤ v) (h : Aop Wfam u X M) : Aop Wfam v X M := by
  rcases h with h | h | ⟨m, hm, hd, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨m, lt_of_lt_of_le hm le, hd, hop⟩)

theorem Aop_cong {Wfam Wgam : ℕ → Set TrioSeq} {u : ℕ} {X : Set TrioSeq}
    {M : TrioSeq} (e : ∀ m : ℕ, m < u → Wfam m = Wgam m) :
    Aop Wfam u X M ↔ Aop Wgam u X M := by
  constructor
  · rintro (h | h | ⟨m, hm, hd, hop⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz => hop z ((e m hm) ▸ hz)⟩)
  · rintro (h | h | ⟨m, hm, hd, hop⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz => hop z ((e m hm).symm ▸ hz)⟩)

/-- Stage family: `Wf n m` is `W_m` for `m < n` (and `∅` above). -/
def Wf : ℕ → ℕ → Set TrioSeq
  | 0 => fun _ => ∅
  | v + 1 => fun m => if m = v then lfpS (Aset (Wf v) v) else Wf v m

/-- **The trio iterated inductive set `W_u`.** -/
def W (u : ℕ) : Set TrioSeq := Wf (u + 1) u

theorem Wf_coh {m n : ℕ} (h : m < n) : Wf n m = Wf (m + 1) m := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ v ih =>
      by_cases hmv : m = v
      · subst hmv; rfl
      · have mlv : m < v := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp h) hmv
        show (if m = v then _ else Wf v m) = _
        rw [if_neg hmv]
        exact ih mlv

theorem Wf_eq_W {m n : ℕ} (h : m < n) : Wf n m = W m := Wf_coh h

theorem W_unfold (u : ℕ) : W u = lfpS (Aset W u) := by
  have stage : W u = lfpS (Aset (Wf u) u) := by
    show Wf (u + 1) u = _
    show (if u = u then _ else Wf u u) = _
    rw [if_pos rfl]
  have cong : ∀ m : ℕ, m < u → Wf u m = W m := fun m hm => Wf_eq_W hm
  have ptw : ∀ X : Set TrioSeq, Aset (Wf u) u X = Aset W u X := by
    intro X; ext M
    exact Aop_cong (Wfam := Wf u) (Wgam := W) (u := u) (X := X) cong
  rw [stage, funext ptw]

theorem A1 (u : ℕ) : Aset W u (W u) = W u := by
  rw [W_unfold u]
  exact lfpS_unfold (Aset_mono W u)

theorem A2 {u : ℕ} {Y : Set TrioSeq} (h : Aset W u Y ⊆ Y) : W u ⊆ Y := by
  rw [W_unfold u]
  exact lfpS_lowerbound h

theorem A2' {u : ℕ} {Y : Set TrioSeq}
    (hY : ∀ M : TrioSeq, Aop W u Y M → M ∈ Y) : W u ⊆ Y :=
  A2 (fun M hM => hY M hM)

theorem A1_intro {u : ℕ} {M : TrioSeq} (h : Aop W u (W u) M) : M ∈ W u := by
  have : M ∈ Aset W u (W u) := h
  rwa [A1 u] at this

theorem W_nil (u : ℕ) : ([] : TrioSeq) ∈ W u :=
  A1_intro (Or.inl ⟨by simp, by simp [lev, entry]⟩)

theorem W_mono {u v : ℕ} (h : u ≤ v) : W u ⊆ W v :=
  A2' (fun _ A => A1_intro (Aop_mono_level h A))

/-! ## W から到達可能性へ -/

/-- Strict `olt` on `translate`-images of standard forms. -/
def Rst : TrioSeq → TrioSeq → Prop :=
  fun a b => ST_TS a ∧ ST_TS b ∧ translate a <o translate b

theorem acc_of_translate_eq {a b : TrioSeq} (ha : ST_TS a)
    (e : translate b = translate a) (h : Acc Rst a) : Acc Rst b :=
  Acc.intro b fun y hy => h.inv ⟨hy.1, ha, by rw [← e]; exact hy.2.2⟩

theorem acc_of_nat_branch
    (hcof : ∀ {M N : TrioSeq}, ST_TS M → ST_TS N → translate N <o translate M →
      ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧))
    {c : TrioSeq} (hc : ST_TS c) (h : ∀ n : ℕ, 1 ≤ n → Acc Rst (c⟦n⟧)) :
    Acc Rst c := by
  refine Acc.intro c ?_
  intro b hb
  obtain ⟨hbst, -, hlt⟩ := hb
  obtain ⟨n, hn, hle⟩ := hcof hc hbst hlt
  have hacc : Acc Rst (c⟦n⟧) := h n hn
  have hst : ST_TS (c⟦n⟧) := ST_TS.oper hc hn
  rcases hle with hlt' | heq
  · exact hacc.inv ⟨hbst, hst, hlt'⟩
  · exact acc_of_translate_eq hst heq hacc

/-- Under Bachmann cofinality every member of `W_u` is accessible. -/
theorem acc_of_W
    (hcof : ∀ {M N : TrioSeq}, ST_TS M → ST_TS N → translate N <o translate M →
      ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧))
    (u : ℕ) : ∀ M : TrioSeq, M ∈ W u → Acc Rst M := by
  show W u ⊆ {M | Acc Rst M}
  refine A2' ?_
  intro c A
  by_cases hc : ST_TS c
  · have hne : c ≠ [] := stts_ne_nil hc
    rcases A with ⟨hlen, hw⟩ | ⟨-, hnat⟩ | ⟨m, -, hd, hgr⟩
    · -- branch 1: `translate c = p_{0,0}(0) = 1`; only `0` is below it.
      have hlen1 : c.length = 1 := by
        have := stps_len_pos hc
        omega
      have hc0 : c = [(0, 0, 0)] := stts_len_one hc hlen1
      have ht : translate c = P 0 0 Z Z := by
        rw [hc0, translate]
        simp
      refine Acc.intro _ ?_
      intro y hy
      obtain ⟨hyst, -, hlt⟩ := hy
      rw [ht] at hlt
      exact absurd (translate_eq_Z_iff.mp (eq_Z_of_olt_one hlt)) (stts_ne_nil hyst)
    · -- branch 2: the ℕ-indexed fundamental sequence.
      exact acc_of_nat_branch hcof hc hnat
    · -- branch 3: the graft branch degenerates to `oper`.
      by_cases hlen : 1 < c.length
      · refine acc_of_nat_branch hcof hc ?_
        intro n hn
        have := hgr [] (W_nil m) based_nil
        rw [← oper_eq_graft_nil_of_domT (n := n) hlen hd] at this
        exact this
      · have hlen1 : c.length = 1 := by
          have := stps_len_pos hc
          omega
        have hc0 : c = [(0, 0, 0)] := stts_len_one hc hlen1
        exfalso
        obtain ⟨hw, -⟩ := hd
        rw [hc0] at hw
        simp [lev, entry] at hw
  · exact Acc.intro c fun y hy => absurd hy.2.1 hc

/-- Cofinality plus `W`-membership give well-foundedness. -/
theorem wf_of_cofinality_and_membership
    (hcof : ∀ {M N : TrioSeq}, ST_TS M → ST_TS N → translate N <o translate M →
      ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧))
    (hmem : ∀ M : TrioSeq, ST_TS M → ∃ u : ℕ, M ∈ W u) :
    WellFounded Rst := by
  refine WellFounded.intro (fun M => ?_)
  by_cases hM : ST_TS M
  · obtain ⟨u, hu⟩ := hmem M hM
    exact acc_of_W hcof u M hu
  · exact Acc.intro M fun y hy => absurd hy.2.1 hM

end Wset

end TRIO
