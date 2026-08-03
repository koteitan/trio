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

/-- Every prefix of `R` has its trailing orphan strictly below `u`. -/
def tbAll (R : TrioSeq) (u : ℕ) : Prop := ∀ k m : ℕ, domT (R.take k) m → m < u

@[simp] theorem tbAll_nil (u : ℕ) : tbAll ([] : TrioSeq) u := by
  intro k m hd
  rw [List.take_nil] at hd
  exact absurd hd (not_domT_nil m)

theorem tbAll_mono {R : TrioSeq} {u v : ℕ} (h : tbAll R u) (huv : u ≤ v) :
    tbAll R v := fun k m hd => lt_of_lt_of_le (h k m hd) huv

theorem tbAll_take {R : TrioSeq} {u l : ℕ} (h : tbAll R u) :
    tbAll (R.take l) u := by
  intro k m hd
  rw [List.take_take] at hd
  exact h _ m hd

/-- A bound on every column's level bounds every prefix's trailing orphan. -/
theorem tbAll_of_lev_bound {R : TrioSeq} {u : ℕ}
    (h : ∀ p ∈ R, 2 * p.2.1 + p.2.2 ≤ u) : tbAll R u := by
  intro k m hd
  obtain ⟨hw, -⟩ := hd
  have hne : (R.take k) ≠ [] := by
    intro hc
    rw [hc] at hw
    simp [lev, entry] at hw
  have hpos : 0 < (R.take k).length := List.length_pos_iff.mpr hne
  have hmem : (R.take k).getD ((R.take k).length - 1) (0, 0, 0) ∈ R.take k :=
    getD_mem_of_lt (by omega)
  have hmem' : (R.take k).getD ((R.take k).length - 1) (0, 0, 0) ∈ R :=
    List.mem_of_mem_take hmem
  have hle := h _ hmem'
  have hw' : 2 * ((R.take k).getD ((R.take k).length - 1) (0, 0, 0)).2.1
      + ((R.take k).getD ((R.take k).length - 1) (0, 0, 0)).2.2 = m + 1 := hw
  omega

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
  (∃ m : ℕ, m < u ∧ domT M m ∧
    ∀ z ∈ Wfam m, based z → tbAll z m → graft M z ∈ X)

def Aset (Wfam : ℕ → Set TrioSeq) (u : ℕ) (X : Set TrioSeq) : Set TrioSeq :=
  {M | Aop Wfam u X M}

theorem Aop_mono_X {Wfam : ℕ → Set TrioSeq} {u : ℕ} {X Y : Set TrioSeq}
    {M : TrioSeq} (h : Aop Wfam u X M) (hXY : X ⊆ Y) : Aop Wfam u Y M := by
  rcases h with h | h | ⟨m, hm, hd, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h.1, fun n hn => hXY (h.2 n hn)⟩)
  · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz hb ht => hXY (hop z hz hb ht)⟩)

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
        have := hgr [] (W_nil m) based_nil (tbAll_nil m)
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

/-! ## 行 0 シフト同変性 -/

theorem nextrel2_shiftr01 {d0 : ℕ} {W : TrioSeq} {a b : ℕ} :
    nextrel2 (shiftr01 d0 0 W) a b ↔ nextrel2 W a b := by
  unfold nextrel2
  rw [shiftr01_length]
  simp only [entry2_shiftr01, le1_shiftr01]

theorem srow_shiftr01 {d0 : ℕ} (W : TrioSeq) (j : ℕ) :
    srow (shiftr01 d0 0 W) j = srow W j := by
  unfold srow
  rw [entry2_shiftr01, entry1_shiftr01]

theorem nextR_shiftr01 {d0 : ℕ} {W : TrioSeq} {i a b : ℕ} :
    nextR (shiftr01 d0 0 W) i a b ↔ nextR W i a b := by
  unfold nextR
  split
  · exact nextrel0_shiftr01
  · split
    · exact nextrel1_shiftr01
    · exact nextrel2_shiftr01

theorem hasParent_shiftr01 {d0 : ℕ} {W : TrioSeq} {i b : ℕ} :
    hasParent (shiftr01 d0 0 W) i b ↔ hasParent W i b := by
  unfold hasParent
  constructor
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, nextR_shiftr01.mp hj0, fun y hy => hu y (nextR_shiftr01.mpr hy)⟩
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, nextR_shiftr01.mpr hj0, fun y hy => hu y (nextR_shiftr01.mp hy)⟩

theorem parent_shiftr01 {d0 : ℕ} {W : TrioSeq} {i b : ℕ} :
    parent (shiftr01 d0 0 W) i b = parent W i b := by
  unfold parent
  congr 1
  funext j0
  exact propext nextR_shiftr01

theorem shiftr01_take (d0 d1 : ℕ) (W : TrioSeq) (k : ℕ) :
    (shiftr01 d0 d1 W).take k = shiftr01 d0 d1 (W.take k) := by
  unfold shiftr01
  rw [List.map_take]

theorem shiftr01_dropLast (d0 d1 : ℕ) (W : TrioSeq) :
    (shiftr01 d0 d1 W).dropLast = shiftr01 d0 d1 W.dropLast := by
  unfold shiftr01
  rw [List.map_dropLast]

theorem gcopy_shiftr01 {d : ℕ} {W : TrioSeq} {r L : ℕ} (hb : r + L ≤ W.length)
    (d0 d1 k : ℕ) :
    gcopy (shiftr01 d 0 W) r L d0 d1 k = shiftr01 d 0 (gcopy W r L d0 d1 k) := by
  show _ = List.map (fun p : ℕ × ℕ × ℕ => ((p.1 + d, p.2.1 + 0, p.2.2) : ℕ × ℕ × ℕ)) _
  unfold gcopy
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro j hj
  have hjlt : j < W.length := by
    have := List.mem_range'_1.1 hj
    omega
  rw [entry0_shiftr01 hjlt, entry1_shiftr01, entry2_shiftr01]
  simp only [Function.comp_apply]
  refine Prod.ext (by dsimp only; omega) (Prod.ext ?_ (by dsimp only))
  dsimp only
  by_cases hg : le1 W r j
  · rw [if_pos hg, if_pos (le1_shiftr01.mpr hg)]
    omega
  · rw [if_neg hg, if_neg (fun hc => hg (le1_shiftr01.mp hc))]

theorem gcopies_shiftr01 {d : ℕ} {W : TrioSeq} {r L : ℕ} (hb : r + L ≤ W.length)
    (d0 d1 n : ℕ) :
    gcopies (shiftr01 d 0 W) r L d0 d1 n
      = shiftr01 d 0 (gcopies W r L d0 d1 n) := by
  show _ = List.map (fun p : ℕ × ℕ × ℕ => ((p.1 + d, p.2.1 + 0, p.2.2) : ℕ × ℕ × ℕ)) _
  unfold gcopies
  rw [List.map_flatMap]
  refine List.flatMap_congr ?_
  intro k _
  exact gcopy_shiftr01 hb d0 d1 k

theorem Pred_shiftr01 {d : ℕ} (W : TrioSeq) :
    Pred (shiftr01 d 0 W) = shiftr01 d 0 (Pred W) := by
  unfold Pred
  rw [shiftr01_length]
  split_ifs with h
  · rfl
  · exact shiftr01_dropLast d 0 W

set_option maxHeartbeats 1000000 in
/-- `oper` is row-0-shift equivariant. -/
theorem oper_shiftr01 (W : TrioSeq) (d n : ℕ) :
    (shiftr01 d 0 W)⟦n⟧ = shiftr01 d 0 (W⟦n⟧) := by
  by_cases hL : W.length - 1 = 0
  · rw [oper_eq_self_of_short n (by rw [shiftr01_length]; exact hL),
      oper_eq_self_of_short n hL]
  · have hlt : W.length - 1 < W.length := by omega
    have hlenmap : (shiftr01 d 0 W).length - 1 = W.length - 1 := by
      rw [shiftr01_length]
    have hLm : (shiftr01 d 0 W).length - 1 ≠ 0 := by rw [shiftr01_length]; exact hL
    have hsr : srow (shiftr01 d 0 W) (W.length - 1) = srow W (W.length - 1) :=
      srow_shiftr01 W (W.length - 1)
    by_cases hp : hasParent W (srow W (W.length - 1)) (W.length - 1)
    · have hpos : 0 < entry W 0 (W.length - 1) := by
        by_contra h
        exact no_hasParent_of_row0_zero (by omega) hp
      have hz : ¬ (entry W 0 (W.length - 1) = 0 ∧ entry W 1 (W.length - 1) = 0 ∧
          entry W 2 (W.length - 1) = 0) := by
        rintro ⟨h1, -, -⟩; omega
      have hpM : hasParent (shiftr01 d 0 W)
          (srow (shiftr01 d 0 W) ((shiftr01 d 0 W).length - 1))
          ((shiftr01 d 0 W).length - 1) := by
        rw [hlenmap, hsr]
        exact hasParent_shiftr01.mpr hp
      have hzM : ¬ (entry (shiftr01 d 0 W) 0 ((shiftr01 d 0 W).length - 1) = 0 ∧
          entry (shiftr01 d 0 W) 1 ((shiftr01 d 0 W).length - 1) = 0 ∧
          entry (shiftr01 d 0 W) 2 ((shiftr01 d 0 W).length - 1) = 0) := by
        rw [hlenmap]
        rintro ⟨h1, -, -⟩
        rw [entry0_shiftr01 hlt] at h1
        omega
      rw [oper_gcopies n hLm hzM hpM, oper_gcopies n hL hz hp, hlenmap, hsr,
        parent_shiftr01, shiftr01_take]
      have hj0lt : parent W (srow W (W.length - 1)) (W.length - 1) < W.length - 1 :=
        nextR_index_lt (parent_nextR hp)
      have he0 := entry0_shiftr01 (d0 := d) (d1 := 0) (W := W) hlt
      have he0' := entry0_shiftr01 (d0 := d) (d1 := 0) (W := W)
        (p := parent W (srow W (W.length - 1)) (W.length - 1)) (by omega)
      have hd0 : entry (shiftr01 d 0 W) 0 (W.length - 1)
          - entry (shiftr01 d 0 W) 0
              (parent W (srow W (W.length - 1)) (W.length - 1))
          = entry W 0 (W.length - 1)
            - entry W 0 (parent W (srow W (W.length - 1)) (W.length - 1)) := by
        rw [he0, he0']
        omega
      have hd1 : entry (shiftr01 d 0 W) 1 (W.length - 1)
          - entry (shiftr01 d 0 W) 1
              (parent W (srow W (W.length - 1)) (W.length - 1))
          = entry W 1 (W.length - 1)
            - entry W 1 (parent W (srow W (W.length - 1)) (W.length - 1)) := by
        rw [entry1_shiftr01, entry1_shiftr01]
      rw [hd0, hd1, gcopies_shiftr01 (by omega), shiftr01_append]
    · have hpM : ¬ hasParent (shiftr01 d 0 W)
          (srow (shiftr01 d 0 W) ((shiftr01 d 0 W).length - 1))
          ((shiftr01 d 0 W).length - 1) := by
        rw [hlenmap, hsr]
        intro hh
        exact hp (hasParent_shiftr01.mp hh)
      have hW : W⟦n⟧ = Pred W := by
        by_cases hz : entry W 0 (W.length - 1) = 0 ∧ entry W 1 (W.length - 1) = 0 ∧
            entry W 2 (W.length - 1) = 0
        · exact oper_eq_pred_of_zero n hL hz
        · exact oper_eq_pred_of_noParent n hL hz hp
      have hWm : (shiftr01 d 0 W)⟦n⟧ = Pred (shiftr01 d 0 W) := by
        by_cases hz : entry (shiftr01 d 0 W) 0 ((shiftr01 d 0 W).length - 1) = 0 ∧
            entry (shiftr01 d 0 W) 1 ((shiftr01 d 0 W).length - 1) = 0 ∧
            entry (shiftr01 d 0 W) 2 ((shiftr01 d 0 W).length - 1) = 0
        · exact oper_eq_pred_of_zero n hLm hz
        · exact oper_eq_pred_of_noParent n hLm hz hpM
      rw [hW, hWm, Pred_shiftr01]

theorem lev_shiftr01 {d : ℕ} (W : TrioSeq) (j : ℕ) :
    lev (shiftr01 d 0 W) j = lev W j := by
  unfold lev
  rw [entry1_shiftr01, entry2_shiftr01]

theorem domT_shiftr01 {d m : ℕ} {W : TrioSeq} :
    domT (shiftr01 d 0 W) m ↔ domT W m := by
  unfold domT
  rw [shiftr01_length, lev_shiftr01, srow_shiftr01, hasParent_shiftr01]

theorem natDom_shiftr01 {d : ℕ} {W : TrioSeq} :
    natDom (shiftr01 d 0 W) ↔ natDom W :=
  ⟨fun h m hm => h m (domT_shiftr01.mpr hm),
   fun h m hm => h m (domT_shiftr01.mp hm)⟩

theorem tbAll_shiftr01 {d u : ℕ} {W : TrioSeq} :
    tbAll (shiftr01 d 0 W) u ↔ tbAll W u := by
  constructor
  · intro h k m hd
    exact h k m (by rw [shiftr01_take]; exact domT_shiftr01.mpr hd)
  · intro h k m hd
    rw [shiftr01_take] at hd
    exact h k m (domT_shiftr01.mp hd)

theorem graft_shiftr01 {W : TrioSeq} (hW : W ≠ []) (z : TrioSeq) (d : ℕ) :
    graft (shiftr01 d 0 W) z = shiftr01 d 0 (graft W z) := by
  have hlt : W.length - 1 < W.length := by
    have : 0 < W.length := List.length_pos_iff.mpr hW
    omega
  unfold graft
  rw [shiftr01_length, entry0_shiftr01 hlt, shiftr01_dropLast, shiftr01_append]
  congr 1
  unfold shiftr01
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro p _
  simp only [Function.comp_apply]
  refine Prod.ext (by dsimp only; omega) (Prod.ext (by dsimp only; omega)
    (by dsimp only))

/-! ## 引数ブロックと最上位分解 -/

/-- `R` is an *argument block*: every column sits strictly below depth `0`. -/
def argOK (R : TrioSeq) : Prop := ∀ p ∈ R, 0 < p.1

/-- `P` is a genuine top-level suffix of `A ++ P`. -/
def rsum (A P : TrioSeq) : Prop := ∀ p ∈ A ++ P, entry P 0 0 ≤ p.1

/-- `W_u` is row-0-shift closed. -/
theorem W_shift {u : ℕ} {M : TrioSeq} (h : M ∈ W u) (d : ℕ) :
    shiftr01 d 0 M ∈ W u := by
  revert h
  show M ∈ W u → _
  have hsub : W u ⊆ {N : TrioSeq | shiftr01 d 0 N ∈ W u} := by
    refine A2' ?_
    intro N A
    refine A1_intro ?_
    rcases A with ⟨hl, hw⟩ | ⟨hnat, hop⟩ | ⟨m, hm, hd, hgr⟩
    · refine Or.inl ⟨by rw [shiftr01_length]; exact hl, ?_⟩
      rw [lev_shiftr01]
      exact hw
    · exact Or.inr (Or.inl ⟨natDom_shiftr01.mpr hnat, fun n hn => by
        rw [oper_shiftr01]
        exact hop n hn⟩)
    · refine Or.inr (Or.inr ⟨m, hm, domT_shiftr01.mpr hd, fun z hz hb ht => ?_⟩)
      have hne : N ≠ [] := by rintro rfl; exact not_domT_nil m hd
      rw [graft_shiftr01 hne]
      exact hgr z hz hb ht
  exact fun h => hsub h

/-- Every nonempty block splits as `A ++ P` with `P` its last top-level tree. -/
theorem split_lastMin : ∀ {M : TrioSeq}, M ≠ [] →
    ∃ A P, M = A ++ P ∧ P ≠ [] ∧ rsum A P ∧
      (∀ p ∈ P.tail, entry P 0 0 < p.1) := by
  intro M
  induction M using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton M' q ih =>
      intro _
      by_cases hM' : M' = []
      · subst hM'
        refine ⟨[], [q], by simp, by simp, ?_, by simp⟩
        intro p hp
        simp only [List.nil_append, List.mem_singleton] at hp
        subst hp
        simp [entry]
      · obtain ⟨A', P', hEq, hPne, hrs, htail⟩ := ih hM'
        have hhd : entry (P' ++ [q]) 0 0 = entry P' 0 0 := by
          rcases P' with _ | ⟨p0, P''⟩
          · exact absurd rfl hPne
          · simp [entry]
        by_cases hq : entry P' 0 0 < q.1
        · refine ⟨A', P' ++ [q], by rw [hEq]; simp, by simp, ?_, ?_⟩
          · intro p hp
            rw [hhd]
            rcases List.mem_append.mp hp with hp | hp
            · exact hrs p (List.mem_append_left _ hp)
            · rcases List.mem_append.mp hp with hp | hp
              · exact hrs p (List.mem_append_right _ hp)
              · simp only [List.mem_singleton] at hp
                subst hp
                omega
          · intro p hp
            rw [hhd]
            rcases P' with _ | ⟨p0, P''⟩
            · exact absurd rfl hPne
            · simp only [List.cons_append, List.tail_cons] at hp
              rcases List.mem_append.mp hp with hp | hp
              · exact htail p (by simpa using hp)
              · simp only [List.mem_singleton] at hp
                subst hp
                exact hq
        · refine ⟨M', [q], rfl, by simp, ?_, by simp⟩
          intro p hp
          have hq0 : entry ([q] : TrioSeq) 0 0 = q.1 := by simp [entry]
          rw [hq0]
          rcases List.mem_append.mp hp with hp | hp
          · rw [hEq] at hp
            have := hrs p hp
            omega
          · simp only [List.mem_singleton] at hp
            subst hp
            exact le_rfl

theorem entry_sub_zero {P : TrioSeq} (hP : P ≠ []) :
    entry (shiftl0 (entry P 0 0) P) 0 0 = 0 := by
  rcases P with _ | ⟨p0, P'⟩
  · exact absurd rfl hP
  · show ((shiftl0 (entry (p0 :: P') 0 0) (p0 :: P')).getD 0 (0, 0, 0)).1 = 0
    rw [shiftl0_cons]
    simp only [List.getD_cons_zero]
    show p0.1 - entry (p0 :: P') 0 0 = 0
    have : entry (p0 :: P') 0 0 = p0.1 := rfl
    omega

theorem rsum_decomp {A P : TrioSeq} (h : rsum A P) :
    shiftr01 (entry P 0 0) 0 (shiftl0 (entry P 0 0) A ++ shiftl0 (entry P 0 0) P)
      = A ++ P := by
  rw [shiftr01_append,
    shiftr01_shiftl0 (fun p hp => h p (List.mem_append_left _ hp)),
    shiftr01_shiftl0 (fun p hp => h p (List.mem_append_right _ hp))]

/-- Prefix commutation for a top-level split. -/
theorem oper_append_gen {A P : TrioSeq} (n : ℕ) (hP : 2 ≤ P.length) (h : rsum A P) :
    (A ++ P)⟦n⟧ = A ++ P⟦n⟧ := by
  set c := entry P 0 0 with hc
  set A₀ := shiftl0 c A with hA0
  set P₀ := shiftl0 c P with hP0
  have hPne : P ≠ [] := by rintro rfl; simp at hP
  have hroot : entry P₀ 0 0 = 0 := entry_sub_zero hPne
  have hlen0 : 2 ≤ P₀.length := by rw [hP0, shiftl0_length]; exact hP
  have hAP : shiftr01 c 0 (A₀ ++ P₀) = A ++ P := rsum_decomp h
  have hPP : shiftr01 c 0 P₀ = P :=
    shiftr01_shiftl0 (fun p hp => h p (List.mem_append_right _ hp))
  have hAA : shiftr01 c 0 A₀ = A :=
    shiftr01_shiftl0 (fun p hp => h p (List.mem_append_left _ hp))
  calc (A ++ P)⟦n⟧ = (shiftr01 c 0 (A₀ ++ P₀))⟦n⟧ := by rw [hAP]
    _ = shiftr01 c 0 ((A₀ ++ P₀)⟦n⟧) := oper_shiftr01 _ _ _
    _ = shiftr01 c 0 (A₀ ++ P₀⟦n⟧) := by
          rw [oper_append_right A₀ P₀ n hlen0 hroot]
    _ = A ++ shiftr01 c 0 (P₀⟦n⟧) := by rw [shiftr01_append, hAA]
    _ = A ++ P⟦n⟧ := by rw [← oper_shiftr01, hPP]

theorem graft_append {A P z : TrioSeq} (hP : P ≠ []) :
    graft (A ++ P) z = A ++ graft P z := by
  have hlen : (A ++ P).length - 1 = A.length + (P.length - 1) := by
    have : 0 < P.length := List.length_pos_iff.mpr hP
    rw [List.length_append]
    omega
  unfold graft
  rw [hlen, entry_append_right, List.dropLast_append_of_ne_nil hP,
    List.append_assoc]

/-- `hasParent` is invariant under a prefix, for a genuine top-level split. -/
theorem hasParent_append_gen {A P : TrioSeq} {i j : ℕ} (hj : j < P.length)
    (h : rsum A P) :
    hasParent (A ++ P) i (A.length + j) ↔ hasParent P i j := by
  have hPne : P ≠ [] := by rintro rfl; simp at hj
  set c := entry P 0 0 with hc
  set A₀ := shiftl0 c A with hA0
  set P₀ := shiftl0 c P with hP0
  have hroot : entry P₀ 0 0 = 0 := entry_sub_zero hPne
  have hAP : shiftr01 c 0 (A₀ ++ P₀) = A ++ P := rsum_decomp h
  have hPP : shiftr01 c 0 P₀ = P :=
    shiftr01_shiftl0 (fun p hp => h p (List.mem_append_right _ hp))
  have hlenA : A₀.length = A.length := by rw [hA0, shiftl0_length]
  have hlenP : P₀.length = P.length := by rw [hP0, shiftl0_length]
  have step1 : hasParent (A ++ P) i (A.length + j)
      ↔ hasParent (A₀ ++ P₀) i (A₀.length + j) := by
    rw [hlenA, ← hAP]
    exact hasParent_shiftr01
  have step3 : hasParent P₀ i j ↔ hasParent P i j := by
    rw [← hPP]
    exact hasParent_shiftr01.symm
  have step2 : hasParent (A₀ ++ P₀) i (A₀.length + j) ↔ hasParent P₀ i j := by
    by_cases hz : entry P₀ 0 j = 0
    · constructor
      · intro hh
        exact absurd hh (fun hh' => no_hasParent_of_row0_zero
          (by rw [entry_append_right]; exact hz) hh')
      · intro hh
        exact absurd hh (fun hh' => no_hasParent_of_row0_zero hz hh')
    · exact hasParent_append_right A₀ P₀ hroot
        (by rw [entry_append_right]; omega)
  rw [step1, step2, step3]

theorem lev_append_right (A P : TrioSeq) (j : ℕ) :
    lev (A ++ P) (A.length + j) = lev P j := by
  unfold lev
  rw [entry_append_right, entry_append_right]

theorem srow_append_right (A P : TrioSeq) (j : ℕ) :
    srow (A ++ P) (A.length + j) = srow P j := by
  unfold srow
  rw [entry_append_right, entry_append_right]

theorem domT_append {A P : TrioSeq} {m : ℕ} (hP : P ≠ []) (h : rsum A P) :
    domT (A ++ P) m ↔ domT P m := by
  have hPlen : 0 < P.length := List.length_pos_iff.mpr hP
  have hlen : (A ++ P).length - 1 = A.length + (P.length - 1) := by
    rw [List.length_append]
    omega
  unfold domT
  rw [hlen, lev_append_right, srow_append_right,
    hasParent_append_gen (by omega) h]

theorem natDom_append {A P : TrioSeq} (hP : P ≠ []) (h : rsum A P) :
    natDom (A ++ P) ↔ natDom P :=
  ⟨fun hn m hm => hn m ((domT_append hP h).mpr hm),
   fun hn m hm => hn m ((domT_append hP h).mp hm)⟩

def XA (A : TrioSeq) (X : Set TrioSeq) : Set TrioSeq := {B | rsum A B → A ++ B ∈ X}

end Wset

end TRIO
