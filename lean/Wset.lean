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

/-! ## 先頭・深さの保存 -/

theorem entry_zero_headD (X : TrioSeq) : entry X 0 0 = (X.headD (0, 0, 0)).1 := by
  cases X <;> simp [entry]

theorem oper_headD (N : TrioSeq) {n : ℕ} (L : 1 < N.length) (hn : 1 ≤ n) :
    (N⟦n⟧).headD (0, 0, 0) = N.headD (0, 0, 0) := by
  obtain ⟨R, hR⟩ := oper_eq_dropLast_append L hn
  rw [hR]
  match N, L with
  | a :: b :: u, _ =>
    simp only [List.dropLast_cons_cons, List.cons_append, List.headD_cons]

/-- `oper` keeps the head (hence the anchoring depth) for `n ≥ 1`. -/
theorem oper_head_eq {B : TrioSeq} {n : ℕ} (hn : 1 ≤ n) :
    entry (B⟦n⟧) 0 0 = entry B 0 0 := by
  by_cases hL : 1 < B.length
  · rw [entry_zero_headD, entry_zero_headD, oper_headD B hL hn]
  · rw [oper_eq_self_of_short n (by omega)]

/-- The `j`-th column of `B` really is a member of `B`. -/
theorem entry_pair_mem {B : TrioSeq} {j : ℕ} (hj : j < B.length) :
    ((entry B 0 j, entry B 1 j, entry B 2 j) : ℕ × ℕ × ℕ) ∈ B := by
  have h : ((entry B 0 j, entry B 1 j, entry B 2 j) : ℕ × ℕ × ℕ)
      = B.getD j (0, 0, 0) := rfl
  have h2 : B.getD j (0, 0, 0) = B[j]'hj := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [h, h2]
  exact List.getElem_mem hj

/-- `oper` never produces a column shallower than the shallowest column of `B`. -/
theorem oper_mem_ge {B : TrioSeq} {c n : ℕ} (h : ∀ p ∈ B, c ≤ p.1) :
    ∀ p ∈ B⟦n⟧, c ≤ p.1 := by
  by_cases hL : B.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact h
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
        dsimp only
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

/-- `graft` never produces a column shallower than the shallowest column. -/
theorem graft_mem_ge {B z : TrioSeq} {c : ℕ} (hB : B ≠ []) (h : ∀ p ∈ B, c ≤ p.1) :
    ∀ p ∈ graft B z, c ≤ p.1 := by
  have hlt : B.length - 1 < B.length := by
    have : 0 < B.length := List.length_pos_iff.mpr hB
    omega
  have hx : c ≤ entry B 0 (B.length - 1) := h _ (entry_pair_mem hlt)
  intro p hp
  rcases List.mem_append.mp hp with hmem | hmem
  · exact h p (List.dropLast_subset _ hmem)
  · rw [List.mem_map] at hmem
    obtain ⟨q, -, rfl⟩ := hmem
    dsimp only
    omega

/-- `graft` keeps the anchoring depth (whenever the result is nonempty). -/
theorem graft_head_eq {B z : TrioSeq} (hB : B ≠ []) (hz : based z)
    (hne : graft B z ≠ []) : entry (graft B z) 0 0 = entry B 0 0 := by
  rcases hB2 : B with _ | ⟨b0, B'⟩
  · exact absurd hB2 hB
  · rcases B' with _ | ⟨b1, B''⟩
    · have hgr : graft [b0] z
          = z.map (fun p => ((p.1 + b0.1, p.2.1, p.2.2) : ℕ × ℕ × ℕ)) := by
        simp [graft, entry]
      rw [hB2] at hne
      rw [hgr] at hne ⊢
      rcases z with _ | ⟨z0, z'⟩
      · simp at hne
      · have h0 : entry (z0 :: z') 0 0 = 0 := hz
        simp [entry] at h0 ⊢
        omega
    · simp [graft, entry]

set_option maxHeartbeats 1000000 in
/-- `A_u(X) ⊆ X` and `A ∈ X` imply `A_u(X⁽ᴬ⁾) ⊆ X⁽ᴬ⁾`. -/
theorem XA_closed {u : ℕ} {X : Set TrioSeq}
    (hX : ∀ M : TrioSeq, Aop W u X M → M ∈ X) {A : TrioSeq} (hA : A ∈ X) :
    ∀ M : TrioSeq, Aop W u (XA A X) M → M ∈ XA A X := by
  intro B AB hrs
  by_cases hBnil : B = []
  · subst hBnil; simpa using hA
  · have hBlen : 0 < B.length := List.length_pos_iff.mpr hBnil
    have hBge : ∀ p ∈ B, entry B 0 0 ≤ p.1 :=
      fun p hp => hrs p (List.mem_append_right _ hp)
    have hAge : ∀ p ∈ A, entry B 0 0 ≤ p.1 :=
      fun p hp => hrs p (List.mem_append_left _ hp)
    rcases AB with ⟨hl, hw⟩ | ⟨hnat, hop⟩ | ⟨m, hm, hd, hgr⟩
    · have hB1 : B.length = 1 := by omega
      by_cases hAnil : A = []
      · subst hAnil; simpa using hX B (Or.inl ⟨hl, hw⟩)
      · have hAlen : 0 < A.length := List.length_pos_iff.mpr hAnil
        have hlast : (A ++ B).length - 1 = A.length + 0 := by
          rw [List.length_append]; omega
        have hnp : ∀ i, ¬ hasParent (A ++ B) i ((A ++ B).length - 1) := by
          intro i hh
          rw [hlast] at hh
          have := (hasParent_append_gen (i := i) (j := 0) (by omega) hrs).mp hh
          obtain ⟨j0, hj0, -⟩ := this
          exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
        have hlev0 : lev (A ++ B) ((A ++ B).length - 1) = 0 := by
          rw [hlast, lev_append_right]
          have : B.length - 1 = 0 := by omega
          exact hw
        have hzz0 : lev B (B.length - 1) = 0 := by
          have : B.length - 1 = 0 := by omega
          rw [this]; exact hw
        refine hX _ (Or.inr (Or.inl ⟨(natDom_append hBnil hrs).mpr
          (natDom_iff.mpr (Or.inl hzz0)), fun n hn => ?_⟩))
        have hpred : (A ++ B)⟦n⟧ = Pred (A ++ B) := by
          by_cases hzz : entry (A ++ B) 0 ((A ++ B).length - 1) = 0 ∧
              entry (A ++ B) 1 ((A ++ B).length - 1) = 0 ∧
              entry (A ++ B) 2 ((A ++ B).length - 1) = 0
          · exact oper_eq_pred_of_zero n (by rw [List.length_append]; omega) hzz
          · exact oper_eq_pred_of_noParent n (by rw [List.length_append]; omega)
              hzz (hnp _)
        rw [hpred]
        unfold Pred
        rw [if_neg (by rw [List.length_append]; omega),
          List.dropLast_append_of_ne_nil hBnil]
        have hdl : B.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
        rw [hdl]
        simpa using hA
    · by_cases hB2 : 2 ≤ B.length
      · refine hX _ (Or.inr (Or.inl ⟨(natDom_append hBnil hrs).mpr hnat,
          fun n hn => ?_⟩))
        rw [oper_append_gen n hB2 hrs]
        refine hop n hn (fun p hp => ?_)
        rw [oper_head_eq hn]
        rcases List.mem_append.mp hp with hp | hp
        · exact hAge p hp
        · exact oper_mem_ge hBge p hp
      · have hB1 : B⟦1⟧ = B := oper_eq_self_of_short 1 (by omega)
        have h1 := hop 1 le_rfl
        rw [hB1] at h1
        exact h1 hrs
    · refine hX _ (Or.inr (Or.inr ⟨m, hm, (domT_append hBnil hrs).mpr hd,
        fun z hz hbz htz => ?_⟩))
      rw [graft_append hBnil]
      refine hgr z hz hbz htz ?_
      by_cases hgz : graft B z = []
      · rw [hgz]
        intro p hp
        simp [entry]
      · intro p hp
        rw [graft_head_eq hBnil hbz hgz]
        rcases List.mem_append.mp hp with hp | hp
        · exact hAge p hp
        · exact graft_mem_ge hBnil hBge p hp

/-- `W_u` is closed under top-level concatenation. -/
theorem W_add {u : ℕ} {A B : TrioSeq} (hA : A ∈ W u) (hB : B ∈ W u)
    (h : rsum A B) : A ++ B ∈ W u :=
  A2' (XA_closed (u := u) (X := W u) (fun _ hM => A1_intro hM) hA) hB h

theorem graft_Om (v z : ℕ) (y : TrioSeq) : graft [((0, v, z) : ℕ × ℕ × ℕ)] y = y := by
  simp [graft, entry]

theorem domT_Om {v z : ℕ} (h : 0 < 2 * v + z) :
    domT [((0, v, z) : ℕ × ℕ × ℕ)] (2 * v + z - 1) := by
  refine ⟨by simp [lev, entry]; omega, ?_⟩
  rintro ⟨j0, hj0, -⟩
  have := nextR_index_lt hj0
  simp at this

theorem Om_mem_W (v z : ℕ) : [((0, v, z) : ℕ × ℕ × ℕ)] ∈ W (2 * v + z) := by
  rcases Nat.eq_zero_or_pos (2 * v + z) with h0 | hpos
  · rw [h0]
    exact A1_intro (Or.inl ⟨by simp, by simp [lev, entry]; omega⟩)
  · refine A1_intro (Or.inr (Or.inr ⟨2 * v + z - 1, by omega, domT_Om hpos, ?_⟩))
    intro y hy _ _
    rw [graft_Om]
    exact W_mono (by omega) hy

/-! ## `cons` に沿う添字ずらし -/

/-- Index shift across a `cons`. -/
theorem entry_cons (p : ℕ × ℕ × ℕ) (R : TrioSeq) (i j : ℕ) :
    entry (p :: R) i (j + 1) = entry R i j := by
  have h := entry_append_right [p] R i j
  simp only [List.length_singleton, List.singleton_append] at h
  rw [Nat.add_comm 1 j] at h
  exact h

theorem nextR_cons (p : ℕ × ℕ × ℕ) (R : TrioSeq) (i j0 j1 : ℕ) :
    nextR (p :: R) i (j0 + 1) (j1 + 1) ↔ nextR R i j0 j1 := by
  have h := nextR_append_right [p] R i j0 j1
  simp only [List.length_singleton, List.singleton_append] at h
  rw [Nat.add_comm 1 j0, Nat.add_comm 1 j1] at h
  exact h

theorem le0_cons (p : ℕ × ℕ × ℕ) (R : TrioSeq) (j0 j1 : ℕ) :
    le0 (p :: R) (j0 + 1) (j1 + 1) ↔ le0 R j0 j1 := by
  have h := le0_append_right [p] R j0 j1
  simp only [List.length_singleton, List.singleton_append] at h
  rw [Nat.add_comm 1 j0, Nat.add_comm 1 j1] at h
  exact h

theorem le1_cons (p : ℕ × ℕ × ℕ) (R : TrioSeq) (j0 j1 : ℕ) :
    le1 (p :: R) (j0 + 1) (j1 + 1) ↔ le1 R j0 j1 := by
  have h := le1_append_right [p] R j0 j1
  simp only [List.length_singleton, List.singleton_append] at h
  rw [Nat.add_comm 1 j0, Nat.add_comm 1 j1] at h
  exact h

theorem srow_cons (p : ℕ × ℕ × ℕ) (R : TrioSeq) (j : ℕ) :
    srow (p :: R) (j + 1) = srow R j := by
  unfold srow
  rw [entry_cons, entry_cons]

theorem len_succ {R : TrioSeq} (hRne : R ≠ []) : R.length = (R.length - 1) + 1 := by
  have : 0 < R.length := List.length_pos_iff.mpr hRne
  omega

theorem entry_cons_last {p : ℕ × ℕ × ℕ} {R : TrioSeq} (hRne : R ≠ []) (i : ℕ) :
    entry (p :: R) i R.length = entry R i (R.length - 1) := by
  conv_lhs => rw [len_succ hRne]
  rw [entry_cons]

theorem le0_cons_last {p : ℕ × ℕ × ℕ} {R : TrioSeq} (hRne : R ≠ []) (j : ℕ) :
    le0 (p :: R) (j + 1) R.length ↔ le0 R j (R.length - 1) := by
  conv_lhs => rw [len_succ hRne]
  rw [le0_cons]

theorem le1_cons_last {p : ℕ × ℕ × ℕ} {R : TrioSeq} (hRne : R ≠ []) (j : ℕ) :
    le1 (p :: R) (j + 1) R.length ↔ le1 R j (R.length - 1) := by
  conv_lhs => rw [len_succ hRne]
  rw [le1_cons]

theorem nextR_cons_last {p : ℕ × ℕ × ℕ} {R : TrioSeq} (hRne : R ≠ []) (i j : ℕ) :
    nextR (p :: R) i (j + 1) R.length ↔ nextR R i j (R.length - 1) := by
  conv_lhs => rw [len_succ hRne]
  rw [nextR_cons]

theorem srow_cons_last {p : ℕ × ℕ × ℕ} {R : TrioSeq} (hRne : R ≠ []) :
    srow (p :: R) R.length = srow R (R.length - 1) := by
  conv_lhs => rw [len_succ hRne]
  rw [srow_cons]

theorem cons_len_lt {p : ℕ × ℕ × ℕ} (R : TrioSeq) : R.length < (p :: R).length := by
  simp

theorem cons_length (p : ℕ × ℕ × ℕ) (R : TrioSeq) : (p :: R).length - 1 = R.length := by
  simp

theorem dropLast_cons {p : ℕ × ℕ × ℕ} {R : TrioSeq} (hRne : R ≠ []) :
    (p :: R).dropLast = p :: R.dropLast := by
  cases R with
  | nil => exact absurd rfl hRne
  | cons a b => simp

/-- Row-0 companion: a column has a row-0 parent iff some earlier column is
strictly shallower. -/
theorem hasParent_zero_iff {M : TrioSeq} {b : ℕ} (hb : b < M.length) :
    hasParent M 0 b ↔ ∃ k, k < b ∧ entry M 0 k < entry M 0 b := by
  classical
  have nR : ∀ k : ℕ, nextR M 0 k b ↔ nextrel0 M k b := by
    intro k; unfold nextR; rw [if_pos rfl]
  constructor
  · rintro ⟨k, hk, -⟩
    have h := (nR k).mp hk
    exact ⟨k, h.2.2.1, h.2.2.2.1⟩
  · rintro ⟨k, hk1, hk2⟩
    set P : ℕ → Prop := fun t => t < b ∧ entry M 0 t < entry M 0 b with hP
    have hPg : P (Nat.findGreatest P b) :=
      Nat.findGreatest_spec (m := k) (le_of_lt hk1) ⟨hk1, hk2⟩
    have hmax : ∀ t, P t → t ≤ Nat.findGreatest P b :=
      fun t ht => Nat.le_findGreatest (le_of_lt ht.1) ht
    refine ⟨Nat.findGreatest P b, (nR _).mpr ?_, ?_⟩
    · refine ⟨by omega, hb, hPg.1, hPg.2, ?_⟩
      intro l hl
      by_contra hcon
      exact absurd (hmax l ⟨hl.2, by omega⟩) (by omega)
    · intro y hy
      have hy' : nextrel0 M y b := (nR y).mp hy
      have hyP : P y := ⟨hy'.2.2.1, hy'.2.2.2.1⟩
      rcases eq_or_lt_of_le (hmax y hyP) with h | h
      · exact h
      · have := hy'.2.2.2.2 (Nat.findGreatest P b) ⟨h, hPg.1⟩
        have := hPg.2
        omega

/-- The root of a principal block is a row-0 ancestor of every column. -/
theorem le0_cons_zero {v z : ℕ} {R : TrioSeq} (hR : argOK R) :
    ∀ j, j < R.length → le0 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 (j + 1) := by
  have key : ∀ N j, j ≤ N → j < R.length →
      le0 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 (j + 1) := by
    intro N
    induction N with
    | zero =>
        intro j hj hjR
        have hj0 : j = 0 := by omega
        subst hj0
        refine ⟨by simp, by simp; omega, Relation.ReflTransGen.single ?_⟩
        refine ⟨by simp, by simp; omega, by omega, ?_, ?_⟩
        · rw [entry_cons]
          have := hR _ (entry_pair_mem (B := R) (j := 0) (by omega))
          simpa [entry] using this
        · intro l hl; omega
    | succ N ih =>
        intro j hj hjR
        have hbnd : j + 1 < (((0, v, z) : ℕ × ℕ × ℕ) :: R).length := by simp; omega
        have hpos : 0 < entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 (j + 1) := by
          rw [entry_cons]
          exact hR _ (entry_pair_mem (B := R) hjR)
        have hex : ∃ k, k < j + 1 ∧
            entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 k
              < entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 (j + 1) := by
          refine ⟨0, by omega, ?_⟩
          simpa [entry] using hpos
        obtain ⟨k, hk, -⟩ := (hasParent_zero_iff hbnd).mpr hex
        have hnk : nextrel0 (((0, v, z) : ℕ × ℕ × ℕ) :: R) k (j + 1) := by
          unfold nextR at hk; rwa [if_pos rfl] at hk
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          exact ⟨by simp, hbnd, Relation.ReflTransGen.single hnk⟩
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have hklt : k' + 1 < j + 1 := hnk.2.2.1
          obtain ⟨-, -, hchain⟩ := ih k' (by omega) (by omega)
          exact ⟨by simp, hbnd, hchain.tail hnk⟩
  intro j hj
  exact key j j le_rfl hj

/-! ## ガード付き graft と主ブロックの展開 -/

/-- The row-1 lift carried by the guarded tower: when the trailing orphan sits
in row 2 at positive depth, the copies raise row 1 up to the orphan's value. -/
def gdelta (M y : TrioSeq) : ℕ :=
  if 0 < entry M 0 (M.length - 1) ∧ 1 < srow M (M.length - 1)
  then entry M 1 (M.length - 1) - entry y 1 0 else 0

/-- **The guarded fundamental-sequence substitution** `M[y]`: replace the
trailing orphan by `y`, re-based at the orphan's depth and lifted in row 1 by
`gdelta`. -/
def ggraft (M y : TrioSeq) : TrioSeq :=
  M.dropLast ++ y.map (fun p =>
    ((p.1 + entry M 0 (M.length - 1), p.2.1 + gdelta M y, p.2.2) : ℕ × ℕ × ℕ))

@[simp] theorem ggraft_nil (M : TrioSeq) : ggraft M [] = M.dropLast := by
  simp [ggraft]

theorem ggraft_Om (v z : ℕ) (y : TrioSeq) :
    ggraft [((0, v, z) : ℕ × ℕ × ℕ)] y = y := by
  have hd : gdelta [((0, v, z) : ℕ × ℕ × ℕ)] y = 0 := by
    unfold gdelta
    rw [if_neg (by simp [entry])]
  simp [ggraft, hd, entry]

/-- `ggraft` commutes with a `cons` on a nonempty block. -/
theorem ggraft_cons {p : ℕ × ℕ × ℕ} {R y : TrioSeq} (hRne : R ≠ []) :
    ggraft (p :: R) y = p :: ggraft R y := by
  have hlen : (p :: R).length - 1 = R.length := by simp
  have he : ∀ i, entry (p :: R) i ((p :: R).length - 1) = entry R i (R.length - 1) := by
    intro i; rw [hlen]; exact entry_cons_last hRne i
  have hs : srow (p :: R) ((p :: R).length - 1) = srow R (R.length - 1) := by
    rw [hlen]; exact srow_cons_last hRne
  have hd : gdelta (p :: R) y = gdelta R y := by
    unfold gdelta; rw [he 0, he 1, hs]
  unfold ggraft
  rw [hd, he 0, dropLast_cons hRne, List.cons_append]

/-- With `R`'s own last column parented inside `R`, the principal root is never a
`nextR`-predecessor of that column, so the parent index just shifts by one. -/
theorem nextR_cons_uniq {v z : ℕ} {R : TrioSeq} (hR : argOK R) (hRne : R ≠ [])
    (hp : hasParent R (srow R (R.length - 1)) (R.length - 1)) :
    ∀ y, nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) y R.length
      → y = parent R (srow R (R.length - 1)) (R.length - 1) + 1 := by
  classical
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  set i1 := srow R (R.length - 1) with hi1
  set q := parent R i1 (R.length - 1) with hq
  have hnrR : nextR R i1 q (R.length - 1) := parent_nextR hp
  have hqlt : q < R.length - 1 := nextR_index_lt hnrR
  have hE : ∀ i, entry (p0 :: R) i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  -- the root is *not* a parent of the last column: `R`'s own parent blocks it
  have hnoroot : ¬ nextR (p0 :: R) i1 0 R.length := by
    intro h0
    by_cases hi : i1 = 0
    · have h0' : nextrel0 (p0 :: R) 0 R.length := by
        unfold nextR at h0; rw [if_pos hi] at h0; exact h0
      have hnr0 : nextrel0 R q (R.length - 1) := by
        have h := hnrR; unfold nextR at h; rw [if_pos hi] at h; exact h
      have hval := h0'.2.2.2.2 (q + 1) ⟨by omega, by omega⟩
      rw [hE 0, entry_cons] at hval
      have := hnr0.2.2.2.1
      omega
    · by_cases hi2 : i1 = 1
      · have h0' : nextrel1 (p0 :: R) 0 R.length := by
          unfold nextR at h0; rw [if_neg hi, if_pos hi2] at h0; exact h0
        have hnr1 : nextrel1 R q (R.length - 1) := by
          have h := hnrR; unfold nextR at h; rw [if_neg hi, if_pos hi2] at h; exact h
        have hle : le0 (p0 :: R) (q + 1) R.length :=
          (le0_cons_last hRne q).mpr hnr1.2.2.2.2.1
        have hval := h0'.2.2.2.2.2 (q + 1) ⟨by omega, hle⟩
        rw [hE 1, entry_cons] at hval
        have := hnr1.2.2.2.1
        omega
      · have h0' : nextrel2 (p0 :: R) 0 R.length := by
          unfold nextR at h0; rw [if_neg hi, if_neg hi2] at h0; exact h0
        have hnr2 : nextrel2 R q (R.length - 1) := by
          have h := hnrR; unfold nextR at h; rw [if_neg hi, if_neg hi2] at h; exact h
        have hle : le1 (p0 :: R) (q + 1) R.length :=
          (le1_cons_last hRne q).mpr hnr2.2.2.2.2.1
        have hval := h0'.2.2.2.2.2 (q + 1) ⟨by omega, hle⟩
        rw [hE 2, entry_cons] at hval
        have := hnr2.2.2.2.1
        omega
  intro y hy
  rcases Nat.eq_zero_or_pos y with rfl | hy0
  · exact absurd hy hnoroot
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have hyR := (nextR_cons_last hRne i1 y').mp hy
    rw [hp.unique hyR hnrR]

/-- **Non-collapsing principal step**: `p_{v,z}(R)[n] = p_{v,z}(R[n])`. -/
theorem oper_cons_nat {v z n : ℕ} {R : TrioSeq} (hR : argOK R) (hRne : R ≠ [])
    (hp : hasParent R (srow R (R.length - 1)) (R.length - 1)) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ = ((0, v, z) : ℕ × ℕ × ℕ) :: R⟦n⟧ := by
  classical
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  set i1 := srow R (R.length - 1) with hi1
  set q := parent R i1 (R.length - 1) with hq
  have hnrR : nextR R i1 q (R.length - 1) := parent_nextR hp
  have hqlt : q < R.length - 1 := nextR_index_lt hnrR
  have hLR : R.length - 1 ≠ 0 := by omega
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  have hzR : ¬ (entry R 0 (R.length - 1) = 0 ∧ entry R 1 (R.length - 1) = 0 ∧
      entry R 2 (R.length - 1) = 0) := by rintro ⟨h1, -, -⟩; omega
  have hMlen : (p0 :: R).length - 1 = R.length := by simp
  have hE : ∀ i, entry (p0 :: R) i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  have hLM : (p0 :: R).length - 1 ≠ 0 := by rw [hMlen]; omega
  have hzM : ¬ (entry (p0 :: R) 0 ((p0 :: R).length - 1) = 0 ∧
      entry (p0 :: R) 1 ((p0 :: R).length - 1) = 0 ∧
      entry (p0 :: R) 2 ((p0 :: R).length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -, -⟩; rw [hE 0] at h1; omega
  have hi1M : srow (p0 :: R) ((p0 :: R).length - 1) = i1 := by
    rw [hMlen]; exact srow_cons_last hRne
  have huniq : ∀ y, nextR (p0 :: R) i1 y R.length → y = q + 1 :=
    nextR_cons_uniq (v := v) (z := z) hR hRne hp
  have hpM : hasParent (p0 :: R) (srow (p0 :: R) ((p0 :: R).length - 1))
      ((p0 :: R).length - 1) := by
    rw [hi1M, hMlen]
    exact ⟨q + 1, (nextR_cons_last hRne _ _).mpr hnrR, huniq⟩
  have hparM : parent (p0 :: R) (srow (p0 :: R) ((p0 :: R).length - 1))
      ((p0 :: R).length - 1) = q + 1 := by
    have heq : parent (p0 :: R) (srow (p0 :: R) ((p0 :: R).length - 1))
        ((p0 :: R).length - 1) = parent (p0 :: R) i1 R.length := by rw [hi1M, hMlen]
    rw [heq]
    refine huniq _ (parent_nextR ?_)
    rw [hi1M, hMlen] at hpM; exact hpM
  have hrange : R.length - (q + 1) = R.length - 1 - q := by omega
  rw [oper_bad_unfold n hLM hzM hpM, oper_bad_unfold n hLR hzR hp,
    hparM, hi1M, hMlen, hE 0, hE 1, entry_cons, entry_cons, hrange,
    List.take_succ_cons, List.cons_append]
  have hqq : parent R (srow R (R.length - 1)) (R.length - 1) = q := by
    rw [← hi1, ← hq]
  rw [hqq, ← hi1]
  congr 1
  congr 1
  refine List.flatMap_congr ?_
  intro k _
  have hshift : List.range' (q + 1) (R.length - 1 - q)
      = (List.range' q (R.length - 1 - q)).map (fun j => j + 1) := by
    rw [List.range'_eq_map_range, List.range'_eq_map_range, List.map_map]
    refine List.map_congr_left ?_
    intro j _
    simp only [Function.comp_apply]
    omega
  rw [hshift, List.map_map]
  refine List.map_congr_left ?_
  intro j _
  simp only [Function.comp_apply, entry_cons, le0_cons, le1_cons]

/-- **`W u` is closed under one expansion step.** -/
theorem oper_closed {u n : ℕ} {M : TrioSeq} (hM : M ∈ W u) (hn : 1 ≤ n) :
    M⟦n⟧ ∈ W u := by
  have hA : Aop W u (W u) M := by
    have h : M ∈ Aset W u (W u) := by rw [A1 u]; exact hM
    exact h
  by_cases hshort : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hshort]; exact hM
  · rcases hA with ⟨hl, -⟩ | ⟨-, hop⟩ | ⟨m, -, hd, hgr⟩
    · exact absurd (by omega : M.length - 1 = 0) hshort
    · exact hop n hn
    · rw [oper_eq_graft_nil_of_domT (n := n) (by omega) hd]
      exact hgr [] (W_nil m) based_nil (tbAll_nil m)

/-- The segment starting at `0` is a prefix. -/
theorem seg_zero_eq_take (M : TrioSeq) {j : ℕ} (h : j ≤ M.length) :
    seg M 0 j = M.take j := by
  unfold seg
  apply List.ext_getElem
  · simp [Nat.min_eq_left h]
  · intro i h1 h2
    have hi : i < M.length := by
      simp only [List.length_map, List.length_range'] at h1
      omega
    simp only [List.getElem_map, List.getElem_range', List.getElem_take,
      ← getD_eq_entries, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Nat.zero_add, Nat.one_mul,
      Option.getD_some]

/-- **Successor principal step**: when `R`'s trailing column carries no
subscript and no row-0 parent inside `R`, the root itself is its parent and
`p_{v,z}(R)⟦n⟧` is `n` literal copies of `p_{v,z}(R.dropLast)`. -/
theorem oper_cons_succ {v z n : ℕ} {R : TrioSeq} (hR : argOK R) (hRne : R ≠ [])
    (hw : lev R (R.length - 1) = 0)
    (hnp : ¬ hasParent R 0 (R.length - 1)) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ =
      (List.range n).flatMap
        (fun _ => (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast)) := by
  classical
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : (p0 :: R).length - 1 = R.length := by simp
  have hE : ∀ i, entry (p0 :: R) i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  have hL : (p0 :: R).length - 1 ≠ 0 := by rw [hMlen]; omega
  have hz : ¬ (entry (p0 :: R) 0 ((p0 :: R).length - 1) = 0 ∧
      entry (p0 :: R) 1 ((p0 :: R).length - 1) = 0 ∧
      entry (p0 :: R) 2 ((p0 :: R).length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -, -⟩; rw [hE 0] at h1; omega
  have hw1 : entry R 1 (R.length - 1) = 0 := by unfold lev at hw; omega
  have hw2 : entry R 2 (R.length - 1) = 0 := by unfold lev at hw; omega
  have hi1 : srow (p0 :: R) ((p0 :: R).length - 1) = 0 := by
    rw [hMlen, srow_cons_last hRne]
    unfold srow
    rw [if_neg (by omega), if_neg (by omega)]
  have hallge : ∀ k, k < R.length - 1 → entry R 0 (R.length - 1) ≤ entry R 0 k := by
    intro k hk
    by_contra hcon
    exact hnp ((hasParent_zero_iff (by omega)).mpr ⟨k, hk, by omega⟩)
  have hnr : nextrel0 (p0 :: R) 0 R.length := by
    refine ⟨by simp, by simp, hRlen, ?_, ?_⟩
    · rw [hE 0]
      have : entry (p0 :: R) 0 0 = 0 := by simp [entry, hp0]
      omega
    · rintro l ⟨hl1, hl2⟩
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [hE 0, entry_cons]
      exact hallge l' (by omega)
  have huniq : ∀ y, nextR (p0 :: R) 0 y R.length → y = 0 := by
    intro y hy
    by_contra hy0
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have hyR : nextrel0 R y' (R.length - 1) := (nextR_cons_last hRne 0 y').mp hy
    have h1 := hallge y' hyR.2.2.1
    have h2 := hyR.2.2.2.1
    omega
  have hnr' : nextR (p0 :: R) 0 0 R.length := by
    unfold nextR; rw [if_pos rfl]; exact hnr
  have hp : hasParent (p0 :: R) (srow (p0 :: R) ((p0 :: R).length - 1))
      ((p0 :: R).length - 1) := by
    rw [hi1, hMlen]
    exact ⟨0, hnr', huniq⟩
  have hpar : parent (p0 :: R) (srow (p0 :: R) ((p0 :: R).length - 1))
      ((p0 :: R).length - 1) = 0 := by
    have hp' : hasParent (p0 :: R) 0 R.length := by rw [hi1, hMlen] at hp; exact hp
    have heq : parent (p0 :: R) (srow (p0 :: R) ((p0 :: R).length - 1))
        ((p0 :: R).length - 1) = parent (p0 :: R) 0 R.length := by rw [hi1, hMlen]
    rw [heq]
    exact huniq _ (parent_nextR hp')
  rw [oper_gcopies n hL hz hp, hpar, hi1, if_neg (by omega), if_neg (by omega),
    List.take_zero, List.nil_append, Nat.sub_zero]
  unfold gcopies
  refine List.flatMap_congr ?_
  intro k _
  have hgc : gcopy (p0 :: R) 0 ((p0 :: R).length - 1) 0 0 k
      = seg (p0 :: R) 0 ((p0 :: R).length - 1) := by
    unfold gcopy seg
    refine List.map_congr_left ?_
    intro j _
    simp
  rw [hgc, seg_zero_eq_take _ (by omega), ← List.dropLast_eq_take,
    dropLast_cons hRne]


/-! ## 行 2 の上限（z < 2 断片） -/

/-- Row 2 never exceeds `1`: the generators are `z`-capped and `oper` copies
row 2 verbatim. -/
def zle1 (M : TrioSeq) : Prop := ∀ p ∈ M, p.2.2 ≤ 1

theorem zle1_oper {B : TrioSeq} {n : ℕ} (h : zle1 B) : zle1 (B⟦n⟧) := by
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
        dsimp only
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

theorem zle1_diagSeqT (v : ℕ) : zle1 (diagSeqT 0 v) := by
  intro p hp
  unfold diagSeqT at hp
  rw [List.mem_map] at hp
  obtain ⟨j, -, rfl⟩ := hp
  dsimp only
  omega

theorem zle1_ST_TS {M : TrioSeq} (h : ST_TS M) : zle1 M := by
  induction h with
  | diag v => exact zle1_diagSeqT v
  | oper _ _ ih => exact zle1_oper ih

/-! ## `W*` の補助 -/

theorem argOK_oper {R : TrioSeq} (hR : argOK R) (n : ℕ) : argOK (R⟦n⟧) :=
  fun p hp => oper_mem_ge (c := 1) (fun q hq => hR q hq) p hp

theorem argOK_graft {R : TrioSeq} (hRne : R ≠ []) (hR : argOK R) (y : TrioSeq) :
    argOK (graft R y) :=
  fun p hp => graft_mem_ge (c := 1) hRne (fun q hq => hR q hq) p hp

theorem argOK_dropLast {R : TrioSeq} (hR : argOK R) : argOK R.dropLast :=
  fun p hp => hR p (List.dropLast_subset _ hp)

theorem based_cons (v z : ℕ) (R : TrioSeq) :
    based (((0, v, z) : ℕ × ℕ × ℕ) :: R) := by simp [based, entry]

theorem rsum_self_cons (v z : ℕ) (R : TrioSeq) :
    ∀ p ∈ (((0, v, z) : ℕ × ℕ × ℕ) :: R),
      entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 0 ≤ p.1 := by
  intro p _
  simp [entry]

theorem graft_cons {v z : ℕ} {R y : TrioSeq} (hRne : R ≠ []) :
    graft (((0, v, z) : ℕ × ℕ × ℕ) :: R) y
      = ((0, v, z) : ℕ × ℕ × ℕ) :: graft R y := by
  have h := graft_append (A := [((0, v, z) : ℕ × ℕ × ℕ)]) (P := R) (z := y) hRne
  simpa [List.cons_append] using h

/-- `n` copies of one tree stay in `W u`. -/
theorem W_flatMap_copies {u : ℕ} {Q : TrioSeq} (hQ : Q ∈ W u)
    (hQr : ∀ p ∈ Q, entry Q 0 0 ≤ p.1) :
    ∀ n : ℕ, ((List.range n).flatMap fun _ => Q) ∈ W u := by
  intro n
  induction n with
  | zero => simpa using W_nil u
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append]
      have hQ1 : ((List.flatMap fun _ => Q) [n]) = Q := by simp
      rw [hQ1]
      refine W_add ih hQ ?_
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · rw [List.mem_flatMap] at hp
        obtain ⟨-, -, hp⟩ := hp
        exact hQr p hp
      · exact hQr p hp

/-- A prefix cannot supply a `nextR`-predecessor once the block itself has one:
the minimality clause of the inner predecessor rules it out.  Unlike
`nextR_src_in_T` this needs **no** anchoring hypothesis on `T`. -/
theorem nextR_src_ge {A T : TrioSeq} {i y q j1 : ℕ}
    (hq : nextR T i q j1) (hy : nextR (A ++ T) i y (A.length + j1)) :
    A.length ≤ y := by
  by_contra hlt
  push_neg at hlt
  have hqlt : q < j1 := nextR_index_lt hq
  unfold nextR at hy hq
  by_cases hi : i = 0
  · rw [if_pos hi] at hy hq
    have hb := hy.2.2.2.2 (A.length + q) ⟨by omega, by omega⟩
    rw [entry_append_right, entry_append_right] at hb
    have := hq.2.2.2.1
    omega
  · rw [if_neg hi] at hy hq
    by_cases hi1 : i = 1
    · rw [if_pos hi1] at hy hq
      have hle : le0 (A ++ T) (A.length + q) (A.length + j1) :=
        (le0_append_right A T q j1).2 hq.2.2.2.2.1
      have hb := hy.2.2.2.2.2 (A.length + q) ⟨by omega, hle⟩
      rw [entry_append_right, entry_append_right] at hb
      have := hq.2.2.2.1
      omega
    · rw [if_neg hi1] at hy hq
      have hle : le1 (A ++ T) (A.length + q) (A.length + j1) :=
        (le1_append_right A T q j1).2 hq.2.2.2.2.1
      have hb := hy.2.2.2.2.2 (A.length + q) ⟨by omega, hle⟩
      rw [entry_append_right, entry_append_right] at hb
      have := hq.2.2.2.1
      omega

/-- A parent inside `T` stays the unique parent after any prefix is prepended. -/
theorem hasParent_append_right_of (A T : TrioSeq) {i j1 : ℕ}
    (h : hasParent T i j1) : hasParent (A ++ T) i (A.length + j1) := by
  obtain ⟨q, hq, huniq⟩ := h
  refine ⟨A.length + q, (nextR_append_right A T i q j1).2 hq, ?_⟩
  intro y hy
  have hge := nextR_src_ge hq hy
  obtain ⟨y', rfl⟩ : ∃ y', y = A.length + y' := ⟨y - A.length, by omega⟩
  have := huniq y' ((nextR_append_right A T i y' j1).1 hy)
  omega

/-- Every dead orphan of a prefix of `graft M z` is one of `M` or one of `z`. -/
theorem tbAll_graft {M z : TrioSeq} {u m : ℕ} (hMne : M ≠ [])
    (hM : tbAll M u) (hmu : m < u) (hz : tbAll z m) :
    tbAll (graft M z) u := by
  classical
  have hMlen : 0 < M.length := List.length_pos_iff.mpr hMne
  set A : TrioSeq := M.dropLast with hA
  set c : ℕ := entry M 0 (M.length - 1) with hc
  have hAlen : A.length = M.length - 1 := by rw [hA, List.length_dropLast]
  have hgz : graft M z = A ++ shiftr01 c 0 z := by
    unfold graft shiftr01
    refine congrArg _ (List.map_congr_left ?_)
    intro p _
    exact Prod.ext rfl (Prod.ext (by dsimp only; omega) rfl)
  intro k m' hd
  by_cases hk : k ≤ A.length
  · have htake : (graft M z).take k = M.take k := by
      rw [hgz, List.take_append_of_le_length hk, hA, List.dropLast_eq_take,
        List.take_take, Nat.min_eq_left (by omega)]
    rw [htake] at hd
    exact hM k m' hd
  · push_neg at hk
    obtain ⟨j, rfl⟩ : ∃ j, k = A.length + j := ⟨k - A.length, by omega⟩
    set Z : TrioSeq := shiftr01 c 0 z with hZ
    have htake : (graft M z).take (A.length + j) = A ++ Z.take j := by
      rw [hgz, take_append_right]
    rw [htake] at hd
    obtain ⟨j0, hj0le, hj0t⟩ : ∃ j0, j0 ≤ Z.length ∧ Z.take j = Z.take j0 := by
      rcases Nat.lt_or_ge Z.length j with h | h
      · exact ⟨Z.length, le_rfl, by
          rw [List.take_of_length_le (le_of_lt h), List.take_of_length_le le_rfl]⟩
      · exact ⟨j, h, rfl⟩
    rw [hj0t] at hd
    have hlZ : (Z.take j0).length = j0 := by
      rw [List.length_take, Nat.min_eq_left hj0le]
    have hlen : (A ++ Z.take j0).length = A.length + j0 := by
      rw [List.length_append, hlZ]
    rcases Nat.eq_zero_or_pos j0 with hj0z | hj0pos
    · rw [hj0z] at hd
      simp only [List.take_zero, List.append_nil] at hd
      rw [hA, List.dropLast_eq_take] at hd
      exact hM _ m' hd
    · obtain ⟨hlev, hnp⟩ := hd
      rw [hlen] at hlev hnp
      have hidx : A.length + j0 - 1 = A.length + (j0 - 1) := by omega
      rw [hidx] at hlev hnp
      have hZd : domT (Z.take j0) m' := by
        refine ⟨?_, ?_⟩
        · rw [hlZ, ← lev_append_right A (Z.take j0) (j0 - 1)]
          exact hlev
        · rw [hlZ]
          intro hh
          refine hnp ?_
          rw [srow_append_right A (Z.take j0) (j0 - 1)]
          exact hasParent_append_right_of A (Z.take j0) hh
      have hshift : Z.take j0 = shiftr01 c 0 (z.take j0) := by
        rw [hZ, shiftr01_take]
      rw [hshift] at hZd
      exact lt_trans (hz j0 m' (domT_shiftr01.mp hZd)) hmu

/-- An argument block `R` is in `W*` when every principal block
`M = p_{v,z}(R)` lands in every stage `u` that both dominates the root level
and dominates the *dead orphans of `M`'s own prefixes*.

The second condition is indexed by `M`, **not** by `R`, and that is exactly what
makes the trio hierarchy work.  A `z = 1` root cannot collapse a `z = 1` orphan
(row-2 parenthood needs a strictly smaller row 2), so `M` can carry `domT M m`
with `m ≥ 2v+z` and the graft clause would be out of reach at `u = 2v+z`;
`tbAll M u` forces `u > m` and puts it back in range.  Indexing by `tbAll R u`
instead is *false*: it counts orphans of `R`'s prefixes that the root revives,
which pushes `u` above `m` in the tower branch and breaks `W u ⊆ W m`
(probe: 52/119 tower blocks violate it, versus 0/264 for the `M`-indexed form). -/
def Wstar : Set TrioSeq :=
  {R | argOK R → ∀ v z u : ℕ, z ≤ 1 → 2 * v + z ≤ u →
    tbAll (((0, v, z) : ℕ × ℕ × ℕ) :: R) u →
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W u}

/-- The principal root inherits `R`'s own parent, shifted by one. -/
theorem hasParent_cons_of {v z : ℕ} {R : TrioSeq} (hR : argOK R) (hRne : R ≠ [])
    (hp : hasParent R (srow R (R.length - 1)) (R.length - 1)) :
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length :=
  ⟨parent R (srow R (R.length - 1)) (R.length - 1) + 1,
    (nextR_cons_last hRne _ _).mpr (parent_nextR hp),
    nextR_cons_uniq hR hRne hp⟩

/-- If the root fails to revive `R`'s trailing orphan, the principal block
inherits `R`'s domain. -/
theorem domT_cons_of_dead {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hd : domT R m)
    (hnp : ¬ hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R)
      (srow R (R.length - 1)) R.length) :
    domT (((0, v, z) : ℕ × ℕ × ℕ) :: R) m := by
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : (p0 :: R).length - 1 = R.length := by simp
  have hlevM : lev (p0 :: R) ((p0 :: R).length - 1) = lev R (R.length - 1) := by
    unfold lev
    rw [hMlen, entry_cons_last hRne 1, entry_cons_last hRne 2]
  have hi1M : srow (p0 :: R) ((p0 :: R).length - 1) = srow R (R.length - 1) := by
    rw [hMlen]; exact srow_cons_last hRne
  exact ⟨by rw [hlevM]; exact hd.1, by rw [hi1M, hMlen]; exact hnp⟩

/-! ## 残る二つの核 -/

/-- **Open core 1 — the guarded tower.**  When the principal root revives `R`'s
trailing orphan, `p_{v,z}(R)⟦n⟧` is an `n`-fold guarded copy tower and its
membership has to be assembled from `R`'s graft closure.  For `srow = 1` the
row-1 lift is `0` and the plain `graft` recursion of the pair-sequence proof
applies; for `srow = 2` the copies raise row 1 by `w - v` on the `le1`-cone of
the root, so the substituted block is the *lifted* tower, not the tower. -/
def TowerOK : Prop :=
  ∀ (v z m u : ℕ) (R : TrioSeq), argOK R → R ≠ [] → domT R m →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    (∀ y ∈ W m, based y → tbAll y m → graft R y ∈ Wstar) →
    z ≤ 1 → 2 * v + z ≤ u → tbAll (((0, v, z) : ℕ × ℕ × ℕ) :: R) u →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W u

/-- **Open core 2 — `tbAll` survives one expansion.**  True on every probe
(56080/56080); the proof needs the cross-copy `le0`/`le1` correspondence. -/
def TbOper : Prop := ∀ (M : TrioSeq) (u n : ℕ), tbAll M u → tbAll (M⟦n⟧) u

/-- **`A_u(W*) ⊆ W*`.** -/
theorem Wstar_closed (htow : TowerOK) (htbo : TbOper) :
    ∀ (u0 : ℕ) (R : TrioSeq), Aop W u0 Wstar R → R ∈ Wstar := by
  intro u0 R AR hR v z u hz1 hvu htb
  by_cases hRnil : R = []
  · subst hRnil
    exact W_mono hvu (Om_mem_W v z)
  · set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
    have hRlen : 0 < R.length := List.length_pos_iff.mpr hRnil
    have hMlen : (p0 :: R).length - 1 = R.length := by simp
    have hi1M : srow (p0 :: R) ((p0 :: R).length - 1) = srow R (R.length - 1) := by
      rw [hMlen]; exact srow_cons_last hRnil
    have hlevM : lev (p0 :: R) ((p0 :: R).length - 1) = lev R (R.length - 1) := by
      unfold lev
      rw [hMlen, entry_cons_last hRnil 1, entry_cons_last hRnil 2]
    have htbdl : tbAll (p0 :: R.dropLast) u := by
      have heq : (p0 :: R.dropLast) = (p0 :: R).take R.length := by
        rw [← dropLast_cons hRnil, List.dropLast_eq_take, hMlen]
      rw [heq]
      exact tbAll_take htb
    rcases AR with ⟨hl, hw⟩ | ⟨hnat, hop⟩ | ⟨m, hm, hd, hgr⟩
    · -- clause 1: `R = [(x,0,0)]`, so `p_{v,z}(R)⟦n⟧` is `n` copies of `Ω_{v,z}`
      have hR1 : R.length = 1 := by omega
      have hw' : lev R (R.length - 1) = 0 := by rw [hR1]; exact hw
      have hnp : ¬ hasParent R 0 (R.length - 1) := by
        rw [hR1]
        rintro ⟨j0, hj0, -⟩
        exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
      have hdl : R.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      refine A1_intro (Or.inr (Or.inl
        ⟨natDom_iff.mpr (Or.inl (by rw [hlevM]; exact hw')), fun n hn => ?_⟩))
      rw [oper_cons_succ hR hRnil hw' hnp, hdl]
      exact W_flatMap_copies (W_mono hvu (Om_mem_W v z)) (rsum_self_cons v z []) n
    · -- clause 2: `natDom R`
      by_cases hp : hasParent R (srow R (R.length - 1)) (R.length - 1)
      · -- `p_{v,z}(R)⟦n⟧ = p_{v,z}(R⟦n⟧)`
        refine A1_intro (Or.inr (Or.inl ⟨natDom_iff.mpr (Or.inr
          (by rw [hi1M, hMlen]; exact hasParent_cons_of hR hRnil hp)),
          fun n hn => ?_⟩))
        have hstep := oper_cons_nat (v := v) (z := z) (n := n) hR hRnil hp
        rw [hstep]
        refine hop n hn (argOK_oper hR n) v z u hz1 hvu ?_
        rw [← hstep]
        exact htbo (p0 :: R) u n htb
      · -- no parent inside `R`: `natDom R` forces the successor case
        have hw0 : lev R (R.length - 1) = 0 := by
          rcases natDom_iff.mp hnat with h | h
          · exact h
          · exact absurd h hp
        have hsr : srow R (R.length - 1) = 0 := by
          unfold srow
          unfold lev at hw0
          rw [if_neg (by omega), if_neg (by omega)]
        have hnp : ¬ hasParent R 0 (R.length - 1) := by rw [← hsr]; exact hp
        refine A1_intro (Or.inr (Or.inl
          ⟨natDom_iff.mpr (Or.inl (by rw [hlevM]; exact hw0)), fun n hn => ?_⟩))
        rw [oper_cons_succ hR hRnil hw0 hnp]
        refine W_flatMap_copies ?_ (rsum_self_cons v z _) n
        by_cases hR2 : 2 ≤ R.length
        · have hop1 := hop 1 le_rfl
          have hpred : R⟦1⟧ = R.dropLast := by
            have hL : R.length - 1 ≠ 0 := by omega
            have he : R⟦1⟧ = Pred R := by
              by_cases hz0 : entry R 0 (R.length - 1) = 0 ∧
                  entry R 1 (R.length - 1) = 0 ∧ entry R 2 (R.length - 1) = 0
              · exact oper_eq_pred_of_zero 1 hL hz0
              · exact oper_eq_pred_of_noParent 1 hL hz0 hp
            rw [he]
            unfold Pred
            rw [if_neg (by omega)]
          rw [hpred] at hop1
          exact hop1 (argOK_dropLast hR) v z u hz1 hvu htbdl
        · have hdl : R.dropLast = [] :=
            List.eq_nil_of_length_eq_zero (by simp; omega)
          rw [hdl]
          exact W_mono hvu (Om_mem_W v z)
    · -- clause 3: `domT R m`
      by_cases hpM : hasParent (p0 :: R) (srow R (R.length - 1)) R.length
      · -- the root revives the orphan: the tower
        refine A1_intro (Or.inr (Or.inl ⟨natDom_iff.mpr (Or.inr
          (by rw [hi1M, hMlen]; exact hpM)), fun n hn => ?_⟩))
        exact htow v z m u R hR hRnil hd hpM hgr hz1 hvu htb n hn
      · -- the orphan stays dead: `p_{v,z}(R)` inherits the graft clause
        have hdM : domT (p0 :: R) m := domT_cons_of_dead hRnil hd hpM
        have hmu : m < u :=
          htb (p0 :: R).length m (by rw [List.take_length]; exact hdM)
        refine A1_intro (Or.inr (Or.inr ⟨m, hmu, hdM, fun y hy hby hty => ?_⟩))
        rw [graft_cons hRnil]
        refine hgr y hy hby hty (argOK_graft hRnil hR y) v z u hz1 hvu ?_
        rw [← graft_cons hRnil]
        exact tbAll_graft (M := p0 :: R) (by simp) htb hmu hty

/-! ## `W*` から W-所属へ -/

/-- The largest subscript level occurring in a block. -/
def maxlev : TrioSeq → ℕ
  | [] => 0
  | p :: t => max (2 * p.2.1 + p.2.2) (maxlev t)

theorem le_maxlev : ∀ {S : TrioSeq}, ∀ p ∈ S, 2 * p.2.1 + p.2.2 ≤ maxlev S := by
  intro S
  induction S with
  | nil => intro p hp; simp at hp
  | cons q S ih =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact le_max_left _ _
      · exact le_trans (ih p hp) (le_max_right _ _)

theorem mem_of_Aclosed_aux (htow : TowerOK) (htbo : TbOper) :
    ∀ (N : ℕ) (M : TrioSeq), M.length ≤ N → zle1 M →
    ∀ X : Set TrioSeq, (∀ (u : ℕ) (M' : TrioSeq), Aop W u X M' → M' ∈ X) →
      M ∈ X := by
  intro N
  induction N with
  | zero =>
      intro M hM hzM X hX
      have hnil : M = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      exact hX 0 [] (Or.inl ⟨by simp, by simp [lev, entry]⟩)
  | succ N ih =>
      intro M hM hzM X hX
      by_cases hMnil : M = []
      · subst hMnil; exact hX 0 [] (Or.inl ⟨by simp, by simp [lev, entry]⟩)
      · obtain ⟨A, P, hEq, hPne, hrs, htail⟩ := split_lastMin hMnil
        subst hEq
        have hPlen : 0 < P.length := List.length_pos_iff.mpr hPne
        have hMlen : A.length + P.length ≤ N + 1 := by
          rw [List.length_append] at hM; exact hM
        by_cases hAnil : A = []
        · subst hAnil
          obtain ⟨p0, R, rfl⟩ : ∃ p0 R, P = p0 :: R := by
            cases P with
            | nil => exact absurd rfl hPne
            | cons a b => exact ⟨a, b, rfl⟩
          have hRgt : ∀ q ∈ R, p0.1 < q.1 := by
            intro q hq
            have := htail q (by simpa using hq)
            simpa [entry] using this
          have hargOK : argOK (shiftl0 p0.1 R) := by
            intro q hq
            rw [mem_shiftl0] at hq
            obtain ⟨r, hr, rfl⟩ := hq
            have := hRgt r hr
            simp only []
            omega
          have hWs : shiftl0 p0.1 R ∈ Wstar := by
            refine ih _ ?_ ?_ Wstar (Wstar_closed htow htbo)
            · rw [shiftl0_length]
              simp only [List.length_cons] at hMlen
              omega
            · intro q hq
              rw [mem_shiftl0] at hq
              obtain ⟨r, hr, rfl⟩ := hq
              exact hzM r (List.mem_append_right _ (List.mem_cons_of_mem _ hr))
          set Q : TrioSeq :=
            ((0, p0.2.1, p0.2.2) : ℕ × ℕ × ℕ) :: shiftl0 p0.1 R with hQ
          have hroot : 2 * p0.2.1 + p0.2.2 ≤ maxlev Q :=
            le_maxlev ((0, p0.2.1, p0.2.2) : ℕ × ℕ × ℕ)
              (by rw [hQ]; exact List.mem_cons_self ..)
          have htb : tbAll Q (maxlev Q) :=
            tbAll_of_lev_bound (fun p hp => le_maxlev p hp)
          have hz1 : p0.2.2 ≤ 1 :=
            hzM p0 (List.mem_append_right _ List.mem_cons_self)
          have hmem : Q ∈ W (maxlev Q) :=
            hWs hargOK p0.2.1 p0.2.2 (maxlev Q) hz1 hroot htb
          have hQeq : Q = shiftl0 p0.1 (p0 :: R) := by
            rw [hQ, shiftl0_cons]
            congr 1
            exact Prod.ext (by dsimp only; omega) rfl
          have hPsub : ∀ x ∈ (p0 :: R), p0.1 ≤ x.1 := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact le_rfl
            · exact le_of_lt (hRgt x hx)
          have hmem' : shiftl0 p0.1 (p0 :: R) ∈ W (maxlev Q) := by
            rw [← hQeq]; exact hmem
          have hP : (p0 :: R) ∈ W (maxlev Q) := by
            have h := W_shift hmem' p0.1
            rwa [shiftr01_shiftl0 hPsub] at h
          simp only [List.nil_append]
          exact A2' (fun M' h => hX (maxlev Q) M' h) hP
        · have hAlen : 0 < A.length := List.length_pos_iff.mpr hAnil
          have hAX : A ∈ X := ih A (by omega)
            (fun q hq => hzM q (List.mem_append_left _ hq)) X hX
          have hPX : P ∈ XA A X := ih P (by omega)
            (fun q hq => hzM q (List.mem_append_right _ hq)) (XA A X)
            (fun u M' h => XA_closed (fun M'' h'' => hX u M'' h'') hAX M' h)
          exact hPX hrs

/-- Every block belongs to every `A`-closed set. -/
theorem mem_of_Aclosed (htow : TowerOK) (htbo : TbOper) {X : Set TrioSeq}
    (hX : ∀ (u : ℕ) (M : TrioSeq), Aop W u X M → M ∈ X) :
    ∀ M : TrioSeq, zle1 M → M ∈ X :=
  fun M hz => mem_of_Aclosed_aux htow htbo M.length M le_rfl hz X hX

/-- Every argument block is in `W*`. -/
theorem mem_Wstar (htow : TowerOK) (htbo : TbOper) (R : TrioSeq) (hz : zle1 R) :
    R ∈ Wstar :=
  mem_of_Aclosed htow htbo (Wstar_closed htow htbo) R hz

/-- **Every block lies in `W u` as soon as `u` bounds its subscript levels.** -/
theorem mem_W_of_bound_aux (htow : TowerOK) (htbo : TbOper) :
    ∀ (N : ℕ) (M : TrioSeq), M.length ≤ N → zle1 M →
    ∀ u : ℕ, (∀ p ∈ M, 2 * p.2.1 + p.2.2 ≤ u) → M ∈ W u := by
  intro N
  induction N with
  | zero =>
      intro M hM _ u _
      have hnil : M = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      exact W_nil u
  | succ N ih =>
      intro M hM hzM u hbd
      by_cases hMnil : M = []
      · subst hMnil; exact W_nil u
      · obtain ⟨A, P, hEq, hPne, hrs, htail⟩ := split_lastMin hMnil
        subst hEq
        have hPlen : 0 < P.length := List.length_pos_iff.mpr hPne
        have hMlen : A.length + P.length ≤ N + 1 := by
          rw [List.length_append] at hM; exact hM
        obtain ⟨p0, R, hPeq⟩ : ∃ p0 R, P = p0 :: R := by
          cases P with
          | nil => exact absurd rfl hPne
          | cons a b => exact ⟨a, b, rfl⟩
        subst hPeq
        have hRgt : ∀ q ∈ R, p0.1 < q.1 := by
          intro q hq
          have := htail q (by simpa using hq)
          simpa [entry] using this
        have hargOK : argOK (shiftl0 p0.1 R) := by
          intro q hq
          rw [mem_shiftl0] at hq
          obtain ⟨r, hr, rfl⟩ := hq
          have := hRgt r hr
          simp only []
          omega
        set Q : TrioSeq :=
          ((0, p0.2.1, p0.2.2) : ℕ × ℕ × ℕ) :: shiftl0 p0.1 R with hQ
        have hQbd : ∀ p ∈ Q, 2 * p.2.1 + p.2.2 ≤ u := by
          intro p hp
          rw [hQ] at hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hbd p0 (List.mem_append_right _ List.mem_cons_self)
          · rw [mem_shiftl0] at hp
            obtain ⟨r, hr, rfl⟩ := hp
            exact hbd r (List.mem_append_right _ (List.mem_cons_of_mem _ hr))
        have hroot : 2 * p0.2.1 + p0.2.2 ≤ u :=
          hbd p0 (List.mem_append_right _ List.mem_cons_self)
        have hz1 : p0.2.2 ≤ 1 :=
          hzM p0 (List.mem_append_right _ List.mem_cons_self)
        have hmem : Q ∈ W u :=
          mem_Wstar htow htbo _
            (fun q hq => by
              rw [mem_shiftl0] at hq
              obtain ⟨r, hr, rfl⟩ := hq
              exact hzM r (List.mem_append_right _ (List.mem_cons_of_mem _ hr)))
            hargOK p0.2.1 p0.2.2 u hz1 hroot (tbAll_of_lev_bound hQbd)
        have hQeq : Q = shiftl0 p0.1 (p0 :: R) := by
          rw [hQ, shiftl0_cons]
          congr 1
          exact Prod.ext (by dsimp only; omega) rfl
        have hPsub : ∀ x ∈ (p0 :: R), p0.1 ≤ x.1 := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact le_rfl
          · exact le_of_lt (hRgt x hx)
        have hmem' : shiftl0 p0.1 (p0 :: R) ∈ W u := by
          rw [← hQeq]; exact hmem
        have hPu : (p0 :: R) ∈ W u := by
          have h := W_shift hmem' p0.1
          rwa [shiftr01_shiftl0 hPsub] at h
        by_cases hAnil : A = []
        · subst hAnil; simpa using hPu
        · have hAlen : 0 < A.length := List.length_pos_iff.mpr hAnil
          have hAu : A ∈ W u :=
            ih A (by omega) (fun q hq => hzM q (List.mem_append_left _ hq)) u
              (fun p hp => hbd p (List.mem_append_left _ hp))
          exact W_add hAu hPu hrs

theorem mem_W_of_bound (htow : TowerOK) (htbo : TbOper) (M : TrioSeq)
    (hz : zle1 M) (u : ℕ) (h : ∀ p ∈ M, 2 * p.2.1 + p.2.2 ≤ u) : M ∈ W u :=
  mem_W_of_bound_aux htow htbo M.length M le_rfl hz u h

/-- Every block lies in `W u` for `u` its maximal subscript level. -/
theorem mem_W_maxlev (htow : TowerOK) (htbo : TbOper) (M : TrioSeq)
    (hz : zle1 M) : M ∈ W (maxlev M) :=
  mem_W_of_bound htow htbo M hz (maxlev M) le_maxlev

theorem W_membership (htow : TowerOK) (htbo : TbOper) :
    ∀ M : TrioSeq, ST_TS M → ∃ u : ℕ, M ∈ W u :=
  fun M hM => ⟨maxlev M, mem_W_maxlev htow htbo M (zle1_ST_TS hM)⟩

/-- **Cofinality + the two open cores give well-foundedness of `olt` on
`ST_TS` images.** -/
theorem wf_olt_ST_TS_of_cofinality (htow : TowerOK) (htbo : TbOper)
    (hcof : ∀ {M N : TrioSeq}, ST_TS M → ST_TS N → translate N <o translate M →
      ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧)) :
    WellFounded (fun a b : TrioSeq =>
      ST_TS a ∧ ST_TS b ∧ translate a <o translate b) :=
  wf_of_cofinality_and_membership hcof (W_membership htow htbo)

end Wset

end TRIO
