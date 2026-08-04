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
  (∀ n : ℕ, 1 ≤ n → M⟦n⟧ ∈ X) ∨
  (∃ m : ℕ, m < u ∧ domT M m ∧
    ∀ z ∈ Wfam m, based z → graft M z ∈ X)

def Aset (Wfam : ℕ → Set TrioSeq) (u : ℕ) (X : Set TrioSeq) : Set TrioSeq :=
  {M | Aop Wfam u X M}

theorem Aop_mono_X {Wfam : ℕ → Set TrioSeq} {u : ℕ} {X Y : Set TrioSeq}
    {M : TrioSeq} (h : Aop Wfam u X M) (hXY : X ⊆ Y) : Aop Wfam u Y M := by
  rcases h with h | h | ⟨m, hm, hd, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl fun n hn => hXY (h n hn))
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
    rcases A with ⟨hlen, hw⟩ | hnat | ⟨m, -, hd, hgr⟩
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

/-! ## 行 1 シフト同変性

`oper` は一様な行 1 シフト `shiftr01 0 d` とも可換だが、最終列のレベルが
正である（`lev W (W.length - 1) ≠ 0`）ときに限る。行 1 を一様に持ち上げると
全零列が非全零になって `srow` が `0` から `1` に跳ぶからで、その分岐だけを
`lev ≠ 0` が凍結する。行 0 は不変、行 2 は不変、行 1 は定数ずれなので
`nextrel*` の狭義不等式も極小性条項もすべて生き残る。 -/

theorem entry_out_row {L : TrioSeq} {i p : ℕ} (hp : L.length ≤ p) :
    entry L i p = 0 := by
  unfold entry
  rw [getD_out hp]
  split_ifs <;> rfl

theorem entry0_shiftr1 {d : ℕ} (W : TrioSeq) (p : ℕ) :
    entry (shiftr01 0 d W) 0 p = entry W 0 p := by
  show ((shiftr01 0 d W).getD p (0, 0, 0)).1 = ((W.getD p (0, 0, 0)).1 : ℕ)
  rcases Nat.lt_or_ge p W.length with hp | hp
  · rw [shiftr01_getD hp]
    exact Nat.add_zero _
  · rw [getD_out (by rw [shiftr01_length]; omega), getD_out hp]

theorem entry1_shiftr1 {d : ℕ} {W : TrioSeq} {p : ℕ} (hp : p < W.length) :
    entry (shiftr01 0 d W) 1 p = entry W 1 p + d := by
  show ((shiftr01 0 d W).getD p (0, 0, 0)).2.1
    = ((W.getD p (0, 0, 0)).2.1 : ℕ) + d
  rw [shiftr01_getD hp]

theorem nextrel0_shiftr1 {d : ℕ} {W : TrioSeq} {a b : ℕ} :
    nextrel0 (shiftr01 0 d W) a b ↔ nextrel0 W a b := by
  unfold nextrel0
  rw [shiftr01_length]
  simp only [entry0_shiftr1]

theorem rtg0_shiftr1 {d : ℕ} {W : TrioSeq} {a b : ℕ} :
    Relation.ReflTransGen (nextrel0 (shiftr01 0 d W)) a b
      ↔ Relation.ReflTransGen (nextrel0 W) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih => exact ih.tail (nextrel0_shiftr1.1 hyz)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih => exact ih.tail (nextrel0_shiftr1.2 hyz)

theorem le0_shiftr1 {d : ℕ} {W : TrioSeq} {a b : ℕ} :
    le0 (shiftr01 0 d W) a b ↔ le0 W a b := by
  unfold le0
  rw [shiftr01_length, rtg0_shiftr1]

theorem nextrel1_shiftr1 {d : ℕ} {W : TrioSeq} {a b : ℕ} :
    nextrel1 (shiftr01 0 d W) a b ↔ nextrel1 W a b := by
  unfold nextrel1
  rw [shiftr01_length]
  constructor
  · rintro ⟨ha, hb, hab, hlt, hle, hmin⟩
    refine ⟨ha, hb, hab, ?_, le0_shiftr1.1 hle, ?_⟩
    · rw [entry1_shiftr1 ha, entry1_shiftr1 hb] at hlt
      omega
    · intro j hj
      have hjlt : j < W.length := hj.2.1
      have := hmin j ⟨hj.1, le0_shiftr1.2 hj.2⟩
      rw [entry1_shiftr1 hb, entry1_shiftr1 hjlt] at this
      omega
  · rintro ⟨ha, hb, hab, hlt, hle, hmin⟩
    refine ⟨ha, hb, hab, ?_, le0_shiftr1.2 hle, ?_⟩
    · rw [entry1_shiftr1 ha, entry1_shiftr1 hb]
      omega
    · intro j hj
      have hj' := le0_shiftr1.1 hj.2
      have := hmin j ⟨hj.1, hj'⟩
      rw [entry1_shiftr1 hb, entry1_shiftr1 hj'.1]
      omega

theorem le1_shiftr1 {d : ℕ} {W : TrioSeq} {a b : ℕ} :
    le1 (shiftr01 0 d W) a b ↔ le1 W a b := by
  unfold le1
  rw [shiftr01_length]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih => exact ih.tail (nextrel1_shiftr1.1 hyz)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih => exact ih.tail (nextrel1_shiftr1.2 hyz)

theorem nextrel2_shiftr1 {d : ℕ} {W : TrioSeq} {a b : ℕ} :
    nextrel2 (shiftr01 0 d W) a b ↔ nextrel2 W a b := by
  unfold nextrel2
  rw [shiftr01_length]
  simp only [entry2_shiftr01, le1_shiftr1]

theorem nextR_shiftr1 {d : ℕ} {W : TrioSeq} {i a b : ℕ} :
    nextR (shiftr01 0 d W) i a b ↔ nextR W i a b := by
  unfold nextR
  split
  · exact nextrel0_shiftr1
  · split
    · exact nextrel1_shiftr1
    · exact nextrel2_shiftr1

theorem hasParent_shiftr1 {d : ℕ} {W : TrioSeq} {i b : ℕ} :
    hasParent (shiftr01 0 d W) i b ↔ hasParent W i b := by
  unfold hasParent
  constructor
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, nextR_shiftr1.mp hj0, fun y hy => hu y (nextR_shiftr1.mpr hy)⟩
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, nextR_shiftr1.mpr hj0, fun y hy => hu y (nextR_shiftr1.mp hy)⟩

theorem parent_shiftr1 {d : ℕ} {W : TrioSeq} {i b : ℕ} :
    parent (shiftr01 0 d W) i b = parent W i b := by
  unfold parent
  congr 1
  funext j0
  exact propext nextR_shiftr1

theorem lev_shiftr1 {d : ℕ} {W : TrioSeq} {j : ℕ} (hj : j < W.length) :
    lev (shiftr01 0 d W) j = lev W j + 2 * d := by
  unfold lev
  rw [entry1_shiftr1 hj, entry2_shiftr01]
  omega

/-- The nonzero-level columns are exactly where `srow` survives a row-1 lift. -/
theorem srow_shiftr1 {d : ℕ} {W : TrioSeq} {j : ℕ} (hj : lev W j ≠ 0) :
    srow (shiftr01 0 d W) j = srow W j := by
  have hjlt : j < W.length := by
    by_contra hc
    exact hj (by unfold lev; rw [entry_out_row (by omega), entry_out_row (by omega)])
  unfold srow
  rw [entry2_shiftr01]
  by_cases h2 : 0 < entry W 2 j
  · rw [if_pos h2, if_pos h2]
  · have h1 : 0 < entry W 1 j := by
      unfold lev at hj
      omega
    rw [if_neg h2, if_neg h2, if_pos h1,
      if_pos (by rw [entry1_shiftr1 hjlt]; omega)]

theorem gcopy_shiftr1 {d : ℕ} {W : TrioSeq} {r L : ℕ} (hb : r + L ≤ W.length)
    (d0 d1 k : ℕ) :
    gcopy (shiftr01 0 d W) r L d0 d1 k = shiftr01 0 d (gcopy W r L d0 d1 k) := by
  show _ = List.map (fun p : ℕ × ℕ × ℕ => ((p.1 + 0, p.2.1 + d, p.2.2) : ℕ × ℕ × ℕ)) _
  unfold gcopy
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro j hj
  have hjlt : j < W.length := by
    have := List.mem_range'_1.1 hj
    omega
  rw [entry0_shiftr1, entry1_shiftr1 hjlt, entry2_shiftr01]
  simp only [Function.comp_apply]
  refine Prod.ext (by dsimp only; omega) (Prod.ext ?_ (by dsimp only))
  dsimp only
  by_cases hg : le1 W r j
  · rw [if_pos hg, if_pos (le1_shiftr1.mpr hg)]
    omega
  · rw [if_neg hg, if_neg (fun hc => hg (le1_shiftr1.mp hc))]
    omega

theorem gcopies_shiftr1 {d : ℕ} {W : TrioSeq} {r L : ℕ} (hb : r + L ≤ W.length)
    (d0 d1 n : ℕ) :
    gcopies (shiftr01 0 d W) r L d0 d1 n
      = shiftr01 0 d (gcopies W r L d0 d1 n) := by
  show _ = List.map (fun p : ℕ × ℕ × ℕ => ((p.1 + 0, p.2.1 + d, p.2.2) : ℕ × ℕ × ℕ)) _
  unfold gcopies
  rw [List.map_flatMap]
  refine List.flatMap_congr ?_
  intro k _
  exact gcopy_shiftr1 hb d0 d1 k

theorem Pred_shiftr1 {d : ℕ} (W : TrioSeq) :
    Pred (shiftr01 0 d W) = shiftr01 0 d (Pred W) := by
  unfold Pred
  rw [shiftr01_length]
  split_ifs with h
  · rfl
  · exact shiftr01_dropLast 0 d W

set_option maxHeartbeats 1000000 in
/-- **`oper` is row-1-shift equivariant on nonzero-level tails.** -/
theorem oper_shiftr1 {W : TrioSeq} (hlev : lev W (W.length - 1) ≠ 0) (d n : ℕ) :
    (shiftr01 0 d W)⟦n⟧ = shiftr01 0 d (W⟦n⟧) := by
  by_cases hL : W.length - 1 = 0
  · rw [oper_eq_self_of_short n (by rw [shiftr01_length]; exact hL),
      oper_eq_self_of_short n hL]
  · have hlt : W.length - 1 < W.length := by omega
    have hlenmap : (shiftr01 0 d W).length - 1 = W.length - 1 := by
      rw [shiftr01_length]
    have hLm : (shiftr01 0 d W).length - 1 ≠ 0 := by rw [shiftr01_length]; exact hL
    have hsr : srow (shiftr01 0 d W) (W.length - 1) = srow W (W.length - 1) :=
      srow_shiftr1 hlev
    have hz : ¬ (entry W 0 (W.length - 1) = 0 ∧ entry W 1 (W.length - 1) = 0 ∧
        entry W 2 (W.length - 1) = 0) := by
      rintro ⟨-, h1, h2⟩
      exact hlev (by unfold lev; omega)
    have hzM : ¬ (entry (shiftr01 0 d W) 0 ((shiftr01 0 d W).length - 1) = 0 ∧
        entry (shiftr01 0 d W) 1 ((shiftr01 0 d W).length - 1) = 0 ∧
        entry (shiftr01 0 d W) 2 ((shiftr01 0 d W).length - 1) = 0) := by
      rw [hlenmap]
      rintro ⟨-, h1, h2⟩
      rw [entry1_shiftr1 hlt] at h1
      rw [entry2_shiftr01] at h2
      exact hlev (by unfold lev; omega)
    by_cases hp : hasParent W (srow W (W.length - 1)) (W.length - 1)
    · have hpM : hasParent (shiftr01 0 d W)
          (srow (shiftr01 0 d W) ((shiftr01 0 d W).length - 1))
          ((shiftr01 0 d W).length - 1) := by
        rw [hlenmap, hsr]
        exact hasParent_shiftr1.mpr hp
      rw [oper_gcopies n hLm hzM hpM, oper_gcopies n hL hz hp, hlenmap, hsr,
        parent_shiftr1, shiftr01_take]
      have hj0lt : parent W (srow W (W.length - 1)) (W.length - 1) < W.length - 1 :=
        nextR_index_lt (parent_nextR hp)
      have hd0 : entry (shiftr01 0 d W) 0 (W.length - 1)
          - entry (shiftr01 0 d W) 0
              (parent W (srow W (W.length - 1)) (W.length - 1))
          = entry W 0 (W.length - 1)
            - entry W 0 (parent W (srow W (W.length - 1)) (W.length - 1)) := by
        rw [entry0_shiftr1, entry0_shiftr1]
      have he1 := entry1_shiftr1 (d := d) (W := W) hlt
      have he1' := entry1_shiftr1 (d := d) (W := W)
        (p := parent W (srow W (W.length - 1)) (W.length - 1)) (by omega)
      have hd1 : entry (shiftr01 0 d W) 1 (W.length - 1)
          - entry (shiftr01 0 d W) 1
              (parent W (srow W (W.length - 1)) (W.length - 1))
          = entry W 1 (W.length - 1)
            - entry W 1 (parent W (srow W (W.length - 1)) (W.length - 1)) := by
        rw [he1, he1']
        omega
      rw [hd0, hd1, gcopies_shiftr1 (by omega), shiftr01_append]
    · have hpM : ¬ hasParent (shiftr01 0 d W)
          (srow (shiftr01 0 d W) ((shiftr01 0 d W).length - 1))
          ((shiftr01 0 d W).length - 1) := by
        rw [hlenmap, hsr]
        intro hh
        exact hp (hasParent_shiftr1.mp hh)
      rw [oper_eq_pred_of_noParent n hL hz hp,
        oper_eq_pred_of_noParent n hLm hzM hpM, Pred_shiftr1]

/-! ## 前置切片で決まる先祖関係

`nextrel0`/`nextrel1` の全条件は添字 `≤ j1` の列しか見ないので、行き先が
前置切片の中にあるかぎり `le0`/`le1` は切片で計算してよい。ガード付き
行 1 リフト `Lift1` を `take`/`dropLast` と交換させるのに使う。 -/

theorem entry_take {X : TrioSeq} {l i j : ℕ} (hj : j < l) :
    entry (X.take l) i j = entry X i j := by
  unfold entry
  have h : (X.take l).getD j (0, 0, 0) = X.getD j (0, 0, 0) := by
    rcases Nat.lt_or_ge j X.length with hx | hx
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [List.length_take]; omega),
        List.getElem?_eq_getElem hx, List.getElem_take]
    · rw [getD_out (by rw [List.length_take]; omega), getD_out hx]
  rw [h]

theorem nextrel0_take {X : TrioSeq} {l a b : ℕ} (hl : l ≤ X.length) (hb : b < l) :
    nextrel0 (X.take l) a b ↔ nextrel0 X a b := by
  have hlen : (X.take l).length = l := by rw [List.length_take]; omega
  unfold nextrel0
  rw [hlen]
  constructor
  · rintro ⟨ha, hb', hab, hlt, hmin⟩
    refine ⟨by omega, by omega, hab, ?_, ?_⟩
    · rw [entry_take (by omega : a < l), entry_take hb] at hlt; exact hlt
    · intro j hj
      have := hmin j hj
      rw [entry_take hb, entry_take (by omega : j < l)] at this
      exact this
  · rintro ⟨ha, hb', hab, hlt, hmin⟩
    refine ⟨by omega, hb, hab, ?_, ?_⟩
    · rw [entry_take (by omega : a < l), entry_take hb]; exact hlt
    · intro j hj
      have := hmin j hj
      rw [entry_take hb, entry_take (by omega : j < l)]
      exact this

theorem rtg0_le {X : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 X) a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | @tail y z _ hyz ih => exact le_trans ih (le_of_lt hyz.2.2.1)

theorem rtg0_take_mp {X : TrioSeq} {l : ℕ} (hl : l ≤ X.length) {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (X.take l)) a b) :
    Relation.ReflTransGen (nextrel0 X) a b := by
  have hlen : (X.take l).length = l := by rw [List.length_take]; omega
  induction h with
  | refl => exact .refl
  | @tail y z _ hyz ih =>
      exact ih.tail ((nextrel0_take hl (by have := hyz.2.1; omega)).1 hyz)

theorem rtg0_take_mpr {X : TrioSeq} {l : ℕ} (hl : l ≤ X.length) {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 X) a b) :
    b < l → Relation.ReflTransGen (nextrel0 (X.take l)) a b := by
  induction h with
  | refl => intro _; exact .refl
  | @tail y z _ hyz ih =>
      intro hz
      exact (ih (by have := hyz.2.2.1; omega)).tail ((nextrel0_take hl hz).2 hyz)

theorem le0_take {X : TrioSeq} {l a b : ℕ} (hl : l ≤ X.length) (hb : b < l) :
    le0 (X.take l) a b ↔ le0 X a b := by
  have hlen : (X.take l).length = l := by rw [List.length_take]; omega
  unfold le0
  rw [hlen]
  constructor
  · rintro ⟨ha, -, hr⟩
    exact ⟨by omega, by omega, rtg0_take_mp hl hr⟩
  · rintro ⟨-, -, hr⟩
    exact ⟨by have := rtg0_le hr; omega, hb, rtg0_take_mpr hl hr hb⟩

theorem nextrel1_take {X : TrioSeq} {l a b : ℕ} (hl : l ≤ X.length) (hb : b < l) :
    nextrel1 (X.take l) a b ↔ nextrel1 X a b := by
  have hlen : (X.take l).length = l := by rw [List.length_take]; omega
  unfold nextrel1
  rw [hlen]
  constructor
  · rintro ⟨ha, -, hab, hlt, hle, hmin⟩
    refine ⟨by omega, by omega, hab, ?_, (le0_take hl hb).1 hle, ?_⟩
    · rw [entry_take (by omega : a < l), entry_take hb] at hlt; exact hlt
    · intro j hj
      have hjb : j ≤ b := rtg0_le hj.2.2.2
      have := hmin j ⟨hj.1, (le0_take hl hb).2 hj.2⟩
      rw [entry_take hb, entry_take (by omega : j < l)] at this
      exact this
  · rintro ⟨ha, -, hab, hlt, hle, hmin⟩
    refine ⟨by omega, hb, hab, ?_, (le0_take hl hb).2 hle, ?_⟩
    · rw [entry_take (by omega : a < l), entry_take hb]; exact hlt
    · intro j hj
      have hjb : j ≤ b := rtg0_le ((le0_take hl hb).1 hj.2).2.2
      have := hmin j ⟨hj.1, (le0_take hl hb).1 hj.2⟩
      rw [entry_take hb, entry_take (by omega : j < l)]
      exact this

theorem rtg1_le {X : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel1 X) a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | @tail y z _ hyz ih => exact le_trans ih (le_of_lt hyz.2.2.1)

theorem rtg1_take_mp {X : TrioSeq} {l : ℕ} (hl : l ≤ X.length) {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel1 (X.take l)) a b) :
    Relation.ReflTransGen (nextrel1 X) a b := by
  have hlen : (X.take l).length = l := by rw [List.length_take]; omega
  induction h with
  | refl => exact .refl
  | @tail y z _ hyz ih =>
      exact ih.tail ((nextrel1_take hl (by have := hyz.2.1; omega)).1 hyz)

theorem rtg1_take_mpr {X : TrioSeq} {l : ℕ} (hl : l ≤ X.length) {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel1 X) a b) :
    b < l → Relation.ReflTransGen (nextrel1 (X.take l)) a b := by
  induction h with
  | refl => intro _; exact .refl
  | @tail y z _ hyz ih =>
      intro hz
      exact (ih (by have := hyz.2.2.1; omega)).tail ((nextrel1_take hl hz).2 hyz)

theorem le1_take {X : TrioSeq} {l a b : ℕ} (hl : l ≤ X.length) (hb : b < l) :
    le1 (X.take l) a b ↔ le1 X a b := by
  have hlen : (X.take l).length = l := by rw [List.length_take]; omega
  unfold le1
  rw [hlen]
  constructor
  · rintro ⟨ha, -, hr⟩
    exact ⟨by omega, by omega, rtg1_take_mp hl hr⟩
  · rintro ⟨-, -, hr⟩
    exact ⟨by have := rtg1_le hr; omega, hb, rtg1_take_mpr hl hr hb⟩

/-! ## ガード付き行 1 リフト `Lift1`

`Lift1 X d` は行 1 を `d` だけ、根 `0` の行 1 錐 `le1 X 0 ·` の上でだけ持ち上げる。
`oper_root_tower` の `glift M L 0 d` は塔の中では（コピー周期性により）これに
一致するので、`W*` はこの**内在的**なリフトで閉じていればよい。 -/

open Classical in
noncomputable def Lift1 (X : TrioSeq) (d : ℕ) : TrioSeq :=
  (List.range X.length).map fun i =>
    ((entry X 0 i, entry X 1 i + (if le1 X 0 i then d else 0),
      entry X 2 i) : ℕ × ℕ × ℕ)

@[simp] theorem Lift1_nil (d : ℕ) : Lift1 ([] : TrioSeq) d = [] := rfl

@[simp] theorem Lift1_length (X : TrioSeq) (d : ℕ) :
    (Lift1 X d).length = X.length := by simp [Lift1]

open Classical in
theorem Lift1_getD {X : TrioSeq} {d i : ℕ} (hi : i < X.length) :
    (Lift1 X d).getD i (0, 0, 0)
      = ((entry X 0 i, entry X 1 i + (if le1 X 0 i then d else 0),
          entry X 2 i) : ℕ × ℕ × ℕ) := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [Lift1_length]; exact hi)]
  unfold Lift1
  simp only [List.getElem_map, List.getElem_range]
  rfl

theorem entry0_Lift1 (X : TrioSeq) (d i : ℕ) :
    entry (Lift1 X d) 0 i = entry X 0 i := by
  show ((Lift1 X d).getD i (0, 0, 0)).1 = ((X.getD i (0, 0, 0)).1 : ℕ)
  rcases Nat.lt_or_ge i X.length with hi | hi
  · rw [Lift1_getD hi]; rfl
  · rw [getD_out (by rw [Lift1_length]; omega), getD_out hi]

theorem entry2_Lift1 (X : TrioSeq) (d i : ℕ) :
    entry (Lift1 X d) 2 i = entry X 2 i := by
  show ((Lift1 X d).getD i (0, 0, 0)).2.2 = ((X.getD i (0, 0, 0)).2.2 : ℕ)
  rcases Nat.lt_or_ge i X.length with hi | hi
  · rw [Lift1_getD hi]; rfl
  · rw [getD_out (by rw [Lift1_length]; omega), getD_out hi]

open Classical in
theorem entry1_Lift1 {X : TrioSeq} {d i : ℕ} (hi : i < X.length) :
    entry (Lift1 X d) 1 i = entry X 1 i + (if le1 X 0 i then d else 0) := by
  show ((Lift1 X d).getD i (0, 0, 0)).2.1 = _
  rw [Lift1_getD hi]

theorem entry_triple {X : TrioSeq} {i : ℕ} (hi : i < X.length) :
    ((entry X 0 i, entry X 1 i, entry X 2 i) : ℕ × ℕ × ℕ) = X[i] := by
  have h : X.getD i (0, 0, 0) = X[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  show (((X.getD i (0, 0, 0)).1, (X.getD i (0, 0, 0)).2.1,
    (X.getD i (0, 0, 0)).2.2) : ℕ × ℕ × ℕ) = X[i]
  rw [h]

@[simp] theorem Lift1_zero (X : TrioSeq) : Lift1 X 0 = X := by
  classical
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hiX : i < X.length := h2
    have hA : (Lift1 X 0)[i] = ((entry X 0 i,
        entry X 1 i + (if le1 X 0 i then 0 else 0), entry X 2 i) : ℕ × ℕ × ℕ) := by
      unfold Lift1
      simp only [List.getElem_map, List.getElem_range]
    rw [hA]
    simp only [Nat.add_zero, ite_self]
    exact entry_triple hiX

theorem based_Lift1 {X : TrioSeq} (d : ℕ) (h : based X) : based (Lift1 X d) := by
  unfold based at h ⊢
  rw [entry0_Lift1]
  exact h

theorem Lift1_take {X : TrioSeq} {d l : ℕ} (hl : l ≤ X.length) :
    (Lift1 X d).take l = Lift1 (X.take l) d := by
  classical
  have hlen : (X.take l).length = l := by rw [List.length_take]; omega
  unfold Lift1
  rw [← List.map_take, List.take_range, Nat.min_eq_left hl, hlen]
  refine List.map_congr_left ?_
  intro i hi
  have hil : i < l := List.mem_range.1 hi
  rw [entry_take hil, entry_take hil, entry_take hil,
    if_congr (le1_take hl hil) rfl rfl]

theorem Lift1_dropLast {X : TrioSeq} {d : ℕ} :
    (Lift1 X d).dropLast = Lift1 X.dropLast d := by
  rw [List.dropLast_eq_take, List.dropLast_eq_take, Lift1_length,
    Lift1_take (by omega)]

/-! ### 錐の骨格

行 0 も行 1 も「親」は一意（`nextrel0/1_uniq_src`）なので、祖先鎖は線形。
`Lift1` は行 0 を触らないので `nextrel0`/`le0` はそのまま保たれる。 -/

theorem nextrel0_Lift1 {X : TrioSeq} {d a b : ℕ} :
    nextrel0 (Lift1 X d) a b ↔ nextrel0 X a b := by
  unfold nextrel0
  rw [Lift1_length]
  simp only [entry0_Lift1]

theorem le0_Lift1 {X : TrioSeq} {d a b : ℕ} :
    le0 (Lift1 X d) a b ↔ le0 X a b := by
  unfold le0
  rw [Lift1_length]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih => exact ih.tail (nextrel0_Lift1.1 hyz)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih => exact ih.tail (nextrel0_Lift1.2 hyz)

/-- The row-0 predecessor of a column is unique: a later candidate would
violate the minimality clause of the earlier one. -/
theorem nextrel0_uniq_src {X : TrioSeq} {a a' b : ℕ}
    (h : nextrel0 X a b) (h' : nextrel0 X a' b) : a = a' := by
  by_contra hne
  rcases Nat.lt_or_ge a a' with hlt | hge
  · have h1 := h.2.2.2.2 a' ⟨hlt, h'.2.2.1⟩
    have h2 := h'.2.2.2.1
    omega
  · have hlt : a' < a := by omega
    have h1 := h'.2.2.2.2 a ⟨hlt, h.2.2.1⟩
    have h2 := h.2.2.2.1
    omega

/-- The row-1 predecessor of a column is unique. -/
theorem nextrel1_uniq_src {X : TrioSeq} {a a' b : ℕ}
    (h : nextrel1 X a b) (h' : nextrel1 X a' b) : a = a' := by
  by_contra hne
  rcases Nat.lt_or_ge a a' with hlt | hge
  · have h1 := h.2.2.2.2.2 a' ⟨hlt, h'.2.2.2.2.1⟩
    have h2 := h'.2.2.2.1
    omega
  · have hlt : a' < a := by omega
    have h1 := h'.2.2.2.2.2 a ⟨hlt, h.2.2.2.2.1⟩
    have h2 := h.2.2.2.1
    omega

/-- Row-0 ancestry is linear: two ancestors of the same column are comparable. -/
theorem le0_of_le0_le0 {X : TrioSeq} {a k b : ℕ}
    (ha : le0 X a b) (hk : le0 X k b) (hak : a < k) : le0 X a k := by
  obtain ⟨-, -, ha⟩ := ha
  obtain ⟨hkl, -, hk⟩ := hk
  have key : ∀ {c : ℕ}, Relation.ReflTransGen (nextrel0 X) k c →
      Relation.ReflTransGen (nextrel0 X) a c →
      Relation.ReflTransGen (nextrel0 X) a k := by
    intro c hkc
    induction hkc with
    | refl => intro h; exact h
    | @tail y z hky hyz ih =>
        intro hac
        cases hac with
        | refl =>
            have h1 : k ≤ y := rtg0_le hky
            have h2 : y < a := hyz.2.2.1
            exact absurd h1 (by omega)
        | @tail y' _ hay' hy'z =>
            have hyy : y' = y := nextrel0_uniq_src hy'z hyz
            subst hyy
            exact ih hay'
  exact ⟨by have := rtg0_le (key hk ha); omega, hkl, key hk ha⟩

theorem le0_refl {X : TrioSeq} {a : ℕ} (h : a < X.length) : le0 X a a :=
  ⟨h, h, .refl⟩

theorem le0_trans {X : TrioSeq} {a b c : ℕ} (h1 : le0 X a b) (h2 : le0 X b c) :
    le0 X a c := ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩

theorem le1_trans {X : TrioSeq} {a b c : ℕ} (h1 : le1 X a b) (h2 : le1 X b c) :
    le1 X a c := ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩

/-- Every column that sits row-0 above `j` and strictly below it in row 1 has a
row-1 predecessor of `j` at or above it. -/
theorem nextrel1_exists {X : TrioSeq} {a j : ℕ} (hj : j < X.length)
    (ha : le0 X a j) (haj : a < j) (hlt : entry X 1 a < entry X 1 j) :
    ∃ c, nextrel1 X c j ∧ a ≤ c := by
  classical
  set P : ℕ → Prop := fun k => le0 X k j ∧ entry X 1 k < entry X 1 j with hP
  have hPa : P a := ⟨ha, hlt⟩
  have haj1 : a ≤ j - 1 := by omega
  have hspec := Nat.findGreatest_spec (P := P) haj1 hPa
  have hle := Nat.findGreatest_le (P := P) (j - 1)
  have hge := Nat.le_findGreatest haj1 hPa
  refine ⟨Nat.findGreatest P (j - 1), ⟨hspec.1.1, hj, by omega, hspec.2,
    hspec.1, ?_⟩, hge⟩
  intro j' hj'
  have hj'le : j' ≤ j := rtg0_le hj'.2.2.2
  rcases Nat.eq_or_lt_of_le hj'le with rfl | hlt'
  · exact le_rfl
  · by_contra hcon
    push_neg at hcon
    exact Nat.findGreatest_is_greatest (P := P) hj'.1 (by omega) ⟨hj'.2, hcon⟩

/-- If `a` is row-1 strictly below every row-0 ancestor of `k` after it, then `a`
is a row-1 ancestor of `k`. -/
theorem le1_gen {X : TrioSeq} {a : ℕ} : ∀ k : ℕ, a < k → k < X.length →
    le0 X a k → (∀ j, a < j → le0 X j k → entry X 1 a < entry X 1 j) →
    le1 X a k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hak hkl hle0 hmin
    have hlt : entry X 1 a < entry X 1 k := hmin k hak (le0_refl hkl)
    obtain ⟨c, hc, hac⟩ := nextrel1_exists hkl hle0 hak hlt
    rcases Nat.eq_or_lt_of_le hac with rfl | hlt2
    · exact ⟨hc.1, hkl, Relation.ReflTransGen.single hc⟩
    · have hck : c < k := hc.2.2.1
      have hle0ck : le0 X c k := hc.2.2.2.2.1
      have hsub : le1 X a c :=
        ih c hck hlt2 hc.1 (le0_of_le0_le0 hle0 hle0ck hlt2)
          (fun j hj hjc => hmin j hj (le0_trans hjc hle0ck))
      exact ⟨hsub.1, hkl, hsub.2.2.tail hc⟩

/-- Everything squeezed between a row-1 edge `a → b` (along row-0 ancestry) is a
row-1 descendant of `a`. -/
theorem le1_of_between {X : TrioSeq} {a b k : ℕ} (h : nextrel1 X a b)
    (hak : a < k) (hkb : le0 X k b) : le1 X a k := by
  refine le1_gen k hak hkb.1 (le0_of_le0_le0 h.2.2.2.2.1 hkb hak) ?_
  intro j hj hjk
  have h1 := h.2.2.2.2.2 j ⟨hj, le0_trans hjk hkb⟩
  have h2 := h.2.2.2.1
  omega

theorem le1_cone_up {X : TrioSeq} {i j : ℕ} (h : le1 X 0 i)
    (hn : nextrel1 X i j) : le1 X 0 j := ⟨h.1, hn.2.1, h.2.2.tail hn⟩

theorem le1_cone_down {X : TrioSeq} {i j : ℕ} (h : le1 X 0 j)
    (hn : nextrel1 X i j) : le1 X 0 i := by
  obtain ⟨h0, -, hr⟩ := h
  cases hr with
  | refl => exact absurd hn.2.2.1 (by omega)
  | @tail c _ hc hcj =>
      have hci : c = i := nextrel1_uniq_src hcj hn
      subst hci
      exact ⟨h0, hn.1, hc⟩

/-- **`Lift1` preserves the row-1 edge relation.**  Raising the cone of the root
by a constant moves both ends of every row-1 edge together, and the minimality
clause survives because anything squeezed under the edge is itself in the cone
(`le1_of_between`). -/
theorem nextrel1_Lift1 {X : TrioSeq} {d a b : ℕ} :
    nextrel1 (Lift1 X d) a b ↔ nextrel1 X a b := by
  classical
  have key : ∀ {a b : ℕ}, nextrel1 X a b → nextrel1 (Lift1 X d) a b := by
    intro a b h
    have hal := h.1
    have hbl := h.2.1
    have hcone : le1 X 0 a ↔ le1 X 0 b :=
      ⟨fun hc => le1_cone_up hc h, fun hc => le1_cone_down hc h⟩
    refine ⟨by rw [Lift1_length]; exact hal, by rw [Lift1_length]; exact hbl,
      h.2.2.1, ?_, le0_Lift1.mpr h.2.2.2.2.1, ?_⟩
    · rw [entry1_Lift1 hal, entry1_Lift1 hbl]
      have hlt := h.2.2.2.1
      by_cases hb : le1 X 0 b
      · rw [if_pos (hcone.mpr hb), if_pos hb]; omega
      · rw [if_neg (fun hc => hb (hcone.mp hc)), if_neg hb]; omega
    · intro j hj
      have hj0 : le0 X j b := le0_Lift1.mp hj.2
      have hjl : j < X.length := hj0.1
      have hjmin := h.2.2.2.2.2 j ⟨hj.1, hj0⟩
      rw [entry1_Lift1 hbl, entry1_Lift1 hjl]
      by_cases hb : le1 X 0 b
      · have hja : le1 X a j := le1_of_between h hj.1 hj0
        have hj0c : le1 X 0 j := le1_trans (le1_cone_down hb h) hja
        rw [if_pos hb, if_pos hj0c]; omega
      · rw [if_neg hb]; omega
  refine ⟨fun h => ?_, key⟩
  have hal : a < X.length := by have := h.1; rwa [Lift1_length] at this
  have hbl : b < X.length := by have := h.2.1; rwa [Lift1_length] at this
  have hab := h.2.2.1
  have hex : ∃ c, nextrel1 X c b := by
    by_cases hb : le1 X 0 b
    · obtain ⟨-, -, hr⟩ := hb
      cases hr with
      | refl => exact absurd hab (by omega)
      | @tail c _ _ hcb => exact ⟨c, hcb⟩
    · have hlt := h.2.2.2.1
      rw [entry1_Lift1 hal, entry1_Lift1 hbl, if_neg hb] at hlt
      obtain ⟨c, hc, -⟩ := nextrel1_exists hbl (le0_Lift1.mp h.2.2.2.2.1) hab
        (by split_ifs at hlt <;> omega)
      exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hex
  have hca : c = a := nextrel1_uniq_src (key hc) h
  subst hca
  exact hc

theorem le1_Lift1 {X : TrioSeq} {d a b : ℕ} :
    le1 (Lift1 X d) a b ↔ le1 X a b := by
  unfold le1
  rw [Lift1_length]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih => exact ih.tail (nextrel1_Lift1.1 hyz)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih => exact ih.tail (nextrel1_Lift1.2 hyz)

theorem nextrel2_Lift1 {X : TrioSeq} {d a b : ℕ} :
    nextrel2 (Lift1 X d) a b ↔ nextrel2 X a b := by
  unfold nextrel2
  rw [Lift1_length]
  simp only [entry2_Lift1, le1_Lift1]

theorem nextR_Lift1 {X : TrioSeq} {d i a b : ℕ} :
    nextR (Lift1 X d) i a b ↔ nextR X i a b := by
  unfold nextR
  split
  · exact nextrel0_Lift1
  · split
    · exact nextrel1_Lift1
    · exact nextrel2_Lift1

theorem hasParent_Lift1 {X : TrioSeq} {d i b : ℕ} :
    hasParent (Lift1 X d) i b ↔ hasParent X i b := by
  unfold hasParent
  constructor
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, nextR_Lift1.mp hj0, fun y hy => hu y (nextR_Lift1.mpr hy)⟩
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, nextR_Lift1.mpr hj0, fun y hy => hu y (nextR_Lift1.mp hy)⟩

theorem parent_Lift1 {X : TrioSeq} {d i b : ℕ} :
    parent (Lift1 X d) i b = parent X i b := by
  unfold parent
  congr 1
  funext j0
  exact propext nextR_Lift1

/-- `srow` survives the lift: a lifted non-root column is in the cone, hence has
strictly positive row 1 already. -/
theorem srow_Lift1 {X : TrioSeq} {d j : ℕ} (hj : j ≠ 0) :
    srow (Lift1 X d) j = srow X j := by
  classical
  unfold srow
  rw [entry2_Lift1]
  by_cases h2 : 0 < entry X 2 j
  · rw [if_pos h2, if_pos h2]
  · rw [if_neg h2, if_neg h2]
    rcases Nat.lt_or_ge j X.length with hjl | hjl
    · rw [entry1_Lift1 hjl]
      by_cases hc : le1 X 0 j
      · have hpos : 0 < entry X 1 j := by
          obtain ⟨-, -, hr⟩ := hc
          cases hr with
          | refl => exact absurd rfl hj
          | @tail c _ hc0 hcj =>
              have := hcj.2.2.2.1
              omega
        rw [if_pos hc, if_pos (by omega : 0 < entry X 1 j + d),
          if_pos hpos]
      · rw [if_neg hc, Nat.add_zero]
    · have h1 : entry X 1 j = 0 := entry_out_row hjl
      have h1' : entry (Lift1 X d) 1 j = 0 :=
        entry_out_row (by rw [Lift1_length]; exact hjl)
      rw [h1, h1']

open Classical in
theorem lev_Lift1_of_cone {X : TrioSeq} {d j : ℕ} (hj : j < X.length) :
    lev (Lift1 X d) j = lev X j + 2 * (if le1 X 0 j then d else 0) := by
  classical
  unfold lev
  rw [entry1_Lift1 hj, entry2_Lift1]
  omega

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
    rcases A with ⟨hl, hw⟩ | hop | ⟨m, hm, hd, hgr⟩
    · refine Or.inl ⟨by rw [shiftr01_length]; exact hl, ?_⟩
      rw [lev_shiftr01]
      exact hw
    · exact Or.inr (Or.inl fun n hn => by
        rw [oper_shiftr01]
        exact hop n hn)
    · refine Or.inr (Or.inr ⟨m, hm, domT_shiftr01.mpr hd, fun z hz hb => ?_⟩)
      have hne : N ≠ [] := by rintro rfl; exact not_domT_nil m hd
      rw [graft_shiftr01 hne]
      exact hgr z hz hb
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
    rcases AB with ⟨hl, hw⟩ | hop | ⟨m, hm, hd, hgr⟩
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
        refine hX _ (Or.inr (Or.inl fun n hn => ?_))
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
      · refine hX _ (Or.inr (Or.inl fun n hn => ?_))
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
        fun z hz hbz => ?_⟩))
      rw [graft_append hBnil]
      refine hgr z hz hbz ?_
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
    intro y hy _
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
  · rcases hA with ⟨hl, -⟩ | hop | ⟨m, -, hd, hgr⟩
    · exact absurd (by omega : M.length - 1 = 0) hshort
    · exact hop n hn
    · rw [oper_eq_graft_nil_of_domT (n := n) (by omega) hd]
      exact hgr [] (W_nil m) based_nil

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
`M = p_{v,z}(R)` lands in **every** stage `a` above its own root level.

The point of quantifying over all `a` is that one and the same block is provable
at different stages by *different* clauses: at a stage above its trailing orphan
by the graft clause, and at a lower stage by the successor clause.  The tower
branch consumes the low end (`tow k ∈ W m`, available because a tower always has
`2v+z ≤ m`), while the graft branch produces the high end.  This is what makes
the global `tbAll` bookkeeping — and with it the whole "junk below `m`" problem —
unnecessary. -/
def Wstar : Set TrioSeq :=
  {R | argOK R → ∀ v z a : ℕ, z ≤ 1 → 2 * v + z ≤ a →
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W a}

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


/-! ## タワー: `srow = 1` の枝 -/

theorem graft_eq_shift (M y : TrioSeq) :
    graft M y = M.dropLast ++ shiftr01 (entry M 0 (M.length - 1)) 0 y := by
  unfold graft shiftr01
  refine congrArg _ (List.map_congr_left ?_)
  intro p _
  exact Prod.ext rfl (Prod.ext (by dsimp only; omega) rfl)

theorem shiftr01_comp (b c : ℕ) (X : TrioSeq) :
    shiftr01 b 0 (shiftr01 c 0 X) = shiftr01 (b + c) 0 X := by
  unfold shiftr01
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro p _
  simp only [Function.comp_apply]
  refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp <;> omega

@[simp] theorem shiftr01_zero (X : TrioSeq) : shiftr01 0 0 X = X := by
  unfold shiftr01
  conv_rhs => rw [← List.map_id X]
  refine List.map_congr_left ?_
  intro p _
  simp

/-- The root is the parent whenever it is a parent at all and `R`'s own trailing
column is an orphan inside `R`. -/
theorem parent_cons_eq_zero {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hd : domT R m)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length = 0 := by
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set i1 := srow R (R.length - 1) with hi1
  have hnr := parent_nextR hpM
  by_contra hq
  obtain ⟨q', hq'⟩ : ∃ q', parent (p0 :: R) i1 R.length = q' + 1 :=
    ⟨parent (p0 :: R) i1 R.length - 1, by omega⟩
  rw [hq'] at hnr
  refine hd.2 ⟨q', (nextR_cons_last hRne i1 q').mp hnr, ?_⟩
  intro y hy
  have h1 := hpM.unique ((nextR_cons_last hRne i1 y).mpr hy) hnr
  omega

/-- The **tower**: `t_0 = 0`, `t_{k+1} = p_{v,z}(R[t_k])`. -/
def tow (v z : ℕ) (R : TrioSeq) : ℕ → TrioSeq
  | 0 => []
  | k + 1 => ((0, v, z) : ℕ × ℕ × ℕ) :: graft R (tow v z R k)

theorem based_tow (v z : ℕ) (R : TrioSeq) : ∀ k, based (tow v z R k)
  | 0 => by simp [tow]
  | _ + 1 => based_cons v z _

/-- **Tower identity for a row-1 collapse.** -/
theorem oper_cons_tower1 {v z m n : ℕ} {R : TrioSeq}
    (hR : argOK R) (hRne : R ≠ []) (hd : domT R m)
    (hi1 : srow R (R.length - 1) = 1)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ = tow v z R n := by
  classical
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set M : TrioSeq := p0 :: R with hMdef
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : M.length - 1 = R.length := by rw [hMdef]; simp
  have hE : ∀ i, entry M i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  have hL : M.length - 1 ≠ 0 := by rw [hMlen]; omega
  have hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -, -⟩; rw [hE 0] at h1; omega
  have hsrM : srow M (M.length - 1) = 1 := by
    rw [hMlen, hMdef, srow_cons_last hRne, hi1]
  have hpM' : hasParent M (srow M (M.length - 1)) (M.length - 1) := by
    rw [hsrM, hMlen, hMdef, ← hi1]
    exact hpM
  have hpar0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0 := by
    rw [hsrM, hMlen]
    have := parent_cons_eq_zero (v := v) (z := z) hRne hd hpM
    rwa [hi1] at this
  have hroot0 : entry M 0 0 = 0 := by rw [hMdef]; simp [entry, hp0]
  set d0 : ℕ := entry M 0 (M.length - 1) with hd0
  have key : ∀ k, gcopy M 0 (M.length - 1) d0 0 k
      = shiftr01 (k * d0) 0 M.dropLast := by
    intro k
    have hdl : M.dropLast = seg M 0 (M.length - 1) := by
      rw [seg_zero_eq_take _ (by omega), List.dropLast_eq_take]
    rw [hdl]
    unfold gcopy seg shiftr01
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro j _
    simp only [Function.comp_apply, Nat.mul_zero, ite_self, Nat.add_zero]
  have hgc : ∀ k, gcopies M 0 (M.length - 1) d0 0 k = tow v z R k := by
    intro k
    induction k with
    | zero => simp [gcopies, tow]
    | succ k ih =>
        unfold gcopies
        rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, key 0]
        simp only [Nat.zero_mul, shiftr01_zero]
        have hstep : ((List.range k).flatMap
              fun x => gcopy M 0 (M.length - 1) d0 0 (Nat.succ x))
            = shiftr01 d0 0 ((List.range k).flatMap
              fun x => gcopy M 0 (M.length - 1) d0 0 x) := by
          unfold shiftr01
          rw [List.map_flatMap]
          refine List.flatMap_congr ?_
          intro x _
          rw [key (Nat.succ x), key x]
          unfold shiftr01
          rw [List.map_map]
          refine List.map_congr_left ?_
          intro p _
          simp only [Function.comp_apply, Nat.succ_mul]
          refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp <;> omega
        rw [hstep]
        have : ((List.range k).flatMap fun x => gcopy M 0 (M.length - 1) d0 0 x)
            = gcopies M 0 (M.length - 1) d0 0 k := rfl
        rw [this, ih]
        show M.dropLast ++ shiftr01 d0 0 (tow v z R k) = tow v z R (k + 1)
        rw [show tow v z R (k + 1) = p0 :: graft R (tow v z R k) from rfl,
          ← graft_cons (v := v) (z := z) hRne, graft_eq_shift]
  rw [oper_gcopies n hL hz hpM', hpar0, hsrM]
  rw [if_pos (by omega : 0 < 1), if_neg (by omega : ¬ (1 < 1))]
  simp only [List.take_zero, List.nil_append, Nat.sub_zero, hroot0, Nat.sub_zero]
  exact hgc n


/-! ## ガード付きタワー（行2の崩壊） -/

theorem entry_append_left (A B : TrioSeq) {i j : ℕ} (hj : j < A.length) :
    entry (A ++ B) i j = entry A i j := by
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hj]

open Classical in
/-- The guarded lift a row-2 tower performs on one copy: row 0 rises by `d0`
everywhere, row 1 by `d1` exactly on the positions `le1`-below the root of `M`,
read modulo the copy length `L`. -/
noncomputable def glift (M : TrioSeq) (L d0 d1 : ℕ) (y : TrioSeq) : TrioSeq :=
  (List.range y.length).map fun idx =>
    ((entry y 0 idx + d0,
      entry y 1 idx + (if le1 M 0 (idx % L) then d1 else 0),
      entry y 2 idx) : ℕ × ℕ × ℕ)

@[simp] theorem glift_nil (M : TrioSeq) (L d0 d1 : ℕ) :
    glift M L d0 d1 [] = [] := rfl

@[simp] theorem glift_length (M : TrioSeq) (L d0 d1 : ℕ) (y : TrioSeq) :
    (glift M L d0 d1 y).length = y.length := by simp [glift]

open Classical in
theorem glift_getD (M : TrioSeq) (L d0 d1 : ℕ) (y : TrioSeq) {i : ℕ}
    (hi : i < y.length) :
    (glift M L d0 d1 y).getD i (0, 0, 0) =
      ((entry y 0 i + d0,
        entry y 1 i + (if le1 M 0 (i % L) then d1 else 0),
        entry y 2 i) : ℕ × ℕ × ℕ) := by
  have hlen : (glift M L d0 d1 y).length = y.length := glift_length _ _ _ _ _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  unfold glift
  simp only [List.getElem_map, List.getElem_range]
  rfl

/-- The lift distributes over a concatenation whose left part is a whole number
of copies. -/
theorem glift_append {M : TrioSeq} {L d0 d1 : ℕ} {A B : TrioSeq}
    (hA : A.length % L = 0) :
    glift M L d0 d1 (A ++ B) = glift M L d0 d1 A ++ glift M L d0 d1 B := by
  classical
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hlenAB : (glift M L d0 d1 (A ++ B)).length = A.length + B.length := by
      simp
    have hlenA : (glift M L d0 d1 A).length = A.length := glift_length _ _ _ _ _
    have hi1 : i < A.length + B.length := by rw [hlenAB] at h1; exact h1
    have hkey : ∀ (X : TrioSeq) (j : ℕ) (hj : j < X.length)
        (hj' : j < (glift M L d0 d1 X).length),
        (glift M L d0 d1 X)[j] =
          ((entry X 0 j + d0,
            entry X 1 j + (if le1 M 0 (j % L) then d1 else 0),
            entry X 2 j) : ℕ × ℕ × ℕ) := by
      intro X j hj hj'
      have h := glift_getD M L d0 d1 X hj
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at h
    rw [hkey (A ++ B) i (by simpa using hi1) h1, List.getElem_append]
    by_cases hi : i < A.length
    · rw [dif_pos (by omega), hkey A i hi (by omega)]
      simp only [entry_append_left A B hi]
    · rw [dif_neg (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, i = A.length + j := ⟨i - A.length, by omega⟩
      have hmod : (A.length + j) % L = j % L := by
        rcases Nat.eq_zero_or_pos L with rfl | hL
        · have : A.length = 0 := by simpa using hA
          rw [this, Nat.zero_add]
        · obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hA
          rw [hc, Nat.mul_add_mod]
      simp only [hlenA, Nat.add_sub_cancel_left]
      rw [hkey B j (by omega) (by simp; omega)]
      simp only [entry_append_right, hmod]

open Classical in
theorem gcopy_getD (M : TrioSeq) {L : ℕ} (d0 d1 k j : ℕ) (hj : j < L) :
    (gcopy M 0 L d0 d1 k).getD j (0, 0, 0)
      = ((entry M 0 j + k * d0,
          entry M 1 j + (if le1 M 0 j then k * d1 else 0),
          entry M 2 j) : ℕ × ℕ × ℕ) := by
  have hlen : (gcopy M 0 L d0 d1 k).length = L := gcopy_len _ _ _ _ _ _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  unfold gcopy
  simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
  rfl

/-- **One guarded copy is the lift of the previous one.** -/
theorem gcopy_succ_glift (M : TrioSeq) (L d0 d1 k : ℕ) :
    gcopy M 0 L d0 d1 (k + 1) = glift M L d0 d1 (gcopy M 0 L d0 d1 k) := by
  classical
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hiL : i < L := by simpa using h1
    have hlenk : (gcopy M 0 L d0 d1 k).length = L := gcopy_len _ _ _ _ _ _
    have hA : (gcopy M 0 L d0 d1 (k + 1))[i] =
        ((entry M 0 i + (k + 1) * d0,
          entry M 1 i + (if le1 M 0 i then (k + 1) * d1 else 0),
          entry M 2 i) : ℕ × ℕ × ℕ) := by
      have h := gcopy_getD M d0 d1 (k + 1) i hiL
      rwa [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [gcopy_len]; exact hiL)] at h
    have hB : (glift M L d0 d1 (gcopy M 0 L d0 d1 k))[i] =
        ((entry (gcopy M 0 L d0 d1 k) 0 i + d0,
          entry (gcopy M 0 L d0 d1 k) 1 i
            + (if le1 M 0 (i % L) then d1 else 0),
          entry (gcopy M 0 L d0 d1 k) 2 i) : ℕ × ℕ × ℕ) := by
      have h := glift_getD M L d0 d1 (gcopy M 0 L d0 d1 k)
        (by rw [gcopy_len]; exact hiL)
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at h
    have hg := gcopy_getD M d0 d1 k i hiL
    have hE0 : entry (gcopy M 0 L d0 d1 k) 0 i = entry M 0 i + k * d0 := by
      show ((gcopy M 0 L d0 d1 k).getD i (0, 0, 0)).1 = _
      rw [hg]
    have hE1 : entry (gcopy M 0 L d0 d1 k) 1 i
        = entry M 1 i + (if le1 M 0 i then k * d1 else 0) := by
      show ((gcopy M 0 L d0 d1 k).getD i (0, 0, 0)).2.1 = _
      rw [hg]
    have hE2 : entry (gcopy M 0 L d0 d1 k) 2 i = entry M 2 i := by
      show ((gcopy M 0 L d0 d1 k).getD i (0, 0, 0)).2.2 = _
      rw [hg]
    rw [hA, hB, hE0, hE1, hE2, Nat.mod_eq_of_lt hiL]
    simp only [Nat.succ_mul]
    by_cases h : le1 M 0 i
    · simp only [if_pos h]
      refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> dsimp only <;> omega
    · simp only [if_neg h]
      refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> dsimp only <;> omega


theorem gcopies_length (M : TrioSeq) (r L d0 d1 n : ℕ) :
    (gcopies M r L d0 d1 n).length = n * L := by
  induction n with
  | zero => simp [gcopies]
  | succ n ih =>
      unfold gcopies at ih ⊢
      rw [List.range_succ, List.flatMap_append]
      simp only [List.length_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, ih, gcopy_len, Nat.succ_mul]

theorem glift_gcopies (M : TrioSeq) (L d0 d1 : ℕ) : ∀ n,
    (List.range n).flatMap (fun k => glift M L d0 d1 (gcopy M 0 L d0 d1 k))
      = glift M L d0 d1 (gcopies M 0 L d0 d1 n) := by
  intro n
  induction n with
  | zero => simp [gcopies]
  | succ n ih =>
      have hmod : (gcopies M 0 L d0 d1 n).length % L = 0 := by
        rw [gcopies_length]
        exact Nat.mul_mod_left n L
      have hsplit : gcopies M 0 L d0 d1 (n + 1)
          = gcopies M 0 L d0 d1 n ++ gcopy M 0 L d0 d1 n := by
        unfold gcopies
        rw [List.range_succ, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [List.range_succ, List.flatMap_append, ih, hsplit,
        glift_append (M := M) (L := L) (d0 := d0) (d1 := d1) hmod]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- **The guarded tower identity**: when the bad root is the very first column,
`M⟦n+1⟧` is `M.dropLast` followed by the guarded lift of `M⟦n⟧`. -/
theorem oper_root_tower {M : TrioSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hpar : parent M (srow M (M.length - 1)) (M.length - 1) = 0) :
    M⟦n + 1⟧ = M.dropLast ++ glift M (M.length - 1)
      (if 0 < srow M (M.length - 1)
        then entry M 0 (M.length - 1) - entry M 0 0 else 0)
      (if 1 < srow M (M.length - 1)
        then entry M 1 (M.length - 1) - entry M 1 0 else 0)
      (M⟦n⟧) := by
  classical
  set L := M.length - 1 with hLdef
  set d0 := (if 0 < srow M L then entry M 0 L - entry M 0 0 else 0) with hd0
  set d1 := (if 1 < srow M L then entry M 1 L - entry M 1 0 else 0) with hd1
  have hgn : M⟦n⟧ = gcopies M 0 L d0 d1 n := by
    rw [oper_gcopies n hL hz hp, hpar]
    simp only [List.take_zero, List.nil_append, Nat.sub_zero]
    rfl
  have hgn1 : M⟦n + 1⟧ = gcopies M 0 L d0 d1 (n + 1) := by
    rw [oper_gcopies (n + 1) hL hz hp, hpar]
    simp only [List.take_zero, List.nil_append, Nat.sub_zero]
    rfl
  have hdl : gcopy M 0 L d0 d1 0 = M.dropLast := by
    rw [gcopy_zero, seg_zero_eq_take _ (by omega), ← List.dropLast_eq_take]
  have hstep : gcopies M 0 L d0 d1 (n + 1)
      = gcopy M 0 L d0 d1 0
        ++ (List.range n).flatMap (fun k => gcopy M 0 L d0 d1 (k + 1)) := by
    unfold gcopies
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  rw [hgn, hgn1, hstep, hdl]
  congr 1
  rw [← glift_gcopies M L d0 d1 n]
  refine List.flatMap_congr ?_
  intro k _
  exact gcopy_succ_glift M L d0 d1 k

/-! ### `glift` = `Lift1` on a root-parented tower

`Gtrans.gexp_guard_transport` (probe: 77460 cases) says the `le1` guard at a
mirror position equals the host guard.  With `j0 = 0` that is exactly the
statement that the **periodic** mask of `oper_root_tower`'s `glift` coincides
with the **intrinsic** cone of the expanded block. -/

open Classical in
theorem oper_eq_gexp {M : TrioSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hpar : parent M (srow M (M.length - 1)) (M.length - 1) = 0) :
    M⟦n⟧ = gexp M 0 (M.length - 1)
      (if 0 < srow M (M.length - 1)
        then entry M 0 (M.length - 1) - entry M 0 0 else 0)
      (if 1 < srow M (M.length - 1)
        then entry M 1 (M.length - 1) - entry M 1 0 else 0) n := by
  rw [oper_gcopies n hL hz hp, hpar]
  unfold gexp
  simp only [Nat.sub_zero]

open Classical in
theorem glift_eq_Lift1 {M : TrioSeq} {n t L d0 d1 : ℕ}
    (hlen : L + 1 = M.length)
    (hgexp : M⟦n⟧ = gexp M 0 L d0 d1 n)
    (hup : ∀ l, 0 < l → l ≤ L → entry M 0 0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 L = entry M 0 0 + d0)
    (hd1pos : 0 < d1) (hle1lp : le1 M 0 L) :
    glift M L 0 t (M⟦n⟧) = Lift1 (M⟦n⟧) t := by
  have hlen' : 0 + L + 1 = M.length := by omega
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with rfl | h
    · omega
    · exact h
  have hlenY : (M⟦n⟧).length = n * L := by
    rw [hgexp, gexp_length hlen']; omega
  unfold glift Lift1
  refine List.map_congr_left ?_
  intro idx hidx
  have hidxlt : idx < n * L := by
    have := List.mem_range.1 hidx
    omega
  have hk : idx / L < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidxlt)
  have hq : idx % L < L := Nat.mod_lt _ hLpos
  have hdm : idx / L * L + idx % L = idx := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod idx L
  have hguard := gexp_guard_transport (M := M) (j0 := 0) (Lb := L) (d0 := d0)
    (d1 := d1) (n := n) (k := idx / L) (q := idx % L) hlen' hk hq
    (by intro l hl0 hlL; exact hup l hl0 (by omega))
    hd0pos (by rw [Nat.zero_add]; exact hd0e) hd1pos (by rw [Nat.zero_add]; exact hle1lp)
  rw [Nat.zero_add, Nat.zero_add, hdm, ← hgexp] at hguard
  refine Prod.ext (by dsimp only; omega) (Prod.ext ?_ (by dsimp only))
  dsimp only
  by_cases hc : le1 M 0 (idx % L)
  · rw [if_pos hc, if_pos (hguard.mpr hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hguard.mp h))]

/-- Row-1 ancestry is strictly increasing in row 1. -/
theorem le1_entry1_lt {X : TrioSeq} {a b : ℕ} (h : le1 X a b) (hne : a ≠ b) :
    entry X 1 a < entry X 1 b := by
  obtain ⟨-, -, hr⟩ := h
  induction hr with
  | refl => exact absurd rfl hne
  | @tail y z hay hyz ih =>
      rcases Nat.eq_or_lt_of_le (rtg1_le hay) with rfl | hlt
      · exact hyz.2.2.2.1
      · exact lt_trans (ih (by omega)) hyz.2.2.2.1

open Classical in
theorem glift_split (M : TrioSeq) (L d0 d1 : ℕ) (y : TrioSeq) :
    glift M L d0 d1 y = shiftr01 d0 0 (glift M L 0 d1 y) := by
  unfold glift shiftr01
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro idx _
  simp only [Function.comp_apply]
  refine Prod.ext (by dsimp only; omega) (Prod.ext (by dsimp only; omega)
    (by dsimp only))

/-- **Tower identity for a row-2 collapse.**  One expansion peels the first copy
and substitutes the *guarded row-1 lift* of the previous tower. -/
theorem oper_cons_tower2 {v z m n : ℕ} {R : TrioSeq}
    (hR : argOK R) (hRne : R ≠ []) (hd : domT R m)
    (hi1 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n + 1⟧
      = ((0, v, z) : ℕ × ℕ × ℕ) ::
        graft R (Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
          (entry R 1 (R.length - 1) - v)) := by
  classical
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set M : TrioSeq := p0 :: R with hMdef
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : M.length - 1 = R.length := by rw [hMdef]; simp
  have hE : ∀ i, entry M i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  have hL : M.length - 1 ≠ 0 := by rw [hMlen]; omega
  have hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -, -⟩; rw [hE 0] at h1; omega
  have hsrM : srow M (M.length - 1) = 2 := by
    rw [hMlen, hMdef, srow_cons_last hRne, hi1]
  have hpM' : hasParent M (srow M (M.length - 1)) (M.length - 1) := by
    rw [hsrM, hMlen, hMdef, ← hi1]; exact hpM
  have hpar0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0 := by
    rw [hsrM, hMlen]
    have := parent_cons_eq_zero (v := v) (z := z) hRne hd hpM
    rwa [hi1] at this
  have hroot0 : entry M 0 0 = 0 := by rw [hMdef]; simp [entry, hp0]
  have hroot1 : entry M 1 0 = v := by rw [hMdef]; simp [entry, hp0]
  set D0 : ℕ := entry M 0 (M.length - 1) - entry M 0 0 with hD0
  set D1 : ℕ := entry M 1 (M.length - 1) - entry M 1 0 with hD1
  -- the row-2 parent supplies the row-1 guard at the tail
  have hnr := parent_nextR hpM'
  rw [hpar0, hsrM] at hnr
  have hn2 : nextrel2 M 0 (M.length - 1) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_neg (by omega)] at hnr
    exact hnr
  have hle1lp : le1 M 0 (M.length - 1) := hn2.2.2.2.2.1
  have hd1pos : 0 < D1 := by
    have := le1_entry1_lt hle1lp (by omega)
    omega
  have hd0e : entry M 0 (M.length - 1) = entry M 0 0 + D0 := by
    rw [hD0, hroot0]; omega
  have hd0pos : 0 < D0 := by
    rw [hD0, hroot0, hMlen, hE 0]; omega
  have hup : ∀ l, 0 < l → l ≤ M.length - 1 → entry M 0 0 < entry M 0 l := by
    intro l hl0 hlL
    rw [hroot0, hMdef]
    have hlt : l - 1 < R.length := by omega
    have : entry (p0 :: R) 0 l = entry R 0 (l - 1) := by
      unfold entry
      rw [hMdef] at hMlen
      show ((p0 :: R).getD l (0, 0, 0)).1 = (R.getD (l - 1) (0, 0, 0)).1
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      simp only [List.getD_cons_succ, Nat.add_sub_cancel]
    rw [this]
    exact hR _ (entry_pair_mem (B := R) hlt)
  have hgexp : M⟦n⟧ = gexp M 0 (M.length - 1) D0 D1 n := by
    have h := oper_eq_gexp (M := M) n hL hz hpM' hpar0
    rwa [hsrM, if_pos (by omega : 0 < 2), if_pos (by omega : 1 < 2)] at h
  have hglift : glift M (M.length - 1) 0 D1 (M⟦n⟧) = Lift1 (M⟦n⟧) D1 :=
    glift_eq_Lift1 (by omega) hgexp hup hd0pos hd0e hd1pos hle1lp
  have hD1val : D1 = entry R 1 (R.length - 1) - v := by
    rw [hD1, hMlen, hE 1, hroot1]
  rw [oper_root_tower n hL hz hpM' hpar0, hsrM,
    if_pos (by omega : 0 < 2), if_pos (by omega : 1 < 2), ← hD0, ← hD1,
    glift_split, hglift, hD1val]
  rw [← graft_cons (v := v) (z := z) hRne, graft_eq_shift]
  congr 2

/-! ### `Lift1` は根が親の展開と可換

コピーは `Lift1` を素通しする（`gcopy_Lift1`）ので、`(Lift1 M t)[n]` は
`M[n]` の周期リフト。`glift_eq_Lift1` と合わせて塔の同変性になる。 -/

open Classical in
theorem gcopy_Lift1 {M : TrioSeq} {L : ℕ} (hL : L ≤ M.length) (t d0 d1 k : ℕ) :
    gcopy (Lift1 M t) 0 L d0 d1 k = glift M L 0 t (gcopy M 0 L d0 d1 k) := by
  classical
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hiL : i < L := by simpa using h1
    have hiM : i < M.length := by omega
    have hA : (gcopy (Lift1 M t) 0 L d0 d1 k)[i]
        = ((entry (Lift1 M t) 0 i + k * d0,
            entry (Lift1 M t) 1 i + (if le1 (Lift1 M t) 0 i then k * d1 else 0),
            entry (Lift1 M t) 2 i) : ℕ × ℕ × ℕ) := by
      have h := gcopy_getD (Lift1 M t) d0 d1 k i hiL
      rwa [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [gcopy_len]; exact hiL)] at h
    have hB : (glift M L 0 t (gcopy M 0 L d0 d1 k))[i]
        = ((entry (gcopy M 0 L d0 d1 k) 0 i + 0,
            entry (gcopy M 0 L d0 d1 k) 1 i
              + (if le1 M 0 (i % L) then t else 0),
            entry (gcopy M 0 L d0 d1 k) 2 i) : ℕ × ℕ × ℕ) := by
      have h := glift_getD M L 0 t (gcopy M 0 L d0 d1 k)
        (by rw [gcopy_len]; exact hiL)
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at h
    have hg := gcopy_getD M d0 d1 k i hiL
    have hE0 : entry (gcopy M 0 L d0 d1 k) 0 i = entry M 0 i + k * d0 := by
      show ((gcopy M 0 L d0 d1 k).getD i (0, 0, 0)).1 = _
      rw [hg]
    have hE1 : entry (gcopy M 0 L d0 d1 k) 1 i
        = entry M 1 i + (if le1 M 0 i then k * d1 else 0) := by
      show ((gcopy M 0 L d0 d1 k).getD i (0, 0, 0)).2.1 = _
      rw [hg]
    have hE2 : entry (gcopy M 0 L d0 d1 k) 2 i = entry M 2 i := by
      show ((gcopy M 0 L d0 d1 k).getD i (0, 0, 0)).2.2 = _
      rw [hg]
    rw [hA, hB, hE0, hE1, hE2, entry0_Lift1, entry1_Lift1 hiM, entry2_Lift1,
      Nat.mod_eq_of_lt hiL]
    by_cases hc : le1 M 0 i
    · simp only [if_pos hc, if_pos (le1_Lift1.mpr hc)]
      refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> dsimp only <;> omega
    · simp only [if_neg hc, if_neg (fun h => hc (le1_Lift1.mp h))]
      refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> dsimp only <;> omega

/-- `glift` distributes over guarded copies with unrelated deltas. -/
theorem glift_gcopies' (M : TrioSeq) (L a b d0 d1 : ℕ) : ∀ n,
    (List.range n).flatMap (fun k => glift M L a b (gcopy M 0 L d0 d1 k))
      = glift M L a b (gcopies M 0 L d0 d1 n) := by
  intro n
  induction n with
  | zero => simp [gcopies]
  | succ n ih =>
      have hmod : (gcopies M 0 L d0 d1 n).length % L = 0 := by
        rw [gcopies_length]
        exact Nat.mul_mod_left n L
      have hsplit : gcopies M 0 L d0 d1 (n + 1)
          = gcopies M 0 L d0 d1 n ++ gcopy M 0 L d0 d1 n := by
        unfold gcopies
        rw [List.range_succ, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [List.range_succ, List.flatMap_append, ih, hsplit,
        glift_append (M := M) (L := L) (d0 := a) (d1 := b) hmod]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem gcopies_Lift1 {M : TrioSeq} {L : ℕ} (hL : L ≤ M.length) (t d0 d1 n : ℕ) :
    gcopies (Lift1 M t) 0 L d0 d1 n = glift M L 0 t (gcopies M 0 L d0 d1 n) := by
  rw [← glift_gcopies' M L 0 t d0 d1 n]
  unfold gcopies
  refine List.flatMap_congr ?_
  intro k _
  exact gcopy_Lift1 hL t d0 d1 k

open Classical in
/-- On a root-parented block the lift passes through the expansion as the
periodic lift. -/
theorem oper_Lift1_root {M : TrioSeq} (n t : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hpar : parent M (srow M (M.length - 1)) (M.length - 1) = 0)
    (hcone : le1 M 0 (M.length - 1)) :
    (Lift1 M t)⟦n⟧ = glift M (M.length - 1) 0 t (M⟦n⟧) := by
  classical
  set L := M.length - 1 with hLdef
  have hMpos : 0 < M.length := by omega
  have hLlt : L < M.length := by omega
  have hNlen : (Lift1 M t).length - 1 = L := by rw [Lift1_length]
  have hcone0 : le1 M 0 0 := le1_refl hMpos
  have hE0 : entry (Lift1 M t) 0 L = entry M 0 L := entry0_Lift1 _ _ _
  have hE2 : entry (Lift1 M t) 2 L = entry M 2 L := entry2_Lift1 _ _ _
  have hE1L : entry (Lift1 M t) 1 L = entry M 1 L + t := by
    rw [entry1_Lift1 hLlt, if_pos hcone]
  have hE10 : entry (Lift1 M t) 1 0 = entry M 1 0 + t := by
    rw [entry1_Lift1 hMpos, if_pos hcone0]
  have hsr : srow (Lift1 M t) L = srow M L := srow_Lift1 (by omega)
  have hzN : ¬ (entry (Lift1 M t) 0 ((Lift1 M t).length - 1) = 0 ∧
      entry (Lift1 M t) 1 ((Lift1 M t).length - 1) = 0 ∧
      entry (Lift1 M t) 2 ((Lift1 M t).length - 1) = 0) := by
    rw [hNlen]
    rintro ⟨h1, h2, h3⟩
    rw [hE0] at h1; rw [hE1L] at h2; rw [hE2] at h3
    exact hz ⟨h1, by omega, h3⟩
  have hpN : hasParent (Lift1 M t) (srow (Lift1 M t) ((Lift1 M t).length - 1))
      ((Lift1 M t).length - 1) := by
    rw [hNlen, hsr]; exact hasParent_Lift1.mpr hp
  have hparN : parent (Lift1 M t) (srow (Lift1 M t) ((Lift1 M t).length - 1))
      ((Lift1 M t).length - 1) = 0 := by
    rw [hNlen, hsr, parent_Lift1]; exact hpar
  rw [oper_gcopies n hL hz hp, hpar]
  rw [oper_gcopies n (by rw [hNlen]; exact hL) hzN hpN, hparN]
  rw [hNlen, hsr, hE0, hE1L, hE10, entry0_Lift1]
  simp only [List.take_zero, List.nil_append, Nat.sub_zero]
  have hd1 : (if 1 < srow M L then entry M 1 L + t - (entry M 1 0 + t) else 0)
      = (if 1 < srow M L then entry M 1 L - entry M 1 0 else 0) := by
    split_ifs <;> omega
  rw [hd1]
  exact gcopies_Lift1 (by omega) t _ _ n

open Classical in
/-- **Tower equivariance**: on a root-parented row-2 tower the guarded row-1
lift commutes with the expansion. -/
theorem oper_Lift1_tower {M : TrioSeq} {n t d0 d1 : ℕ}
    (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hpar : parent M (srow M (M.length - 1)) (M.length - 1) = 0)
    (hgexp : M⟦n⟧ = gexp M 0 (M.length - 1) d0 d1 n)
    (hup : ∀ l, 0 < l → l ≤ M.length - 1 → entry M 0 0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (M.length - 1) = entry M 0 0 + d0)
    (hd1pos : 0 < d1) (hle1lp : le1 M 0 (M.length - 1)) :
    (Lift1 M t)⟦n⟧ = Lift1 (M⟦n⟧) t := by
  rw [oper_Lift1_root n t hL hz hp hpar hle1lp]
  exact glift_eq_Lift1 (by omega) hgexp hup hd0pos hd0e hd1pos hle1lp

/-! ## リフト閉 `W*`

`Wstar` を**ガード付き行 1 リフトで閉じた**形に強める。`t = 0` が従来の主張。
上昇コピー塔では各コピーの根が行 1 で上昇するので、必要な段が上がっていく。
接ぎ木閉包 `hgr` は段 `m`（`k = 1`）でしか使えないが、それ以上のリフトは
`Wstar2` 自身が供給する — これが塔を閉じる仕掛け。 -/

def Wstar2 : Set TrioSeq :=
  {R | argOK R → ∀ v z a t : ℕ, z ≤ 1 → 2 * (v + t) + z ≤ a →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t ∈ W a}

/-- **The row-2 tower core, proved.**  Induction on the copy count with the lift
amount universally quantified: `hgr` is consumed only at the single stage `m`. -/
theorem towerGraft2_lift :
    ∀ (v z m : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 →
      domT R m → srow R (R.length - 1) = 2 →
      (∀ y ∈ W m, based y → graft R y ∈ Wstar2) →
      hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
        R.length →
      ∀ n s : ℕ,
        Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧) s ∈ W (2 * (v + s) + z) := by
  classical
  intro v z m R hR hRne hz1 hd hi1 hgr hpM
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set M : TrioSeq := p0 :: R with hMdef
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : M.length - 1 = R.length := by rw [hMdef]; simp
  have hE : ∀ i, entry M i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  have hL : M.length - 1 ≠ 0 := by rw [hMlen]; omega
  have hzz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -, -⟩; rw [hE 0] at h1; omega
  have hsrM : srow M (M.length - 1) = 2 := by
    rw [hMlen, hMdef, srow_cons_last hRne, hi1]
  have hpM' : hasParent M (srow M (M.length - 1)) (M.length - 1) := by
    rw [hsrM, hMlen, hMdef, ← hi1]; exact hpM
  have hpar0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0 := by
    rw [hsrM, hMlen]
    have := parent_cons_eq_zero (v := v) (z := z) hRne hd hpM
    rwa [hi1] at this
  have hroot1 : entry M 1 0 = v := by rw [hMdef]; simp [entry, hp0]
  have hroot2 : entry M 2 0 = z := by rw [hMdef]; simp [entry, hp0]
  have hnr := parent_nextR hpM'
  rw [hpar0, hsrM] at hnr
  have hn2 : nextrel2 M 0 (M.length - 1) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_neg (by omega)] at hnr
    exact hnr
  have hle1lp : le1 M 0 (M.length - 1) := hn2.2.2.2.2.1
  have hwv : v < entry R 1 (R.length - 1) := by
    have := le1_entry1_lt hle1lp (by omega)
    rw [hroot1, hMlen, hE 1] at this
    exact this
  have hz2 : z < entry R 2 (R.length - 1) := by
    have := hn2.2.2.2.1
    rw [hroot2, hMlen, hE 2] at this
    exact this
  set d1 : ℕ := entry R 1 (R.length - 1) - v with hd1
  have hlev := hd.1
  unfold lev at hlev
  have hbound : 2 * (v + d1) + z ≤ m := by rw [hd1]; omega
  have hM0 : M⟦0⟧ = [] := by
    rw [oper_gcopies 0 hL hzz hpM', hpar0]
    simp [gcopies]
  have hstep : ∀ j, M⟦j + 1⟧ = p0 :: graft R (Lift1 (M⟦j⟧) d1) := by
    intro j
    rw [hd1]
    exact oper_cons_tower2 hR hRne hd hi1 hpM
  have hbased : ∀ j, based (M⟦j⟧) := by
    intro j
    cases j with
    | zero => rw [hM0]; exact based_nil
    | succ j => rw [hstep j]; exact based_cons v z _
  have key : ∀ j s : ℕ, Lift1 (M⟦j⟧) s ∈ W (2 * (v + s) + z) := by
    intro j
    induction j with
    | zero => intro s; rw [hM0]; simpa using W_nil (2 * (v + s) + z)
    | succ j ih =>
        intro s
        have hmem : Lift1 (M⟦j⟧) d1 ∈ W m := W_mono hbound (ih d1)
        have hb : based (Lift1 (M⟦j⟧) d1) := based_Lift1 _ (hbased j)
        have hres := hgr _ hmem hb (argOK_graft hRne hR _) v z
          (2 * (v + s) + z) s hz1 (le_refl _)
        rw [hstep j]
        exact hres
  exact key

/-- The `t = 0` instance: the former open core `TowerGraft2`. -/
theorem towerGraft2_holds :
    ∀ (v z m a : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 → 2 * v + z ≤ a →
      domT R m → srow R (R.length - 1) = 2 →
      (∀ y ∈ W m, based y → graft R y ∈ Wstar2) →
      hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
        R.length →
      ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a := by
  intro v z m a R hR hRne hz1 hva hd hi1 hgr hpM n _
  have h0 := towerGraft2_lift v z m R hR hRne hz1 hd hi1 hgr hpM n 0
  rw [Lift1_zero, Nat.add_zero] at h0
  exact W_mono hva h0

/-! ### `Lift1` の `cons` 分解

`Wstar2` の枝分けは持ち上げた主ブロック `Lift1 ((0,v,z) :: R) t` について
行うので、その尾部 `Rt` が `R` と同じ `srow`/`hasParent` を持つことを示す。
行 1 の錐は `nextrel1` を保つ（`nextrel1_Lift1`）から、根を挟んだ添字ずらし
`nextR_cons` と合わせて `Rt` の親構造は `R` のそれと一致する。 -/

theorem entry_tail (L : TrioSeq) (i j : ℕ) :
    entry L.tail i j = entry L i (j + 1) := by
  cases L with
  | nil => simp [entry, getD_out]
  | cons a l => rw [List.tail_cons, entry_cons]

/-- A column at or below the root's row 1 is outside the cone. -/
theorem not_le1_zero_of_le {X : TrioSeq} {j : ℕ} (hj : j ≠ 0)
    (h : entry X 1 j ≤ entry X 1 0) : ¬ le1 X 0 j := by
  intro hc
  exact absurd (le1_entry1_lt hc (Ne.symm hj)) (by omega)

open Classical in
/-- The root of a nonempty block is always lifted by the full amount. -/
theorem Lift1_head {X : TrioSeq} (hX : X ≠ []) (d : ℕ) :
    Lift1 X d = ((entry X 0 0, entry X 1 0 + d, entry X 2 0) : ℕ × ℕ × ℕ)
      :: (Lift1 X d).tail := by
  have hlen : 0 < X.length := List.length_pos_iff.mpr hX
  obtain ⟨m, hm⟩ : ∃ m, X.length = m + 1 := ⟨X.length - 1, by omega⟩
  have hc : le1 X 0 0 := le1_refl (by omega)
  unfold Lift1
  rw [hm, List.range_succ_eq_map]
  simp only [List.map_cons, List.tail_cons, if_pos hc]

/-- The `cons` form of the lifted principal block. -/
theorem Lift1_cons_eq {v z t : ℕ} {R : TrioSeq} :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t
      = ((0, v + t, z) : ℕ × ℕ × ℕ)
        :: (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).tail := by
  have h := Lift1_head (X := ((0, v, z) : ℕ × ℕ × ℕ) :: R)
    (by simp) t
  have e0 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 0 = 0 := by simp [entry]
  have e1 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 = v := by simp [entry]
  have e2 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 0 = z := by simp [entry]
  rw [e0, e1, e2] at h
  exact h

section LiftTail

variable {v z t : ℕ} {R : TrioSeq}

/-- The lifted argument block. -/
noncomputable def ltail (v z : ℕ) (R : TrioSeq) (t : ℕ) : TrioSeq :=
  (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).tail

theorem lift_cons : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t
    = ((0, v + t, z) : ℕ × ℕ × ℕ) :: ltail v z R t := Lift1_cons_eq

theorem entry_ltail (i j : ℕ) :
    entry (ltail v z R t) i j
      = entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t) i (j + 1) :=
  entry_tail _ i j

theorem ltail_length : (ltail v z R t).length = R.length := by
  unfold ltail
  rw [List.length_tail, Lift1_length]
  simp

theorem ltail_ne (hRne : R ≠ []) : ltail v z R t ≠ [] := by
  intro h
  have hl := ltail_length (v := v) (z := z) (R := R) (t := t)
  rw [h] at hl
  have hpos : 0 < R.length := List.length_pos_iff.mpr hRne
  simp at hl
  omega

theorem entry0_ltail (j : ℕ) : entry (ltail v z R t) 0 j = entry R 0 j := by
  rw [entry_ltail, entry0_Lift1, entry_cons]

theorem entry2_ltail (j : ℕ) : entry (ltail v z R t) 2 j = entry R 2 j := by
  rw [entry_ltail, entry2_Lift1, entry_cons]

theorem entry1_ltail_of_le {j : ℕ} (h : entry R 1 j ≤ v) :
    entry (ltail v z R t) 1 j = entry R 1 j := by
  classical
  rw [entry_ltail]
  rcases Nat.lt_or_ge (j + 1) (((0, v, z) : ℕ × ℕ × ℕ) :: R).length with hj | hj
  · have hjR : j < R.length := by simpa using hj
    have h0 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 = v := by simp [entry]
    have hle : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 (j + 1)
        ≤ entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 := by
      rw [h0, entry_cons]; exact h
    rw [entry1_Lift1 hj, if_neg (not_le1_zero_of_le (by omega) hle), entry_cons]
    omega
  · have hjR : R.length ≤ j := by simpa using hj
    rw [entry_out_row (L := Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)
        (by rw [Lift1_length]; exact hj),
      entry_out_row (L := R) hjR]

theorem lev_ltail_of_zero {j : ℕ} (h : lev R j = 0) :
    lev (ltail v z R t) j = 0 := by
  unfold lev at h ⊢
  rw [entry2_ltail, entry1_ltail_of_le (v := v) (z := z) (t := t) (by omega)]
  omega

theorem argOK_ltail (hR : argOK R) : argOK (ltail v z R t) := by
  intro p hp
  obtain ⟨j, hj, hpj⟩ := List.mem_iff_getElem.mp hp
  have hjR : j < R.length := by
    rw [ltail_length] at hj; exact hj
  have hpe : p = (ltail v z R t).getD j (0, 0, 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp [hpj]
  have : p.1 = entry (ltail v z R t) 0 j := by rw [hpe]; rfl
  rw [this, entry0_ltail]
  exact hR _ (entry_pair_mem (B := R) hjR)

theorem nextR_ltail {i a b : ℕ} :
    nextR (ltail v z R t) i a b ↔ nextR R i a b := by
  have h1 : nextR (ltail v z R t) i a b
      ↔ nextR (((0, v + t, z) : ℕ × ℕ × ℕ) :: ltail v z R t) i (a + 1) (b + 1) :=
    (nextR_cons _ _ i a b).symm
  rw [h1, ← lift_cons, nextR_Lift1, nextR_cons]

theorem hasParent_ltail {i b : ℕ} :
    hasParent (ltail v z R t) i b ↔ hasParent R i b := by
  unfold hasParent
  constructor
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, nextR_ltail.mp hj0, fun y hy => hu y (nextR_ltail.mpr hy)⟩
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, nextR_ltail.mpr hj0, fun y hy => hu y (nextR_ltail.mp hy)⟩

theorem srow_ltail (j : ℕ) : srow (ltail v z R t) j = srow R j := by
  have h : srow (ltail v z R t) j
      = srow (((0, v + t, z) : ℕ × ℕ × ℕ) :: ltail v z R t) (j + 1) :=
    (srow_cons _ _ j).symm
  rw [h, ← lift_cons, srow_Lift1 (by omega), srow_cons]

theorem ltail_dropLast :
    ((0, v + t, z) : ℕ × ℕ × ℕ) :: (ltail v z R t).dropLast
      = Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t := by
  by_cases hRne : R = []
  · subst hRne
    have h0 : ltail v z ([] : TrioSeq) t = [] := by
      have hl := ltail_length (v := v) (z := z) (R := ([] : TrioSeq)) (t := t)
      simpa using hl
    conv_rhs => rw [List.dropLast_nil, lift_cons]
    rw [h0]
    simp
  · have h1 : (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast
        = Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R).dropLast) t := Lift1_dropLast
    rw [dropLast_cons hRne] at h1
    conv_rhs => rw [← h1]
    rw [lift_cons]
    exact (dropLast_cons (ltail_ne hRne)).symm

end LiftTail

theorem lev_Lift1_ge {X : TrioSeq} {d j : ℕ} : lev X j ≤ lev (Lift1 X d) j := by
  classical
  unfold lev
  rw [entry2_Lift1]
  rcases Nat.lt_or_ge j X.length with hj | hj
  · rw [entry1_Lift1 hj]; omega
  · rw [entry_out_row (L := Lift1 X d) (by rw [Lift1_length]; exact hj),
      entry_out_row (L := X) hj]

theorem nil_mem_Wstar2 : ([] : TrioSeq) ∈ Wstar2 := by
  intro _ v z a t _ hva
  rw [lift_cons]
  have h0 : ltail v z ([] : TrioSeq) t = [] := by
    have hl := ltail_length (v := v) (z := z) (R := ([] : TrioSeq)) (t := t)
    simpa using hl
  rw [h0]
  exact W_mono hva (Om_mem_W (v + t) z)

/-! ### 行 2 タワーの持ち上げ済み所属 -/

open Classical in
/-- The row-2 graft tower closes **with the lift**: `oper_Lift1_tower` moves the
lift across the expansion and `towerGraft2_lift` supplies the membership. -/
theorem towerGraft2_lift_mem {v z m a t : ℕ} {R : TrioSeq} (hR : argOK R)
    (hRne : R ≠ []) (hz1 : z ≤ 1) (hva : 2 * (v + t) + z ≤ a)
    (hd : domT R m) (hi1 : srow R (R.length - 1) = 2)
    (hgr : ∀ y ∈ W m, based y → graft R y ∈ Wstar2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t ∈ W a := by
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set M : TrioSeq := p0 :: R with hMdef
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : M.length - 1 = R.length := by rw [hMdef]; simp
  have hE : ∀ i, entry M i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  have hL : M.length - 1 ≠ 0 := by rw [hMlen]; omega
  have hzz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -, -⟩; rw [hE 0] at h1; omega
  have hsrM : srow M (M.length - 1) = 2 := by
    rw [hMlen, hMdef, srow_cons_last hRne, hi1]
  have hpM' : hasParent M (srow M (M.length - 1)) (M.length - 1) := by
    rw [hsrM, hMlen, hMdef, ← hi1]; exact hpM
  have hpar0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0 := by
    rw [hsrM, hMlen]
    have := parent_cons_eq_zero (v := v) (z := z) hRne hd hpM
    rwa [hi1] at this
  have hroot0 : entry M 0 0 = 0 := by rw [hMdef]; simp [entry, hp0]
  have hroot1 : entry M 1 0 = v := by rw [hMdef]; simp [entry, hp0]
  have hnr := parent_nextR hpM'
  rw [hpar0, hsrM] at hnr
  have hn2 : nextrel2 M 0 (M.length - 1) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_neg (by omega)] at hnr
    exact hnr
  have hle1lp : le1 M 0 (M.length - 1) := hn2.2.2.2.2.1
  have hwv : v < entry R 1 (R.length - 1) := by
    have := le1_entry1_lt hle1lp (by omega)
    rw [hroot1, hMlen, hE 1] at this
    exact this
  have hup : ∀ l, 0 < l → l ≤ M.length - 1 → entry M 0 0 < entry M 0 l := by
    intro l hl0 hl1
    rw [hMlen] at hl1
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    rw [hroot0, hMdef, entry_cons]
    exact hR _ (entry_pair_mem (B := R) (by omega))
  set D0 : ℕ := (if 0 < srow M (M.length - 1)
    then entry M 0 (M.length - 1) - entry M 0 0 else 0) with hD0
  set D1 : ℕ := (if 1 < srow M (M.length - 1)
    then entry M 1 (M.length - 1) - entry M 1 0 else 0) with hD1
  have hd0pos : 0 < D0 := by
    rw [hD0, hsrM, if_pos (by omega), hroot0, hMlen, hE 0]; omega
  have hd0e : entry M 0 (M.length - 1) = entry M 0 0 + D0 := by
    rw [hD0, hsrM, if_pos (by omega), hroot0, hMlen, hE 0]; omega
  have hd1pos : 0 < D1 := by
    rw [hD1, hsrM, if_pos (by omega), hroot1, hMlen, hE 1]; omega
  refine A1_intro (Or.inr (Or.inl (fun n _ => ?_)))
  have hgexp : M⟦n⟧ = gexp M 0 (M.length - 1) D0 D1 n :=
    oper_eq_gexp n hL hzz hpM' hpar0
  rw [oper_Lift1_tower hL hzz hpM' hpar0 hgexp hup hd0pos hd0e hd1pos hle1lp]
  exact W_mono hva (towerGraft2_lift v z m R hR hRne hz1 hd hi1 hgr hpM n t)

/-! ## `Wstar2` の閉包

行 2 タワーは `towerGraft2_lift_mem` で閉じた。残る核は三つ:

* `LiftInner`  — B2a（`R` 内部が悪根）でのリフト同変性。probe 0/7440。
* `LiftTower1` — 行 1 タワー。リフトすると全コピーの根が上がるので、接ぎ木
  閉包が段 `m` ではなく `m + 2t` で要る。`Lift1`（強錐）では `hgr` から出ない
  ことが確認済み（弱錐リフト `Lstar` なら遺伝的に閉じるが B2a を壊す）。
* `LiftTowerExp2` — 展開節由来の行 2 タワー（旧 `TowerExp` の行 2 部分）。 -/

/-- **Open core (B2a)** — the guarded row-1 lift commutes with an expansion
whose bad root lies inside `R`. -/
def LiftInner : Prop :=
  ∀ (v z t n : ℕ) (R : TrioSeq), argOK R → R ≠ [] →
    hasParent R (srow R (R.length - 1)) (R.length - 1) →
    (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)⟦n⟧
      = Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧) t

/-- **Open core (row-1 tower)** — the copies are plain row-0 shifts, so the
lifted tower needs the graft closure one stage up. -/
def LiftTower1 : Prop :=
  ∀ (v z u0 a t : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 →
    2 * (v + t) + z ≤ a → Aop W u0 Wstar2 R → (∃ m, domT R m) →
    srow R (R.length - 1) = 1 →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t ∈ W a

/-- **Open core (row-2 tower over an expansion datum)** — no graft closure is on
hand. -/
def LiftTowerExp2 : Prop :=
  ∀ (v z a t : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 →
    2 * (v + t) + z ≤ a → (∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar2) → (∃ m, domT R m) →
    srow R (R.length - 1) = 2 →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t ∈ W a

/-- In a row-1 tower the root level is below the collapse level. -/
theorem tower1_le {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ []) (hz1 : z ≤ 1)
    (hd : domT R m) (hi1 : srow R (R.length - 1) = 1)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    2 * v + z ≤ m := by
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  have hpar := parent_cons_eq_zero hRne hd hpM
  have hnr := parent_nextR hpM
  rw [hpar, hi1] at hnr
  have h1 : nextrel1 (p0 :: R) 0 R.length := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_pos rfl] at hnr
    exact hnr
  have hlt : entry (p0 :: R) 1 0 < entry (p0 :: R) 1 R.length := h1.2.2.2.1
  have h0 : entry (p0 :: R) 1 0 = v := by simp [entry, hp0]
  have hE1 : entry (p0 :: R) 1 R.length = entry R 1 (R.length - 1) :=
    entry_cons_last hRne 1
  have hz2 : entry R 2 (R.length - 1) = 0 := by
    by_contra h
    unfold srow at hi1
    rw [if_pos (by omega)] at hi1
    omega
  have hlev := hd.1
  unfold lev at hlev
  omega

/-- **The single Buchholz-(1) core**: the graft closure of every block at every
stage.  In Buchholz 1987 this is manufactured, not assumed: `W_u ⊆ X^(a)` by
(A2), because `X^(a)` is `A`-closed by the one-step mirror 2.4(a).  The trio
mirror has UBI reattachment blockers, so the closure is named here. -/
def GraftAll : Prop :=
  ∀ (S : TrioSeq), argOK S → S ≠ [] →
    ∀ (u : ℕ) (y : TrioSeq), y ∈ W u → based y → graft S y ∈ Wstar2

/-- `Wstar2` version of `tower1_mem`: the row-1 graft tower stays in `W`. -/
theorem tower1_mem2 {v z m a : ℕ} {R : TrioSeq} (hR : argOK R) (hRne : R ≠ [])
    (hz1 : z ≤ 1) (hva : 2 * v + z ≤ a) (hd : domT R m)
    (hi1 : srow R (R.length - 1) = 1)
    (hgr : ∀ y ∈ W m, based y → graft R y ∈ Wstar2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ k, tow v z R k ∈ W a := by
  have hvm : 2 * v + z ≤ m := tower1_le hRne hz1 hd hi1 hpM
  have key : ∀ k, ∀ a', 2 * v + z ≤ a' → tow v z R k ∈ W a' := by
    intro k
    induction k with
    | zero => intro a' _; simpa [tow] using W_nil a'
    | succ k ih =>
        intro a' ha'
        have hk : tow v z R k ∈ W m := ih m hvm
        have hgk := hgr (tow v z R k) hk (based_tow v z R k)
        have h := hgk (argOK_graft hRne hR _) v z a' 0 hz1 (by omega)
        rw [Lift1_zero] at h
        exact h
  exact fun k => key k a hva

/-- The lifted argument's trailing column is a cone member, so its level rises
by `2t`. -/
theorem entry1_ltail_of_cone {v z t : ℕ} {R : TrioSeq} {j : ℕ}
    (hc : le1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 (j + 1)) :
    entry (ltail v z R t) 1 j = entry R 1 j + t := by
  classical
  have hj : j + 1 < (((0, v, z) : ℕ × ℕ × ℕ) :: R).length := hc.2.1
  rw [entry_ltail, entry1_Lift1 hj, if_pos hc, entry_cons]

/-- **`LiftTower1` from the graft closure.**  The lifted block is again a
root-parented row-1 tower, over the lifted argument at stage `m + 2t`. -/
theorem liftTower1_of_graftAll (hga : GraftAll) : LiftTower1 := by
  classical
  rintro v z u0 a t R hR hRne hz1 hva - ⟨m, hd⟩ hi1 hpM
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set M : TrioSeq := p0 :: R with hMdef
  set Rt : TrioSeq := ltail v z R t with hRtdef
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hRtlen : Rt.length = R.length := ltail_length
  have hRtne : Rt ≠ [] := ltail_ne hRne
  have hRtOK : argOK Rt := argOK_ltail hR
  -- the trailing orphan is a cone member
  have hpar0 := parent_cons_eq_zero hRne hd hpM
  have hnr := parent_nextR hpM
  rw [hpar0, hi1] at hnr
  have hn1 : nextrel1 M 0 R.length := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_pos rfl] at hnr
    exact hnr
  have hcone : le1 M 0 R.length := ⟨hn1.1, hn1.2.1, Relation.ReflTransGen.single hn1⟩
  have hconej : le1 M 0 ((R.length - 1) + 1) := by
    rw [← len_succ hRne]
    exact hcone
  -- the lifted data
  have hsrRt : srow Rt (Rt.length - 1) = 1 := by
    rw [hRtlen, hRtdef, srow_ltail]; exact hi1
  have hlevRt : lev Rt (Rt.length - 1) = (m + 2 * t) + 1 := by
    unfold lev
    rw [hRtlen, hRtdef, entry2_ltail, entry1_ltail_of_cone hconej]
    have hm := hd.1
    unfold lev at hm
    omega
  have hdRt : domT Rt (m + 2 * t) := by
    refine ⟨hlevRt, ?_⟩
    rw [hRtlen, hRtdef, srow_ltail, hasParent_ltail]
    exact hd.2
  have hpMt : hasParent (((0, v + t, z) : ℕ × ℕ × ℕ) :: Rt)
      (srow Rt (Rt.length - 1)) Rt.length := by
    rw [← lift_cons, hsrRt, hRtlen, ← hi1]
    exact hasParent_Lift1.mpr hpM
  -- the tower closes at stage m + 2t supplied by the graft closure
  have hgr : ∀ y ∈ W (m + 2 * t), based y → graft Rt y ∈ Wstar2 :=
    fun y hy hb => hga Rt hRtOK hRtne (m + 2 * t) y hy hb
  refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
  rw [hMdef, lift_cons, ← hRtdef,
    oper_cons_tower1 hRtOK hRtne hdRt hsrRt hpMt]
  exact tower1_mem2 hRtOK hRtne hz1 hva hdRt hsrRt hgr hpMt n

/-- **`LiftTowerExp2` from the graft closure**: the clause-2 datum is not even
needed once the closure is free. -/
theorem liftTowerExp2_of_graftAll (hga : GraftAll) : LiftTowerExp2 := by
  rintro v z a t R hR hRne hz1 hva - ⟨m, hd⟩ hi1 hpM
  exact towerGraft2_lift_mem hR hRne hz1 hva hd hi1
    (fun y hy hb => hga R hR hRne m y hy hb) hpM

/-- **`A_u(W*₂) ⊆ W*₂`** modulo the three cores. -/
theorem Wstar2_closed (hin : LiftInner) (ht1 : LiftTower1)
    (he2 : LiftTowerExp2) :
    ∀ (u0 : ℕ) (R : TrioSeq), Aop W u0 Wstar2 R → R ∈ Wstar2 := by
  classical
  intro u0 R AR hR v z a t hz1 hva
  by_cases hRnil : R = []
  · subst hRnil
    exact nil_mem_Wstar2 hR v z a t hz1 hva
  · set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
    set M : TrioSeq := p0 :: R with hMdef
    set Rt : TrioSeq := ltail v z R t with hRtdef
    have hN : Lift1 M t = ((0, v + t, z) : ℕ × ℕ × ℕ) :: Rt := lift_cons
    have hRlen : 0 < R.length := List.length_pos_iff.mpr hRnil
    have hRtlen : Rt.length = R.length := ltail_length
    have hRtne : Rt ≠ [] := ltail_ne hRnil
    have hRtOK : argOK Rt := argOK_ltail hR
    have hMlen : M.length - 1 = R.length := by rw [hMdef]; simp
    have hMlen2 : 1 < M.length := by rw [hMdef]; simp; omega
    have hCd : R.dropLast ∈ Wstar2 → (Lift1 M t).dropLast ∈ W a := by
      intro h
      rw [Lift1_dropLast, hMdef, dropLast_cons hRnil]
      exact h (argOK_dropLast hR) v z a t hz1 hva
    have hdead : (∃ m', domT M m') → R.dropLast ∈ Wstar2 → Lift1 M t ∈ W a := by
      rintro ⟨m', hdm⟩ hdl
      have hlen3 : (Lift1 M t).length - 1 = M.length - 1 := by rw [Lift1_length]
      have hdN : domT (Lift1 M t)
          (lev (Lift1 M t) ((Lift1 M t).length - 1) - 1) := by
        constructor
        · have hge := lev_Lift1_ge (X := M) (d := t) (j := M.length - 1)
          have h2 : lev M (M.length - 1) = m' + 1 := hdm.1
          rw [hlen3]; omega
        · rw [hlen3, srow_Lift1 (by rw [hMlen]; omega), hasParent_Lift1]
          exact hdm.2
      refine A1_intro (Or.inr (Or.inl (fun n _ => ?_)))
      rw [oper_eq_graft_nil_of_domT (n := n)
        (by rw [Lift1_length]; exact hMlen2) hdN, graft_nil]
      exact hCd hdl
    have hsucc : lev R (R.length - 1) = 0 → ¬ hasParent R 0 (R.length - 1) →
        R.dropLast ∈ Wstar2 → Lift1 M t ∈ W a := by
      intro hw0 hnp hdl
      have hwt : lev Rt (Rt.length - 1) = 0 := by
        rw [hRtlen, hRtdef]; exact lev_ltail_of_zero hw0
      have hnpt : ¬ hasParent Rt 0 (Rt.length - 1) := by
        rw [hRtlen, hRtdef, hasParent_ltail]; exact hnp
      refine A1_intro (Or.inr (Or.inl (fun n _ => ?_)))
      rw [hN, oper_cons_succ hRtOK hRtne hwt hnpt]
      refine W_flatMap_copies ?_ (rsum_self_cons (v + t) z _) n
      have hh := hCd hdl
      rw [hN, dropLast_cons hRtne] at hh
      exact hh
    have hsplit : lev R (R.length - 1) ≠ 0 →
        srow R (R.length - 1) = 1 ∨ srow R (R.length - 1) = 2 := by
      intro hw0
      unfold srow
      unfold lev at hw0
      by_cases h2' : 0 < entry R 2 (R.length - 1)
      · rw [if_pos h2']; exact Or.inr rfl
      · rw [if_neg h2', if_pos (by omega)]; exact Or.inl rfl
    rcases AR with ⟨hl, hw⟩ | hop | ⟨m, hm, hd, hgr⟩
    · -- clause 1
      have hR1 : R.length = 1 := by omega
      have hw' : lev R (R.length - 1) = 0 := by rw [hR1]; exact hw
      have hnp : ¬ hasParent R 0 (R.length - 1) := by
        rw [hR1]
        rintro ⟨j0, hj0, -⟩
        exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
      have hdl : R.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      exact hsucc hw' hnp (by rw [hdl]; exact nil_mem_Wstar2)
    · -- clause 2
      have hpredmem : ¬ hasParent R (srow R (R.length - 1)) (R.length - 1) →
          R.dropLast ∈ Wstar2 := by
        intro hp
        by_cases hR2 : 2 ≤ R.length
        · have hop1 := hop 1 le_rfl
          have hpred : R⟦1⟧ = R.dropLast := by
            have hLR : R.length - 1 ≠ 0 := by omega
            have he : R⟦1⟧ = Pred R := by
              by_cases hz0 : entry R 0 (R.length - 1) = 0 ∧
                  entry R 1 (R.length - 1) = 0 ∧ entry R 2 (R.length - 1) = 0
              · exact oper_eq_pred_of_zero 1 hLR hz0
              · exact oper_eq_pred_of_noParent 1 hLR hz0 hp
            rw [he]
            unfold Pred
            rw [if_neg (by omega)]
          rwa [hpred] at hop1
        · have hdl : R.dropLast = [] :=
            List.eq_nil_of_length_eq_zero (by simp; omega)
          rw [hdl]; exact nil_mem_Wstar2
      by_cases hp : hasParent R (srow R (R.length - 1)) (R.length - 1)
      · -- B2a
        refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
        rw [hMdef, hin v z t n R hR hRnil hp, oper_cons_nat hR hRnil hp]
        exact hop n hn (argOK_oper hR n) v z a t hz1 hva
      · by_cases hw0 : lev R (R.length - 1) = 0
        · have hsr : srow R (R.length - 1) = 0 := by
            unfold srow
            unfold lev at hw0
            rw [if_neg (by omega), if_neg (by omega)]
          exact hsucc hw0 (by rw [← hsr]; exact hp) (hpredmem hp)
        · obtain ⟨m', hm'⟩ : ∃ m', lev R (R.length - 1) = m' + 1 :=
            ⟨lev R (R.length - 1) - 1, by omega⟩
          have hdR : domT R m' := ⟨hm', hp⟩
          by_cases hpM : hasParent M (srow R (R.length - 1)) R.length
          · rcases hsplit hw0 with hs1 | hs2
            · exact ht1 v z u0 a t R hR hRnil hz1 hva (Or.inr (Or.inl hop))
                ⟨m', hdR⟩ hs1 hpM
            · exact he2 v z a t R hR hRnil hz1 hva hop ⟨m', hdR⟩ hs2 hpM
          · exact hdead ⟨m', domT_cons_of_dead hRnil hdR hpM⟩ (hpredmem hp)
    · -- clause 3
      have hdlW : R.dropLast ∈ Wstar2 := by
        have h := hgr [] (W_nil m) based_nil
        rwa [graft_nil] at h
      by_cases hpM : hasParent M (srow R (R.length - 1)) R.length
      · rcases hsplit (by rw [hd.1]; omega) with hs1 | hs2
        · exact ht1 v z u0 a t R hR hRnil hz1 hva
            (Or.inr (Or.inr ⟨m, hm, hd, hgr⟩)) ⟨m, hd⟩ hs1 hpM
        · exact towerGraft2_lift_mem hR hRnil hz1 hva hd hs2 hgr hpM
      · exact hdead ⟨m, domT_cons_of_dead hRnil hd hpM⟩ hdlW

/-! ## 残る核: タワー枝 -/

/-- **The one remaining core.**  When the principal root revives `R`'s trailing
orphan, `p_{v,z}(R)⟦n⟧` is an `n`-fold guarded copy tower.  For `srow = 1` the
row-1 lift is `0` and the plain `graft` recursion applies; for `srow = 2` the
copies raise row 1 by `w - v` on the `le1`-cone of the root, so the substituted
block is the *lifted* tower.  Stated against `R`'s raw `Aop` datum, so it covers
both the graft-clause and the successor-clause shapes of `R`. -/
def TowerOK : Prop :=
  ∀ (v z u0 a : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 → 2 * v + z ≤ a →
    Aop W u0 Wstar R → (∃ m, domT R m) →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a

/-- **`A_u(W*) ⊆ W*`.** -/
theorem Wstar_closed (htow : TowerOK) :
    ∀ (u0 : ℕ) (R : TrioSeq), Aop W u0 Wstar R → R ∈ Wstar := by
  intro u0 R AR hR v z a hz1 hva
  by_cases hRnil : R = []
  · subst hRnil
    exact W_mono hva (Om_mem_W v z)
  · set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
    have hRlen : 0 < R.length := List.length_pos_iff.mpr hRnil
    have hMlen : (p0 :: R).length - 1 = R.length := by simp
    have hMlen2 : 1 < (p0 :: R).length := by simp; omega
    have hi1M : srow (p0 :: R) ((p0 :: R).length - 1) = srow R (R.length - 1) := by
      rw [hMlen]; exact srow_cons_last hRnil
    have hlevM : lev (p0 :: R) ((p0 :: R).length - 1) = lev R (R.length - 1) := by
      unfold lev
      rw [hMlen, entry_cons_last hRnil 1, entry_cons_last hRnil 2]
    -- `p_{v,z}(R.dropLast) ∈ W a`, given that `R.dropLast` is in `W*`
    have hdlmem : R.dropLast ∈ Wstar → (p0 :: R.dropLast) ∈ W a := by
      intro h
      exact h (argOK_dropLast hR) v z a hz1 hva
    rcases AR with ⟨hl, hw⟩ | hop | ⟨m, hm, hd, hgr⟩
    · -- clause 1: `R = [(x,0,0)]`, so `p_{v,z}(R)⟦n⟧` is `n` copies of `Ω_{v,z}`
      have hR1 : R.length = 1 := by omega
      have hw' : lev R (R.length - 1) = 0 := by rw [hR1]; exact hw
      have hnp : ¬ hasParent R 0 (R.length - 1) := by
        rw [hR1]
        rintro ⟨j0, hj0, -⟩
        exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
      have hdl : R.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
      rw [oper_cons_succ hR hRnil hw' hnp, hdl]
      exact W_flatMap_copies (W_mono hva (Om_mem_W v z)) (rsum_self_cons v z []) n
    · -- clause 2: every expansion of `R` is in `W*`
      have hpredmem : ¬ hasParent R (srow R (R.length - 1)) (R.length - 1) →
          (p0 :: R.dropLast) ∈ W a := by
        intro hp
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
          exact hdlmem hop1
        · have hdl : R.dropLast = [] :=
            List.eq_nil_of_length_eq_zero (by simp; omega)
          rw [hdl]
          exact W_mono hva (Om_mem_W v z)
      by_cases hp : hasParent R (srow R (R.length - 1)) (R.length - 1)
      · -- `p_{v,z}(R)⟦n⟧ = p_{v,z}(R⟦n⟧)`
        refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
        rw [oper_cons_nat hR hRnil hp]
        exact hop n hn (argOK_oper hR n) v z a hz1 hva
      · by_cases hw0 : lev R (R.length - 1) = 0
        · -- successor step
          have hsr : srow R (R.length - 1) = 0 := by
            unfold srow
            unfold lev at hw0
            rw [if_neg (by omega), if_neg (by omega)]
          have hnp : ¬ hasParent R 0 (R.length - 1) := by rw [← hsr]; exact hp
          refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
          rw [oper_cons_succ hR hRnil hw0 hnp]
          exact W_flatMap_copies (hpredmem hp) (rsum_self_cons v z _) n
        · -- `R`'s trailing column is a dead orphan
          obtain ⟨m', hm'⟩ : ∃ m', lev R (R.length - 1) = m' + 1 :=
            ⟨lev R (R.length - 1) - 1, by omega⟩
          have hdR : domT R m' := ⟨hm', hp⟩
          by_cases hpM : hasParent (p0 :: R) (srow R (R.length - 1)) R.length
          · -- revived by the root: the tower
            refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
            exact htow v z u0 a R hR hRnil hz1 hva (Or.inr (Or.inl hop)) ⟨m', hdR⟩ hpM n hn
          · -- still dead: `p_{v,z}(R)⟦n⟧ = p_{v,z}(R.dropLast)`
            have hdM : domT (p0 :: R) m' := domT_cons_of_dead hRnil hdR hpM
            refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
            rw [oper_eq_graft_nil_of_domT (n := n) hMlen2 hdM, graft_nil,
              dropLast_cons hRnil]
            exact hpredmem hp
    · -- clause 3: `domT R m` with the graft closure
      have hdlW : R.dropLast ∈ Wstar := by
        have h := hgr [] (W_nil m) based_nil
        rwa [graft_nil] at h
      by_cases hpM : hasParent (p0 :: R) (srow R (R.length - 1)) R.length
      · -- revived by the root: the tower
        refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
        exact htow v z u0 a R hR hRnil hz1 hva
          (Or.inr (Or.inr ⟨m, hm, hd, hgr⟩)) ⟨m, hd⟩ hpM n hn
      · have hdM : domT (p0 :: R) m := domT_cons_of_dead hRnil hd hpM
        by_cases hma : m < a
        · -- the graft clause survives the root
          refine A1_intro (Or.inr (Or.inr ⟨m, hma, hdM, fun y hy hby => ?_⟩))
          rw [graft_cons hRnil]
          exact hgr y hy hby (argOK_graft hRnil hR y) v z a hz1 hva
        · -- the stage is below the orphan: fall back on the successor route
          refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
          rw [oper_eq_graft_nil_of_domT (n := n) hMlen2 hdM, graft_nil,
            dropLast_cons hRnil]
          exact hdlmem hdlW


/-- **Row-1 tower membership.** -/
theorem tower1_mem {v z m a : ℕ} {R : TrioSeq} (hR : argOK R) (hRne : R ≠ [])
    (hz1 : z ≤ 1) (hva : 2 * v + z ≤ a) (hd : domT R m)
    (hi1 : srow R (R.length - 1) = 1)
    (hgr : ∀ y ∈ W m, based y → graft R y ∈ Wstar)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ k, tow v z R k ∈ W a := by
  have hvm : 2 * v + z ≤ m := tower1_le hRne hz1 hd hi1 hpM
  have key : ∀ k, ∀ a', 2 * v + z ≤ a' → tow v z R k ∈ W a' := by
    intro k
    induction k with
    | zero => intro a' _; simpa [tow] using W_nil a'
    | succ k ih =>
        intro a' ha'
        have hk : tow v z R k ∈ W m := ih m hvm
        have hgk := hgr (tow v z R k) hk (based_tow v z R k)
        exact hgk (argOK_graft hRne hR _) v z a' hz1 ha'
  exact fun k => key k a hva

/-- **Open core A** — the guarded row-2 tower: the copies raise row 1 by `w - v`
on the `le1`-cone of the root, so the substituted block is the *lifted* tower. -/
def TowerGraft2 : Prop :=
  ∀ (v z m a : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 → 2 * v + z ≤ a →
    domT R m → srow R (R.length - 1) = 2 →
    (∀ y ∈ W m, based y → graft R y ∈ Wstar) →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a

/-- **Open core B** — a tower whose argument block arrived by the successor
clause, so no graft closure is on hand. -/
def TowerExp : Prop :=
  ∀ (v z m a : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 → 2 * v + z ≤ a →
    domT R m → (∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar) →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a

/-- The row-1 graft tower is **proved**; only the two cores above are left. -/
theorem towerOK_of (h2 : TowerGraft2) (he : TowerExp) : TowerOK := by
  intro v z u0 a R hR hRne hz1 hva AR hdR hpM n hn
  obtain ⟨m0, hm0⟩ := hdR
  have hlevpos : 0 < lev R (R.length - 1) := by rw [hm0.1]; omega
  have hsr : srow R (R.length - 1) = 1 ∨ srow R (R.length - 1) = 2 := by
    unfold srow
    unfold lev at hlevpos
    by_cases h2' : 0 < entry R 2 (R.length - 1)
    · rw [if_pos h2']; exact Or.inr rfl
    · rw [if_neg h2', if_pos (by omega)]; exact Or.inl rfl
  rcases AR with ⟨hl, hw⟩ | hop | ⟨m, hm, hd, hgr⟩
  · exfalso
    have hR1 : R.length = 1 := by
      have := List.length_pos_iff.mpr hRne
      omega
    have h := hm0.1
    rw [hR1] at h
    simp only [Nat.sub_self] at h
    omega
  · exact he v z m0 a R hR hRne hz1 hva hm0 hop hpM n hn
  · rcases hsr with h1 | h1
    · rw [oper_cons_tower1 hR hRne hd h1 hpM]
      exact tower1_mem hR hRne hz1 hva hd h1 hgr hpM n
    · exact h2 v z m a R hR hRne hz1 hva hd h1 hgr hpM n hn

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

theorem mem_of_Aclosed_aux (htow : TowerOK) :
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
            refine ih _ ?_ ?_ Wstar (Wstar_closed htow)
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
            hWs hargOK p0.2.1 p0.2.2 (maxlev Q) hz1 hroot
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
theorem mem_of_Aclosed (htow : TowerOK) {X : Set TrioSeq}
    (hX : ∀ (u : ℕ) (M : TrioSeq), Aop W u X M → M ∈ X) :
    ∀ M : TrioSeq, zle1 M → M ∈ X :=
  fun M hz => mem_of_Aclosed_aux htow M.length M le_rfl hz X hX

/-- Every argument block is in `W*`. -/
theorem mem_Wstar (htow : TowerOK) (R : TrioSeq) (hz : zle1 R) :
    R ∈ Wstar :=
  mem_of_Aclosed htow (Wstar_closed htow) R hz

/-- **Every block lies in `W u` as soon as `u` bounds its subscript levels.** -/
theorem mem_W_of_bound_aux (htow : TowerOK) :
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
          mem_Wstar htow _
            (fun q hq => by
              rw [mem_shiftl0] at hq
              obtain ⟨r, hr, rfl⟩ := hq
              exact hzM r (List.mem_append_right _ (List.mem_cons_of_mem _ hr)))
            hargOK p0.2.1 p0.2.2 u hz1 hroot
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

theorem mem_W_of_bound (htow : TowerOK) (M : TrioSeq)
    (hz : zle1 M) (u : ℕ) (h : ∀ p ∈ M, 2 * p.2.1 + p.2.2 ≤ u) : M ∈ W u :=
  mem_W_of_bound_aux htow M.length M le_rfl hz u h

/-- Every block lies in `W u` for `u` its maximal subscript level. -/
theorem mem_W_maxlev (htow : TowerOK) (M : TrioSeq)
    (hz : zle1 M) : M ∈ W (maxlev M) :=
  mem_W_of_bound htow M hz (maxlev M) le_maxlev

theorem W_membership (htow : TowerOK) :
    ∀ M : TrioSeq, ST_TS M → ∃ u : ℕ, M ∈ W u :=
  fun M hM => ⟨maxlev M, mem_W_maxlev htow M (zle1_ST_TS hM)⟩

/-- **Cofinality + the two open cores give well-foundedness of `olt` on
`ST_TS` images.** -/
theorem wf_olt_ST_TS_of_cofinality (htow : TowerOK)
    (hcof : ∀ {M N : TrioSeq}, ST_TS M → ST_TS N → translate N <o translate M →
      ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧)) :
    WellFounded (fun a b : TrioSeq =>
      ST_TS a ∧ ST_TS b ∧ translate a <o translate b) :=
  wf_of_cofinality_and_membership hcof (W_membership htow)

end Wset

end TRIO
