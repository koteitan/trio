/-
ArgDom.lean: 引数支配（ホスト非依存の共終性核）。

核の比較器は**心材シフト** `hshift w1 e f`: 行 0 は一様に `+e`、行 1 は
「木の経路上で行 1 が `w1` を超え続ける心材」でのみ `+f`（遮断された
部分木は行 0 のみシフト）。ホスト内では経路補題によりガード付き写像
`(e0 j + e, e1 j + [le1 N r j]·f, e2 j)` と一致する。
-/
import Cofinality

namespace TRIO

open Three
open Classical

/-- The heartwood shift: row 0 uniformly `+e`; row 1 `+f` on the heartwood
(the tree region reachable through columns with row 1 above `w1`). -/
def hshift (w1 e f : ℕ) : TrioSeq → TrioSeq
  | [] => []
  | p :: rest =>
      if w1 < p.2.1 then
        (p.1 + e, p.2.1 + f, p.2.2)
          :: (hshift w1 e f (rest.takeWhile fun q => p.1 < q.1)
              ++ hshift w1 e f (rest.dropWhile fun q => p.1 < q.1))
      else
        (p.1 + e, p.2.1, p.2.2)
          :: (shiftr01 e 0 (rest.takeWhile fun q => p.1 < q.1)
              ++ hshift w1 e f (rest.dropWhile fun q => p.1 < q.1))
  termination_by M => M.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

@[simp] theorem hshift_nil (w1 e f : ℕ) : hshift w1 e f [] = [] := by
  rw [hshift]

theorem hshift_cons (w1 e f : ℕ) (p : ℕ × ℕ × ℕ) (rest : TrioSeq) :
    hshift w1 e f (p :: rest)
      = if w1 < p.2.1 then
          (p.1 + e, p.2.1 + f, p.2.2)
            :: (hshift w1 e f (rest.takeWhile fun q => p.1 < q.1)
                ++ hshift w1 e f (rest.dropWhile fun q => p.1 < q.1))
        else
          (p.1 + e, p.2.1, p.2.2)
            :: (shiftr01 e 0 (rest.takeWhile fun q => p.1 < q.1)
                ++ hshift w1 e f (rest.dropWhile fun q => p.1 < q.1)) := by
  rw [hshift]

/-- **The host bridge**: inside a host `M`, the heartwood shift of a sibling
forest `[a, a+l)` under a guarded tree parent `pa` is the guarded map. -/
theorem hshift_gseg {M : TrioSeq} {r e f : ℕ} :
    ∀ (l : ℕ), ∀ {a pa : ℕ}, le1 M r pa → pa < a → a + l ≤ M.length →
      (∀ j, a ≤ j → j < a + l → entry M 0 pa < entry M 0 j) →
      (∀ j, pa < j → j < a → entry M 0 a ≤ entry M 0 j) →
      (List.range' a l).map (fun j =>
          ((entry M 0 j + e,
            entry M 1 j + (if le1 M r j then f else 0),
            entry M 2 j) : ℕ × ℕ × ℕ))
        = hshift (entry M 1 r) e f ((List.range' a l).map fun j =>
            ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l IH =>
    intro a pa hpa ha hlen hup hpre
    rcases l with - | l
    · show ([] : TrioSeq) = hshift _ e f []
      rw [hshift_nil]
    have hedge : nextrel0 M pa a := by
      refine ⟨by omega, by omega, ha, hup a le_rfl (by omega), ?_⟩
      intro x ⟨hx1, hx2⟩
      exact hpre x hx1 hx2
    have hguard : le1 M r a ↔ entry M 1 r < entry M 1 a := le1_step hpa hedge
    set q : ℕ → Bool := fun j => decide (entry M 0 a < entry M 0 j) with hqdef
    obtain ⟨m, hm, ht, hd, hall, hend⟩ := range'_split_takeWhile q l (a + 1)
    have hqs : ((fun x : ℕ × ℕ × ℕ => decide (entry M 0 a < x.1))
          ∘ fun j => ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) = q := by
      funext j
      simp only [Function.comp_apply, hqdef]
    -- unfold both sides one step
    simp only [List.range'_succ, List.map_cons]
    rw [hshift_cons]
    simp only [List.takeWhile_map, List.dropWhile_map, hqs, ht, hd]
    have hlsplit : List.range' (a + 1) l
        = List.range' (a + 1) m ++ List.range' (a + 1 + m) (l - m) := by
      rw [← ht, ← hd, List.takeWhile_append_dropWhile]
    rw [hlsplit, List.map_append]
    -- the tail recursion is common to both branches
    have htail : (List.range' (a + 1 + m) (l - m)).map (fun j =>
          ((entry M 0 j + e,
            entry M 1 j + (if le1 M r j then f else 0),
            entry M 2 j) : ℕ × ℕ × ℕ))
        = hshift (entry M 1 r) e f ((List.range' (a + 1 + m) (l - m)).map fun j =>
            ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
      rcases Nat.eq_or_lt_of_le hm with rfl | hmL
      · rw [Nat.sub_self]
        show ([] : TrioSeq) = hshift _ e f []
        rw [hshift_nil]
      · have hqe := hend hmL
        have he0 : entry M 0 (a + 1 + m) ≤ entry M 0 a := by
          have : q (a + 1 + m) = false := hqe
          simp only [hqdef, decide_eq_false_iff_not, Nat.not_lt] at this
          exact this
        refine IH (l - m) (by omega) hpa (by omega) (by omega) ?_ ?_
        · intro j h1 h2
          exact hup j (by omega) (by omega)
        · intro j h1 h2
          rcases Nat.lt_or_ge j a with hja | hja
          · exact le_trans he0 (hpre j h1 hja)
          · rcases Nat.eq_or_lt_of_le hja with rfl | hja'
            · exact he0
            · have := hall j (by omega) (by omega)
              simp only [hqdef, decide_eq_true_eq] at this
              exact le_trans he0 this.le
    by_cases hthr : entry M 1 r < entry M 1 a
    · rw [if_pos hthr, if_pos (hguard.2 hthr)]
      have hsub : (List.range' (a + 1) m).map (fun j =>
            ((entry M 0 j + e,
              entry M 1 j + (if le1 M r j then f else 0),
              entry M 2 j) : ℕ × ℕ × ℕ))
          = hshift (entry M 1 r) e f ((List.range' (a + 1) m).map fun j =>
              ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
        refine IH m (by omega) (hguard.2 hthr) (by omega) (by omega) ?_ ?_
        · intro j h1 h2
          have := hall j h1 (by omega)
          simp only [hqdef, decide_eq_true_eq] at this
          exact this
        · intro j h1 h2
          omega
      rw [hsub, htail]
    · rw [if_neg hthr, if_neg (fun h => hthr (hguard.1 h)), Nat.add_zero]
      have hnog : ∀ j, a + 1 ≤ j → j < a + 1 + m → ¬ le1 M r j := by
        intro j h1 h2 hle1
        refine hthr (hguard.1 ?_)
        refine le1_of_le1_subtree (by omega)
          ((rtg1_to_rtg0 hpa.2.2).tail hedge) (by omega) ?_ hle1
        intro x hx1 hx2
        have := hall x (by omega) (by omega)
        simp only [hqdef, decide_eq_true_eq] at this
        exact this
      have hsub : (List.range' (a + 1) m).map (fun j =>
            ((entry M 0 j + e,
              entry M 1 j + (if le1 M r j then f else 0),
              entry M 2 j) : ℕ × ℕ × ℕ))
          = shiftr01 e 0 ((List.range' (a + 1) m).map fun j =>
              ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
        unfold shiftr01
        rw [List.map_map]
        refine List.map_congr_left ?_
        intro j hj
        have hjb := List.mem_range'_1.1 hj
        simp only [Function.comp_apply]
        rw [if_neg (hnog j hjb.1 (by omega))]
      rw [hsub, htail]

/-! ## seqlex の道具 -/

theorem seqlex_of_sle_not_prefix : ∀ {W X Y : TrioSeq}, sle X (W ++ Y) →
    (∀ X', X ≠ W ++ X') → ∀ (Y' : TrioSeq), seqlex X (W ++ Y') := by
  intro W
  induction W with
  | nil =>
    intro X Y _ hnp _
    exact absurd (by simp : X = [] ++ X) (hnp X)
  | cons w W' ih =>
    intro X Y h hnp Y'
    rcases X with _ | ⟨x, X''⟩
    · simp
    · rw [List.cons_append] at h ⊢
      rcases h with he | hs
      · exact absurd he (by
          have := hnp Y
          rw [List.cons_append] at this
          exact this)
      · rw [seqlex_cons_cons] at hs
        rcases hs with hp | ⟨rfl, hs'⟩
        · exact Or.inl hp
        · refine Or.inr ⟨rfl, ih (Y := Y) (Or.inr hs') ?_ Y'⟩
          intro Z hZ
          exact hnp Z (by rw [hZ, List.cons_append])

/-- A comparison that is already over by the end of `P` does not see `Y`. -/
theorem sle_take_of_short : ∀ {P X Y : TrioSeq}, sle X (P ++ Y) →
    X.length ≤ P.length → sle X P := by
  intro P
  induction P with
  | nil =>
    intro X Y _ hlen
    have : X = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    exact Or.inl this
  | cons p P' ih =>
    intro X Y h hlen
    rcases X with _ | ⟨x, X''⟩
    · exact Or.inr (by simp)
    · simp only [List.length_cons] at hlen
      rw [List.cons_append] at h
      rcases h with he | hs
      · have hx : x = p := by simpa using congrArg List.headI he
        have hX'' : X'' = P' ++ Y := by simpa using congrArg List.tail he
        have hY : Y = [] := by
          have : X''.length = P'.length + Y.length := by
            rw [hX'']
            simp
          exact List.eq_nil_of_length_eq_zero (by omega)
        rw [hY, List.append_nil] at hX''
        exact Or.inl (by rw [hx, hX''])
      · rw [seqlex_cons_cons] at hs
        rcases hs with hp | ⟨rfl, hs'⟩
        · exact Or.inr (Or.inl hp)
        · rcases ih (Or.inr hs') (by omega) with he' | hs''
          · exact Or.inl (by rw [he'])
          · exact Or.inr (Or.inr ⟨rfl, hs''⟩)

/-- Truncating the smaller side on the right keeps it below. -/
theorem sle_of_append_left {X Y W : TrioSeq} (h : sle (X ++ Y) W) : sle X W := by
  refine sle_trans ?_ h
  rcases Y with _ | ⟨y, Y'⟩
  · exact Or.inl (by simp)
  · exact Or.inr (seqlex_prefix (by simp) X)

/-! ## 統一核の定義 -/

/-- `hshift` with a zero row-1 lift is the uniform row-0 shift. -/
theorem hshift_f0 (w1 e : ℕ) : ∀ A : TrioSeq, hshift w1 e 0 A = shiftr01 e 0 A
  | [] => by
    rw [hshift_nil]
    rfl
  | p :: rest => by
    rw [hshift_cons]
    have h1 := hshift_f0 w1 e (rest.takeWhile fun q => p.1 < q.1)
    have h2 := hshift_f0 w1 e (rest.dropWhile fun q => p.1 < q.1)
    have hsplit : shiftr01 e 0 rest
        = shiftr01 e 0 (rest.takeWhile fun q => p.1 < q.1)
          ++ shiftr01 e 0 (rest.dropWhile fun q => p.1 < q.1) := by
      unfold shiftr01
      rw [← List.map_append, List.takeWhile_append_dropWhile]
    split_ifs with h
    · rw [h1, h2, shiftr01_cons, ← hsplit, Nat.add_zero]
    · rw [h2, shiftr01_cons, ← hsplit, Nat.add_zero]
  termination_by A => A.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

/-- Right-visible columns of `A` below level `L` carry row 1 at least `w`. -/
def SpineOK (A : TrioSeq) (L w : ℕ) : Prop :=
  ∀ (U V : TrioSeq) (x : ℕ × ℕ × ℕ), A = U ++ x :: V → x.1 < L →
    (∀ y ∈ V, x.1 < y.1) → w ≤ x.2.1

/-- **The host-free core of trio Bachmann cofinality** (probe: 57549
instances, 0 violations).  Two columns with the *same* label rows `(w1+·, z)`
at depths `u` and `u+e`, row-1 siblings via `SpineOK`; the deeper argument
`B` is dominated by the heartwood shift of the shallower argument. -/
def ArgDomCore : Prop :=
  ∀ {X A1 B A2 Z : TrioSeq} {u w1 z e f : ℕ},
    ST_TS ((X ++ (u, w1, z) :: (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) ++ Z) →
    0 < e → (f = 0 ∨ z = 0) →
    (∀ x ∈ A1, u < x.1) →
    (∀ x ∈ B, u + e < x.1) →
    (∀ x ∈ A2, u < x.1) →
    (A2 = [] ∨ (A2.headI).1 ≤ u + e) →
    (Z = [] ∨ (Z.headI).1 ≤ u) →
    SpineOK A1 (u + e) w1 →
    sle B (hshift w1 e f (A1 ++ (u + e, w1 + f, z) :: (B ++ A2)))

/-! ## 一様シフトの道具（`i1 = 1`, `f = 0` の鎖） -/

theorem shiftr01_append (d0 d1 : ℕ) (A B : TrioSeq) :
    shiftr01 d0 d1 (A ++ B) = shiftr01 d0 d1 A ++ shiftr01 d0 d1 B :=
  List.map_append

theorem shiftr01_injective (d0 d1 : ℕ) {X Y : TrioSeq}
    (h : shiftr01 d0 d1 X = shiftr01 d0 d1 Y) : X = Y := by
  induction X generalizing Y with
  | nil =>
    rcases Y with - | ⟨y, Y'⟩
    · rfl
    · exact absurd h (by simp [shiftr01])
  | cons x X' ih =>
    rcases Y with - | ⟨y, Y'⟩
    · exact absurd h (by simp [shiftr01])
    · rw [shiftr01_cons, shiftr01_cons] at h
      obtain ⟨h1, h2⟩ := List.cons_eq_cons.1 h
      have hxy : x = y := by
        obtain ⟨x1, x2, x3⟩ := x
        obtain ⟨y1, y2, y3⟩ := y
        simp only [Prod.mk.injEq] at h1 ⊢
        omega
      rw [hxy, ih h2]

theorem collt_shiftr01 (d0 d1 : ℕ) {p q : ℕ × ℕ × ℕ} :
    collt ((p.1 + d0, p.2.1 + d1, p.2.2)) ((q.1 + d0, q.2.1 + d1, q.2.2))
      ↔ collt p q := by
  unfold collt
  dsimp only
  omega

theorem seqlex_shiftr01 (d0 d1 : ℕ) : ∀ {X Y : TrioSeq},
    seqlex (shiftr01 d0 d1 X) (shiftr01 d0 d1 Y) ↔ seqlex X Y := by
  intro X
  induction X with
  | nil =>
    intro Y
    rcases Y with - | ⟨y, Y'⟩
    · simp [shiftr01]
    · simp [shiftr01]
  | cons x X' ih =>
    intro Y
    rcases Y with - | ⟨y, Y'⟩
    · simp [shiftr01]
    · rw [shiftr01_cons, shiftr01_cons, seqlex_cons_cons, seqlex_cons_cons]
      constructor
      · rintro (hp | ⟨he, hs⟩)
        · exact Or.inl ((collt_shiftr01 d0 d1).1 hp)
        · refine Or.inr ⟨?_, ih.1 hs⟩
          obtain ⟨x1, x2, x3⟩ := x
          obtain ⟨y1, y2, y3⟩ := y
          simp only [Prod.mk.injEq] at he ⊢
          omega
      · rintro (hp | ⟨rfl, hs⟩)
        · exact Or.inl ((collt_shiftr01 d0 d1).2 hp)
        · exact Or.inr ⟨rfl, ih.2 hs⟩

theorem sle_shiftr01 (d0 d1 : ℕ) {X Y : TrioSeq} :
    sle (shiftr01 d0 d1 X) (shiftr01 d0 d1 Y) ↔ sle X Y := by
  unfold sle
  rw [seqlex_shiftr01]
  constructor
  · rintro (he | hs)
    · exact Or.inl (shiftr01_injective d0 d1 he)
    · exact Or.inr hs
  · rintro (rfl | hs)
    · exact Or.inl rfl
    · exact Or.inr hs

/-- `shiftr01` commutes with the copy tower. -/
theorem shiftr01_copies (d0 d1 : ℕ) (blk : TrioSeq) (n : ℕ) :
    shiftr01 d0 d1 (copies d0 d1 blk n) = copies d0 d1 (shiftr01 d0 d1 blk) n := by
  unfold copies shiftr01
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [List.map_map, List.map_map]
  congr 1
  funext p
  dsimp only [Function.comp_apply]
  simp only [Prod.mk.injEq]
  exact ⟨by omega, by omega, trivial⟩

/-- **The peel** (uniform case): a self-referential bound unfolds into the
copy tower. -/
theorem peel_aux (d w z : ℕ) : ∀ (n : ℕ) (X Q A2 : TrioSeq) (a : ℕ),
    X.length ≤ n →
    sle X (Q ++ (a, w, z) :: shiftr01 d 0 (X ++ A2)) →
    ∃ m, sle X (Q ++ copies d 0 ((a, w, z) :: shiftr01 d 0 Q) m) := by
  intro n
  induction n with
  | zero =>
    intro X Q A2 a hlen _
    have hX : X = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hX
    refine ⟨0, ?_⟩
    rw [copies_zero, List.append_nil]
    rcases Q with _ | ⟨q, Q'⟩
    · exact Or.inl rfl
    · exact Or.inr (by simp)
  | succ n ih =>
    intro X Q A2 a hlen h
    by_cases hpre : ∃ X', X = Q ++ (a, w, z) :: X'
    · obtain ⟨X', rfl⟩ := hpre
      have hstep : sle X' (shiftr01 d 0 Q
          ++ (a + d, w, z) :: shiftr01 d 0 (X' ++ A2)) := by
        have h' : sle (Q ++ (a, w, z) :: X')
            (Q ++ (a, w, z) :: shiftr01 d 0 ((Q ++ (a, w, z) :: X') ++ A2)) := h
        have hc : sle ((a, w, z) :: X')
            ((a, w, z) :: shiftr01 d 0 ((Q ++ (a, w, z) :: X') ++ A2)) :=
          (sle_append_cancel Q).1 h'
        have hc2 : sle X' (shiftr01 d 0 ((Q ++ (a, w, z) :: X') ++ A2)) :=
          (sle_append_cancel [(a, w, z)]).1 (by simpa using hc)
        have hrw : shiftr01 d 0 ((Q ++ (a, w, z) :: X') ++ A2)
            = shiftr01 d 0 Q ++ (a + d, w, z) :: shiftr01 d 0 (X' ++ A2) := by
          rw [List.append_assoc, List.cons_append, shiftr01_append, shiftr01_cons]
          rfl
        rwa [hrw] at hc2
      have hlen' : X'.length ≤ n := by
        simp only [List.length_append, List.length_cons] at hlen
        omega
      obtain ⟨m, hm⟩ := ih X' (shiftr01 d 0 Q) A2 (a + d) hlen' hstep
      refine ⟨m + 1, ?_⟩
      have hrw : Q ++ copies d 0 ((a, w, z) :: shiftr01 d 0 Q) (m + 1)
          = (Q ++ [(a, w, z)]) ++
              (shiftr01 d 0 Q
                ++ copies d 0 ((a + d, w, z)
                    :: shiftr01 d 0 (shiftr01 d 0 Q)) m) := by
        rw [copies_succ_front, shiftr01_copies, shiftr01_cons]
        simp
      rw [hrw]
      have he : Q ++ (a, w, z) :: X' = (Q ++ [(a, w, z)]) ++ X' := by simp
      rw [he]
      exact (sle_append_cancel _).2 hm
    · refine ⟨1, Or.inr ?_⟩
      rw [copies_one]
      have hW : sle X ((Q ++ [(a, w, z)]) ++ shiftr01 d 0 (X ++ A2)) := by
        simpa using h
      have hnp : ∀ X', X ≠ (Q ++ [(a, w, z)]) ++ X' := by
        intro X' hX'
        exact hpre ⟨X', by rw [hX']; simp⟩
      have := seqlex_of_sle_not_prefix hW hnp (shiftr01 d 0 Q)
      simpa using this

/-! ## スパイン条件の導出 -/

theorem getD_append_right' (A B : TrioSeq) (i : ℕ) :
    (A ++ B).getD (A.length + i) (0, 0, 0) = B.getD i (0, 0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

/-- **The spine condition from a row-1 ancestry to the dropped column.**
Right-visible columns of `R` are row-0 ancestors of the dropped column
(window pivot), hence chain nodes of the `le1`-ancestry; the path lemma
bounds their row 1 strictly above the root. -/
theorem spineOK_of_le1 {G R : TrioSeq} {v0 w1 w2 : ℕ} {lp : ℕ × ℕ × ℕ}
    (hle1 : le1 ((G ++ ((v0, w1, w2) :: R)) ++ [lp]) G.length
      (G ++ ((v0, w1, w2) :: R)).length) :
    SpineOK R lp.1 w1 := by
  intro U V x hR hxlt hV
  set M := (G ++ ((v0, w1, w2) :: R)) ++ [lp] with hMdef
  set A := G ++ ((v0, w1, w2) :: U) with hAdef
  have hMeq : M = A ++ (x :: (V ++ [lp])) := by
    rw [hMdef, hAdef, hR]
    simp
  have hAlen : A.length = G.length + 1 + U.length := by
    rw [hAdef]
    simp
    omega
  have hj1 : (G ++ ((v0, w1, w2) :: R)).length = A.length + 1 + V.length := by
    rw [hR, hAlen]
    simp
    omega
  have hMlen : M.length = (G ++ ((v0, w1, w2) :: R)).length + 1 := by
    rw [hMdef]
    simp
    omega
  have hgx : M.getD A.length (0, 0, 0) = x := by
    have h := getD_append_right' A (x :: (V ++ [lp])) 0
    rw [Nat.add_zero] at h
    rw [hMeq]
    exact h
  -- window: everything after `x` up to the dropped column is strictly above it
  have hwin : ∀ y, A.length < y → y ≤ (G ++ ((v0, w1, w2) :: R)).length →
      entry M 0 A.length < entry M 0 y := by
    intro y hy1 hy2
    obtain ⟨t, rfl⟩ : ∃ t, y = A.length + (t + 1) := ⟨y - A.length - 1, by omega⟩
    have hgy : M.getD (A.length + (t + 1)) (0, 0, 0)
        = (V ++ [lp]).getD t (0, 0, 0) := by
      conv_lhs => rw [hMeq]
      rw [getD_append_right' A (x :: (V ++ [lp])) (t + 1), List.getD_cons_succ]
    show (M.getD A.length (0, 0, 0)).1 < (M.getD (A.length + (t + 1)) (0, 0, 0)).1
    rw [hgx, hgy]
    rcases Nat.lt_or_ge t V.length with ht | ht
    · have hmem : (V ++ [lp]).getD t (0, 0, 0) ∈ V := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht,
          List.getElem?_eq_getElem ht]
        exact List.getElem_mem _
      exact hV _ hmem
    · have htv : t = V.length := by omega
      subst htv
      have he : (V ++ [lp]).getD V.length (0, 0, 0) = lp := by
        have h := getD_append_right' V [lp] 0
        rw [Nat.add_zero] at h
        exact h
      rw [he]
      exact hxlt
  -- `x` is a row-0 chain node of the ancestry
  have hxrtg : Relation.ReflTransGen (nextrel0 M) A.length
      (G ++ ((v0, w1, w2) :: R)).length := by
    refine rtg0_of_window (by omega) (by omega) ?_
    intro l hl1 hl2
    exact hwin l hl1 hl2
  have hrootx : Relation.ReflTransGen (nextrel0 M) G.length A.length :=
    rtg0_comparable (rtg1_to_rtg0 hle1.2.2) hxrtg (by omega)
  have hbound := le1_chain_window hle1.2.2 A.length hrootx hxrtg (by omega)
  -- read the two row-1 values
  have hgr : M.getD G.length (0, 0, 0) = (v0, w1, w2) := by
    have h := getD_append_right' G (((v0, w1, w2) :: R) ++ [lp]) 0
    rw [Nat.add_zero] at h
    rw [hMdef, List.append_assoc]
    rw [h]
    rfl
  have e1 : entry M 1 G.length = w1 := by
    show (M.getD G.length (0, 0, 0)).2.1 = w1
    rw [hgr]
  have e2 : entry M 1 A.length = x.2.1 := by
    show (M.getD A.length (0, 0, 0)).2.1 = x.2.1
    rw [hgx]
  rw [e1, e2] at hbound
  omega

end TRIO
