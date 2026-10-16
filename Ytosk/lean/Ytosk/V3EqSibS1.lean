/-
**EqSibUpg は S1 から出る（2026-10-17、t1）。**

S1（closure の V3PDef: 隣り合う兄弟の部分木の列は辞書式で増えない）と構造の不変条件
（R0P・R1S・Z2・SibDec・Z1C・BumpE2・BumpLeaf）から EqSibUpg（V3PassRoot）を示す。

r の子 c に前の兄弟があり、c ののりしろの子 j の真の子孫 y で P_1(y) = r とする。
- e1 c = e1 r + 1・e2 c = 1。j の子 k（y の祖先）は e1 k = e1 c なので、BumpLeaf で k は葉・j の最後の子・
  j は c の最後の子。よって y = k。
- c の最初の子は j（j の前の兄弟 j′ があれば、S1(j′, j) で j′ の最初の子の行 1 が e1 c になり、BumpLeaf で
  j′ が c の最後の子になって矛盾）。j の最初の子は k。よって subT c = c, j, k, …。
- c の直前の兄弟 b′ と S1(b′, c): b′ の列は c と同じ、b′ + 1 = のりしろの子、b′ + 2 は行 1 が e1 c の子で、
  BumpLeaf で b′ の部分木は b′, b′+1, b′+2 だけ。c = b′ + 3 で、b′ + 2 は c に上げられる（upg (b′+2) = c）。
-/
import Ytosk.V3PassRoot
import Ytosk.V3PDef
import Ytosk.V3InvJ

namespace Ytosk

open T

theorem col_getElem' {M : Mat} {i : Nat} (hi : i < M.length) : col M i = M[i] := by
  unfold col; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

/-- The prefix of `M.drop i` while `p` holds: empty, or the column `i` followed by the rest. -/
theorem tw_drop (M : Mat) (i : Nat) (p : Nat × Nat × Nat → Bool) :
    (M.drop i).takeWhile p = [] ∨
      (i < M.length ∧ p (col M i) = true ∧
        (M.drop i).takeWhile p = col M i :: (M.drop (i + 1)).takeWhile p) := by
  by_cases hi : i < M.length
  · rw [List.drop_eq_getElem_cons hi, ← col_getElem' hi]
    cases hp : p (col M i)
    · left; simp [hp]
    · right; exact ⟨hi, rfl, by simp [hp]⟩
  · left; rw [List.drop_eq_nil_of_le (by omega)]; rfl

theorem seqLtB_cons_false {p q : Nat × Nat × Nat} {A B : Mat} (h : seqLtB (p :: A) (q :: B) = false) :
    colLtB p q = false ∧ (p = q → seqLtB A B = false) := by
  simp only [seqLtB, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h
  refine ⟨h.1, fun hpq => ?_⟩
  rcases h.2 with h | h
  · subst hpq; simp at h
  · exact h

theorem seqLtB_nil_cons {q : Nat × Nat × Nat} {B : Mat} : seqLtB [] (q :: B) = true := rfl

/-- `¬ (a < b)` for columns, in components. -/
theorem colLtB_false {a b : Nat × Nat × Nat} (h : colLtB a b = false) :
    b.1 < a.1 ∨ (b.1 = a.1 ∧ (b.2.1 < a.2.1 ∨ (b.2.1 = a.2.1 ∧ b.2.2 ≤ a.2.2))) := by
  unfold colLtB at h
  have := of_decide_eq_false h
  omega

/-- The parent of the next column when its row 0 is larger. -/
theorem par0_next {M : Mat} {i : Nat} (h : entry M 0 i < entry M 0 (i + 1)) : par M 0 (i + 1) = some i :=
  (par0_spec M).mpr ⟨by omega, h, fun j h1 h2 => by omega⟩

theorem entry_col (M : Mat) (i : Nat) :
    col M i = (entry M 0 i, entry M 1 i, entry M 2 i) := by
  unfold entry col; simp

/-- The predecessor of `c` in a sorted list containing some `b < c`. -/
theorem pred_split {l : List Nat} (hs : l.Pairwise (· < ·)) {b c : Nat} (hb : b ∈ l) (hc : c ∈ l)
    (hbc : b < c) : ∃ a l₁ l₂, l = l₁ ++ a :: c :: l₂ := by
  classical
  set a := Nat.findGreatest (fun e => e ∈ l ∧ e < c) c with ha
  have hPa : a ∈ l ∧ a < c := Nat.findGreatest_spec (P := fun e => e ∈ l ∧ e < c) (m := b)
    (by omega) ⟨hb, hbc⟩
  obtain ⟨l₁, l₂, h⟩ := consec_split hs hPa.1 hc hPa.2 (fun e he ⟨h1, h2⟩ => by
    have := Nat.findGreatest_is_greatest (P := fun e => e ∈ l ∧ e < c) (n := c) h1 (by omega)
    exact this ⟨he, h2⟩)
  exact ⟨a, l₁, l₂, h⟩

/-- The second column of `subT M a` (a forced child of `a`). -/
theorem subT_second {M : Mat} {a : Nat} {q : Nat × Nat × Nat} {U : Mat}
    (h : seqLtB (subT M a) (col M a :: q :: U) = false) :
    a + 1 < M.length ∧ entry M 0 a < entry M 0 (a + 1) ∧
      seqLtB ((M.drop (a + 1)).takeWhile (fun q => decide (entry M 0 a < q.1))) (q :: U) = false := by
  unfold subT at h
  have h2 := (seqLtB_cons_false h).2 rfl
  rcases tw_drop M (a + 1) (fun q => decide (entry M 0 a < q.1)) with h0 | ⟨hl, hp, _⟩
  · rw [h0] at h2; simp [seqLtB] at h2
  · refine ⟨hl, ?_, h2⟩
    have : entry M 0 (a + 1) = (col M (a + 1)).1 := by rw [entry_col]
    rw [this]; simpa using hp

section
variable {M : Mat} (hR0 : R0P M) (hR1 : R1S M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M)
  (hBE : BumpE2 M) (hBL : BumpLeaf M) (hS1 : S1 M)
include hR0 hR1 hZ2 hSD hZ1 hBE hBL hS1

/-- **EqSibUpg from S1.** -/
theorem eqSibUpg_of_S1 : EqSibUpg M := by
  intro r b c j y hb hc hbc hj hjb hjy hjy' hy1
  have hcr : par M 0 c = some r := (mem_children_iff.mp hc).2
  have hjc : par M 0 j = some c := (mem_children_iff.mp hj).2
  have hrc := par_lt M 0 c r hcr
  have hcj := par_lt M 0 j c hjc
  have hjyl : j < y := lt_of_le_of_ne hjy.le hjy'
  have hyl : y < M.length := anc0_lt_len hjy hjy'
  have hAry : Anc0 M r y := anc0_of_par M 1 r y hy1
  have hAcj : Anc0 M c j := Anc0.step hjc (Anc0.refl c)
  have hAcy : Anc0 M c y := hAcj.trans hjy
  have hpath := hpath_of_par1 hy1 hAry (by omega)
  have he1c : entry M 1 r < entry M 1 c :=
    hpath c (Anc0.step hcr (Anc0.refl r)) hAcy (by omega) (by omega)
  have he1c' := hR1 c r hcr
  have he0c := hR0 c r hcr
  have he2c : entry M 2 c = 1 := hBE c j hj hjb
  have hbj : bump M c = (entry M 0 c + 1, entry M 1 c, 1) := rfl
  have he2j : entry M 2 j = 1 := e2_of_col (hjb.trans hbj)
  have he1j : entry M 1 j = entry M 1 c := e1_of_col (hjb.trans hbj)
  have he0j : entry M 0 j = entry M 0 c + 1 := e0_of_col (hjb.trans hbj)
  have he2r : entry M 2 r = 0 := by
    have := hZ2 r
    by_contra h
    have := hZ1 r c (by omega) hc
    omega
  -- the child `k` of `j` above `y`
  obtain ⟨k, hkj, hky⟩ := anc0_child hjy hjy'
  have hk : k ∈ children M j := mem_children_iff.mpr ⟨by have := hky.le; omega, hkj⟩
  have hjk := par_lt M 0 k j hkj
  have he1k_le : entry M 1 k ≤ entry M 1 j := hZ1 j k he2j hk
  have he1k_gt : entry M 1 r < entry M 1 k := by
    by_cases hky' : k = y
    · subst hky'; exact par1_entry_lt hy1
    · exact hpath k (Anc0.step hkj (Anc0.step hjc (Anc0.step hcr (Anc0.refl r))))
        hky (by omega) hky'
  obtain ⟨hk2, hkleaf, hjlast, hclast⟩ := hBL c j k hj hjb hk (by omega)
  -- `j + 1 = k`
  have hj1 : par M 0 (j + 1) = some j := child_succ (Anc0.step hkj (Anc0.refl j)) (by omega)
  have hj1M : j + 1 < M.length := by have := hky.le; omega
  have hj1k : j + 1 = k := by
    have hj1ch : j + 1 ∈ children M j := mem_children_iff.mpr ⟨hj1M, hj1⟩
    have hle : j + 1 ≤ k := by omega
    rcases Nat.eq_or_lt_of_le hle with h | h
    · exact h
    · exfalso
      obtain ⟨l₁, l₂, hsp⟩ := List.append_of_mem hj1ch
      have hkl₂ : k ∈ l₂ := by
        have hs := children_sorted M j
        rw [hsp] at hs hk
        rcases List.mem_append.mp hk with h' | h'
        · have := (List.pairwise_append.mp hs).2.2 k h' (j + 1) (by simp); omega
        · rcases List.mem_cons.mp h' with h' | h'
          · omega
          · exact h'
      have hle' := sib_le hSD l₂ l₁ (j + 1) hsp k hkl₂
      unfold colLe at hle'
      rw [entry_col M k, entry_col M (j + 1)] at hle'
      simp only at hle'
      have he0k := hR0 k j hkj
      have he0j1 := hR0 (j + 1) j hj1
      have hle1 : entry M 1 (j + 1) ≤ entry M 1 j := hZ1 j (j + 1) he2j hj1ch
      obtain ⟨_, _, hl, _⟩ := hBL c j (j + 1) hj hjb hj1ch (by omega)
      rw [hjlast] at hl
      cases hl; omega
  subst hj1k
  -- `c + 1 = j`
  have hc1 : par M 0 (c + 1) = some c := child_succ hAcj (by omega)
  have hc1ch : c + 1 ∈ children M c := mem_children_iff.mpr ⟨by omega, hc1⟩
  have hc1j : c + 1 = j := by
    rcases Nat.eq_or_lt_of_le (show c + 1 ≤ j by omega) with h | h
    · exact h
    · exfalso
      obtain ⟨j', l₁, l₂, hsp⟩ := pred_split (children_sorted M c) hc1ch hj h
      obtain ⟨hj'j, hj'm, _, _⟩ := split_consec (children_sorted M c) hsp
      have hj'c : par M 0 j' = some c := (mem_children_iff.mp hj'm).2
      have hcolle := hSD c l₁ l₂ j' j hsp
      have he0j' := hR0 j' c hj'c
      have he1j' : entry M 1 j' ≤ entry M 1 c := hZ1 c j' he2c hj'm
      have he2j' := hZ2 j'
      unfold colLe at hcolle
      rw [entry_col M j, entry_col M j'] at hcolle
      simp only at hcolle
      have hcolj' : col M j' = bump M c := by
        rw [entry_col M j', hbj]
        have : entry M 1 j' = entry M 1 c := by omega
        have : entry M 2 j' = 1 := by omega
        simp only [Prod.mk.injEq]; omega
      have hS := hS1 c l₁ l₂ j' j hsp
      have hsubj : subT M j = col M j :: col M (j + 1) ::
          (M.drop (j + 2)).takeWhile (fun q => decide (entry M 0 j < q.1)) := by
        unfold subT
        rcases tw_drop M (j + 1) (fun q => decide (entry M 0 j < q.1)) with h0 | ⟨_, _, he⟩
        · exfalso
          have h1 := hR0 (j + 1) j hj1
          have hd : decide (entry M 0 j < (col M (j + 1)).1) = true := by
            rw [entry_col M (j + 1)]; simp only [decide_eq_true_eq]; omega
          rw [List.drop_eq_getElem_cons hj1M, ← col_getElem' hj1M] at h0
          simp [List.takeWhile_cons, hd] at h0
        · rw [he]
      have hcj' : col M j' = col M j := by rw [hcolj', hjb]
      rw [hsubj, ← hcj'] at hS
      obtain ⟨_, _, hS2⟩ := subT_second hS
      rcases tw_drop M (j' + 1) (fun q => decide (entry M 0 j' < q.1)) with h0 | ⟨hl, hp, he⟩
      · rw [h0] at hS2; simp [seqLtB] at hS2
      · rw [he] at hS2
        have hlt := colLtB_false (seqLtB_cons_false hS2).1
        have hpe : entry M 0 j' < entry M 0 (j' + 1) := by
          have : entry M 0 (j' + 1) = (col M (j' + 1)).1 := by rw [entry_col]
          rw [this]; simpa using hp
        have hp1 := par0_next hpe
        have hch : j' + 1 ∈ children M j' := mem_children_iff.mpr ⟨hl, hp1⟩
        have he0 := hR0 (j' + 1) j' hp1
        have he0k := hR0 (j + 1) j hj1
        rw [entry_col M (j' + 1), entry_col M (j + 1)] at hlt
        simp only at hlt
        obtain ⟨_, _, _, hl'⟩ := hBL c j' (j' + 1) hj'm hcolj' hch (by omega)
        rw [hclast] at hl'
        cases hl'; omega
  subst hc1j
  -- the predecessor `b'` of `c` among the children of `r`
  obtain ⟨b', l₁, l₂, hsp⟩ := pred_split (children_sorted M r) hb hc hbc
  obtain ⟨hb'c, hb'm, _, hnb⟩ := split_consec (children_sorted M r) hsp
  have hb'r : par M 0 b' = some r := (mem_children_iff.mp hb'm).2
  have hrb' := par_lt M 0 b' r hb'r
  have hcolle := hSD r l₁ l₂ b' c hsp
  have he0b' := hR0 b' r hb'r
  have he1b' := hR1 b' r hb'r
  have he2b' := hZ2 b'
  unfold colLe at hcolle
  rw [entry_col M c, entry_col M b'] at hcolle
  simp only at hcolle
  have he1b'c : entry M 1 b' = entry M 1 c := by omega
  have he2b'1 : entry M 2 b' = 1 := by omega
  have hcolb' : col M b' = col M c := by rw [entry_col M b', entry_col M c]; simp only [Prod.mk.injEq]; omega
  have hS := hS1 r l₁ l₂ b' c hsp
  have hsubc : subT M c = col M c :: col M (c + 1) :: col M (c + 1 + 1) ::
      (M.drop (c + 1 + 2)).takeWhile (fun q => decide (entry M 0 c < q.1)) := by
    unfold subT
    have hc1M : c + 1 < M.length := by omega
    have hc2M : c + 1 + 1 < M.length := by omega
    have h1 := hR0 (c + 1) c hc1
    have h2 := hR0 (c + 1 + 1) (c + 1) hj1
    rw [List.drop_eq_getElem_cons hc1M, ← col_getElem' hc1M, List.takeWhile_cons,
      List.drop_eq_getElem_cons hc2M, ← col_getElem' hc2M, List.takeWhile_cons]
    simp only [entry_col] at h1 h2 ⊢
    simp [h1, h2]
    all_goals omega
  rw [hsubc, ← hcolb'] at hS
  obtain ⟨hb1M, hb1e, hS2⟩ := subT_second hS
  have hb1 := par0_next hb1e
  have hb1ch : b' + 1 ∈ children M b' := mem_children_iff.mpr ⟨hb1M, hb1⟩
  have he0b1 := hR0 (b' + 1) b' hb1
  have he1b1 : entry M 1 (b' + 1) ≤ entry M 1 b' := hZ1 b' (b' + 1) he2b'1 hb1ch
  have he2b1 := hZ2 (b' + 1)
  rcases tw_drop M (b' + 1) (fun q => decide (entry M 0 b' < q.1)) with h0 | ⟨_, _, he⟩
  · rw [h0] at hS2; simp [seqLtB] at hS2
  rw [he] at hS2
  obtain ⟨hlt1, heq1⟩ := seqLtB_cons_false hS2
  have hlt1' := colLtB_false hlt1
  rw [entry_col M (b' + 1), entry_col M (c + 1)] at hlt1'
  simp only at hlt1'
  have he0c1 := hR0 (c + 1) c hc1
  have hcolb1 : col M (b' + 1) = col M (c + 1) := by
    rw [entry_col M (b' + 1), entry_col M (c + 1)]; simp only [Prod.mk.injEq]; omega
  have hS3 := heq1 hcolb1
  rcases tw_drop M (b' + 1 + 1) (fun q => decide (entry M 0 b' < q.1)) with h0 | ⟨hb2M, hp2, he2⟩
  · rw [h0] at hS3; simp [seqLtB] at hS3
  rw [he2] at hS3
  have hlt2 := colLtB_false (seqLtB_cons_false hS3).1
  have he0k := hR0 (c + 1 + 1) (c + 1) hj1
  rw [entry_col M (b' + 1 + 1), entry_col M (c + 1 + 1)] at hlt2
  simp only at hlt2
  have hb2e : entry M 0 (b' + 1) < entry M 0 (b' + 1 + 1) := by omega
  have hb2 := par0_next hb2e
  have hb2ch : b' + 1 + 1 ∈ children M (b' + 1) := mem_children_iff.mpr ⟨hb2M, hb2⟩
  have he1b2 : entry M 1 (b' + 1 + 1) ≤ entry M 1 (b' + 1) := hZ1 (b' + 1) (b' + 1 + 1) (by omega) hb2ch
  have he0b2 := hR0 _ _ hb2
  have hcolbb : col M (b' + 1) = bump M b' := by
    rw [entry_col M (b' + 1)]; show _ = (entry M 0 b' + 1, entry M 1 b', 1); simp only [Prod.mk.injEq]; omega
  obtain ⟨hb22, hb2leaf, hb1last, hb'last⟩ := hBL b' (b' + 1) (b' + 1 + 1) hb1ch hcolbb hb2ch (by omega)
  -- `c = b' + 3`
  have hc3 : c = b' + 1 + 1 + 1 := by
    have hcge : b' + 1 + 1 + 1 ≤ c := by
      by_contra hlt
      have : c = b' + 1 ∨ c = b' + 1 + 1 := by omega
      rcases this with rfl | rfl
      · rw [hb1] at hcr; cases hcr; omega
      · rw [hb2] at hcr; cases hcr; omega
    by_contra hne
    have h3c : b' + 1 + 1 + 1 < c := by omega
    have hAr3 : Anc0 M r (b' + 1 + 1 + 1) :=
      anc_between (Anc0.step hcr (Anc0.refl r)) _ (by omega) (by omega)
    by_cases he3 : entry M 0 b' < entry M 0 (b' + 1 + 1 + 1)
    · have hAb2 : Anc0 M b' (b' + 1 + 1) := Anc0.step hb2 (Anc0.step hb1 (Anc0.refl b'))
      have hA3 := anc0_next hAb2 he3
      obtain ⟨p, hpb, hp3⟩ := anc0_child hA3 (by omega)
      have hpch : p ∈ children M b' := mem_children_iff.mpr ⟨by have := hp3.le; omega, hpb⟩
      have hpb1 : p = b' + 1 := by
        have := List.mem_of_getLast? hb'last
        have hmax : p ≤ b' + 1 := by
          obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp hb'last
          have hs := children_sorted M b'
          rw [hl] at hs hpch
          rcases List.mem_append.mp hpch with h' | h'
          · have := (List.pairwise_append.mp hs).2.2 p h' (b' + 1) (by simp); omega
          · simp at h'; omega
        have := par_lt M 0 p b' hpb
        omega
      subst hpb1
      obtain ⟨p', hpb', hp3'⟩ := anc0_child hp3 (by omega)
      have hp'ch : p' ∈ children M (b' + 1) := mem_children_iff.mpr ⟨by have := hp3'.le; omega, hpb'⟩
      have hp'b2 : p' = b' + 1 + 1 := by
        have hmax : p' ≤ b' + 1 + 1 := by
          obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp hb1last
          have hs := children_sorted M (b' + 1)
          rw [hl] at hs hp'ch
          rcases List.mem_append.mp hp'ch with h' | h'
          · have := (List.pairwise_append.mp hs).2.2 p' h' (b' + 1 + 1) (by simp); omega
          · simp at h'; omega
        have := par_lt M 0 p' (b' + 1) hpb'
        omega
      subst hp'b2
      obtain ⟨p'', hpb'', hp3''⟩ := anc0_child hp3' (by omega)
      have : p'' ∈ children M (b' + 1 + 1) :=
        mem_children_iff.mpr ⟨by have := hp3''.le; omega, hpb''⟩
      rw [hb2leaf] at this; simp at this
    · have hne3 : r ≠ b' + 1 + 1 + 1 := by omega
      have he3r := anc0_e0_lt hAr3 hne3
      obtain ⟨p, hp⟩ := par0_of_anc hAr3 hne3
      have hAp := anc0_par hAr3 hne3 hp
      have he0p := hR0 _ p hp
      have hpr : r = p := anc0_eq_of_e0 hAp (Anc0.refl p) (by omega)
      subst hpr
      have h3ch : b' + 1 + 1 + 1 ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
      exact hnb _ h3ch ⟨by omega, h3c⟩
  -- `b' + 2` is upgraded to `c`
  have hP1b2 : par M 1 (b' + 1 + 1) = some r := by
    show climb (par M 0) (fun q => decide (entry M 1 q < entry M 1 (b' + 1 + 1))) (b' + 1 + 1 + 1)
      (par M 0 (b' + 1 + 1)) = some r
    rw [hb2]
    have h1 : ¬ entry M 1 (b' + 1) < entry M 1 (b' + 1 + 1) := by omega
    have h2 : ¬ entry M 1 b' < entry M 1 (b' + 1 + 1) := by omega
    have h3 : entry M 1 r < entry M 1 (b' + 1 + 1) := by omega
    simp [climb, h1, h2, h3, hb1, hb'r]
  have hP1c : par M 1 c = some r := par1_of_child hcr he1c
  have hu : upg M (b' + 1 + 1) = some c := by
    unfold upg
    rw [if_neg (show ¬ (entry M 1 (b' + 1 + 1) = 0 ∨ entry M 2 (b' + 1 + 1) = 1 ∨
      b' + 1 + 1 + 1 = M.length) by omega), hP1b2]
    dsimp only
    rw [← hc3, if_pos ⟨hP1c, by rw [entry_col M c]; simp only [Prod.mk.injEq]; omega⟩]
  unfold isUpg
  rw [List.any_eq_true]
  exact ⟨b' + 1 + 1, List.mem_range.mpr (by omega), by simp [hu]⟩

end

/-- **R-S1**: every standard matrix other than SRO satisfies `S1` (shared history invariant). -/
def S1Std : Prop := ∀ M, Std M → M ≠ SRO → S1 M

/-- **PassRootRes from S1** (and the structural invariants of `SInvX`). -/
theorem passRootRes_of_S1 {M : Mat} {r L : Nat} {ρ : Valn} (hX : SInvX M) (hS1 : S1 M)
    (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    PassRootRes M r L ρ :=
  passRootRes_of_eqSib hX.toSInv
    (eqSibUpg_of_S1 hX.r0p hX.r1s hX.z2 hX.loc.1 hX.loc.2.1 hX.loc.2.2.1 hX.loc.2.2.2 hS1) hlen h1 hx2

end Ytosk
