/-
**S1 は t = 1 の展開で保たれる（2026-10-16、t0）。**

t = 1 の展開 N = gexp M r L d0 0 n（r = P_1(x) は x の行 0 の祖先、d0 = e0 x − e0 r ≥ 1）は、
第 k コピーが悪い部分の行 0 を k·d0 だけ一様にずらしたもの（行 1・行 2 は同じ）。
S1 の並びの形 `S1s`（V3S1T0）を、t = 0 と同じ 3 つの場合で示す。
- a ≥ x: 1 周期前の組 (a − L, b − L) に帰着（行 0 のずれ `shc` は辞書式の順序を変えない）。
- a, b < x: M の組。b の部分木が x まで届くとき、N は x で col N x = (e0 x, e1 r, e2 r) < col x で続く。
- a < x ≤ b: b = x（コピーの行 0 は e0 x 以上で、等しいのは x だけ）、a は M での x の前の兄弟。
-/
import Ytosk.V3S1T0

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## 行 0 のずれ -/

/-- Shift row 0 by `d`. -/
def shc (d : Nat) (p : Nat × Nat × Nat) : Nat × Nat × Nat := (p.1 + d, p.2.1, p.2.2)

theorem colLtB_shc (d : Nat) (p q : Nat × Nat × Nat) : colLtB (shc d p) (shc d q) = colLtB p q := by
  unfold colLtB shc
  simp only [decide_eq_decide]
  omega

theorem shc_beq (d : Nat) (p q : Nat × Nat × Nat) : (shc d p == shc d q) = (p == q) := by
  obtain ⟨p1, p2, p3⟩ := p
  obtain ⟨q1, q2, q3⟩ := q
  unfold shc
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.decide_eq_true]
  by_cases h : p1 = q1 ∧ p2 = q2 ∧ p3 = q3
  · obtain ⟨rfl, rfl, rfl⟩ := h; simp
  · have : ¬ (p1 + d = q1 + d ∧ p2 = q2 ∧ p3 = q3) := fun h' => h ⟨by omega, h'.2⟩
    simp [this, h]

theorem seqLtB_map_shc (d : Nat) : ∀ A B : Mat, seqLtB (A.map (shc d)) (B.map (shc d)) = seqLtB A B
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: A, q :: B => by
    simp only [List.map_cons, seqLtB, colLtB_shc, shc_beq, seqLtB_map_shc d A B]

theorem takeWhile_map' {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ l : List α, (l.map f).takeWhile p = (l.takeWhile (p ∘ f)).map f
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.takeWhile_cons, Function.comp]
    split <;> simp [takeWhile_map' f p l]

/-! ## 行 0 の祖先の間 -/

theorem anc0_between {M : Mat} {r x : Nat} (h : Anc0 M r x) :
    ∀ j, r < j → j ≤ x → entry M 0 r < entry M 0 j := by
  induction h with
  | refl => intro j h1 h2; omega
  | @step b c hp ha ih =>
    intro j h1 h2
    have hs := (par0_spec _).mp hp
    rcases Nat.lt_or_ge j b with h3 | h3
    · exact ih j h1 (by omega)
    rcases Nat.eq_or_lt_of_le h3 with rfl | h4
    · exact ih _ h1 (le_refl _)
    · have hle : entry M 0 r ≤ entry M 0 b := by
        rcases Nat.eq_or_lt_of_le ha.le with e | e
        · rw [e]
        · exact le_of_lt (ih b e (le_refl _))
      rcases Nat.eq_or_lt_of_le h2 with rfl | h5
      · omega
      · have := hs.2.2 j h4 h5; omega

/-! ## t = 1 の展開 N の列 -/

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
  (he1 : entry M 1 r < entry M 1 (r + L)) (hn : 1 ≤ n)
include hlen hL hA hd0e he1 hn

omit hL hA hd0e he1 hn in
theorem lenT1 : (TRIO.gexp M r L d0 0 n).length = r + n * L := TRIO.gexp_length hlen

omit hL hA hd0e he1 in
theorem colT1_low {i : Nat} (hi : i < r + L) : col (TRIO.gexp M r L d0 0 n) i = col M i := by
  unfold col
  rcases Nat.lt_or_ge i r with h | h
  · rw [TRIO.gexp_getD_low hlen h]
  · have e := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := 0) (n := n)
      (k := 0) (q := i - r) hlen (by omega) (by omega)
    rw [show r + (0 * L + (i - r)) = i by omega] at e
    rw [e, show r + (i - r) = i by omega]
    simp only [Nat.zero_mul, Nat.add_zero, ite_self]
    unfold TRIO.entry; rfl

omit hL hA hd0e he1 in
theorem entryT1_low {i : Nat} (hi : i < r + L) : entry (TRIO.gexp M r L d0 0 n) 0 i = entry M 0 i := by
  rw [entry0_col, entry0_col, colT1_low hlen hn hi]

omit hA hd0e he1 hn in
/-- **The copies are periodic up to the row-0 shift.** -/
theorem colT1_per {i : Nat} (hi : r + L ≤ i) (hiN : i < r + n * L) :
    col (TRIO.gexp M r L d0 0 n) i = shc d0 (col (TRIO.gexp M r L d0 0 n) (i - L)) := by
  obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (n := n) hL (by omega) hiN
  have hk1 : 1 ≤ k := by
    by_contra h; have : k = 0 := by omega
    subst this; omega
  have e : r + (k * L + q) - L = r + ((k - 1) * L + q) := by
    have : k * L = (k - 1) * L + L := by
      rw [← Nat.succ_mul, show (k - 1).succ = k by omega]
    omega
  unfold col
  rw [e, TRIO.gexp_getD_mir hlen hk hq, TRIO.gexp_getD_mir hlen (by omega) hq]
  unfold shc
  simp only [Nat.mul_zero, ite_self, Nat.add_zero, Prod.mk.injEq, and_true]
  have : k * d0 = (k - 1) * d0 + d0 := by
    rw [← Nat.succ_mul, show (k - 1).succ = k by omega]
  omega

omit hA hd0e he1 hn in
theorem entryT1_per {i : Nat} (hi : r + L ≤ i) (hiN : i < r + n * L) :
    entry (TRIO.gexp M r L d0 0 n) 0 i = entry (TRIO.gexp M r L d0 0 n) 0 (i - L) + d0 := by
  rw [entry0_col, entry0_col, colT1_per hlen hL hi hiN]; rfl

omit he1 hn in
/-- The bad part lies strictly above `r` in row 0. -/
theorem e0T1_bad {j : Nat} (h1 : r < j) (h2 : j ≤ r + L) : entry M 0 r < entry M 0 j :=
  anc0_between hA j h1 h2

omit he1 hn in
theorem d0_pos : 0 < d0 := by
  have := e0T1_bad hlen hL hA hd0e (j := r + L) (by omega) (le_refl _); omega

omit he1 in
/-- Every column of the copies after the first is at least `x` in row 0, with equality only at `x`. -/
theorem e0T1_copies {i : Nat} (hi : r + L ≤ i) (hiN : i < r + n * L) :
    entry M 0 (r + L) ≤ entry (TRIO.gexp M r L d0 0 n) 0 i ∧
      (i ≠ r + L → entry M 0 (r + L) < entry (TRIO.gexp M r L d0 0 n) 0 i) := by
  have hd := d0_pos hlen hL hA hd0e
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [entryT1_per hlen hL hi hiN]
    rcases Nat.lt_or_ge (i - L) (r + L) with h | h
    · rw [entryT1_low hlen hn h]
      rcases Nat.eq_or_lt_of_le (show r ≤ i - L by omega) with h' | h'
      · rw [← h']; constructor
        · omega
        · intro hne; omega
      · have := e0T1_bad hlen hL hA hd0e (j := i - L) h' (by omega)
        constructor <;> [omega; (intro _; omega)]
    · have := ih (i - L) (by omega) h (by omega)
      constructor <;> [omega; (intro _; omega)]

omit hL hA hd0e he1 hn in
theorem takeN_T1 (hn : 1 ≤ n) : (TRIO.gexp M r L d0 0 n).take (r + L) = M.take (r + L) := by
  have hlN := lenT1 (d0 := d0) (n := n) hlen
  have hnL : r + L ≤ r + n * L := by
    have := Nat.mul_le_mul_right L hn; omega
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_take] at h1 h2
    simp only [List.getElem_take]
    have := colT1_low (d0 := d0) hlen hn (i := i) (by omega)
    rwa [col_getElem (by omega), col_getElem (by omega)] at this

omit hL hA hd0e he1 in
theorem dropT1_split {i : Nat} (hi : i ≤ r + L) :
    (TRIO.gexp M r L d0 0 n).drop i = (M.take (r + L)).drop i ++ (TRIO.gexp M r L d0 0 n).drop (r + L) := by
  conv_lhs => rw [← List.take_append_drop (r + L) (TRIO.gexp M r L d0 0 n)]
  rw [List.drop_append_of_le_length (by
    simp only [List.length_take, lenT1 hlen]
    have := Nat.mul_le_mul_right L hn; omega), takeN_T1 hlen hn]

omit hA hd0e he1 hn in
/-- **The drop is a prefix of the shifted drop one period earlier.** -/
theorem dropT1_prefix {i : Nat} (hi : r + L ≤ i) (hiN : i ≤ r + n * L) :
    (TRIO.gexp M r L d0 0 n).drop i <+: ((TRIO.gexp M r L d0 0 n).drop (i - L)).map (shc d0) := by
  have hlN := lenT1 (d0 := d0) (n := n) hlen
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_take, List.length_map]; omega
  · intro k h1 h2
    simp only [List.length_drop] at h1
    simp only [List.getElem_drop, List.getElem_take, List.getElem_map]
    have e := colT1_per (d0 := d0) (n := n) hlen hL (i := i + k) (by omega) (by omega)
    rw [col_getElem (by omega), col_getElem (by omega)] at e
    convert e using 3; omega

/-- **S1 is kept by the `t = 1` expansion** (sequence form). -/
theorem S1s_t1 (hS : S1s M) : S1s (TRIO.gexp M r L d0 0 n) := by
  have hlN := lenT1 (d0 := d0) (n := n) hlen
  have hd := d0_pos hlen hL hA hd0e
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b hab hbN he hpar hbet
  rw [hlN] at hbN
  have hxN : r + L ≤ r + n * L := by have := Nat.mul_le_mul_right L hn; omega
  rcases Nat.lt_or_ge a (r + L) with ha | ha
  · -- facts about `x` in `N`
    have hcolx : r + L < r + n * L → col (TRIO.gexp M r L d0 0 n) (r + L) =
        (entry M 0 (r + L), entry M 1 r, entry M 2 r) := by
      intro h
      rw [colT1_per hlen hL (le_refl _) h, show r + L - L = r by omega, colT1_low hlen hn (by omega)]
      unfold shc; rw [hd0e]; unfold col entry; simp
    have hlt : ∀ c : Nat × Nat × Nat, c = (entry M 0 (r + L), entry M 1 r, entry M 2 r) →
        colLtB c (col M (r + L)) = true := by
      intro c hc; subst hc
      unfold colLtB; simp only [decide_eq_true_eq]
      right; refine ⟨by rw [entry0_col], Or.inl ?_⟩
      have : entry M 1 (r + L) = (col M (r + L)).2.1 := by unfold entry col; simp
      omega
    rcases Nat.lt_or_ge b (r + L) with hb | hb
    · -- both before `x`
      have heM : entry M 0 a = entry M 0 b := by
        rw [← entryT1_low hlen hn ha, ← entryT1_low hlen hn hb]; exact he
      have hparM : ∃ p, par M 0 a = some p := by
        obtain ⟨p, hp'⟩ := hpar
        exact ⟨p, by rw [← hp']; exact par0_congr_e0 (fun q hq => (entryT1_low hlen hn (by omega)).symm)⟩
      have hbetM : ∀ j, a < j → j < b → entry M 0 a < entry M 0 j := fun j h1 h2 => by
        have := hbet j h1 h2
        rwa [entryT1_low hlen hn (by omega), entryT1_low hlen hn (by omega)] at this
      have hM := hS a b hab (by omega) heM hparM hbetM
      have hmemb : col M b ∈ (M.take (r + L)).drop (a + 1) := by
        rw [← col_take M hb]; exact mem_drop_col (by omega) (by rw [List.length_take]; omega)
      have hsa : subT (TRIO.gexp M r L d0 0 n) a = subT M a := by
        unfold subT
        rw [colT1_low hlen hn ha, entryT1_low hlen hn ha, dropT1_split hlen hn (by omega),
          dropM_split hlen (by omega)]
        congr 1
        have hf : ∃ y ∈ (M.take (r + L)).drop (a + 1),
            (fun q : Nat × Nat × Nat => decide (entry M 0 a < q.1)) y = false :=
          ⟨col M b, hmemb, by simp [← entry0_col, heM]⟩
        rw [← takeWhile_prefix_eq _ (List.prefix_append _ _) hf,
          ← takeWhile_prefix_eq _ (List.prefix_append _ _) hf]
      rw [hsa]
      set pb : Nat × Nat × Nat → Bool := fun q => decide (entry M 0 b < q.1) with hpb
      rcases takeWhile_all_or pb ((M.take (r + L)).drop (b + 1)) with hall | hf
      · have eM : subT M b = (col M b :: (M.take (r + L)).drop (b + 1)) ++ [col M (r + L)].takeWhile pb := by
          unfold subT; rw [dropM_split hlen (by omega), takeWhile_append_all _ _ _ hall]; rfl
        have eN : subT (TRIO.gexp M r L d0 0 n) b =
            (col M b :: (M.take (r + L)).drop (b + 1)) ++
              ((TRIO.gexp M r L d0 0 n).drop (r + L)).takeWhile pb := by
          unfold subT
          rw [colT1_low hlen hn hb, entryT1_low hlen hn hb, dropT1_split hlen hn (by omega),
            takeWhile_append_all _ _ _ hall]; rfl
        rw [eN]
        cases hc : ((TRIO.gexp M r L d0 0 n).drop (r + L)).takeWhile pb with
        | nil =>
          rw [List.append_nil]
          cases hq : seqLtB (subT M a) (col M b :: (M.take (r + L)).drop (b + 1))
          · rfl
          · have := seqLtB_prefix (B := subT M b) hq (by rw [eM]; exact List.prefix_append _ _)
            rw [hM] at this; exact absurd this (by simp)
        | cons c0 rest =>
          have hxlt : r + L < r + n * L := by
            by_contra h
            have : (TRIO.gexp M r L d0 0 n).drop (r + L) = [] := List.drop_eq_nil_of_le (by omega)
            rw [this] at hc; simp at hc
          rw [List.drop_eq_getElem_cons (by omega), ← col_getElem (by omega), hcolx hxlt,
            List.takeWhile_cons] at hc
          split at hc
          · rename_i hpr
            simp only [List.cons.injEq] at hc
            obtain ⟨rfl, rfl⟩ := hc
            have hpx : pb (col M (r + L)) = true := by
              simp only [hpb, decide_eq_true_eq] at hpr ⊢
              rw [← entry0_col]; exact hpr
            rw [eM, List.takeWhile_cons, if_pos hpx, List.takeWhile_nil] at hM
            exact seqLtB_snoc_lt _ hM (hlt _ rfl)
          · simp at hc
      · have hsb : subT (TRIO.gexp M r L d0 0 n) b = subT M b := by
          unfold subT
          rw [colT1_low hlen hn hb, entryT1_low hlen hn hb, dropT1_split hlen hn (by omega),
            dropM_split hlen (by omega)]
          congr 1
          rw [← takeWhile_prefix_eq _ (List.prefix_append _ _) hf,
            ← takeWhile_prefix_eq _ (List.prefix_append _ _) hf]
        rw [hsb]; exact hM
    · -- `a` before `x`, `b` in the copies: `b = x`, and `a` is the previous sibling of `x` in `M`
      have hcp := e0T1_copies hlen hL hA hd0e hn (i := b) hb hbN
      have hxlt : r + L < r + n * L := by omega
      have hcx := (e0T1_copies hlen hL hA hd0e hn (i := r + L) (le_refl _) hxlt).1
      have hbx : b = r + L := by
        by_contra hne
        have h1 := hcp.2 hne
        have h2 := hbet (r + L) (by omega) (by omega)
        have h3 : entry (TRIO.gexp M r L d0 0 n) 0 (r + L) = entry M 0 (r + L) := by
          rw [entry0_col, hcolx hxlt]
        omega
      subst hbx
      have hex : entry (TRIO.gexp M r L d0 0 n) 0 (r + L) = entry M 0 (r + L) := by
        rw [entry0_col, hcolx hxlt]
      have heM : entry M 0 a = entry M 0 (r + L) := by rw [← entryT1_low hlen hn ha, he, hex]
      have hparM : ∃ p, par M 0 a = some p := by
        obtain ⟨p, hp'⟩ := hpar
        exact ⟨p, by rw [← hp']; exact par0_congr_e0 (fun q hq => (entryT1_low hlen hn (by omega)).symm)⟩
      have hbetM : ∀ j, a < j → j < r + L → entry M 0 a < entry M 0 j := fun j h1 h2 => by
        have := hbet j h1 h2
        rwa [entryT1_low hlen hn (by omega), entryT1_low hlen hn (by omega)] at this
      have hM := hS a (r + L) ha (by omega) heM hparM hbetM
      -- `M`'s subtree of `x` is `[col x]`; `a`'s subtree is the same in `N`
      have hsx : subT M (r + L) = [col M (r + L)] := by
        unfold subT; rw [List.drop_eq_nil_of_le (by omega)]; rfl
      have hmemb : col M (r + L) ∈ M.drop (a + 1) := mem_drop_col (by omega) (by omega)
      have hsa : subT (TRIO.gexp M r L d0 0 n) a = subT M a := by
        unfold subT
        rw [colT1_low hlen hn ha, entryT1_low hlen hn ha, dropT1_split hlen hn (by omega),
          dropM_split hlen (by omega)]
        congr 1
        rw [dropM_split hlen (by omega)] at hmemb
        rcases List.mem_append.mp hmemb with hm | hm
        · exact absurd (List.mem_drop_iff_getElem.mp hm) (by
            rintro ⟨k, hk, e⟩
            simp only [List.length_take] at hk
            rw [List.getElem_take, ← col_getElem (by omega)] at e
            have : entry M 0 (a + 1 + k) = entry M 0 (r + L) := by rw [entry0_col, entry0_col, e]
            have := hbetM (a + 1 + k) (by omega) (by omega); omega)
        · simp only [List.mem_singleton] at hm
          have hfx : (fun q : Nat × Nat × Nat => decide (entry M 0 a < q.1)) (col M (r + L)) = false := by
            simp [← entry0_col, heM]
          rw [takeWhile_append_all _ _ _ ?_, takeWhile_append_all _ _ _ ?_]
          · congr 1
            rw [List.drop_eq_getElem_cons (by omega), ← col_getElem (by omega), hcolx hxlt,
              List.takeWhile_cons, List.takeWhile_cons, if_neg, if_neg]
            · simpa using hfx
            · simp only [decide_eq_true_eq, not_lt]; rw [heM]
          all_goals
            intro y hy
            obtain ⟨k, hk, rfl⟩ := List.mem_drop_iff_getElem.mp hy
            simp only [List.length_take] at hk
            rw [List.getElem_take, ← col_getElem (by omega), ← entry0_col]
            simp only [decide_eq_true_eq]
            exact hbetM _ (by omega) (by omega)
      rw [hsa]
      unfold subT
      rw [hcolx hxlt]
      rw [hsx] at hM
      have := seqLtB_snoc_lt (P := []) ((TRIO.gexp M r L d0 0 n).drop (r + L + 1)
        |>.takeWhile (fun q => decide (entry (TRIO.gexp M r L d0 0 n) 0 (r + L) < q.1))) hM (hlt _ rfl)
      simpa using this
  · -- `a` in the copies: one period earlier
    have hbx : r + L ≤ b := by omega
    have heA := entryT1_per (d0 := d0) (n := n) hlen hL ha (by omega)
    have heB := entryT1_per (d0 := d0) (n := n) hlen hL hbx hbN
    have he' : entry (TRIO.gexp M r L d0 0 n) 0 (a - L) = entry (TRIO.gexp M r L d0 0 n) 0 (b - L) := by
      have := he; rw [heA, heB] at this; omega
    have hpar' : ∃ p, par (TRIO.gexp M r L d0 0 n) 0 (a - L) = some p := by
      apply par0_exists
      rcases Nat.eq_or_lt_of_le (show r ≤ a - L by omega) with h3 | h3
      · -- `a = x`: no sibling after it
        exfalso
        have hax : a = r + L := by omega
        subst hax
        have h1 := (e0T1_copies hlen hL hA hd0e hn (i := b) hbx hbN).2 (by omega)
        have h2 : entry (TRIO.gexp M r L d0 0 n) 0 (r + L) = entry M 0 (r + L) := by
          rw [entryT1_per hlen hL (le_refl _) (by omega), show r + L - L = r by omega,
            entryT1_low hlen hn (by omega), hd0e]
        omega
      · refine ⟨r, h3, ?_⟩
        rw [entryT1_low hlen hn (by omega : r < r + L)]
        rcases Nat.lt_or_ge (a - L) (r + L) with h4 | h4
        · rw [entryT1_low hlen hn h4]; exact e0T1_bad hlen hL hA hd0e h3 (by omega)
        · have := (e0T1_copies hlen hL hA hd0e hn (i := a - L) h4 (by omega)).1
          have := e0T1_bad hlen hL hA hd0e (j := r + L) (by omega) (le_refl _); omega
    have hbet' : ∀ j, a - L < j → j < b - L →
        entry (TRIO.gexp M r L d0 0 n) 0 (a - L) < entry (TRIO.gexp M r L d0 0 n) 0 j := by
      intro j h1 h2
      have := hbet (j + L) (by omega) (by omega)
      rw [heA, entryT1_per (d0 := d0) (n := n) hlen hL (i := j + L) (by omega) (by omega),
        show j + L - L = j by omega] at this
      omega
    have IH := ih (a - L) (by omega) (b - L) (by omega) (by rw [hlN]; omega) he' hpar' hbet'
    have hmemb : col (TRIO.gexp M r L d0 0 n) b ∈ (TRIO.gexp M r L d0 0 n).drop (a + 1) :=
      mem_drop_col (by omega) (by rw [hlN]; omega)
    have hpr : ∀ q : Nat × Nat × Nat,
        decide (entry (TRIO.gexp M r L d0 0 n) 0 a < (shc d0 q).1) =
          decide (entry (TRIO.gexp M r L d0 0 n) 0 (a - L) < q.1) := by
      intro q; unfold shc; rw [heA]; simp only [decide_eq_decide]; omega
    have hpb : ∀ q : Nat × Nat × Nat,
        decide (entry (TRIO.gexp M r L d0 0 n) 0 b < (shc d0 q).1) =
          decide (entry (TRIO.gexp M r L d0 0 n) 0 (b - L) < q.1) := by
      intro q; unfold shc; rw [heB]; simp only [decide_eq_decide]; omega
    have hsa : subT (TRIO.gexp M r L d0 0 n) a = (subT (TRIO.gexp M r L d0 0 n) (a - L)).map (shc d0) := by
      unfold subT
      rw [colT1_per (d0 := d0) (n := n) hlen hL ha (by omega), List.map_cons]
      congr 1
      have hpre := dropT1_prefix (d0 := d0) (n := n) hlen hL (i := a + 1) (by omega) (by omega)
      rw [show a + 1 - L = a - L + 1 by omega] at hpre
      rw [takeWhile_prefix_eq _ hpre ⟨_, hmemb, by
        simp only [decide_eq_false_iff_not, not_lt]; rw [← entry0_col, he]⟩, takeWhile_map']
      congr 1
      congr 1
      exact funext hpr
    have hsb : subT (TRIO.gexp M r L d0 0 n) b <+: (subT (TRIO.gexp M r L d0 0 n) (b - L)).map (shc d0) := by
      unfold subT
      rw [colT1_per (d0 := d0) (n := n) hlen hL hbx hbN, List.map_cons]
      apply List.prefix_cons_inj _ |>.mpr
      have hpre := dropT1_prefix (d0 := d0) (n := n) hlen hL (i := b + 1) (by omega) (by omega)
      rw [show b + 1 - L = b - L + 1 by omega] at hpre
      have := takeWhile_prefix (fun q => decide (entry (TRIO.gexp M r L d0 0 n) 0 b < q.1)) hpre
      rw [takeWhile_map'] at this
      have e : List.takeWhile ((fun q => decide (entry (TRIO.gexp M r L d0 0 n) 0 b < q.1)) ∘ shc d0)
          (List.drop (b - L + 1) (TRIO.gexp M r L d0 0 n)) =
          List.takeWhile (fun q => decide (entry (TRIO.gexp M r L d0 0 n) 0 (b - L) < q.1))
          (List.drop (b - L + 1) (TRIO.gexp M r L d0 0 n)) := by
        congr 1; exact funext hpb
      rwa [e] at this
    cases hq : seqLtB (subT (TRIO.gexp M r L d0 0 n) a) (subT (TRIO.gexp M r L d0 0 n) b)
    · rfl
    · rw [hsa] at hq
      have h2 := seqLtB_prefix hq hsb
      rw [seqLtB_map_shc, IH] at h2; exact absurd h2 (by simp)

/-- **S1 of `N = M[n]`** for the `t = 1` expansion. -/
theorem S1_t1 (hR0 : R0P M) (hR0N : R0P (TRIO.gexp M r L d0 0 n)) (hS : S1 M) :
    S1 (TRIO.gexp M r L d0 0 n) :=
  S1_of_S1s hR0N (S1s_t1 hlen hL hA hd0e he1 hn (S1s_of_S1 hR0 hS))

end

end Ytosk
