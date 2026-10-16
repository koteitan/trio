/-
**S1 は t = 0 の展開で保たれる（2026-10-16、t0）。**

t = 0 の展開は写しだけ: N = M[n] = G ++ B^n（G = M.take r、B = M[r..x−1]、x = r + L は最後の列）。
S1（兄弟の部分木の列の並びは辞書式で増えない、V3PDef）を、隣り合う兄弟 a < b を
「行 0 が同じで、間の列の行 0 はどれも大きい」という並びの形 `S1s` で扱う（R0P のもとで同値）。
-/
import Ytosk.V3PStruct
import Ytosk.V3InvSeed

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## t = 0 の展開は写し -/

/-- **The `t = 0` expansion is a plain copy**: `gexp M r L 0 0 n = M.take r ++ (M[r, r+L))^n`. -/
theorem gexp_t0_eq {M : Mat} {r L : Nat} (hrL : r + L ≤ M.length) (n : Nat) :
    TRIO.gexp M r L 0 0 n = M.take r ++ (List.replicate n ((M.drop r).take L)).flatten := by
  unfold TRIO.gexp TRIO.gcopies
  congr 1
  have hc : ∀ k, TRIO.gcopy M r L 0 0 k = (M.drop r).take L := by
    intro k
    unfold TRIO.gcopy
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range', List.getElem_take, List.getElem_drop,
        Nat.mul_zero, Nat.add_zero, ite_self]
      unfold TRIO.entry
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h1; omega)]
      simp
  simp only [hc]
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ']; simp

/-! ## S1 の並びの形 -/

/-- **S1 in sequence form**: `a < b` with the same row 0, a parent of `a`, and every column strictly between
with a larger row 0 (i.e. consecutive siblings). -/
def S1s (M : Mat) : Prop :=
  ∀ a b, a < b → b < M.length → entry M 0 a = entry M 0 b → (∃ p, par M 0 a = some p) →
    (∀ j, a < j → j < b → entry M 0 a < entry M 0 j) → seqLtB (subT M a) (subT M b) = false

/-- A sorted list with `a < b` both in it and nothing strictly between splits as `l₁ ++ a :: b :: l₂`. -/
theorem sorted_split : ∀ {l : List Nat} {a b : Nat}, l.Pairwise (· < ·) → a ∈ l → b ∈ l → a < b →
    (∀ j ∈ l, a < j → j < b → False) → ∃ l₁ l₂, l = l₁ ++ a :: b :: l₂
  | [], _, _, _, ha, _, _, _ => by simp at ha
  | c :: l, a, b, hs, ha, hb, hab, hn => by
    have hs' := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp ha with rfl | ha'
    · -- `a` is the head: `b` is the next element
      rcases List.mem_cons.mp hb with rfl | hb'
      · omega
      cases l with
      | nil => simp at hb'
      | cons d l =>
        rcases List.mem_cons.mp hb' with rfl | hb''
        · exact ⟨[], l, rfl⟩
        · have hdb : d < b := (List.pairwise_cons.mp hs'.2).1 b hb''
          exact absurd (hn d (by simp) (hs'.1 d (by simp)) hdb) id
    · rcases List.mem_cons.mp hb with rfl | hb'
      · have := hs'.1 a ha'; omega
      obtain ⟨l₁, l₂, e⟩ := sorted_split hs'.2 ha' hb' hab (fun j hj => hn j (by simp [hj]))
      exact ⟨c :: l₁, l₂, by rw [e]; rfl⟩

/-- In a split sorted list, nothing lies strictly between `a` and `b`. -/
theorem split_no_between {l₁ l₂ : List Nat} {a b : Nat} (hs : (l₁ ++ a :: b :: l₂).Pairwise (· < ·))
    {j : Nat} (hj : j ∈ l₁ ++ a :: b :: l₂) (h1 : a < j) (h2 : j < b) : False := by
  rw [List.pairwise_append] at hs
  rcases List.mem_append.mp hj with hj | hj
  · have := hs.2.2 j hj a (by simp); omega
  · have hs2 := List.pairwise_cons.mp hs.2.1
    rcases List.mem_cons.mp hj with rfl | hj
    · omega
    rcases List.mem_cons.mp hj with rfl | hj
    · omega
    · have := (List.pairwise_cons.mp hs2.2).1 j hj; omega

theorem S1s_of_S1 {M : Mat} (hR0 : R0P M) (h : S1 M) : S1s M := by
  intro a b hab hbM he ⟨p, hpa⟩ hbet
  have hpa' := (par0_spec M).mp hpa
  have hpb : par M 0 b = some p := by
    refine (par0_spec M).mpr ⟨by omega, by omega, fun j hj1 hj2 => ?_⟩
    rcases Nat.lt_trichotomy j a with h1 | rfl | h1
    · have := hpa'.2.2 j hj1 h1; omega
    · omega
    · have := hbet j h1 hj2; omega
  have haM : a < M.length := by omega
  have hac : a ∈ children M p := mem_children_iff.mpr ⟨haM, hpa⟩
  have hbc : b ∈ children M p := mem_children_iff.mpr ⟨hbM, hpb⟩
  obtain ⟨l₁, l₂, e⟩ := sorted_split (children_sorted M p) hac hbc hab (fun j hj h1 h2 => by
    have hpj := (mem_children_iff.mp hj).2
    have := hbet j h1 h2
    rw [hR0 j p hpj, hR0 a p hpa] at this; omega)
  exact h p l₁ l₂ a b e

theorem S1_of_S1s {M : Mat} (hR0 : R0P M) (h : S1s M) : S1 M := by
  intro p l₁ l₂ a b hch
  have hs := children_sorted M p
  rw [hch] at hs
  have hac : a ∈ children M p := by rw [hch]; simp
  have hbc : b ∈ children M p := by rw [hch]; simp
  have hab : a < b := by
    have := (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 b (by simp); exact this
  have hpa := (mem_children_iff.mp hac).2
  have hpb := (mem_children_iff.mp hbc).2
  have he : entry M 0 a = entry M 0 b := by rw [hR0 a p hpa, hR0 b p hpb]
  have hpb' := (par0_spec M).mp hpb
  apply h a b hab (mem_children_iff.mp hbc).1 he ⟨p, hpa⟩
  intro j h1 h2
  have hpa' := (par0_spec M).mp hpa
  have hle := hpb'.2.2 j (by omega) h2
  rcases Nat.lt_or_ge (entry M 0 a) (entry M 0 j) with h3 | h3
  · exact h3
  · exfalso
    have := hpa'.2.1
    have := (mem_children_iff.mp hbc).1
    have hpj : par M 0 j = some p := (par0_spec M).mpr ⟨by omega, by omega, fun i hi1 hi2 => by
      have := hpb'.2.2 i hi1 (by omega); omega⟩
    have hjc : j ∈ children M p := mem_children_iff.mpr ⟨by omega, hpj⟩
    rw [hch] at hjc
    exact split_no_between hs hjc h1 h2

/-! ## 辞書式順序と takeWhile の補題 -/

theorem seqLtB_self : ∀ A : Mat, seqLtB A A = false
  | [] => rfl
  | p :: A => by
    simp only [seqLtB, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff]
    refine ⟨?_, seqLtB_self A⟩
    unfold colLtB; simp

/-- A list is never below its own prefix. -/
theorem seqLtB_of_prefix_false : ∀ {A B : Mat}, B <+: A → seqLtB A B = false
  | [], [], _ => rfl
  | [], _ :: _, h => by have := h.length_le; simp at this
  | _ :: _, [], _ => rfl
  | p :: A, q :: B, h => by
    obtain ⟨t, ht⟩ := h
    simp only [List.cons_append, List.cons.injEq] at ht
    obtain ⟨rfl, ht⟩ := ht
    simp only [seqLtB, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff]
    exact ⟨by unfold colLtB; simp, seqLtB_of_prefix_false ⟨t, ht⟩⟩

/-- Not below `P ++ [c]` and `c′ < c`: not below `P ++ c′ :: R`. -/
theorem seqLtB_snoc_lt : ∀ {A P : Mat} {c c' : Nat × Nat × Nat} (R : Mat), seqLtB A (P ++ [c]) = false →
    colLtB c' c = true → seqLtB A (P ++ c' :: R) = false
  | [], [], _, _, _, h, _ => by simp [seqLtB] at h
  | [], _ :: _, _, _, _, h, _ => by simp [seqLtB] at h
  | p :: A, [], c, c', R, h, hc => by
    simp only [List.nil_append, seqLtB, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h ⊢
    unfold colLtB at h hc ⊢
    simp only [decide_eq_false_iff_not, decide_eq_true_eq] at h hc ⊢
    have hne : p ≠ c' := by intro e; subst e; exact h.1 hc
    exact ⟨by omega, Or.inl (beq_eq_false_iff_ne.mpr hne)⟩
  | p :: A, q :: P, c, c', R, h, hc => by
    simp only [List.cons_append, seqLtB, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h ⊢
    refine ⟨h.1, ?_⟩
    rcases h.2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (seqLtB_snoc_lt R h2 hc)

theorem takeWhile_prefix_eq {α : Type} (p : α → Bool) : ∀ {l l' : List α}, l <+: l' → (∃ y ∈ l, p y = false) →
    l.takeWhile p = l'.takeWhile p
  | [], _, _, ⟨_, hy, _⟩ => by simp at hy
  | a :: l, l', h, ⟨y, hy, hpy⟩ => by
    obtain ⟨t, rfl⟩ := h
    simp only [List.cons_append, List.takeWhile_cons]
    split
    · congr 1
      apply takeWhile_prefix_eq p ⟨t, rfl⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · rename_i hpa; rw [hpa] at hpy; simp at hpy
      · exact ⟨y, hy', hpy⟩
    · rfl

theorem takeWhile_prefix {α : Type} (p : α → Bool) : ∀ {l l' : List α}, l <+: l' →
    l.takeWhile p <+: l'.takeWhile p
  | [], _, _ => List.nil_prefix
  | a :: l, l', h => by
    obtain ⟨t, rfl⟩ := h
    simp only [List.cons_append, List.takeWhile_cons]
    split
    · exact List.prefix_cons_inj _ |>.mpr (takeWhile_prefix p ⟨t, rfl⟩)
    · exact List.nil_prefix

theorem takeWhile_append_all {α : Type} (p : α → Bool) : ∀ (l X : List α), (∀ y ∈ l, p y = true) →
    (l ++ X).takeWhile p = l ++ X.takeWhile p
  | [], _, _ => rfl
  | a :: l, X, h => by
    simp only [List.cons_append, List.takeWhile_cons, h a (by simp), if_true]
    rw [takeWhile_append_all p l X (fun y hy => h y (by simp [hy]))]

theorem takeWhile_all_or {α : Type} (p : α → Bool) (l : List α) :
    (∀ y ∈ l, p y = true) ∨ ∃ y ∈ l, p y = false := by
  by_cases h : ∀ y ∈ l, p y = true
  · exact Or.inl h
  · simp only [not_forall] at h
    obtain ⟨y, hy, h⟩ := h; exact Or.inr ⟨y, hy, by simpa using h⟩

/-! ## 行 0 の親の存在 -/

/-- **A row-0 parent exists** when some earlier column has a smaller row 0. -/
theorem par0_exists {M : Mat} {a : Nat} (h : ∃ j, j < a ∧ entry M 0 j < entry M 0 a) :
    ∃ p, par M 0 a = some p := by
  obtain ⟨j, hj, hjv⟩ := h
  let P : Nat → Prop := fun k => entry M 0 k < entry M 0 a
  have hex : ∃ k, k ≤ a - 1 ∧ P k := ⟨j, by omega, hjv⟩
  refine ⟨Nat.findGreatest P (a - 1), (par0_spec M).mpr ⟨?_, ?_, ?_⟩⟩
  · have := Nat.findGreatest_le (P := P) (a - 1); omega
  · obtain ⟨k, hk, hPk⟩ := hex
    exact Nat.findGreatest_spec hk hPk
  · intro i hi1 hi2
    have := Nat.findGreatest_is_greatest hi1 (by omega : i ≤ a - 1)
    simp only [P, not_lt] at this; exact this

theorem entry0_col (M : Mat) (i : Nat) : entry M 0 i = (col M i).1 := by unfold entry col; simp

theorem col_getElem {M : Mat} {i : Nat} (hi : i < M.length) : col M i = M[i] := by
  unfold col; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

/-! ## t = 0 の展開 N の列 -/

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
include hlen hL hp hn

/-- The copies after the first. -/
abbrev cpy (M : Mat) (r L n : Nat) : Mat := (List.replicate (n - 1) ((M.drop r).take L)).flatten

omit hL hp in
theorem gexp_t0_split : TRIO.gexp M r L 0 0 n = M.take (r + L) ++ cpy M r L n := by
  rw [gexp_t0_eq (by omega), List.take_add, List.append_assoc]
  congr 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.replicate_succ, List.flatten_cons]; simp [cpy]

omit hL hp hn in
theorem lenT0 : (TRIO.gexp M r L 0 0 n).length = r + n * L := TRIO.gexp_length hlen

omit hL hp in
theorem colT0_low {i : Nat} (hi : i < r + L) : col (TRIO.gexp M r L 0 0 n) i = col M i := by
  rw [gexp_t0_split hlen hn]
  unfold col
  rw [TRIO.getD_append_left (by rw [List.length_take]; omega), TRIO.getD_take hi]

omit hL hp in
theorem entryT0_low {i : Nat} (hi : i < r + L) : entry (TRIO.gexp M r L 0 0 n) 0 i = entry M 0 i := by
  rw [entry0_col, entry0_col, colT0_low hlen hn hi]

omit hp hn in
/-- **The copies are periodic.** -/
theorem colT0_per {i : Nat} (hi : r + L ≤ i) (hiN : i < r + n * L) :
    col (TRIO.gexp M r L 0 0 n) i = col (TRIO.gexp M r L 0 0 n) (i - L) := by
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
  simp

omit hp hn in
theorem entryT0_per {i : Nat} (hi : r + L ≤ i) (hiN : i < r + n * L) :
    entry (TRIO.gexp M r L 0 0 n) 0 i = entry (TRIO.gexp M r L 0 0 n) 0 (i - L) := by
  rw [entry0_col, entry0_col, colT0_per hlen hL hi hiN]

omit hn in
/-- The bad part lies strictly above `r` in row 0. -/
theorem e0_bad {j : Nat} (h1 : r < j) (h2 : j < r + L) : entry M 0 r < entry M 0 j := by
  have := (par0_spec M).mp hp
  have := this.2.2 j h1 h2; omega

omit hn in
theorem e0_r_x : entry M 0 r < entry M 0 (r + L) := ((par0_spec M).mp hp).2.1

/-- Every column from `r` on is at least `r` in row 0. -/
theorem e0T0_ge {i : Nat} (hi : r ≤ i) (hiN : i < r + n * L) :
    entry M 0 r ≤ entry (TRIO.gexp M r L 0 0 n) 0 i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.lt_or_ge i (r + L) with h | h
    · rw [entryT0_low hlen hn h]
      rcases Nat.eq_or_lt_of_le hi with rfl | h'
      · exact le_refl _
      · exact le_of_lt (e0_bad hlen hL hp h' h)
    · rw [entryT0_per hlen hL h hiN]; exact ih (i - L) (by omega) (by omega) (by omega)

omit hp hn in
/-- **The drop is a prefix one period earlier.** -/
theorem dropT0_prefix {i : Nat} (hi : r + L ≤ i) (hiN : i ≤ r + n * L) :
    (TRIO.gexp M r L 0 0 n).drop i <+: (TRIO.gexp M r L 0 0 n).drop (i - L) := by
  have hlN := lenT0 (n := n) hlen
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_take]; omega
  · intro k h1 h2
    simp only [List.length_drop] at h1
    simp only [List.getElem_drop, List.getElem_take]
    have e := colT0_per (n := n) hlen hL (i := i + k) (by omega) (by omega)
    rw [col_getElem (by omega), col_getElem (by omega)] at e
    convert e using 2; omega

/-- The first copy after `x` starts with `col r`. -/
theorem cpy_head (hn2 : 2 ≤ n) : ∃ R, cpy M r L n = col M r :: R := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hd : (M.drop r).take L = col M r :: ((M.drop r).take L).tail := by
    have hr : r < M.length := by omega
    cases hc : (M.drop r).take L with
    | nil => have := congrArg List.length hc; simp at this; omega
    | cons c t =>
      have := congrArg (fun l => l[0]?) hc
      simp only [List.getElem?_take, List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
      rw [if_pos hL, List.getElem?_eq_getElem hr] at this
      simp only [Option.some.injEq] at this
      rw [col_getElem hr, this]; rfl
  refine ⟨((M.drop r).take L).tail ++ (List.replicate m ((M.drop r).take L)).flatten, ?_⟩
  show (List.replicate (m + 1) ((M.drop r).take L)).flatten = _
  rw [List.replicate_succ, List.flatten_cons, hd]; rfl

omit hlen hL hp hn in
theorem mem_drop_col {M : Mat} {i j : Nat} (hij : i ≤ j) (hj : j < M.length) : col M j ∈ M.drop i := by
  rw [col_getElem hj]
  exact List.mem_iff_getElem.mpr ⟨j - i, by simp; omega, by simp only [List.getElem_drop]; congr 1; omega⟩

omit hL hp hn in
theorem dropM_split {i : Nat} (hi : i ≤ r + L) :
    M.drop i = (M.take (r + L)).drop i ++ [col M (r + L)] := by
  have h1 : M.drop (r + L) = [col M (r + L)] := by
    rw [List.drop_eq_getElem_cons (by omega), col_getElem (by omega), List.drop_eq_nil_of_le (by omega)]
  conv_lhs => rw [← List.take_append_drop (r + L) M]
  rw [List.drop_append_of_le_length (by simp; omega), h1]

omit hL hp in
theorem dropN_split {i : Nat} (hi : i ≤ r + L) :
    (TRIO.gexp M r L 0 0 n).drop i = (M.take (r + L)).drop i ++ cpy M r L n := by
  rw [gexp_t0_split hlen hn, List.drop_append_of_le_length (by simp; omega)]

/-- **S1 is kept by the `t = 0` expansion** (sequence form). -/
theorem S1s_t0 (hS : S1s M) : S1s (TRIO.gexp M r L 0 0 n) := by
  have hlN := lenT0 (n := n) hlen
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b hab hbN he hpar hbet
  rw [hlN] at hbN
  rcases Nat.lt_or_ge a (r + L) with ha | ha
  · rcases Nat.lt_or_ge b (r + L) with hb | hb
    · -- both before `x`: the pair of `M`
      have heM : entry M 0 a = entry M 0 b := by
        rw [← entryT0_low hlen hn ha, ← entryT0_low hlen hn hb]; exact he
      have hparM : ∃ p, par M 0 a = some p := by
        obtain ⟨p, hp'⟩ := hpar
        exact ⟨p, by rw [← hp']; exact par0_congr_e0 (fun q hq => (entryT0_low hlen hn (by omega)).symm)⟩
      have hbetM : ∀ j, a < j → j < b → entry M 0 a < entry M 0 j := fun j h1 h2 => by
        have := hbet j h1 h2
        rwa [entryT0_low hlen hn (by omega), entryT0_low hlen hn (by omega)] at this
      have hM := hS a b hab (by omega) heM hparM hbetM
      have hmemb : col M b ∈ (M.take (r + L)).drop (a + 1) := by
        rw [← col_take M hb]; exact mem_drop_col (by omega) (by rw [List.length_take]; omega)
      have hsa : subT (TRIO.gexp M r L 0 0 n) a = subT M a := by
        unfold subT
        rw [colT0_low hlen hn ha, entryT0_low hlen hn ha, dropN_split hlen hn (by omega),
          dropM_split hlen (by omega)]
        congr 1
        have hf : ∃ y ∈ (M.take (r + L)).drop (a + 1), (fun q : Nat × Nat × Nat => decide (entry M 0 a < q.1)) y = false :=
          ⟨col M b, hmemb, by simp [← entry0_col, heM]⟩
        rw [← takeWhile_prefix_eq _ (List.prefix_append _ _) hf, ← takeWhile_prefix_eq _ (List.prefix_append _ _) hf]
      rw [hsa]
      set pb : Nat × Nat × Nat → Bool := fun q => decide (entry M 0 b < q.1) with hpb
      rcases takeWhile_all_or pb ((M.take (r + L)).drop (b + 1)) with hall | hf
      · have eM : subT M b = (col M b :: (M.take (r + L)).drop (b + 1)) ++ [col M (r + L)].takeWhile pb := by
          unfold subT; rw [dropM_split hlen (by omega), takeWhile_append_all _ _ _ hall]; rfl
        have eN : subT (TRIO.gexp M r L 0 0 n) b =
            (col M b :: (M.take (r + L)).drop (b + 1)) ++ (cpy M r L n).takeWhile pb := by
          unfold subT
          rw [colT0_low hlen hn hb, entryT0_low hlen hn hb, dropN_split hlen hn (by omega),
            takeWhile_append_all _ _ _ hall]; rfl
        rw [eN]
        cases hc : (cpy M r L n).takeWhile pb with
        | nil =>
          rw [List.append_nil]
          cases hq : seqLtB (subT M a) (col M b :: (M.take (r + L)).drop (b + 1))
          · rfl
          · have := seqLtB_prefix (B := subT M b) hq (by rw [eM]; exact List.prefix_append _ _)
            rw [hM] at this; exact absurd this (by simp)
        | cons c0 rest =>
          have hn2 : 2 ≤ n := by
            by_contra h
            have : n = 1 := by omega
            subst this; simp [cpy] at hc
          obtain ⟨R, hR⟩ := cpy_head hlen hL hp hn hn2
          rw [hR] at hc
          simp only [List.takeWhile_cons] at hc
          split at hc
          · rename_i hpr
            simp only [List.cons.injEq] at hc
            obtain ⟨rfl, -⟩ := hc
            have hrx := e0_r_x hlen hL hp
            have hpx : pb (col M (r + L)) = true := by
              simp only [hpb, decide_eq_true_eq] at hpr ⊢
              rw [← entry0_col] at hpr ⊢; omega
            rw [eM, List.takeWhile_cons, if_pos hpx, List.takeWhile_nil] at hM
            apply seqLtB_snoc_lt rest hM
            unfold colLtB; simp only [decide_eq_true_eq]; left
            rw [← entry0_col, ← entry0_col]; exact hrx
          · simp at hc
      · have hsb : subT (TRIO.gexp M r L 0 0 n) b = subT M b := by
          unfold subT
          rw [colT0_low hlen hn hb, entryT0_low hlen hn hb, dropN_split hlen hn (by omega),
            dropM_split hlen (by omega)]
          congr 1
          rw [← takeWhile_prefix_eq _ (List.prefix_append _ _) hf, ← takeWhile_prefix_eq _ (List.prefix_append _ _) hf]
        rw [hsb]; exact hM
    · -- `a` before `x`, `b` in the copies: `a = r`, `b = x`
      have hn2 : 2 ≤ n := by
        by_contra h
        have : n * L ≤ 1 * L := Nat.mul_le_mul_right L (by omega)
        omega
      have hx : entry (TRIO.gexp M r L 0 0 n) 0 (r + L) = entry M 0 r := by
        rw [entryT0_per hlen hL (le_refl _) (by
          have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
          omega), show r + L - L = r by omega, entryT0_low hlen hn (by omega)]
      have hge := e0T0_ge hlen hL hp hn (i := b) (by omega) hbN
      have hrx := e0_r_x hlen hL hp
      have har : a = r := by
        rcases Nat.lt_trichotomy a r with h | h | h
        · have := hbet r h (by omega)
          rw [entryT0_low hlen hn (by omega : r < r + L)] at this; omega
        · exact h
        · have hba := e0_bad hlen hL hp h ha
          rw [← entryT0_low hlen hn ha] at hba
          rcases Nat.eq_or_lt_of_le hb with hb' | hb'
          · rw [← hb', hx] at he; omega
          · have := hbet (r + L) (by omega) hb'; omega
      have har' : r = a := har.symm
      subst har'
      have hbx : b = r + L := by
        rcases Nat.eq_or_lt_of_le hb with hb' | hb'
        · exact hb'.symm
        · have := hbet (r + L) (by omega) hb'
          rw [hx, entryT0_low hlen hn (by omega : r < r + L)] at this; omega
      subst hbx
      apply seqLtB_of_prefix_false
      unfold subT
      have hcol := colT0_per (n := n) hlen hL (i := r + L) (le_refl _) (by
        have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
        omega)
      have hent := entryT0_per (n := n) hlen hL (i := r + L) (le_refl _) (by
        have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
        omega)
      rw [show r + L - L = r by omega] at hcol hent
      rw [hcol, hent]
      apply List.prefix_cons_inj _ |>.mpr
      apply takeWhile_prefix
      have := dropT0_prefix (n := n) hlen hL (i := r + L + 1) (by omega) (by omega)
      rwa [show r + L + 1 - L = r + 1 by omega] at this
  · -- `a` in the copies: one period earlier
    have hbx : r + L ≤ b := by omega
    have heA := entryT0_per (n := n) hlen hL ha (by omega)
    have heB := entryT0_per (n := n) hlen hL hbx hbN
    have he' : entry (TRIO.gexp M r L 0 0 n) 0 (a - L) = entry (TRIO.gexp M r L 0 0 n) 0 (b - L) := by
      rw [← heA, ← heB]; exact he
    have hpar' : ∃ p, par (TRIO.gexp M r L 0 0 n) 0 (a - L) = some p := by
      obtain ⟨p, hpa⟩ := hpar
      have hs := (par0_spec _).mp hpa
      apply par0_exists
      rcases Nat.lt_or_ge p (a - L) with h1 | h1
      · exact ⟨p, h1, by rw [← heA]; exact hs.2.1⟩
      rcases Nat.lt_or_ge p (r + L) with h2 | h2
      · have hgp := e0T0_ge hlen hL hp hn (i := p) (by omega) (by omega)
        rcases Nat.eq_or_lt_of_le (show r ≤ a - L by omega) with h3 | h3
        · exfalso
          have := hs.2.1
          rw [heA, ← h3, entryT0_low hlen hn (by omega : r < r + L)] at this; omega
        · refine ⟨r, h3, ?_⟩
          rw [entryT0_low hlen hn (by omega : r < r + L), ← heA]
          have := hs.2.1; omega
      · refine ⟨p - L, by omega, ?_⟩
        rw [← entryT0_per (n := n) hlen hL h2 (by omega), ← heA]; exact hs.2.1
    have hbet' : ∀ j, a - L < j → j < b - L →
        entry (TRIO.gexp M r L 0 0 n) 0 (a - L) < entry (TRIO.gexp M r L 0 0 n) 0 j := by
      intro j h1 h2
      have := hbet (j + L) (by omega) (by omega)
      rw [heA, entryT0_per (n := n) hlen hL (i := j + L) (by omega) (by omega),
        show j + L - L = j by omega] at this
      exact this
    have IH := ih (a - L) (by omega) (b - L) (by omega) (by rw [hlN]; omega) he' hpar' hbet'
    have hmemb : col (TRIO.gexp M r L 0 0 n) b ∈ (TRIO.gexp M r L 0 0 n).drop (a + 1) :=
      mem_drop_col (by omega) (by rw [hlN]; omega)
    have hsa : subT (TRIO.gexp M r L 0 0 n) a = subT (TRIO.gexp M r L 0 0 n) (a - L) := by
      unfold subT
      rw [colT0_per (n := n) hlen hL ha (by omega), heA]
      congr 1
      have hpre := dropT0_prefix (n := n) hlen hL (i := a + 1) (by omega) (by omega)
      rw [show a + 1 - L = a - L + 1 by omega] at hpre
      apply takeWhile_prefix_eq _ hpre
      refine ⟨_, hmemb, ?_⟩
      simp only [decide_eq_false_iff_not, not_lt]
      rw [← entry0_col, ← heA, he]
    have hsb : subT (TRIO.gexp M r L 0 0 n) b <+: subT (TRIO.gexp M r L 0 0 n) (b - L) := by
      unfold subT
      rw [colT0_per (n := n) hlen hL hbx hbN, heB]
      apply List.prefix_cons_inj _ |>.mpr
      apply takeWhile_prefix
      have := dropT0_prefix (n := n) hlen hL (i := b + 1) (by omega) (by omega)
      rwa [show b + 1 - L = b - L + 1 by omega] at this
    cases hq : seqLtB (subT (TRIO.gexp M r L 0 0 n) a) (subT (TRIO.gexp M r L 0 0 n) b)
    · rfl
    · rw [hsa] at hq
      have := seqLtB_prefix hq hsb
      rw [IH] at this; exact absurd this (by simp)

/-- **S1 of `N = M[n]`** for the `t = 0` expansion. -/
theorem S1_t0 (hR0 : R0P M) (hR0N : R0P (TRIO.gexp M r L 0 0 n)) (hS : S1 M) :
    S1 (TRIO.gexp M r L 0 0 n) :=
  S1_of_S1s hR0N (S1s_t0 hlen hL hp hn (S1s_of_S1 hR0 hS))

end

end Ytosk
