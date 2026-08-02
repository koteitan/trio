/-
**トリオ数列の記法 `p_{a1,a2}(b)+c` と翻訳 `translate`。**

添字は自然数の**対** (a1, a2) — 行 1 と行 2 のラベルの組であり、文字であって
順序数ではない（BMOCF と同じ設計）。順序 `<o` は添字対優先の辞書式:
a1 → a2 → 引数 → 後続和。BMS の列比較（行 0 → 行 1 → 行 2）の項側の対応物。

2 行の形式化 ~/proofs/lean-yapss/git/lean/Term.lean と同じ設計。
-/
import Trio
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Find

namespace TRIO

inductive Three : Type where
  | Z : Three
  | P : ℕ → ℕ → Three → Three → Three
  deriving DecidableEq, Repr, Inhabited

namespace Three

/-! ## 添字対優先の辞書式順序 -/

/-- The subscript-pair-first lexicographic order on `Three`. -/
def olt : Three → Three → Prop
  | Z, Z => False
  | Z, P _ _ _ _ => True
  | P _ _ _ _, Z => False
  | P a1 a2 b c, P e1 e2 f g =>
      a1 < e1 ∨ (a1 = e1 ∧ a2 < e2) ∨ (a1 = e1 ∧ a2 = e2 ∧ olt b f)
        ∨ (a1 = e1 ∧ a2 = e2 ∧ b = f ∧ olt c g)

@[inherit_doc] infix:50 " <o " => olt

/-- `x ≤o y` iff `x <o y ∨ x = y`. -/
def ole (x y : Three) : Prop := x <o y ∨ x = y

@[inherit_doc] infix:50 " ≤o " => ole

@[simp] theorem olt_Z_Z : ¬ (Z <o Z) := fun h => h

@[simp] theorem olt_Z_P (a1 a2 : ℕ) (b c : Three) : Z <o P a1 a2 b c := trivial

@[simp] theorem olt_P_Z (a1 a2 : ℕ) (b c : Three) : ¬ (P a1 a2 b c <o Z) :=
  fun h => h

@[simp] theorem olt_P_P {a1 a2 e1 e2 : ℕ} {b c f g : Three} :
    P a1 a2 b c <o P e1 e2 f g ↔
      a1 < e1 ∨ (a1 = e1 ∧ a2 < e2) ∨ (a1 = e1 ∧ a2 = e2 ∧ b <o f)
        ∨ (a1 = e1 ∧ a2 = e2 ∧ b = f ∧ c <o g) := Iff.rfl

theorem olt_irrefl (x : Three) : ¬ x <o x := by
  induction x with
  | Z => simp
  | P a1 a2 b c ihb ihc => simp [ihb, ihc]

@[simp] theorem not_olt_Z (x : Three) : ¬ x <o Z := by
  cases x <;> simp

theorem olt_trans {x y z : Three} (hxy : x <o y) (hyz : y <o z) : x <o z := by
  induction z generalizing x y with
  | Z => exact absurd hyz (not_olt_Z y)
  | P c1 c2 c3 c4 ih3 ih4 =>
    cases x with
    | Z => simp
    | P a1 a2 a3 a4 =>
      obtain ⟨e1, e2, e3, e4, rfl⟩ : ∃ e1 e2 e3 e4, y = P e1 e2 e3 e4 := by
        cases y with
        | Z => exact absurd hxy (not_olt_Z _)
        | P e1 e2 e3 e4 => exact ⟨e1, e2, e3, e4, rfl⟩
      rw [olt_P_P] at hxy hyz ⊢
      rcases hxy with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, h1⟩ | ⟨rfl, rfl, rfl, h1⟩ <;>
        rcases hyz with h2 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h2⟩ | ⟨rfl, rfl, rfl, h2⟩
      · exact Or.inl (Nat.lt_trans h1 h2)
      · exact Or.inl h1
      · exact Or.inl h1
      · exact Or.inl h1
      · exact Or.inl h2
      · exact Or.inr (Or.inl ⟨rfl, Nat.lt_trans h1 h2⟩)
      · exact Or.inr (Or.inl ⟨rfl, h1⟩)
      · exact Or.inr (Or.inl ⟨rfl, h1⟩)
      · exact Or.inl h2
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ih3 h1 h2⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1⟩))
      · exact Or.inl h2
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, ih4 h1 h2⟩))

theorem olt_ole_trans {x y z : Three} (hxy : x <o y) (hyz : y ≤o z) : x <o z := by
  rcases hyz with h | rfl
  · exact olt_trans hxy h
  · exact hxy

/-- Strict monotonicity of a principal term in its argument. -/
theorem olt_P_b {b1 b2 : Three} (a1 a2 : ℕ) (c1 c2 : Three) (h : b1 <o b2) :
    P a1 a2 b1 c1 <o P a1 a2 b2 c2 := by simp [h]

/-- Strict monotonicity of a principal term in its tail. -/
theorem olt_P_c {c1 c2 : Three} (a1 a2 : ℕ) (b : Three) (h : c1 <o c2) :
    P a1 a2 b c1 <o P a1 a2 b c2 := by simp [h]

/-- Leading subscript pair of a term. -/
def lead : Three → ℕ × ℕ
  | Z => (0, 0)
  | P a1 a2 _ _ => (a1, a2)

@[simp] theorem lead_Z : lead Z = (0, 0) := rfl
@[simp] theorem lead_P (a1 a2 : ℕ) (b c : Three) :
    lead (P a1 a2 b c) = (a1, a2) := rfl

/-- Subscript-pair-first domination: a term whose leading pair is
lexicographically below `(w1, w2)` (or which is `Z`) is strictly below *any*
principal term `p_{w1,w2}(b)+c`, regardless of its argument and tail. -/
theorem olt_P_of_lead_lt {t : Three} {w1 w2 : ℕ} (b c : Three)
    (h : t = Z ∨ (lead t).1 < w1 ∨ ((lead t).1 = w1 ∧ (lead t).2 < w2)) :
    t <o P w1 w2 b c := by
  cases t with
  | Z => simp
  | P a1 a2 b' c' =>
    simp only [lead_P] at h
    rcases h with h | h | ⟨h1, h2⟩
    · exact absurd h (by simp)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h2⟩)

end Three

/-! ## 翻訳 `translate : TrioSeq → Three`

行 0 を森の深さ優先表記として読む: 先頭の列 `(x, y, z)` は主要項
`p_{y,z}(…)` になり、引数は行 0 の値が `> x` である極大な後続ブロック
（子孫）の翻訳、後続和は残り（兄弟以降）の翻訳。 -/

open Three in
def translate : TrioSeq → Three
  | [] => Z
  | p :: rest =>
    P p.2.1 p.2.2 (translate (rest.takeWhile fun q => p.1 < q.1))
                  (translate (rest.dropWhile fun q => p.1 < q.1))
  termination_by M => M.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

open Three

theorem lead_translate (M : TrioSeq) :
    lead (translate M) = match M with | [] => (0, 0) | p :: _ => (p.2.1, p.2.2) := by
  cases M <;> simp [translate]

/-! ### List bookkeeping helpers -/

section ListHelpers

variable {α : Type*} {p : α → Bool} {xs ys : List α}

theorem takeWhile_append_all (h : ∀ x ∈ xs, p x) :
    (xs ++ ys).takeWhile p = xs ++ ys.takeWhile p := by
  rw [List.takeWhile_append, if_pos (by rw [List.takeWhile_eq_self_iff.2 h])]

theorem dropWhile_append_all (h : ∀ x ∈ xs, p x) :
    (xs ++ ys).dropWhile p = ys.dropWhile p := by
  rw [List.dropWhile_append, if_pos (by simp [List.dropWhile_eq_nil_iff.2 h])]

theorem takeWhile_append_not {x : α} (hx : x ∈ xs) (hnx : ¬ p x) :
    (xs ++ ys).takeWhile p = xs.takeWhile p := by
  rw [List.takeWhile_append, if_neg]
  intro hlen
  exact hnx (List.takeWhile_eq_self_iff.1
    ((List.takeWhile_sublist p).eq_of_length hlen) x hx)

theorem dropWhile_append_not {x : α} (hx : x ∈ xs) (hnx : ¬ p x) :
    (xs ++ ys).dropWhile p = xs.dropWhile p ++ ys := by
  rw [List.dropWhile_append, if_neg]
  intro hempty
  exact hnx (List.dropWhile_eq_nil_iff.1 (List.isEmpty_iff.1 hempty) x hx)

/-- A suffix as an index map (indexing via the total `getD`). -/
theorem drop_eq_map_getD (xs : List α) (a : ℕ) (d : α) :
    xs.drop a = (List.range' a (xs.length - a)).map fun i => xs.getD i d := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_drop, List.getElem_map, List.getElem_range']
    have hi : a + 1 * i < xs.length := by simp at h2 ⊢; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp [Nat.one_mul]

end ListHelpers

/-- The column triple read through `entry`. -/
theorem getD_eq_entries (M : TrioSeq) (j : ℕ) :
    M.getD j (0, 0, 0) = (entry M 0 j, entry M 1 j, entry M 2 j) := rfl

/-! ## Row-0 monotonicity of the parent relation -/

theorem nextrel0_entry0_less {M : TrioSeq} {j0 j1 : ℕ} (h : nextrel0 M j0 j1) :
    entry M 0 j0 < entry M 0 j1 := h.2.2.2.1

theorem le0_entry0_mono {M : TrioSeq} {j0 j1 : ℕ} (h : le0 M j0 j1) :
    entry M 0 j0 ≤ entry M 0 j1 := by
  obtain ⟨-, -, hchain⟩ := h
  induction hchain with
  | refl => exact le_rfl
  | tail _ hyz ih => exact ih.trans (nextrel0_entry0_less hyz).le

/-- Indices increase along the row-0 Next relation. -/
theorem nextrel0_index_less {M : TrioSeq} {a b : ℕ} (h : nextrel0 M a b) : a < b :=
  h.2.2.1

theorem nextrel0_rtrancl_index_le {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hyz ih => exact ih.trans (nextrel0_index_less hyz).le

/-- Key interval lemma: along a row-0 ancestry, *every* index in `(j0, j1]`
has row-0 strictly above `j0`. -/
theorem le0_interval_gt {M : TrioSeq} {j0 j1 : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) j0 j1) :
    ∀ k, j0 < k ∧ k ≤ j1 → entry M 0 j0 < entry M 0 k := by
  induction h with
  | refl => intro k hk; omega
  | @tail y z hj0y hyz ih =>
    have yz : entry M 0 y < entry M 0 z := nextrel0_entry0_less hyz
    have j0y : j0 ≤ y := nextrel0_rtrancl_index_le hj0y
    have j0le : entry M 0 j0 ≤ entry M 0 y := by
      rcases Nat.lt_or_ge j0 y with hlt | hge
      · exact (ih y ⟨hlt, le_rfl⟩).le
      · have : j0 = y := le_antisymm j0y hge
        exact this ▸ le_rfl
    intro k ⟨hk1, hk2⟩
    rcases Nat.lt_or_ge y k with hyk | hky
    case inr =>
      exact ih k ⟨hk1, hky⟩
    rcases eq_or_lt_of_le hk2 with rfl | hkz
    · exact lt_of_le_of_lt j0le yz
    · have hmid : entry M 0 z ≤ entry M 0 k := hyz.2.2.2.2 k ⟨hyk, hkz⟩
      exact lt_of_le_of_lt j0le (lt_of_lt_of_le yz hmid)

open Classical in
/-- **The row-0 ascension matrix is 1 on the whole bad part**: every index in
`[j0, j1]` is a row-0 descendant of `j0`, given a row-0 ancestry `j0 → j1`.
From any interior `k` the nearest-lower-row-0 parent stays in `[j0, k)` because
every interior column is strictly above `j0` in row 0. -/
theorem le0_interval_desc {M : TrioSeq} {j0 j1 : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) j0 j1) (hb1 : j1 < M.length) :
    ∀ k, j0 ≤ k → k ≤ j1 → Relation.ReflTransGen (nextrel0 M) j0 k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk0 hk1
    rcases Nat.eq_or_lt_of_le hk0 with rfl | hlt
    · exact .refl
    · -- the nearest preceding column with smaller row 0
      have hPj0 : entry M 0 j0 < entry M 0 k := le0_interval_gt h k ⟨hlt, hk1⟩
      set Q : ℕ → Prop := fun q => entry M 0 q < entry M 0 k with hQ
      have hj0k : j0 ≤ k - 1 := by omega
      set p := Nat.findGreatest Q (k - 1) with hp
      have hQp : Q p := Nat.findGreatest_spec (P := Q) hj0k hPj0
      have hj0p : j0 ≤ p := Nat.le_findGreatest hj0k hPj0
      have hpk : p < k := by
        have : p ≤ k - 1 := Nat.findGreatest_le _
        omega
      have hstep : nextrel0 M p k := by
        refine ⟨by omega, by omega, hpk, hQp, ?_⟩
        intro j ⟨hj1, hj2⟩
        by_contra hcon
        push Not at hcon
        exact absurd (Nat.findGreatest_is_greatest (P := Q) hj1 (by omega)) (by
          simp only [hQ]
          omega)
      exact (ih p hpk hj0p (by omega)).tail hstep

/-! ## Row-1 chains (for the `i1 = 2` branch) -/

theorem nextrel1_entry1_less {M : TrioSeq} {j0 j1 : ℕ} (h : nextrel1 M j0 j1) :
    entry M 1 j0 < entry M 1 j1 := h.2.2.2.1

theorem nextrel1_index_less {M : TrioSeq} {a b : ℕ} (h : nextrel1 M a b) : a < b :=
  h.2.2.1

theorem rtg1_index_le {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel1 M) a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hyz ih => exact ih.trans (nextrel1_index_less hyz).le

/-- A *proper* row-1 ancestry strictly increases the row-1 value. -/
theorem rtg1_entry1_lt {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel1 M) a b) (hne : a ≠ b) :
    entry M 1 a < entry M 1 b := by
  induction h with
  | refl => exact absurd rfl hne
  | @tail y z hay hyz ih =>
    by_cases hay' : a = y
    · exact hay' ▸ nextrel1_entry1_less hyz
    · exact lt_trans (ih hay') (nextrel1_entry1_less hyz)

/-- Row-1 steps refine row-0 ancestry. -/
theorem rtg1_to_rtg0 {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel1 M) a b) :
    Relation.ReflTransGen (nextrel0 M) a b := by
  induction h with
  | refl => exact .refl
  | tail _ hyz ih => exact ih.trans hyz.2.2.2.2.1.2.2

/-! ## Shape lemmas for `translate` -/

/-- If every column after the head lies strictly above it in row 0, the whole
list reads as one tree: a single principal term with empty tail. -/
theorem translate_single_tree {p : ℕ × ℕ × ℕ} {R : TrioSeq}
    (h : ∀ x ∈ R, p.1 < x.1) :
    translate (p :: R) = P p.2.1 p.2.2 (translate R) Z := by
  have tw : R.takeWhile (fun q => p.1 < q.1) = R :=
    List.takeWhile_eq_self_iff.2 (by simpa using h)
  have dw : R.dropWhile (fun q => p.1 < q.1) = [] :=
    List.dropWhile_eq_nil_iff.2 (by simpa using h)
  rw [translate, tw, dw, translate]

/-- A block `(v0, w1, w2) :: R` (body all above `v0`) followed by a tail `T`
that re-opens at or below `v0` translates to a single principal whose argument
is `R` and whose siblings are `T`. -/
theorem translate_block_append {v0 w1 w2 : ℕ} {R T : TrioSeq}
    (hR : ∀ x ∈ R, v0 < x.1) (hT : T = [] ∨ ¬ v0 < (T.headI).1) :
    translate (((v0, w1, w2) :: R) ++ T) = P w1 w2 (translate R) (translate T) := by
  have hR' : ∀ x ∈ R, (fun q : ℕ × ℕ × ℕ => decide (v0 < q.1)) x = true := by
    intro x hx; simpa using hR x hx
  have twT : (R ++ T).takeWhile (fun q => v0 < q.1) = R := by
    rcases hT with rfl | hT
    · simpa using List.takeWhile_eq_self_iff.2 hR'
    · rcases T with - | ⟨t, ts⟩
      · simpa using List.takeWhile_eq_self_iff.2 hR'
      · rw [takeWhile_append_all hR']
        simp only [List.headI] at hT
        simp [hT]
  have dwT : (R ++ T).dropWhile (fun q => v0 < q.1) = T := by
    rcases hT with rfl | hT
    · simpa using List.dropWhile_eq_nil_iff.2 hR'
    · rcases T with - | ⟨t, ts⟩
      · simpa using List.dropWhile_eq_nil_iff.2 hR'
      · rw [dropWhile_append_all hR']
        simp only [List.headI] at hT
        simp [hT]
  rw [List.cons_append, translate]
  show P w1 w2 (translate ((R ++ T).takeWhile fun q => v0 < q.1))
      (translate ((R ++ T).dropWhile fun q => v0 < q.1)) = _
  rw [twT, dwT]

/-! ## Context congruence (BADCTX) -/

/-- If two tails `Z1, Z2` share the same first column's row-0 value and all
their other columns lie at or above it, a common good part `G` preserves a
strict decrease between them. -/
theorem translate_ctx_cong {z1 z2 : ℕ × ℕ × ℕ} {T1 T2 : TrioSeq}
    (base : translate (z1 :: T1) <o translate (z2 :: T2))
    (root : z1.1 = z2.1)
    (r1 : ∀ x ∈ T1, z1.1 ≤ x.1)
    (r2 : ∀ x ∈ T2, z2.1 ≤ x.1)
    (G : TrioSeq) :
    translate (G ++ z1 :: T1) <o translate (G ++ z2 :: T2) := by
  match G with
  | [] => simpa using base
  | g :: G' =>
    by_cases allG : ∀ x ∈ G', g.1 < x.1
    · by_cases hPg : g.1 < z1.1
      · -- the whole tail nests under `g`; pass to `G'`
        have aZ1 : ∀ x ∈ z1 :: T1, g.1 < x.1 := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hPg
          · exact lt_of_lt_of_le hPg (r1 _ hx)
        have aZ2 : ∀ x ∈ z2 :: T2, g.1 < x.1 := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact root ▸ hPg
          · exact lt_of_lt_of_le (root ▸ hPg) (r2 _ hx)
        have all1 : ∀ x ∈ G' ++ z1 :: T1, g.1 < x.1 := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          exacts [allG x h, aZ1 x h]
        have all2 : ∀ x ∈ G' ++ z2 :: T2, g.1 < x.1 := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          exacts [allG x h, aZ2 x h]
        have e1 : translate (g :: (G' ++ z1 :: T1))
            = P g.2.1 g.2.2 (translate (G' ++ z1 :: T1)) Z := by
          rw [translate, List.takeWhile_eq_self_iff.2 (by simpa using all1),
            List.dropWhile_eq_nil_iff.2 (by simpa using all1), translate]
        have e2 : translate (g :: (G' ++ z2 :: T2))
            = P g.2.1 g.2.2 (translate (G' ++ z2 :: T2)) Z := by
          rw [translate, List.takeWhile_eq_self_iff.2 (by simpa using all2),
            List.dropWhile_eq_nil_iff.2 (by simpa using all2), translate]
        simp only [List.cons_append]
        rw [e1, e2]
        exact olt_P_b _ _ _ _ (translate_ctx_cong base root r1 r2 G')
      · -- the tail is a sibling after `g`'s subtree; use the base case
        have hPg2 : ¬ g.1 < z2.1 := root ▸ hPg
        have allG' : ∀ x ∈ G', (fun q : ℕ × ℕ × ℕ => decide (g.1 < q.1)) x = true := by
          intro x hx; simpa using allG x hx
        have tw1 : (G' ++ z1 :: T1).takeWhile (fun q => g.1 < q.1) = G' := by
          rw [takeWhile_append_all allG']
          simp [hPg]
        have dw1 : (G' ++ z1 :: T1).dropWhile (fun q => g.1 < q.1) = z1 :: T1 := by
          rw [dropWhile_append_all allG']
          simp [hPg]
        have tw2 : (G' ++ z2 :: T2).takeWhile (fun q => g.1 < q.1) = G' := by
          rw [takeWhile_append_all allG']
          simp [hPg2]
        have dw2 : (G' ++ z2 :: T2).dropWhile (fun q => g.1 < q.1) = z2 :: T2 := by
          rw [dropWhile_append_all allG']
          simp [hPg2]
        have e1 : translate (g :: (G' ++ z1 :: T1))
            = P g.2.1 g.2.2 (translate G') (translate (z1 :: T1)) := by
          rw [translate, tw1, dw1]
        have e2 : translate (g :: (G' ++ z2 :: T2))
            = P g.2.1 g.2.2 (translate G') (translate (z2 :: T2)) := by
          rw [translate, tw2, dw2]
        simp only [List.cons_append]
        rw [e1, e2]
        exact olt_P_c _ _ _ base
    · -- `G'` already drops to/below `g`; recurse on the shorter tail of `G'`
      push Not at allG
      obtain ⟨x, hx, hnx⟩ := allG
      have hnx' : ¬ (fun q : ℕ × ℕ × ℕ => decide (g.1 < q.1)) x = true := by
        simpa using hnx
      have tw1 : (G' ++ z1 :: T1).takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw1 : (G' ++ z1 :: T1).dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ z1 :: T1 := dropWhile_append_not hx hnx'
      have tw2 : (G' ++ z2 :: T2).takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw2 : (G' ++ z2 :: T2).dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ z2 :: T2 := dropWhile_append_not hx hnx'
      have e1 : translate (g :: (G' ++ z1 :: T1))
          = P g.2.1 g.2.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((G'.dropWhile fun q => g.1 < q.1) ++ z1 :: T1)) := by
        rw [translate, tw1, dw1]
      have e2 : translate (g :: (G' ++ z2 :: T2))
          = P g.2.1 g.2.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((G'.dropWhile fun q => g.1 < q.1) ++ z2 :: T2)) := by
        rw [translate, tw2, dw2]
      simp only [List.cons_append]
      rw [e1, e2]
      exact olt_P_c _ _ _
        (translate_ctx_cong base root r1 r2 (G'.dropWhile fun q => g.1 < q.1))
  termination_by G.length
  decreasing_by
  · simp
  · simp [Nat.lt_succ_of_le (List.length_dropWhile_le _ G')]

/-- The search row is at most 2. -/
theorem srow_le2 (M : TrioSeq) (j : ℕ) : srow M j ≤ 2 := by
  unfold srow; split
  · simp
  · split <;> simp

end TRIO
