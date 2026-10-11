/-
**P の構造の部分 S1・S4 は接頭辞で保たれる（closure、2026-10-11）。**

- S4: 関係する列はどれも c 以下なので、M.take k の親・祖先・成分は M と同じ。
- S1: 兄弟 a < b がどちらも接頭辞にあれば、a の部分木は b の前で終わるので変わらず、b の部分木は M の b の部分木の
  先頭部分になる。辞書式で「a の部分木 < b の部分木の先頭部分」なら「a の部分木 < b の部分木」。
-/
import Ytosk.V3PDef

namespace Ytosk

open T

/-! ## S4 -/

theorem s4_take {M : Mat} (h : S4 M) (k : Nat) : S4 (M.take k) := by
  intro c q d h2 hp1 hp0 hA hdc
  have hck : c < k := by
    by_contra hn
    rw [entry_out (by rw [List.length_take]; omega) 2] at h2
    exact absurd h2 (by decide)
  have hdk : d < k := lt_of_le_of_lt hA.le hck
  rw [entry_take M 2 hck] at h2
  rw [par_take M 1 c hck] at hp1
  rw [par_take M 0 d hdk] at hp0
  obtain ⟨h1, h2'⟩ := h c q d h2 hp1 hp0 (anc0_of_take hA) hdc
  refine ⟨by rw [entry_take M 2 hdk]; exact h1, fun t ht1 ht2 htd htc => ?_⟩
  have htk : t < k := lt_of_le_of_lt ht2.le hck
  rw [entry_take M 1 hck, entry_take M 1 htk]
  exact h2' t (anc0_of_take ht1) (anc0_of_take ht2) htd htc

/-! ## S1 -/

theorem takeWhile_take' {α : Type} (p : α → Bool) : ∀ (l : List α) (n : Nat),
    (l.take n).takeWhile p = (l.takeWhile p).take n
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | a :: l, n + 1 => by
    simp only [List.take_succ_cons, List.takeWhile_cons]
    split
    · simp [takeWhile_take' p l n]
    · simp

theorem takeWhile_length_le {α : Type} (p : α → Bool) : ∀ (l : List α) (j : Nat) (y : α),
    l[j]? = some y → p y = false → (l.takeWhile p).length ≤ j
  | [], _, _, h, _ => by simp at h
  | a :: l, 0, y, h, hp => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [List.takeWhile_cons, hp]
  | a :: l, j + 1, y, h, hp => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.takeWhile_cons]
    split
    · simp only [List.length_cons]; have := takeWhile_length_le p l j y h hp; omega
    · simp

/-- Lexicographically below a prefix of `B` means below `B`. -/
theorem seqLtB_prefix : ∀ {A B' B : Mat}, seqLtB A B' = true → B' <+: B → seqLtB A B = true
  | [], [], _, h, _ => by simp [seqLtB] at h
  | [], _ :: _, B, _, hp => by
    obtain ⟨t, rfl⟩ := hp; simp [seqLtB]
  | _ :: _, [], _, h, _ => by simp [seqLtB] at h
  | p :: A, q :: B', B, h, hp => by
    obtain ⟨t, rfl⟩ := hp
    simp only [List.cons_append, seqLtB, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, seqLtB_prefix h2 ⟨t, rfl⟩⟩

theorem subT_take (M : Mat) {k a : Nat} (ha : a < k) :
    subT (M.take k) a =
      col M a :: ((M.drop (a + 1)).takeWhile (fun q => decide (entry M 0 a < q.1))).take (k - (a + 1)) := by
  unfold subT
  rw [col_take M ha, entry_take M 0 ha, List.drop_take, takeWhile_take']

theorem S1_take {M : Mat} (hR0 : R0P M) (h : S1 M) (k : Nat) : S1 (M.take k) := by
  intro p l₁ l₂ a b hch
  rw [children_take] at hch
  obtain ⟨rest, hr⟩ := filter_lt_prefix (children M p) k (children_sorted M p)
  have hM : children M p = l₁ ++ a :: b :: (l₂ ++ rest) := by rw [hr, hch]; simp
  have ha : a ∈ (children M p).filter (fun c => decide (c < k)) := by rw [hch]; simp
  have hb : b ∈ (children M p).filter (fun c => decide (c < k)) := by rw [hch]; simp
  rw [List.mem_filter] at ha hb
  have hak : a < k := by simpa using ha.2
  have hbk : b < k := by simpa using hb.2
  have hab : a < b := by
    have hs := children_sorted M p
    rw [hM] at hs
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 b (by simp)
  have hbM : b < M.length := (mem_children hb.1).2
  have hpa : par M 0 a = some p := (mem_children_iff.mp ha.1).2
  have hpb : par M 0 b = some p := (mem_children_iff.mp hb.1).2
  have he : entry M 0 b = entry M 0 a := by rw [hR0 b p hpb, hR0 a p hpa]
  -- the subtree of `a` ends before `b`
  have hlen : ((M.drop (a + 1)).takeWhile (fun q => decide (entry M 0 a < q.1))).length ≤ b - (a + 1) := by
    apply takeWhile_length_le _ _ (b - (a + 1)) (col M b)
    · rw [List.getElem?_drop, show a + 1 + (b - (a + 1)) = b by omega]
      unfold col; rw [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem hbM]; simp
    · have : (col M b).1 = entry M 0 b := by unfold col entry; simp
      simp [this, he]
  have hA : subT (M.take k) a = subT M a := by
    rw [subT_take M hak, List.take_of_length_le (by omega)]; rfl
  have hB : subT (M.take k) b <+: subT M b := by
    rw [subT_take M hbk]
    exact List.prefix_cons_inj _ |>.mpr (List.take_prefix _ _)
  have hM' := h p l₁ (l₂ ++ rest) a b hM
  rw [hA]
  cases hq : seqLtB (subT M a) (subT (M.take k) b)
  · rfl
  · rw [seqLtB_prefix hq hB] at hM'; exact absurd hM' (by simp)

end Ytosk
