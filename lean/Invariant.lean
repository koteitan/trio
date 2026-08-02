/-
Invariant.lean: 位置的不変量の展開保存（ガード付きコピー上）。

`z0ok`（行 0 が 0 の列はラベルも 0）と `noninc`（行 2 ≤ 行 1）の
`oper` 保存。行 1 の規律 `r1ok` の保存はスパイン⊆D と climb を要する
別区画（続く部分）。
-/
import Goper
import Column

namespace TRIO

open Classical

/-- Membership shape of a guarded-copies column. -/
theorem mem_gcopies {M : TrioSeq} {r L d0 d1 n : ℕ} {x : ℕ × ℕ × ℕ}
    (hx : x ∈ gcopies M r L d0 d1 n) :
    ∃ j k, r ≤ j ∧ j < r + L ∧ k < n ∧
      x = (entry M 0 j + k * d0,
           entry M 1 j + (if le1 M r j then k * d1 else 0), entry M 2 j) := by
  unfold gcopies at hx
  obtain ⟨k, hk, hxk⟩ := List.mem_flatMap.1 hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hxk
  have hjb := List.mem_range'_1.1 hj
  have hkb := List.mem_range.1 hk
  exact ⟨j, k, hjb.1, hjb.2, hkb, rfl⟩

theorem getD_mem_of_lt {A : TrioSeq} {j : ℕ} (hj : j < A.length) :
    A.getD j (0, 0, 0) ∈ A := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

/-- Membership form of `noninc`. -/
theorem noninc_mem {M : TrioSeq} (h : noninc M) {x : ℕ × ℕ × ℕ} (hx : x ∈ M) :
    x.2.2 ≤ x.2.1 := by
  obtain ⟨i, hi, hxe⟩ := List.getElem_of_mem hx
  have := h i (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), hxe] at this
  exact this

theorem noninc_of_mem {M : TrioSeq} (h : ∀ x ∈ M, x.2.2 ≤ x.2.1) : noninc M := by
  intro j hj
  exact h _ (getD_mem_of_lt hj)

/-- Membership form of `z0ok`. -/
theorem z0ok_mem {M : TrioSeq} (h : z0ok M) {x : ℕ × ℕ × ℕ} (hx : x ∈ M)
    (hx0 : x.1 = 0) : x.2.1 = 0 ∧ x.2.2 = 0 := by
  obtain ⟨i, hi, hxe⟩ := List.getElem_of_mem hx
  have := h i (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), hxe] at this
  exact this hx0

theorem z0ok_of_mem {M : TrioSeq} (h : ∀ x ∈ M, x.1 = 0 → x.2.1 = 0 ∧ x.2.2 = 0) :
    z0ok M := by
  intro j hj h0
  exact h _ (getD_mem_of_lt hj) h0

/-- The entry triple at a valid position is a member. -/
theorem entry_triple_mem {M : TrioSeq} {j : ℕ} (hj : j < M.length) :
    ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ) ∈ M := by
  rw [← getD_eq_entries]
  exact getD_mem_of_lt hj

/-- **`noninc` is preserved by the expansion step.** -/
theorem noninc_oper {M : TrioSeq} {n : ℕ} (h : noninc M) : noninc (M⟦n⟧) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact h
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz]
    unfold Pred
    split_ifs
    · exact h
    · exact noninc_dropLast h
  by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL hz hp]
    unfold Pred
    split_ifs
    · exact h
    · exact noninc_dropLast h
  case pos =>
    rw [oper_gcopies n hL hz hp]
    refine noninc_of_mem ?_
    intro x hx
    rcases List.mem_append.1 hx with hm | hm
    · exact noninc_mem h (List.mem_of_mem_take hm)
    · obtain ⟨l, k, h1, h2, h3, rfl⟩ := mem_gcopies hm
      have hl : l < M.length := by omega
      have h21 := noninc_mem h (entry_triple_mem hl)
      simp only [] at h21 ⊢
      omega

/-- **`z0ok` is preserved by the expansion step.** -/
theorem z0ok_oper {M : TrioSeq} {n : ℕ} (h : z0ok M) : z0ok (M⟦n⟧) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact h
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz]
    unfold Pred
    split_ifs
    · exact h
    · exact z0ok_dropLast h
  by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL hz hp]
    unfold Pred
    split_ifs
    · exact h
    · exact z0ok_dropLast h
  case pos =>
    -- shift data: `d1 > 0` forces `d0 > 0`
    have np := parent_nextR hp
    have j0lt := nextR_index_lt np
    have chain := nextR_chain0 np
    have hd0pos : 0 < srow M (M.length - 1) →
        0 < entry M 0 (M.length - 1)
          - entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1)) := by
      intro _
      have := le0_interval_gt chain (M.length - 1) ⟨j0lt, le_rfl⟩
      omega
    rw [oper_gcopies n hL hz hp]
    refine z0ok_of_mem ?_
    intro x hx hx0
    rcases List.mem_append.1 hx with hm | hm
    · exact z0ok_mem h (List.mem_of_mem_take hm) hx0
    · obtain ⟨l, k, h1, h2, h3, rfl⟩ := mem_gcopies hm
      have hl : l < M.length := by omega
      simp only [] at hx0 ⊢
      -- row 0 of the copy column is zero: base is zero and the shift vanishes
      have hbase : entry M 0 l = 0 ∧ k * (if 0 < srow M (M.length - 1)
          then entry M 0 (M.length - 1)
            - entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1))
          else 0) = 0 := by omega
      have hz0 := z0ok_mem h (entry_triple_mem hl) hbase.1
      simp only [] at hz0
      constructor
      · -- the row-1 lift also vanishes
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp [hz0.1]
        · by_cases hi2 : 1 < srow M (M.length - 1)
          · -- `d1 > 0` would force `d0 > 0`, contradicting the zero row 0
            have hd0 := hd0pos (by omega)
            have : k * (entry M 0 (M.length - 1)
                - entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1))) = 0 := by
              have := hbase.2
              rwa [if_pos (by omega : 0 < srow M (M.length - 1))] at this
            have hk0 : k = 0 := by
              rcases Nat.mul_eq_zero.1 this with h' | h'
              · exact h'
              · omega
            omega
          · rw [if_neg hi2]
            split_ifs <;> simp [hz0.1]
      · exact hz0.2

/-! ## スパイン補題: 鎖上の節はガードを継承する -/

/-- Any row-0 chain node between `r` and a row-1 descendant `j1` of `r` is
itself a row-1 descendant (the spine of the `t = 2` decomposition lies in the
heartwood).  Immediate from the path lemma. -/
theorem le1_of_chain_le1 {M : TrioSeq} {r x j1 : ℕ} (h : le1 M r j1)
    (hrx : Relation.ReflTransGen (nextrel0 M) r x)
    (hxj : Relation.ReflTransGen (nextrel0 M) x j1) : le1 M r x := by
  have hxb : x < M.length := by
    have h1 := nextrel0_rtrancl_index_le hxj
    have h2 := h.2.1
    omega
  refine (le1_iff_chain_window hxb hrx).2 ?_
  intro y hry hyx hyne
  exact le1_chain_window h.2.2 y hry (hyx.trans hxj) hyne

/-! ## `gcopies` の位置補題 -/

theorem gcopy_getD {M : TrioSeq} {r L d0 d1 k q : ℕ} (hq : q < L) :
    (gcopy M r L d0 d1 k).getD q (0, 0, 0)
      = (entry M 0 (r + q) + k * d0,
         entry M 1 (r + q) + (if le1 M r (r + q) then k * d1 else 0),
         entry M 2 (r + q)) := by
  unfold gcopy
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range' (by simpa using hq)]
  rw [Nat.one_mul]
  rfl

theorem gcopiesFrom_length (M : TrioSeq) (r L d0 d1 k0 m : ℕ) :
    (gcopiesFrom M r L d0 d1 k0 m).length = m * L := by
  induction m generalizing k0 with
  | zero => rw [gcopiesFrom_zero, Nat.zero_mul]; rfl
  | succ m ih =>
    rw [gcopiesFrom_succ, List.length_append, gcopy_len, ih, Nat.succ_mul]
    omega

theorem gcopiesFrom_getD {M : TrioSeq} {r L d0 d1 : ℕ} :
    ∀ {i q k0 m : ℕ}, i < m → q < L →
      (gcopiesFrom M r L d0 d1 k0 m).getD (i * L + q) (0, 0, 0)
        = (entry M 0 (r + q) + (k0 + i) * d0,
           entry M 1 (r + q)
             + (if le1 M r (r + q) then (k0 + i) * d1 else 0),
           entry M 2 (r + q)) := by
  intro i
  induction i with
  | zero =>
    intro q k0 m hi hq
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [gcopiesFrom_succ, Nat.zero_mul, Nat.zero_add,
      getD_append_left (by rw [gcopy_len]; exact hq), gcopy_getD hq,
      Nat.add_zero]
  | succ i ih =>
    intro q k0 m hi hq
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [gcopiesFrom_succ,
      getD_app_right _ _ (by rw [gcopy_len]; rw [Nat.succ_mul]; omega),
      gcopy_len,
      show (i + 1) * L + q - L = i * L + q from by rw [Nat.succ_mul]; omega,
      ih (by omega) hq]
    rw [show k0 + 1 + i = k0 + (i + 1) from by omega]

theorem gcopies_length (M : TrioSeq) (r L d0 d1 n : ℕ) :
    (gcopies M r L d0 d1 n).length = n * L := by
  rw [gcopies_eq_from, gcopiesFrom_length]

theorem gcopies_getD {M : TrioSeq} {r L d0 d1 k q n : ℕ}
    (hk : k < n) (hq : q < L) :
    (gcopies M r L d0 d1 n).getD (k * L + q) (0, 0, 0)
      = (entry M 0 (r + q) + k * d0,
         entry M 1 (r + q) + (if le1 M r (r + q) then k * d1 else 0),
         entry M 2 (r + q)) := by
  rw [gcopies_eq_from, gcopiesFrom_getD hk hq, Nat.zero_add]

/-! ## 行 1 の規律の保存 -/

/-- The r1ok witness is the unique row-0 Next source. -/
theorem witness_nextrel0 {M : TrioSeq} {j k : ℕ} (hj : j < M.length) (hk : k < j)
    (hlev : (M.getD k (0, 0, 0)).1 + 1 = (M.getD j (0, 0, 0)).1)
    (hwin : ∀ l, k < l → l < j → (M.getD j (0, 0, 0)).1 ≤ (M.getD l (0, 0, 0)).1) :
    nextrel0 M k j := by
  refine ⟨by omega, hj, hk, ?_, ?_⟩
  · show entry M 0 k < entry M 0 j
    have e1 : entry M 0 k = (M.getD k (0, 0, 0)).1 := rfl
    have e2 : entry M 0 j = (M.getD j (0, 0, 0)).1 := rfl
    omega
  · intro l ⟨h1, h2⟩
    show entry M 0 j ≤ entry M 0 l
    have e1 : entry M 0 l = (M.getD l (0, 0, 0)).1 := rfl
    have e2 : entry M 0 j = (M.getD j (0, 0, 0)).1 := rfl
    have := hwin l h1 h2
    omega

end TRIO
