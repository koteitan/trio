/-
**落とす補題: 変化の集合 C（`ChgX`）の構造。**

構造の不変条件（R0P・Z2・SibDec・Z1C・UAT・UAB）のもとで:
- 行 2 が 1 の列を par1 で指す列はない（`no_par1_of_e2`）。
- 行 2 が 1 の列の最後の子がのりしろ列なら、子はすべてのりしろ列（`all_bump_of_last`）。
- 上げの先の形（`upg_spec`）。
-/
import Ytosk.V3Chg

namespace Ytosk

open T

/-- An ancestor-type upgrade never comes from below a bump child of its target. -/
def UAB (M : Mat) : Prop :=
  ∀ i k, upg M i = some k → k ≠ i + 1 → ∀ j, j ∈ children M k → col M j = bump M k → ¬ Anc0 M j i

/-! ## 行 2 が 1 の列 -/

/-- **No column has a row-1 parent with row 2 equal to `1`.** -/
theorem no_par1_of_e2 {M : Mat} (hZ1 : Z1C M) {i d : Nat} (hd : d < M.length) (he : entry M 2 i = 1)
    (hp : par M 1 d = some i) : False := by
  have hA := anc0_of_par M 1 i d hp
  have hid : i ≠ d := by have := par_lt M 1 d i hp; omega
  obtain ⟨p, hpi, hpd⟩ := anc0_child hA hid
  have hpl : p < M.length := by have := hpd.le; omega
  have hpc : p ∈ children M i := mem_children_iff.mpr ⟨hpl, hpi⟩
  have h1 := hZ1 i p he hpc
  have h2 := par1_between hp p hpd (par_lt M 0 p i hpi)
  have h3 := par1_entry_lt hp
  omega

theorem colLe_trans {a b c : Nat × Nat × Nat} (h1 : colLe a b) (h2 : colLe b c) : colLe a c := by
  unfold colLe at *
  omega

/-- Siblings do not increase (any two, not only consecutive ones). -/
theorem sib_le {M : Mat} (hSD : SibDec M) {p : Nat} :
    ∀ (l₂ l₁ : List Nat) (a : Nat), children M p = l₁ ++ a :: l₂ → ∀ b ∈ l₂, colLe (col M b) (col M a)
  | [], _, _, _, b, hb => absurd hb (by simp)
  | c :: l₂, l₁, a, h, b, hb => by
    have hac := hSD p l₁ l₂ a c h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hac
    · have h' : children M p = (l₁ ++ [a]) ++ c :: l₂ := by rw [h]; simp
      exact colLe_trans (sib_le hSD l₂ (l₁ ++ [a]) c h' b hb) hac

/-- **All children are bump columns** when row 2 is `1` and the last child is the bump column. -/
theorem all_bump_of_last {M : Mat} (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M)
    {i j : Nat} {L : List Nat} (he : entry M 2 i = 1) (hch : children M i = L ++ [j])
    (hjb : col M j = bump M i) : ∀ c ∈ children M i, col M c = bump M i := by
  intro c hc
  rw [hch] at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hc
    have hch' : children M i = l₁ ++ c :: (l₂ ++ [j]) := by rw [hch, hl]; simp
    have hle := sib_le hSD (l₂ ++ [j]) l₁ c hch' j (by simp)
    have hcm : c ∈ children M i := by rw [hch']; simp
    have hpc : par M 0 c = some i := (mem_children_iff.mp hcm).2
    have h0 := hR0 c i hpc
    have h1 := hZ1 i c he hcm
    have h2 := hZ2 c
    rw [hjb] at hle
    unfold colLe bump at hle
    unfold bump
    have e0 : (col M c).1 = entry M 0 c := rfl
    have e1 : (col M c).2.1 = entry M 1 c := rfl
    have e2 : (col M c).2.2 = entry M 2 c := rfl
    simp only at hle
    rw [e0, e1, e2] at hle
    have hc1 : entry M 1 c = entry M 1 i := by omega
    have hc2 : entry M 2 c = 1 := by omega
    rcases hcol : col M c with ⟨a0, a1, a2⟩
    rw [hcol] at e0 e1 e2
    simp only at e0 e1 e2
    rw [e0, e1, e2, h0, hc1, hc2]
  · rw [List.mem_singleton] at hc; rw [hc]; exact hjb

/-! ## 部分木 -/

/-- **Subtrees are intervals.** -/
theorem anc_between {M : Mat} {a b : Nat} (h : Anc0 M a b) : ∀ j, a ≤ j → j ≤ b → Anc0 M a j := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro haj hjb
    rcases Nat.eq_or_lt_of_le haj with rfl | hlt
    · exact Anc0.refl _
    · have he := anc0_interval h j hlt hjb
      obtain ⟨p, hp⟩ := par0_some_of hlt he
      have hpj := par_lt M 0 j p hp
      have hap := par0_ge_of_anc h hlt hjb hp
      exact Anc0.step hp (ih p hpj hap (by omega))

/-- An ancestor of a column has a smaller row 0. -/
theorem anc0_e0_lt {M : Mat} {a b : Nat} (h : Anc0 M a b) (hne : a ≠ b) : entry M 0 a < entry M 0 b :=
  anc0_interval h b (lt_of_le_of_ne h.le hne) (Nat.le_refl _)

/-- **Ancestors are determined by their row 0.** -/
theorem anc0_eq_of_e0 {M : Mat} {a b d : Nat} (ha : Anc0 M a d) (hb : Anc0 M b d)
    (he : entry M 0 a = entry M 0 b) : a = b := by
  rcases anc0_total ha hb with h | h
  · by_contra hne; have := anc0_e0_lt h hne; omega
  · by_contra hne; have := anc0_e0_lt h (Ne.symm hne); omega

theorem entry_out' {M : Mat} {k : Nat} (hk : M.length ≤ k) (i : Nat) : entry M i k = 0 := by
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
  split_ifs <;> rfl

/-- A column beyond the matrix has no parent. -/
theorem par0_out' {M : Mat} {c : Nat} (hc : M.length ≤ c) : par M 0 c = none := by
  cases h : par M 0 c with
  | none => rfl
  | some p =>
    have := ((par0_spec M).mp h).2.1
    rw [entry_out' hc] at this; omega

theorem anc0_lt_len {M : Mat} {a b : Nat} (h : Anc0 M a b) (hne : a ≠ b) : b < M.length := by
  cases h with
  | refl => exact absurd rfl hne
  | step hp _ =>
    by_contra hc
    rw [par0_out' (by omega)] at hp; cases hp

/-- The first column after an ancestor with children is its child. -/
theorem child_succ {M : Mat} {i d : Nat} (h : Anc0 M i d) (hne : i ≠ d) : par M 0 (i + 1) = some i := by
  have hid : i < d := lt_of_le_of_ne h.le hne
  have hA := anc_between h (i + 1) (by omega) (by omega)
  cases hA with
  | @step b _ hp hA' =>
    have := hA'.le; have := par_lt M 0 _ _ hp
    have hb : b = i := by omega
    rw [hb] at hp; exact hp

/-! ## 上げの先 -/

/-- **The shape of an upgrade target**: same row-1 parent, row 0 and row 2 one above it,
and it is the next column or an ancestor. -/
theorem upg_spec {M : Mat} {n k : Nat} (h : upg M n = some k) :
    ∃ m, par M 1 n = some m ∧ par M 1 k = some m ∧
      col M k = (entry M 0 m + 1, entry M 1 n, entry M 2 m + 1) ∧
      (k = n + 1 ∨ (Anc0 M k n ∧ k < n)) := by
  unfold upg at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i m hm
      simp only at h
      split at h
      · rename_i hcl
        have hc : n + 1 = k := Option.some.inj h
        subst hc
        exact ⟨m, hm, hcl.1, hcl.2, Or.inl rfl⟩
      · rw [upgClimb_find] at h
        have hp := List.find?_some h
        simp only [decide_eq_true_eq] at hp
        have hmem := List.mem_of_find?_eq_some h
        exact ⟨m, hm, hp.1, hp.2.1, Or.inr ⟨anc0_of_mem_ancL hmem, mem_ancL_lt hmem⟩⟩

/-- **An upgrade to the next column comes from a leaf.** -/
theorem leaf_of_upg_next {M : Mat} (hR0 : R0P M) {i : Nat} (h : upg M i = some (i + 1)) :
    ∀ d, Anc0 M i d → d = i := by
  intro d hd
  by_contra hne
  have hp := child_succ hd (Ne.symm hne)
  obtain ⟨m, hm, _, hcol, _⟩ := upg_spec h
  have h0 := hR0 _ _ hp
  have e0 : entry M 0 (i + 1) = (col M (i + 1)).1 := rfl
  rw [hcol] at e0
  simp only at e0
  have hmi := anc0_e0_lt (anc0_of_par M 1 m i hm) (by have := par_lt M 1 i m hm; omega)
  omega

theorem upg_succ_lt {M : Mat} {n k : Nat} (h : upg M n = some k) : n + 1 < M.length := by
  unfold upg at h
  split at h
  · cases h
  · rename_i hc
    have h1 : entry M 1 n ≠ 0 := fun e => hc (Or.inl e)
    have h3 : n + 1 ≠ M.length := fun e => hc (Or.inr (Or.inr e))
    have hn : n < M.length := by
      by_contra hn; exact h1 (entry_out' (by omega) 1)
    omega

/-! ## x を落とすときの構造の変化 -/

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
include hx

/-- The ancestors of `x` other than `x` are ancestors of `x − 1`. -/
theorem anc_xm1 {c : Nat} (h : Anc0 M c x) (hc : c < x) : Anc0 M c (x - 1) := by
  cases h with
  | refl => omega
  | @step b _ hp hA =>
    have hbx := par_lt M 0 x b hp
    exact Anc0.trans hA (anc_between (Anc0.step hp (Anc0.refl b)) (x - 1) (by omega) (by omega))

/-- `topped` changes only where `x` is a child. -/
theorem topped_take_eq {i : Nat} (hi : i < x) (h : x ∉ children M i) :
    topped (M.take x) i = topped M i := by
  unfold topped
  rw [children_take, children_filter_x hx h]
  cases hl : (children M i).getLast? with
  | none => rfl
  | some c =>
    have hcm := List.mem_of_getLast? hl
    have hcx : c < x := by
      have := (mem_children hcm).2
      have hne : c ≠ x := fun e => h (e ▸ hcm)
      omega
    simp only [col_take M hcx, bump_take M hi]

/-- **Where the counting changes**: at the parent of `x`, or at the target of the upgrade of `x − 1`. -/
theorem cnt_change {i c : Nat} (hi : i < x) (hcx : c < x)
    (h : ¬ (Counted (M.take x) i c ↔ Counted M i c)) : x ∈ children M c ∨ upg M (x - 1) = some c := by
  by_contra hn
  rw [not_or] at hn
  obtain ⟨hxc, hu⟩ := hn
  apply h
  have htop := topped_take_eq hx hcx hxc
  have hup : isUpg (M.take x) c = isUpg M c := by
    apply Bool.eq_iff_iff.mpr
    rw [isUpg_take M (by omega) c]
    unfold isUpg
    rw [List.any_eq_true]
    constructor
    · rintro ⟨j, hj, hjc⟩
      exact ⟨j, List.mem_range.mpr (by omega), decide_eq_true hjc⟩
    · rintro ⟨j, hj, hjc⟩
      have hjc' : upg M j = some c := of_decide_eq_true hjc
      have := upg_succ_lt hjc'
      refine ⟨j, ?_, hjc'⟩
      by_contra hjx
      have : j = x - 1 := by omega
      exact hu (this ▸ hjc')
  unfold Counted
  rw [col_take M hcx, bump_take M hi, htop, hup]

end

end Ytosk
