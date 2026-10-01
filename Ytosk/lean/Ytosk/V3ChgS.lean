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

end Ytosk
