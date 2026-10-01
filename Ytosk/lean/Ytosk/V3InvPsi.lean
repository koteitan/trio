/-
**のりしろの子の下の葉 Ψ（`BumpLeaf`）と、そこから UAB・UAT。**

`BumpLeaf M`: k ののりしろの子 j の子 c で、行 1 が k 以上なら、c は行 2 が 0 の葉で、j の最後の子、
j は k の最後の子。展開の不変条件として UAB の代わりに使う（上げを使わない局所的な形）。
- 実測: SRO からの展開の全接頭辞 118993 個で例外 0（実例 62568 件）。SRO 自身では偽（UAB も偽）。
- `uab_of_bumpLeaf`: UAB は BumpLeaf から出る。上げ i → k（祖先型）の的 k の、i へ向かうのりしろの子 j の
  下では、i は k の部分木の最後の列になり、上げの条件「行 0 が k < i+1」と両立しない。
- UAT は UAB から（`UAT_take` を全長で）。
-/
import Ytosk.V3InvExp
import Ytosk.V3T0S

namespace Ytosk

open T

/-- **Leaves under a bump child**: a child `c` of a bump child `j` of `k` with row 1 at least that of `k`
is a row-2-zero leaf, the last child of `j`, and `j` is the last child of `k`. -/
def BumpLeaf (M : Mat) : Prop :=
  ∀ k j c, j ∈ children M k → col M j = bump M k → c ∈ children M j → entry M 1 k ≤ entry M 1 c →
    entry M 2 c = 0 ∧ children M c = [] ∧ (children M j).getLast? = some c ∧
      (children M k).getLast? = some j

/-! ## 部分木の補題 -/

/-- The column after `i` is in the subtree of an ancestor `k` of `i` when its row 0 is larger. -/
theorem anc0_next {M : Mat} {k i : Nat} (hA : Anc0 M k i)
    (he : entry M 0 k < entry M 0 (i + 1)) : Anc0 M k (i + 1) := by
  have hki := hA.le
  obtain ⟨p, hp⟩ := par0_some_of (M := M) (show k < i + 1 by omega) he
  obtain ⟨hpi, hlt, hbet⟩ := (par0_spec M).mp hp
  have hkp : k ≤ p := by
    by_contra h
    have := hbet k (by omega) (by omega); omega
  exact Anc0.step hp (anc_between hA p hkp (by omega))

/-- A descendant of `k` after the last child `j` of `k` is a descendant of `j`. -/
theorem anc0_last_child {M : Mat} {k j a : Nat} (hl : (children M k).getLast? = some j)
    (hA : Anc0 M k a) (hja : j ≤ a) (ha : a < M.length) : Anc0 M j a := by
  have hjc : j ∈ children M k := List.mem_of_getLast? hl
  have hkj := (mem_children hjc).1
  obtain ⟨c, hpc, hca⟩ := anc0_child hA (by omega)
  have hcm : c ∈ children M k := mem_children_iff.mpr ⟨by have := hca.le; omega, hpc⟩
  have hcj : c ≤ j := by
    have hs := children_sorted M k
    obtain ⟨l, hl'⟩ : ∃ l, children M k = l ++ [j] := by
      rcases List.eq_nil_or_concat (children M k) with h | ⟨l, b, h⟩
      · rw [h] at hl; simp at hl
      · rw [List.concat_eq_append] at h; rw [h] at hl; simp at hl; subst hl; exact ⟨l, h⟩
    rw [hl'] at hcm hs
    rcases List.mem_append.mp hcm with h | h
    · exact le_of_lt ((List.pairwise_append.mp hs).2.2 c h j (by simp))
    · simp at h; omega
  rcases Nat.eq_or_lt_of_le hcj with h | h
  · rw [← h]; exact hca
  · exfalso
    have hAcj : Anc0 M c j := anc_between hca j (by omega) hja
    have hpj : par M 0 j = some k := (mem_children_iff.mp hjc).2
    have := (anc0_par hAcj (by omega) hpj).le
    have := (mem_children hcm).1
    omega

/-- A leaf has no proper descendants. -/
theorem anc0_leaf {M : Mat} {c a : Nat} (hl : children M c = []) (hA : Anc0 M c a) : a = c := by
  by_contra hne
  obtain ⟨d, hpd, hda⟩ := anc0_child hA (Ne.symm hne)
  have hdl : d < M.length := by
    by_contra h; rw [par0_out' (by omega)] at hpd; cases hpd
  have : d ∈ children M c := mem_children_iff.mpr ⟨hdl, hpd⟩
  rw [hl] at this; simp at this

/-! ## BumpLeaf ⇒ UAB ⇒ UAT -/

/-- **UAB from BumpLeaf.** -/
theorem uab_of_bumpLeaf {M : Mat} (hBL : BumpLeaf M) : UAB M := by
  intro i k hu hne j hj hjb hAji
  obtain ⟨m, hm1, hk1, hcol, hcase⟩ := upg_spec hu
  rcases hcase with h | ⟨hAki, hki⟩
  · exact hne h
  have he0 := upg_climb_e0 hu hne
  have hn := upg_succ_lt hu
  -- `i` has row 2 different from `1`, `j` has row 2 equal to `1`
  have hi2 : entry M 2 i ≠ 1 := by
    intro h; unfold upg at hu; rw [if_pos (Or.inr (Or.inl h))] at hu; cases hu
  have hj2 : entry M 2 j = 1 := by have : entry M 2 j = (col M j).2.2 := rfl; rw [this, hjb]; rfl
  have hji : j ≠ i := fun h => hi2 (h ▸ hj2)
  obtain ⟨c, hpc, hci⟩ := anc0_child hAji hji
  have hcl : c < M.length := by
    have := hci.le; have := upg_succ_lt hu; omega
  have hcj : c ∈ children M j := mem_children_iff.mpr ⟨hcl, hpc⟩
  -- row 1 of `c` is at least that of `k` (= that of `i`)
  have hk1e : entry M 1 k = entry M 1 i := by
    have : entry M 1 k = (col M k).2.1 := rfl; rw [this, hcol]
  have hmk : m < k := par_lt M 1 k m hk1
  have hjk := (mem_children hj).1
  have hc1 : entry M 1 k ≤ entry M 1 c := by
    rw [hk1e]
    exact par1_between hm1 c hci (by have := (mem_children hcj).1; omega)
  obtain ⟨_, hleaf, hlastc, hlastj⟩ := hBL k j c hj hjb hcj hc1
  have hic : i = c := anc0_leaf hleaf hci
  -- `i + 1` is in the subtree of `k`, hence of `j`, hence of `c`
  have hAk1 := anc0_next hAki he0
  have hAj1 := anc0_last_child hlastj hAk1 (by have := hAji.le; omega) hn
  have hAc1 := anc0_last_child hlastc hAj1 (by omega) hn
  have := anc0_leaf hleaf hAc1
  omega

/-- **UAT from UAB.** -/
theorem uat_of_uab {M : Mat} (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAB : UAB M) :
    UAT M := by
  have := UAT_take hR0 hZ2 hSD hZ1 hUAB M.length
  rwa [List.take_length] at this

/-! ## 先頭部分で保たれる -/

theorem bumpLeaf_take {M : Mat} (h : BumpLeaf M) (m : Nat) : BumpLeaf (M.take m) := by
  intro k j c hj hjb hc h1
  obtain ⟨hjm, hjM⟩ := mem_children_take hj
  obtain ⟨hcm, hcM⟩ := mem_children_take hc
  have hkj := (mem_children hjM).1
  have hjc := (mem_children hcM).1
  rw [col_take M hjm, bump_take M (by omega)] at hjb
  rw [entry_take M 1 (by omega), entry_take M 1 hcm] at h1
  obtain ⟨h2, hleaf, hlc, hlj⟩ := h k j c hjM hjb hcM h1
  refine ⟨by rw [entry_take M 2 hcm]; exact h2, ?_, ?_, ?_⟩
  · rw [children_take, hleaf]; rfl
  · -- the last child of `j` in `M` is `c`, which survives
    rw [children_take]
    obtain ⟨l, hl⟩ : ∃ l, children M j = l ++ [c] := by
      rcases List.eq_nil_or_concat (children M j) with h' | ⟨l, b, h'⟩
      · rw [h'] at hlc; simp at hlc
      · rw [List.concat_eq_append] at h'; rw [h'] at hlc; simp at hlc; subst hlc; exact ⟨l, h'⟩
    rw [hl, List.filter_append]
    simp [hcm]
  · rw [children_take]
    obtain ⟨l, hl⟩ : ∃ l, children M k = l ++ [j] := by
      rcases List.eq_nil_or_concat (children M k) with h' | ⟨l, b, h'⟩
      · rw [h'] at hlj; simp at hlj
      · rw [List.concat_eq_append] at h'; rw [h'] at hlj; simp at hlj; subst hlj; exact ⟨l, h'⟩
    rw [hl, List.filter_append]
    simp [hjm]

end Ytosk
