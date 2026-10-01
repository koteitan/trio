/-
**落とす補題の組み立て (1)**: 数える子の列。

列 i の数える子の列 `CL M i`。M.take x の数える子の列は M の数える子の列の先頭部分（`cl_prefix`）。
数える子でなくなりうるのは M.take x での最後の子だけで、x はもとから最後なので、余分な子は末尾に付く。
-/
import Ytosk.V3ChgS

namespace Ytosk

open T

instance (M : Mat) (i : Nat) : DecidablePred (Counted M i) := fun c => by
  unfold Counted; infer_instance

/-- The counted children of `i`, left to right. -/
def CL (M : Mat) (i : Nat) : List Nat := (children M i).filter (fun c => decide (Counted M i c))

/-- **The counted values are the values of the counted children.** -/
theorem cvals_eq_map {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (i : Nat) :
    cvals M ρ i = (CL M i).map ρ.o := by
  unfold cvals CL
  have : (children M i).map (cnt M ρ i) = (children M i).map (fun c => if Counted M i c then ρ.o c else z) := by
    apply List.map_congr_left; intro c _; exact cnt_eq_ite M ρ i c
  rw [this]
  apply nzs_map_ite
  intro c hc _
  exact single_ne_z (single_o hC hG (mem_children hc).2)

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M)
include hx hR0 hZ2 hSD hZ1 hUAT

omit hR0 hZ2 hSD hZ1 hUAT in
/-- A child whose counting changes is the last child in `M.take x`. -/
theorem cnt_change_last {i c : Nat} (hi : i < x) (hc : c ∈ children M i) (hcx : c < x)
    (h : ¬ (Counted (M.take x) i c ↔ Counted M i c)) : ∀ d ∈ children M i, d < x → d ≤ c := by
  intro d hd hdx
  have hAc : Anc0 M c (x - 1) := by
    rcases cnt_change hx hi hcx h with hxc | hu
    · exact anc_xm1 hx (Anc0.step (mem_children_iff.mp hxc).2 (Anc0.refl c)) hcx
    · obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
      rcases hcase with h' | ⟨hA, _⟩
      · omega
      · exact hA
  by_contra hlt
  have hcd : Anc0 M c d := anc_between hAc d (by omega) (by omega)
  have hpd : par M 0 d = some i := (mem_children_iff.mp hd).2
  have := (anc0_par hcd (by omega) hpd).le
  have := (mem_children hc).1
  omega

/-- **The counted children of `M.take x` are a prefix of those of `M`.** -/
theorem cl_prefix {i : Nat} (hi : i < x) : ∃ Tl, CL M i = CL (M.take x) i ++ Tl := by
  have hcnt := counted_take_last (M := M) (by omega) hR0 hZ2 hSD hZ1 hUAT
  rw [show M.length - 1 = x by omega] at hcnt
  -- the children of `i` in `M`: those below `x`, then possibly `x`
  set A := (children M i).filter (fun d => decide (d < x)) with hA
  have hchM : ∃ X, children M i = A ++ X ∧ ∀ d ∈ X, d = x := by
    by_cases hxi : x ∈ children M i
    · exact ⟨[x], children_split_x hx hxi, by simp⟩
    · exact ⟨[], by rw [hA, children_filter_x hx hxi]; simp, by simp⟩
  obtain ⟨X, hchM, hX⟩ := hchM
  have hchT : children (M.take x) i = A := children_take M x i
  -- agreement of the two countings except at the last element of `A`
  have hagree : ∀ d ∈ A, (∃ e ∈ A, d < e) →
      (decide (Counted (M.take x) i d) = decide (Counted M i d)) := by
    intro d hd ⟨e, he, hde⟩
    rw [hA, List.mem_filter] at hd he
    have hdx : d < x := by simpa using hd.2
    have hex : e < x := by simpa using he.2
    apply decide_eq_decide.mpr
    by_contra hne
    have := cnt_change_last hx hi hd.1 hdx hne e he.1 hex
    omega
  unfold CL
  rw [hchT, hchM, List.filter_append]
  -- split `A` at its last element
  rcases List.eq_nil_or_concat A with hnil | ⟨A', ℓ, hAl⟩
  · rw [hnil]; simp
  · rw [List.concat_eq_append] at hAl
    have hsorted : A.Pairwise (· < ·) := (children_sorted M i).filter _
    rw [hAl] at hsorted ⊢
    have hA'ℓ : ∀ d ∈ A', d < ℓ := by
      intro d hd
      exact (List.pairwise_append.mp hsorted).2.2 d hd ℓ (by simp)
    have hfilt : A'.filter (fun d => decide (Counted M i d)) =
        A'.filter (fun d => decide (Counted (M.take x) i d)) := by
      apply List.filter_congr
      intro d hd
      exact (hagree d (by rw [hAl]; simp [hd]) ⟨ℓ, by rw [hAl]; simp, hA'ℓ d hd⟩).symm
    have hℓx : ℓ < x := by
      have : ℓ ∈ A := by rw [hAl]; simp
      rw [hA, List.mem_filter] at this; simpa using this.2
    have hℓM : ℓ ∈ children M i := by
      have : ℓ ∈ A := by rw [hAl]; simp
      rw [hA, List.mem_filter] at this; exact this.1
    simp only [List.filter_append, hfilt, List.filter_cons, List.filter_nil, List.append_assoc]
    by_cases hT : Counted (M.take x) i ℓ
    · have hM : Counted M i ℓ :=
        hcnt i ℓ hi (by rw [children_take, List.mem_filter]; exact ⟨hℓM, by simpa using hℓx⟩) hT
      simp only [decide_eq_true hT, decide_eq_true hM, if_true]
      exact ⟨X.filter (fun d => decide (Counted M i d)), by simp⟩
    · simp only [decide_eq_false hT]
      exact ⟨(if Counted M i ℓ then [ℓ] else []) ++ X.filter (fun d => decide (Counted M i d)), by
        by_cases hM : Counted M i ℓ <;> simp [hM]⟩

end

/-! ## t = 1・q ≠ r の基底: r とその下の v は変わらない -/

/-- The row-1 parent of a child with a larger row 1 is its parent. -/
theorem par1_of_child {M : Mat} {p r : Nat} (hp : par M 0 p = some r) (h1 : entry M 1 r < entry M 1 p) :
    par M 1 p = some r := by
  show climb (par M 0) (fun q => decide (entry M 1 q < entry M 1 p)) (p + 1) (par M 0 p) = some r
  rw [hp]
  simp [climb, h1]

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB

/-- **`v(r)` does not change** (`t = 1`, `q ≠ r`). -/
theorem v_r_not_chg {r : Nat} (hA : Anc0 M r x) (hrx : r ≠ x) (hqr : par M 0 x ≠ some r)
    (hpath : ∀ s, Anc0 M r s → Anc0 M s x → s ≠ r → s ≠ x → entry M 1 r < entry M 1 s) :
    ¬ ChgX M x false r := by
  intro hC
  have hr : r < x := lt_of_le_of_ne hA.le hrx
  obtain ⟨p, hpr, hpx⟩ := anc0_child hA hrx
  have hpne : p ≠ x := fun e => hqr (e ▸ hpr)
  have hpx' : p < x := lt_of_le_of_ne hpx.le hpne
  have h1 := hpath p (Anc0.step hpr (Anc0.refl r)) hpx (by have := par_lt M 0 p r hpr; omega) hpne
  exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hC).1 rfl hr |>.2.2 p hpx' (par1_of_child hpr h1)

/-- **A `v` read through `P_1` or an ancestor-type upgrade from a column before `x` does not change.** -/
theorem v_read_not_chg {g d : Nat} (hd : d < x)
    (h : par M 1 d = some g ∨ (upg M d = some g ∧ g < d)) : ¬ ChgX M x false g := by
  intro hC
  have hgd : g < d := by
    rcases h with h | h
    · exact par_lt M 1 d g h
    · exact h.2
  have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hC).1 rfl (by omega)
  rcases h with h | ⟨hu, _⟩
  · exact hT.2.2 d hd h
  · obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
    rcases hcase with h' | ⟨hAg, _⟩
    · omega
    · exact no_anc_upg hx hR0 hZ2 hSD hZ1 hUAT hUAB hT (by omega) hu hAg hgd

end

end Ytosk
