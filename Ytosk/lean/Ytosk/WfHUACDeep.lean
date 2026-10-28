/-
HUAC through a deep return: a grandchild c of the upgrade target k (through a
surviving bump child j) whose column returns to the row-1 level of a row-1
ancestor a of m = P0(k).  Then v(c) = v(a), and finite support of v(m) in v(a)
is enough.  The case a = m is the old return witness; the old support witness
is the case where the support is checked against v(c) directly.
-/
import Ytosk.V3HUACShape

namespace Ytosk.WfHUACDeep
open T
open HUACSupport

/-- `Up1 M a x`: `a` is reached from `x` by zero or more row-1 parent steps. -/
inductive Up1 (M : Mat) : Nat → Nat → Prop
  | refl (x : Nat) : Up1 M x x
  | step {a x y : Nat} : par M 1 x = some y → Up1 M a y → Up1 M a x

/-- Generic transport: support of `v(m)` in `v(c)` for a surviving grandchild. -/
theorem dom_of_grandchild_support {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {n k m j c : Nat}
    (hn : n < M.length) (hu : upg M n = some k)
    (hkm : par M 0 k = some m)
    (hj : j ∈ children M k) (hjb : col M j = bump M k)
    (hBP : bumpTerm M ρ k j ∈ summands (sumN (one :: (children M k).map (bumpTerm M ρ k))))
    (hc : c ∈ children M j) (hoG : ρ.o c ∈ summands (sumN ((children M j).map ρ.o)))
    (hsupport : Support (ρ.v m) (ρ.v c)) :
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z]) := by
  have _hj := hj
  have hcN := (mem_children hc).2
  obtain ⟨m', hm', hk0⟩ := upg_target_par0 S.r0p hu
  rw [hkm] at hk0; cases hk0
  obtain ⟨y, hy⟩ := o_psi_sub hC hcN
  rw [sf_ot (hG.ot_v c hcN)] at hy
  have hV_o : ∀ u, Dom (comps u (ρ.v m)) (comps u (ρ.o c) ++ [z]) := by
    rw [hy]
    exact dom_of_index_support (hG.ot_v c hcN) hsupport
  have ho_G : ∀ u, Dom (comps u (ρ.o c))
      (comps u (sumN ((children M j).map ρ.o)) ++ [z]) :=
    fun u g hg => ⟨g, List.mem_append_left _ (comps_summand_subH u hoG g hg), le_refl _⟩
  have hGot : isOT (sumN ((children M j).map ρ.o)) = true :=
    isOT_sumN _ (by intro q hq; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq; exact hG.ot_o d (mem_children hd).2)
  have hG_B : ∀ u, Dom (comps u (sumN ((children M j).map ρ.o)))
      (comps u (bumpTerm M ρ k j) ++ [z]) := by
    unfold bumpTerm
    rw [if_pos hjb]
    exact OmegaComps.dom_comps_omega hGot
  let P := sumN (one :: (children M k).map (bumpTerm M ρ k))
  have hB_P : ∀ u, Dom (comps u (bumpTerm M ρ k j)) (comps u P ++ [z]) :=
    fun u g hg => ⟨g, List.mem_append_left _ (comps_summand_subH u hBP g hg), le_refl _⟩
  have hP_W : ∀ u, Dom (comps u P) (comps u (bumpW M ρ k) ++ [z]) :=
    OmegaComps.dom_comps_omega (isOT_bumpP hG k)
  have hW_v : ∀ u, Dom (comps u (bumpW M ρ k)) (comps u (ρ.v n) ++ [z]) := by
    intro u g hg
    refine ⟨g, List.mem_append_left _ ?_, le_refl _⟩
    rw [value_at_target S hC hG hn hu]
    exact SumComps.mem_add_right hg
  rw [hm']
  simp only [vOpt]
  exact HUACPath.comp_dom_trans hV_o (HUACPath.comp_dom_trans ho_G
    (HUACPath.comp_dom_trans hG_B (HUACPath.comp_dom_trans hB_P (HUACPath.comp_dom_trans hP_W hW_v))))

/-- Generic transport from component domination of `v(m)` by `v(c)`. -/
theorem dom_of_grandchild_dom {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {n k m j c : Nat}
    (hn : n < M.length) (hu : upg M n = some k)
    (hkm : par M 0 k = some m)
    (hj : j ∈ children M k) (hjb : col M j = bump M k)
    (hBP : bumpTerm M ρ k j ∈ summands (sumN (one :: (children M k).map (bumpTerm M ρ k))))
    (hc : c ∈ children M j) (hoG : ρ.o c ∈ summands (sumN ((children M j).map ρ.o)))
    (hdom : ∀ u, Dom (comps u (ρ.v m)) (comps u (ρ.v c) ++ [z])) :
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z]) := by
  have _hj := hj
  have hcN := (mem_children hc).2
  obtain ⟨m', hm', hk0⟩ := upg_target_par0 S.r0p hu
  rw [hkm] at hk0; cases hk0
  obtain ⟨y, hy⟩ := o_psi_sub hC hcN
  rw [sf_ot (hG.ot_v c hcN)] at hy
  have hV_o : ∀ u, Dom (comps u (ρ.v m)) (comps u (ρ.o c) ++ [z]) := by
    rw [hy]
    exact HUACPath.comp_dom_trans hdom (HUACPath.index_comp_dom (hG.ot_v c hcN))
  have ho_G : ∀ u, Dom (comps u (ρ.o c))
      (comps u (sumN ((children M j).map ρ.o)) ++ [z]) :=
    fun u g hg => ⟨g, List.mem_append_left _ (comps_summand_subH u hoG g hg), le_refl _⟩
  have hGot : isOT (sumN ((children M j).map ρ.o)) = true :=
    isOT_sumN _ (by intro q hq; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq; exact hG.ot_o d (mem_children hd).2)
  have hG_B : ∀ u, Dom (comps u (sumN ((children M j).map ρ.o)))
      (comps u (bumpTerm M ρ k j) ++ [z]) := by
    unfold bumpTerm
    rw [if_pos hjb]
    exact OmegaComps.dom_comps_omega hGot
  let P := sumN (one :: (children M k).map (bumpTerm M ρ k))
  have hB_P : ∀ u, Dom (comps u (bumpTerm M ρ k j)) (comps u P ++ [z]) :=
    fun u g hg => ⟨g, List.mem_append_left _ (comps_summand_subH u hBP g hg), le_refl _⟩
  have hP_W : ∀ u, Dom (comps u P) (comps u (bumpW M ρ k) ++ [z]) :=
    OmegaComps.dom_comps_omega (isOT_bumpP hG k)
  have hW_v : ∀ u, Dom (comps u (bumpW M ρ k)) (comps u (ρ.v n) ++ [z]) := by
    intro u g hg
    refine ⟨g, List.mem_append_left _ ?_, le_refl _⟩
    rw [value_at_target S hC hG hn hu]
    exact SumComps.mem_add_right hg
  rw [hm']
  simp only [vOpt]
  exact HUACPath.comp_dom_trans hV_o (HUACPath.comp_dom_trans ho_G
    (HUACPath.comp_dom_trans hG_B (HUACPath.comp_dom_trans hB_P (HUACPath.comp_dom_trans hP_W hW_v))))

/-- Two row-2-zero columns with the same row-1 entry, row-1 parent and upgrade
have the same value. -/
theorem value_eq_of_same_rhs {M : Mat} {ρ : Valn} (hC : Cons M ρ) {c a : Nat}
    (hc : c < M.length) (ha : a < M.length)
    (h1 : entry M 1 c = entry M 1 a) (hc2 : entry M 2 c = 0) (ha2 : entry M 2 a = 0)
    (hp : par M 1 c = par M 1 a) (hup : upg M c = upg M a) : ρ.v c = ρ.v a := by
  rw [(hC c hc).2, (hC a ha).2]
  unfold vRhs
  rw [h1, hc2, ha2, hp, hup]
  simp

theorem up1_le {M : Mat} {a x : Nat} (h : Up1 M a x) : a ≤ x := by
  induction h with
  | refl => exact le_refl _
  | step hp _ ih => have := par_lt M 1 _ _ hp; omega

theorem up1_anc0 {M : Mat} {a x : Nat} (h : Up1 M a x) : Anc0 M a x := by
  induction h with
  | refl => exact Anc0.refl _
  | step hp _ ih => exact ih.trans (anc0_of_par M 1 _ _ hp)

theorem up1_e1_le {M : Mat} {a x : Nat} (h : Up1 M a x) : entry M 1 a ≤ entry M 1 x := by
  induction h with
  | refl => exact le_refl _
  | step hp _ ih => have := par1_entry_lt hp; omega

/-- Strictly between `a` and `x` (and at `x` itself, when `x ≠ a`) row 1 is above `a`'s. -/
theorem up1_hi {M : Mat} {a x : Nat} (h : Up1 M a x) :
    ∀ s, Anc0 M a s → Anc0 M s x → s ≠ a → entry M 1 a < entry M 1 s := by
  induction h with
  | refl =>
    intro s h1 h2 hne
    exact absurd (le_antisymm h2.le h1.le) hne
  | @step x y hp hA ih =>
    intro s h1 h2 hne
    have hyx := par1_entry_lt hp
    have hay := up1_e1_le hA
    have hYX := anc0_of_par M 1 y x hp
    by_cases hsy : s ≤ y
    · exact ih s h1 (anc_between h2 y hsy hYX.le) hne
    · have := par1_between hp s h2 (by omega)
      omega

/-- The ancestor list of `x` passes through `a`, above `a`'s row 1 before it. -/
theorem up1_split {M : Mat} {a x : Nat} (h : Up1 M a x) :
    ∃ S, x :: ancL M x = S ++ a :: ancL M a ∧ ∀ s ∈ S, entry M 1 a < entry M 1 s := by
  by_cases hax : a = x
  · subst hax; exact ⟨[], rfl, by simp⟩
  · obtain ⟨S, hS, hSp⟩ := ancL_through (up1_anc0 h) hax
    refine ⟨x :: S, by rw [hS]; rfl, ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact up1_hi h s (up1_anc0 h) (Anc0.refl _) (Ne.symm hax)
    · obtain ⟨h1, _, h3, h4⟩ := hSp s hs
      exact up1_hi h s h3 h4 (by omega)

theorem find_congr_mem {l : List Nat} {p q : Nat → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.find?_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem find_skip {S l : List Nat} {p : Nat → Bool} (h : ∀ x ∈ S, p x = false) :
    (S ++ l).find? p = l.find? p := by
  induction S with
  | nil => rfl
  | cons x S ih =>
    simp only [List.cons_append, List.find?_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- **Deep return**: a grandchild of the upgrade target through a bump child that
returns to the row-1 level of a row-1 ancestor `a` of `m` has `a`'s row-1 parent
and upgrade. -/
theorem deep_return {M : Mat} (S : SInv M) {n k m j c a : Nat}
    (hn : n < M.length) (hu : upg M n = some k) (hkn : k < n)
    (hkm : par M 0 k = some m)
    (hj : j ∈ children M k) (hjb : col M j = bump M k)
    (hc : c ∈ children M j) (hcn : c < n) (hA : Up1 M a m)
    (hc1 : entry M 1 c = entry M 1 a) (hc2 : entry M 2 c = 0) (ha2 : entry M 2 a = 0) :
    par M 1 c = par M 1 a ∧ upg M c = upg M a := by
  obtain ⟨m', hm', hkm'⟩ := upg_target_par0 S.r0p hu
  rw [hkm] at hkm'; cases hkm'
  obtain ⟨m'', hm'', hk1, hcol, hcase⟩ := upg_spec hu
  rw [hm'] at hm''; cases hm''
  have hmk := par1_entry_lt hk1
  have hjk1 : entry M 1 j = entry M 1 k := e1_of_col hjb
  have hjk := (mem_children_iff.mp hj).2
  have hcj := (mem_children_iff.mp hc).2
  have hkj := (mem_children hj).1
  have hjc := (mem_children hc).1
  have hmkN := par_lt M 0 k m hkm
  have ham := up1_e1_le hA
  have hAam := up1_anc0 hA
  have hale := hAam.le
  obtain ⟨Sp, hSp, hSpp⟩ := up1_split hA
  have hancc : ancL M c = j :: k :: (Sp ++ a :: ancL M a) := by
    rw [ancL_eq hcj, ancL_eq hjk, ancL_eq hkm, hSp]
  have hpar : par M 1 c = par M 1 a := by
    rw [par1_find M c, hancc, hc1, par1_find M a]
    simp only [List.find?_cons]
    have hj' : ¬ entry M 1 j < entry M 1 a := by omega
    have hk' : ¬ entry M 1 k < entry M 1 a := by omega
    simp only [decide_eq_false hj', decide_eq_false hk']
    rw [find_skip (fun s hs => decide_eq_false (by have := hSpp s hs; omega))]
    simp
  refine ⟨hpar, ?_⟩
  -- geometry for the upgrade search
  have hA : Anc0 M k n := by rcases hcase with h | h; omega; exact h.1
  have hAak : Anc0 M a k := hAam.trans (Anc0.step hkm (Anc0.refl m))
  have hanext : par M 0 (a + 1) = some a := child_succ hAak (by omega)
  have had : entry M 0 a < entry M 0 (a + 1) := by
    have := S.r0p (a + 1) a hanext
    omega
  have hAcnext : Anc0 M k (c + 1) := anc_between hA (c + 1) (by omega) (by omega)
  have hkd : entry M 0 k < entry M 0 (c + 1) := anc0_e0_lt hAcnext (by omega)
  have hmk0 : entry M 0 m < entry M 0 k := by have := S.r0p k m hkm; omega
  have hamd : entry M 0 a ≤ entry M 0 m := by
    by_cases ham' : a = m
    · rw [ham']
    · exact (anc0_e0_lt hAam ham').le
  have hcd : entry M 0 a < entry M 0 (c + 1) := by omega
  by_cases h10 : entry M 1 a = 0
  · simp [upg, hc1, h10]
  have hcN : c + 1 < M.length := by omega
  have haN : a + 1 < M.length := by omega
  unfold upg
  rw [hc1, hc2, ha2, if_neg (by omega), if_neg (by omega), hpar]
  cases hp : par M 1 a with
  | none => rfl
  | some p =>
    have hpa : entry M 0 p < entry M 0 a :=
      anc0_e0_lt (anc0_of_par M 1 p a hp) (by have := par_lt M 1 a p hp; omega)
    have hnotc : ¬ (par M 1 (c + 1) = some p ∧
        col M (c + 1) = (entry M 0 p + 1, entry M 1 a, entry M 2 p + 1)) := by
      rintro ⟨_, h⟩
      have := e0_of_col h
      omega
    have hnota : ¬ (par M 1 (a + 1) = some p ∧
        col M (a + 1) = (entry M 0 p + 1, entry M 1 a, entry M 2 p + 1)) := by
      rintro ⟨_, h⟩
      have := e0_of_col h
      omega
    simp only
    rw [if_neg hnotc, if_neg hnota, upgClimb_find, upgClimb_find, hancc]
    have hfj : decide (par M 1 j = some p ∧
        col M j = (entry M 0 p + 1, entry M 1 a, entry M 2 p + 1) ∧
        entry M 0 j < entry M 0 (c + 1)) = false := by
      apply decide_eq_false
      rintro ⟨_, h, _⟩
      have := e1_of_col h
      omega
    have hfk : decide (par M 1 k = some p ∧
        col M k = (entry M 0 p + 1, entry M 1 a, entry M 2 p + 1) ∧
        entry M 0 k < entry M 0 (c + 1)) = false := by
      apply decide_eq_false
      rintro ⟨_, h, _⟩
      have := e1_of_col h
      omega
    simp only [List.find?_cons, hfj, hfk]
    rw [find_skip (fun s hs => decide_eq_false (by
      rintro ⟨_, h, _⟩
      have := e1_of_col h
      have := hSpp s hs
      omega))]
    have hfa : decide (par M 1 a = some p ∧
        col M a = (entry M 0 p + 1, entry M 1 a, entry M 2 p + 1) ∧
        entry M 0 a < entry M 0 (c + 1)) = false := by
      apply decide_eq_false
      rintro ⟨_, h, _⟩
      have := e2_of_col h
      omega
    simp only [List.find?_cons, hfa]
    apply find_congr_mem
    intro q hq
    have hqa : entry M 0 q < entry M 0 a :=
      anc0_e0_lt (anc0_of_mem_ancL hq) (by have := mem_ancL_lt hq; omega)
    have h1 : entry M 0 q < entry M 0 (c + 1) := by omega
    have h2 : entry M 0 q < entry M 0 (a + 1) := by omega
    simp only [h1, h2, and_true]

theorem up1_par1 {M : Mat} {a x : Nat} (h : Up1 M a x) (hne : a ≠ x) :
    ∃ w, par M 1 w = some a := by
  induction h with
  | refl => exact absurd rfl hne
  | @step x y hp hA ih =>
    by_cases hay : a = y
    · subst hay; exact ⟨x, hp⟩
    · exact ih hay

/-- Row 2 vanishes along the row-1 chain from `m` (row 2 of `m` is `0`). -/
theorem up1_e2 {M : Mat} (S : SInv M) {a x : Nat} (h : Up1 M a x) (hx2 : entry M 2 x = 0) :
    entry M 2 a = 0 := by
  by_cases hax : a = x
  · rw [hax]; exact hx2
  · obtain ⟨w, hw⟩ := up1_par1 h hax
    have := par1_e2_ne_one S.z1c hw
    have := S.z2 a
    omega

/-- Value residual along the chain: every upgrade increment of a chain column
strictly below `a` is supported in `v(a)`. -/
def StepSupport (M : Mat) (ρ : Valn) (a m : Nat) : Prop :=
  ∀ y, Up1 M a y → Up1 M y m → y ≠ a →
    ∀ t, upg M y = some t → Support (last (ρ.v t)) (ρ.v a)

theorem up1_trans {M : Mat} {a y x : Nat} (h1 : Up1 M a y) (h2 : Up1 M y x) : Up1 M a x := by
  revert h1
  induction h2 with
  | refl => exact id
  | step hp _ ih => intro h1; exact Up1.step hp (ih h1)

/-- Support of `v(x)` in `v(a)` along the row-1 chain from the increments. -/
theorem support_up1 {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {a x : Nat} (hA : Up1 M a x) (hxN : x < M.length) (hx2 : entry M 2 x = 0)
    (hst : ∀ y, Up1 M a y → Up1 M y x → y ≠ a →
      ∀ t, upg M y = some t → Support (last (ρ.v t)) (ρ.v a)) :
    Support (ρ.v x) (ρ.v a) := by
  induction hA with
  | refl => intro q hq; exact Or.inr hq
  | @step x y hp hA ih =>
    have hyx := par_lt M 1 x y hp
    have hy2 : entry M 2 y = 0 := by
      have := par1_e2_ne_one S.z1c hp
      have := S.z2 y
      omega
    have hay := up1_le hA
    have hxa : x ≠ a := by omega
    have h1 : entry M 1 x ≠ 0 := by have := par1_entry_lt hp; omega
    have ihy := ih (by omega) hy2 (fun w h1 h2 hne t ht => hst w h1 (Up1.step hp h2) hne t ht)
    refine support_value_of_inputs hC hG hxN hx2 (by rw [hp]; exact ihy) ?_
    intro t ht
    exact hst x (Up1.step hp hA) (Up1.refl x) hxa t ht

/-- Weaker value residual: component domination (instead of literal support)
of every upgrade increment strictly below `a` by `v(a)`. -/
def StepDom (M : Mat) (ρ : Valn) (a m : Nat) : Prop :=
  ∀ y, Up1 M a y → Up1 M y m → y ≠ a →
    ∀ t, upg M y = some t → ∀ u, Dom (comps u (last (ρ.v t))) (comps u (ρ.v a) ++ [z])

theorem stepDom_of_stepSupport {M : Mat} {ρ : Valn} {a m : Nat} (h : StepSupport M ρ a m) :
    StepDom M ρ a m :=
  fun y h1 h2 hne t ht => dom_of_support (h y h1 h2 hne t ht)

/-- Component domination of `v(x)` by `v(a)` along the row-1 chain. -/
theorem dom_up1 {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {a x : Nat} (hA : Up1 M a x) (hxN : x < M.length) (hx2 : entry M 2 x = 0)
    (hst : ∀ y, Up1 M a y → Up1 M y x → y ≠ a →
      ∀ t, upg M y = some t → ∀ u, Dom (comps u (last (ρ.v t))) (comps u (ρ.v a) ++ [z])) :
    ∀ u, Dom (comps u (ρ.v x)) (comps u (ρ.v a) ++ [z]) := by
  induction hA with
  | refl => intro u g hg; exact ⟨g, List.mem_append_left _ hg, le_refl _⟩
  | @step x y hp hA ih =>
    have hyx := par_lt M 1 x y hp
    have hy2 : entry M 2 y = 0 := by
      have := par1_e2_ne_one S.z1c hp
      have := S.z2 y
      omega
    have hay := up1_le hA
    have hxa : x ≠ a := by omega
    have h1 : entry M 1 x ≠ 0 := by have := par1_entry_lt hp; omega
    have ihy := ih (by omega) hy2 (fun w h1 h2 hne t ht => hst w h1 (Up1.step hp h2) hne t ht)
    have hpOT := vOpt_ot hG hxN
    rw [hp] at hpOT
    simp only [vOpt] at hpOT
    rw [(hC x hxN).2]
    unfold vRhs
    rw [if_neg h1, if_pos hx2, hp]
    simp only [vOpt]
    cases hu : upg M x with
    | none =>
      rw [sf_ot (isOT_add hpOT isOT_one)]
      intro u g hg
      rcases comps_add_sub u _ _ g hg with hg | hg
      · exact ihy u g hg
      · exact ⟨z, List.mem_append_right _ (by simp), by simp [comps_one_eq hg]⟩
    | some t =>
      rw [sf_ot (isOT_add hpOT (isOT_last (hG.ot_v t (upg_lt hxN hu))))]
      intro u g hg
      rcases comps_add_sub u _ _ g hg with hg | hg
      · exact ihy u g hg
      · exact hst x (Up1.step hp hA) (Up1.refl x) hxa t hu u g hg

/-- Deep return witness (residual shape).  Survival of the two chosen summands
is explicit; `a` is `m` or a row-1 ancestor of `m` at the row-1 level of `c`;
the remaining value part is `StepDom` (implied by `StepSupport`). -/
def DeepWitness (M : Mat) (ρ : Valn) (n k m : Nat) : Prop :=
  ∃ j c a, j ∈ children M k ∧ col M j = bump M k ∧
    bumpTerm M ρ k j ∈ summands (sumN (one :: (children M k).map (bumpTerm M ρ k))) ∧
    c ∈ children M j ∧ ρ.o c ∈ summands (sumN ((children M j).map ρ.o)) ∧
    c < n ∧ Up1 M a m ∧ entry M 1 c = entry M 1 a ∧ entry M 2 c = 0 ∧
    StepDom M ρ a m

theorem dom_of_deep {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {n k m : Nat}
    (hn : n < M.length) (hu : upg M n = some k) (hkn : k < n)
    (hkm : par M 0 k = some m) (hw : DeepWitness M ρ n k m) :
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z]) := by
  obtain ⟨j, c, a, hj, hjb, hBP, hc, hoG, hcn, hA, h1, hc2, hst⟩ := hw
  have hcN := (mem_children hc).2
  have hmN : m < M.length := by
    have := par_lt M 0 k m hkm
    have := upg_lt hn hu
    omega
  have hm2 : entry M 2 m = 0 := by
    obtain ⟨m', hm', hk0⟩ := upg_target_par0 S.r0p hu
    rw [hkm] at hk0; cases hk0
    obtain ⟨m'', hm'', _, hcol, _⟩ := upg_spec hu
    rw [hm'] at hm''; cases hm''
    have := e2_of_col hcol; have := S.z2 k; omega
  have ha2 := up1_e2 S hA hm2
  have haN : a < M.length := by have := up1_le hA; omega
  obtain ⟨hp, hup⟩ := deep_return S hn hu hkn hkm hj hjb hc hcn hA h1 hc2 ha2
  have hv := value_eq_of_same_rhs hC hcN haN h1 hc2 ha2 hp hup
  have hs := dom_up1 S hC hG hA hmN hm2 (fun y h1 h2 hne t ht => hst y h1 h2 hne t ht)
  exact dom_of_grandchild_dom S hC hG hn hu hkm hj hjb hBP hc hoG (by rw [hv]; exact hs)

/-- Residual: at a dangerous absorption, a zero head index, the last return
copy, or a deep return witness exists. -/
def HUACDeepShape : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ →
    ∀ n k m, upg N n = some k → k < n → par N 0 k = some m →
      HUACShapes.Danger (vOpt σ (par N 1 n)) (bumpW N σ k) →
      lev (bumpW N σ k) = z ∨ HUACCopy.ReturnWitness N n k m ∨ DeepWitness N σ n k m

/-- Bridge: the deep shape residual gives HUAC. -/
theorem hUAC_of_deep (hS : HUACDeepShape) : HUAC := by
  intro N σ rk hN hNe hC hR hG n k hu hkn
  have S := sInv_std hN hNe
  have hn : n < N.length := by have := upg_succ_lt hu; omega
  obtain ⟨m, _, hkm⟩ := upg_target_par0 S.r0p hu
  by_cases hd : HUACShapes.Danger (vOpt σ (par N 1 n)) (bumpW N σ k)
  · rcases hS N σ rk hN hNe hC hR hG n k m hu hkn hkm hd with hzero | hw | hw
    · exact HUACZero.dom_of_zero S hC hG hn hu hzero
    · exact HUACCopy.dom_of_return S hC hG hn hu hkn hkm hw
    · exact dom_of_deep S hC hG hn hu hkn hkm hw
  · exact HUACShapes.dom_of_no_danger S hC hG hn hu hd

end Ytosk.WfHUACDeep
