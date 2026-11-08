/-
**t = 2, sv: the flow of `T2SVStrict` (combinatorial part, 2026-11-08).**

The property "σ increases" is abstract here: `SV w` (the `v` of `w` grows) and `SA w` (the argument of `w` grows).
From the rules
- `hRU` (an upgraded column has the `v` of its target),
- `hRC` (the last counted child carries the increase to the argument of its parent),
- `hRB` (the last child of a bump child carries the increase to the `v` of the parent),
and the base `SV (x − 1)`, the argument of `r` grows (`flow_top`).

The walk: a column `w` looks at its children from the right. A counted child ends the walk (`hRC`), a bump child
ends it (`hRB`, and `w` then has no counted child by `TopC`), and an upgraded topped child `u` passes the walk to
the subtree of the previous sibling, which ends at the upgrader `u − 1` (`no_anc_upg`, `vupg`). `ChgX` and its
structure (`chg_struct`) supply the facts that the walk does not break.
-/
import Ytosk.V3SVFlowS

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The source of a segment of the flow. -/
def FSrc (M : Mat) (x r : Nat) (SV : Nat → Prop) (e : Nat) : Prop :=
  e < x ∧ HighD M r e ∧ ChgX M x false e ∧ SV e ∧ (∀ c, c ∈ children M e → False) ∧ entry M 2 e = 0

/-- The `v` of `w` changes and grows, and `w` has no counted child. -/
def FPV (M : Mat) (x : Nat) (SV : Nat → Prop) (w : Nat) : Prop :=
  ChgX M x false w ∧ SV w ∧ CL (M.take x) w = []

/-- The `o` of `w` changes and the argument of `w` grows. -/
def FPA (M : Mat) (x : Nat) (SA : Nat → Prop) (w : Nat) : Prop :=
  ChgX M x true w ∧ SA w

theorem highD_of_anc {M : Mat} {r e k : Nat} (he : HighD M r e) (hrk : Anc0 M r k) (hke : Anc0 M k e)
    (hkr : k ≠ r) : HighD M r k :=
  ⟨hrk, fun h => hkr h.symm, fun q hrq hqk hqr => he.2.2 q hrq (Anc0.trans hqk hke) hqr⟩

theorem exists_max_mem : ∀ {l : List Nat}, l ≠ [] → ∃ m ∈ l, ∀ c ∈ l, c ≤ m
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨m, hm, hmax⟩ := exists_max_mem (l := b :: l) (by simp)
    by_cases hab : a ≤ m
    · refine ⟨m, by simp [hm], ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hab
      · exact hmax c hc'
    · refine ⟨a, by simp, ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact le_rfl
      · have := hmax c hc'; omega

/-- The last child. -/
theorem last_child {M : Mat} {k c0 : Nat} (hc0 : c0 ∈ children M k) :
    ∃ l ∈ children M k, ∀ c ∈ children M k, c ≤ l :=
  exists_max_mem (List.ne_nil_of_mem hc0)

/-- The previous sibling. -/
theorem prev_child {M : Mat} {w j : Nat} (hj : j ∈ children M w) (hwj : w + 1 < j) :
    ∃ s ∈ children M w, s < j ∧ ∀ c ∈ children M w, ¬ (s < c ∧ c < j) := by
  have h1 : w + 1 ∈ (children M w).filter (fun c => decide (c < j)) :=
    List.mem_filter.mpr ⟨first_child hj, by simp; omega⟩
  obtain ⟨s, hs, hmax⟩ := exists_max_mem (List.ne_nil_of_mem h1)
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  refine ⟨s, hs1, by simpa using hs2, fun c hc hsc => ?_⟩
  have := hmax c (List.mem_filter.mpr ⟨hc, by simp; omega⟩)
  omega

theorem chgT_of {M : Mat} {x : Nat} {SV SA : Nat → Prop} {k : Nat} (h : FPV M x SV k ∨ FPA M x SA k) :
    ChgX M x true k := by
  rcases h with h | h
  · exact ChgX.ov h.1
  · exact h.1

theorem cl_nil_of {N : Mat} {w : Nat} (h : ∀ c ∈ children N w, ¬ Counted N w c) : CL N w = [] := by
  unfold CL; rw [List.filter_eq_nil_iff]; intro c hc; simpa using h c hc

section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk)
  {x r : Nat} (hx : x + 1 = M.length) (hxr : par M 0 x = some r) (he2r : entry M 2 r = 0)
  (hux : upg M (x - 1) = some x)
include I hx hxr he2r hux

omit he2r in
/-- Only `r` has `x` as a child. -/
theorem x_child_eq {w : Nat} (h : x ∈ children M w) : w = r := by
  have := (mem_children_iff.mp h).2; rw [hxr] at this; exact (Option.some.inj this).symm

omit he2r in
theorem child_lt_x {w c : Nat} (hwr : w ≠ r) (hc : c ∈ children M w) : c < x := by
  have hcM := (mem_children hc).2
  by_contra h
  have : c = x := by omega
  subst this
  exact hwr (x_child_eq I hx hxr hux hc)

omit he2r in
/-- Countedness is the same in `M.take x` below `r`. -/
theorem cnt_eqN {w j : Nat} (hw : w < x) (hj : j < x) (hjr : j ≠ r) :
    (Counted (M.take x) w j ↔ Counted M w j) := by
  by_contra h
  rcases cnt_change hx hw hj h with hxc | hu
  · exact hjr (x_child_eq I hx hxr hux hxc)
  · rw [hux] at hu; cases hu; omega

omit he2r in
/-- **An uncounted non-bump child** is an upgrade target and topped. -/
theorem u_node {w j : Nat} (hjx : j < x) (hjr : j ≠ r) (hb : col M j ≠ bump M w)
    (hnc : ¬ Counted (M.take x) w j) (hw : w < x) :
    (∃ i, i + 1 < x ∧ upg M i = some j) ∧ topped M j = true := by
  have h : isUpg (M.take x) j = true ∧ topped (M.take x) j = true := by
    by_contra hn
    apply hnc
    exact ⟨by rw [col_take M hjx, bump_take M hw]; exact hb, hn⟩
  have hxj : x ∉ children M j := fun h' => hjr (x_child_eq I hx hxr hux h')
  exact ⟨(isUpg_take M (by omega) j).mp h.1, by rw [← topped_take_eq hx hjx hxj]; exact h.2⟩

/-- **The walk** from a child `j` of `w` (all later children of `w` below `x` are upgraded and topped). -/
theorem flow_sib (SV SA : Nat → Prop)
    (hRU : ∀ i j, upg M i = some j → j < x → HighD M r j → SV j → SV i)
    (hRC : ∀ w j, w < x → (w = r ∨ HighD M r w) → j ∈ children M w → j < x → Counted (M.take x) w j →
      (∀ j' ∈ children M w, j < j' → j' < x → ¬ Counted (M.take x) w j') → HighD M r j →
      (FPV M x SV j ∨ FPA M x SA j) → SA w)
    (hRB : ∀ w j k, w < x → HighD M r w → j ∈ children M w → col M j = bump M w →
      (∀ j' ∈ children M w, j < j' → j' < x → col M j' ≠ bump M w) → k ∈ children M j →
      (∀ k' ∈ children M j, k' ≤ k) → HighD M r k → (FPV M x SV k ∨ FPA M x SA k) → SV w)
    (hnr : ∀ j ∈ children M r, upg M r ≠ some j) :
    ∀ n w, x - w = n → (w = r ∨ HighD M r w) → w < x →
      ∀ j, j ∈ children M w → j < x →
      (∀ j' ∈ children M w, j < j' → j' < x → col M j' ≠ bump M w ∧ ¬ Counted (M.take x) w j') →
      ∀ e, EndAt M j e → FSrc M x r SV e → FPA M x SA w ∨ (w ≠ r ∧ FPV M x SV w) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro w hwn hw hwx
  have hrw : r ≤ w := by
    rcases hw with rfl | hw
    · exact le_rfl
    · exact hw.1.le
  have hAw : Anc0 M r w := by
    rcases hw with rfl | hw
    · exact Anc0.refl _
    · exact hw.1
  have hMx : x < M.length := by omega
  -- the result for proper descendants of `w`
  have G : ∀ k, w < k → k < x → HighD M r k → ∀ e, EndAt M k e → FSrc M x r SV e →
      FPV M x SV k ∨ FPA M x SA k := by
    intro k hwk hkx hk e hke hse
    by_cases hnil : ∃ c, c ∈ children M k
    · obtain ⟨c0, hc0⟩ := hnil
      obtain ⟨l, hl, hlmax⟩ := last_child hc0
      have hkr : k ≠ r := by omega
      have hlx : l < x := child_lt_x I hx hxr hux hkr hl
      have hle := endAt_last hl hlmax hke (by have := hse.1; omega)
      rcases ihn (x - k) (by omega) k rfl (Or.inr hk) hkx l hl hlx
          (fun j' hj' hlj' _ => absurd (hlmax j' hj') (by omega)) e hle hse with h | ⟨_, h⟩
      · exact Or.inr h
      · exact Or.inl h
    · have hnil' : ∀ c, c ∈ children M k → False := fun c hc => hnil ⟨c, hc⟩
      have hke' := endAt_leaf hke (by have := hse.1; omega) hnil'
      subst hke'
      exact Or.inl ⟨hse.2.2.1, hse.2.2.2.1, cl_nil_of (fun c hc _ => by
        rw [children_take] at hc; exact hnil' c (List.mem_filter.mp hc).1)⟩
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ihj =>
  intro hj hjx hlater e hje hse
  have hwj := (mem_children hj).1
  have hjr : j ≠ r := by omega
  have hseH := hse.2.1
  have hex := hse.1
  have hAje : Anc0 M j e := hje.2.1 e hje.1 le_rfl
  have hjH : HighD M r j := highD_of_anc hseH (Anc0.trans hAw (anc0_of_child hj)) hAje hjr
  by_cases hbj : col M j = bump M w
  · ---- `j` is a bump child of `w`
    have hwr : w ≠ r := by
      rintro rfl; have := I.be _ j hj hbj; omega
    have hwH : HighD M r w := hw.resolve_left hwr
    have he2j : entry M 2 j = 1 := by
      have : entry M 2 j = (col M j).2.2 := rfl; rw [this, hbj]; rfl
    have hch : ∃ c, c ∈ children M j := by
      by_contra hn; push Not at hn
      have := endAt_leaf hje (by omega) (fun c hc => hn c hc)
      subst this; have := hse.2.2.2.2.2; omega
    obtain ⟨c0, hc0⟩ := hch
    obtain ⟨k, hk, hkmax⟩ := last_child hc0
    have hke := endAt_last hk hkmax hje (by omega)
    have hkx : k < x := by have := hke.1; omega
    have hjk := (mem_children hk).1
    have hkH : HighD M r k :=
      highD_of_anc hseH (Anc0.trans (Anc0.trans hAw (anc0_of_child hj)) (anc0_of_child hk))
        (hke.2.1 e hke.1 le_rfl) (by omega)
    have hGk := G k (by omega) hkx hkH e hke hse
    have he1w : entry M 1 w ≠ 0 := by
      have := hwH.2.2 w hwH.1 (Anc0.refl w) hwr; omega
    have he2w : entry M 2 w ≠ 0 := by have := I.be w j hj hbj; omega
    have hchg : ChgX M x false w := ChgX.vbump he1w he2w hj hbj hk (chgT_of hGk)
    have hSV := hRB w j k hwx hwH hj hbj (fun j' hj' hjj' hj'x => (hlater j' hj' hjj' hj'x).1) hk hkmax hkH hGk
    have hTop := (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hchg).1 rfl hwx
    exact Or.inr ⟨hwr, hchg, hSV, cl_nil_of hTop.2.1⟩
  by_cases hcj : Counted (M.take x) w j
  · ---- `j` is counted
    have hGj := G j hwj hjx hjH e hje hse
    have hSA := hRC w j hwx hw hj hjx hcj (fun j' hj' hjj' hj'x => (hlater j' hj' hjj' hj'x).2) hjH hGj
    have hcM : Counted M w j := (cnt_eqN I hx hxr hux hwx hjx hjr).mp hcj
    exact Or.inl ⟨ChgX.ochild hj hcM.1 hcM.2 (chgT_of hGj), hSA⟩
  ---- `j` is upgraded and topped
  obtain ⟨⟨i, hix, hui⟩, htop⟩ := u_node I hx hxr hux hjx hjr hbj hcj hwx
  have he2j : 1 ≤ entry M 2 j := upg_target_e2 hui
  have hchb : ∃ b, b ∈ children M j ∧ (∀ c ∈ children M j, c ≤ b) ∧ col M b = bump M j := by
    unfold topped at htop
    cases hl : (children M j).getLast? with
    | none =>
      exfalso
      have hnil : children M j = [] := List.getLast?_eq_none_iff.mp hl
      have := endAt_leaf hje (by omega) (fun c hc => by rw [hnil] at hc; simp at hc)
      subst this; have := hse.2.2.2.2.2; omega
    | some b =>
      rw [hl] at htop
      have hbm : b ∈ children M j := List.mem_of_getLast? hl
      refine ⟨b, hbm, fun c hc => ?_, by simpa using htop⟩
      obtain ⟨m, hm, hmax⟩ := last_child hbm
      rcases List.getLast?_eq_some_iff.mp hl with ⟨l', hl'⟩
      have hs := children_sorted M j
      rw [hl'] at hs hc
      rcases List.mem_append.mp hc with hc' | hc'
      · exact le_of_lt ((List.pairwise_append.mp hs).2.2 c hc' b (by simp))
      · simp at hc'; omega
  obtain ⟨b, hb, hbmax, hbb⟩ := hchb
  have hbe := endAt_last hb hbmax hje (by omega)
  have he2b : entry M 2 b = 1 := by
    have : entry M 2 b = (col M b).2.2 := rfl; rw [this, hbb]; rfl
  have hchk : ∃ c, c ∈ children M b := by
    by_contra hn; push Not at hn
    have := endAt_leaf hbe (by omega) (fun c hc => hn c hc)
    subst this; have := hse.2.2.2.2.2; omega
  obtain ⟨c0, hc0⟩ := hchk
  obtain ⟨k, hk, hkmax⟩ := last_child hc0
  have hke := endAt_last hk hkmax hbe (by omega)
  have hkx : k < x := by have := hke.1; omega
  have hjb := (mem_children hb).1
  have hbk := (mem_children hk).1
  have hkH : HighD M r k :=
    highD_of_anc hseH (Anc0.trans (Anc0.trans (Anc0.trans hAw (anc0_of_child hj)) (anc0_of_child hb))
      (anc0_of_child hk)) (hke.2.1 e hke.1 le_rfl) (by omega)
  have hGk := G k (by omega) hkx hkH e hke hse
  have he1j : entry M 1 j ≠ 0 := by
    have := hjH.2.2 j hjH.1 (Anc0.refl j) hjr; omega
  have he2j' : entry M 2 j ≠ 0 := by have := I.be j b hb hbb; omega
  have hchgj : ChgX M x false j := ChgX.vbump he1j he2j' hb hbb hk (chgT_of hGk)
  have hSVj := hRB j b k hjx hjH hb hbb (fun j' hj' hbj' _ => absurd (hbmax j' hj') (by omega)) hk hkmax hkH hGk
  have hTopj := (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hchgj).1 rfl hjx
  -- the upgrader is `j − 1`
  obtain ⟨m, hm1, hm2, hcol, hcase⟩ := upg_spec hui
  have hij : j = i + 1 := by
    rcases hcase with h | ⟨hA, hlt⟩
    · exact h
    · exact absurd (no_anc_upg hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hTopj hjx hui hA hlt) id
  obtain ⟨he1i, he2i⟩ := upg_e12 hui
  have he2i0 : entry M 2 i = 0 := by have := I.z2 i; omega
  have hchgi : ChgX M x false i := ChgX.vupg he1i he2i0 hui hchgj
  have hSVi := hRU i j hui hjx hjH hSVj
  by_cases hfirst : j = w + 1
  · ---- `j` is the first child: `w` itself is the upgrader
    have hiw : i = w := by omega
    subst hiw
    have hwr : i ≠ r := by
      rintro rfl; exact hnr j hj hui
    refine Or.inr ⟨hwr, hchgi, hSVi, cl_nil_of (fun c hc hcc => ?_)⟩
    rw [children_take] at hc
    obtain ⟨hcm, hcx⟩ := List.mem_filter.mp hc
    have hcx' : c < x := by simpa using hcx
    have hic := (mem_children hcm).1
    rcases Nat.eq_or_lt_of_le (show j ≤ c by omega) with rfl | hjc
    · exact hcj hcc
    · exact (hlater c hcm hjc hcx').2 hcc
  ---- the previous sibling `s`; its subtree ends at the upgrader `j − 1`
  have hwj1 : w + 1 < j := by omega
  obtain ⟨s, hs, hsj, hnb⟩ := prev_child hj hwj1
  have hes := endAt_sib hs hj hsj hnb
  have hi1 : i = j - 1 := by omega
  have hsx : s < x := by omega
  have hws := (mem_children hs).1
  have hAsi : Anc0 M s (j - 1) := hes.2.1 (j - 1) hes.1 le_rfl
  have hiH : HighD M r (j - 1) := by
    refine ⟨Anc0.trans (Anc0.trans hAw (anc0_of_child hs)) hAsi, by omega, ?_⟩
    intro q hrq hqi hqr
    have hwi : Anc0 M w (j - 1) := Anc0.trans (anc0_of_child hs) hAsi
    rcases anc0_total hqi hwi with hqw | hwq
    · rcases hw with rfl | hwH
      · exact absurd (anc0_antisymm hqw hrq) hqr
      · exact hwH.2.2 q hrq hqw hqr
    · by_cases hqw : q = w
      · subst hqw
        rcases hw with rfl | hwH
        · exact absurd rfl hqr
        · exact hwH.2.2 q hrq (Anc0.refl q) hqr
      have hwq' : w < q := lt_of_le_of_ne hwq.le (Ne.symm hqw)
      have hmj : Anc0 M m j := anc0_of_par M 1 m j hm2
      have hmj' : m ≠ j := by have := par_lt M 1 j m hm2; omega
      have hmw : Anc0 M m w := anc0_of_par_ne hmj hmj' (mem_children_iff.mp hj).2
      have hm1' : par M 1 (j - 1) = some m := by rw [← hi1]; exact hm1
      have hbet := par1_between hm1' q hqi (by have := hmw.le; omega)
      have he1eq : entry M 1 j = entry M 1 i := by
        have : entry M 1 j = (col M j).2.1 := rfl; rw [this, hcol]
      have := hjH.2.2 j hjH.1 (Anc0.refl j) hjr
      rw [hi1] at he1eq
      omega
  have hSrc : FSrc M x r SV (j - 1) := by
    refine ⟨by omega, hiH, hi1 ▸ hchgi, hi1 ▸ hSVi, end_no_child hes hsj (by omega), hi1 ▸ he2i0⟩
  refine ihj s hsj hs hsx (fun j' hj' hsj' hj'x => ?_) (j - 1) hes hSrc
  rcases Nat.eq_or_lt_of_le (show j ≤ j' by by_contra h; exact hnb j' hj' ⟨hsj', by omega⟩) with rfl | hjj'
  · exact ⟨hbj, hcj⟩
  · exact hlater j' hj' hjj' hj'x

/-- **The flow reaches `r`**: the argument of `r` grows. -/
theorem flow_top (SV SA : Nat → Prop) (hbase : SV (x - 1))
    (hp1 : par M 1 (x - 1) = some r) (he2l : entry M 2 (x - 1) = 0)
    (hRU : ∀ i j, upg M i = some j → j < x → HighD M r j → SV j → SV i)
    (hRC : ∀ w j, w < x → (w = r ∨ HighD M r w) → j ∈ children M w → j < x → Counted (M.take x) w j →
      (∀ j' ∈ children M w, j < j' → j' < x → ¬ Counted (M.take x) w j') → HighD M r j →
      (FPV M x SV j ∨ FPA M x SA j) → SA w)
    (hRB : ∀ w j k, w < x → HighD M r w → j ∈ children M w → col M j = bump M w →
      (∀ j' ∈ children M w, j < j' → j' < x → col M j' ≠ bump M w) → k ∈ children M j →
      (∀ k' ∈ children M j, k' ≤ k) → HighD M r k → (FPV M x SV k ∨ FPA M x SA k) → SV w)
    (hnr : ∀ j ∈ children M r, upg M r ≠ some j) : SA r := by
  have hrl : r < x - 1 := par_lt M 1 (x - 1) r hp1
  have hAr : Anc0 M r (x - 1) := anc0_of_par M 1 r (x - 1) hp1
  obtain ⟨l, hl, hlA⟩ := child_toward hAr (by omega) (by omega)
  have hlx : l < x := by have := hlA.le; omega
  have hxc : x ∈ children M r := mem_children_iff.mpr ⟨by omega, hxr⟩
  have hEnd : EndAt M l (x - 1) := ⟨hlA.le, fun t ht1 ht2 => anc_between hlA t ht1 ht2, by
    rw [show x - 1 + 1 = x by omega]; exact not_anc_sib hl hxc (by omega)⟩
  have hH : HighD M r (x - 1) := ⟨hAr, by omega, fun q hrq hqx hqr => by
    have h1 := par1_between hp1 q hqx (lt_of_le_of_ne hrq.le (Ne.symm hqr))
    have h2 := par1_entry_lt hp1
    omega⟩
  have hnc : ∀ c, c ∈ children M (x - 1) → False := fun c hc => by
    have h1 := (mem_children hc).1
    have h2 := (mem_children hc).2
    have hc' : c = x := by omega
    subst hc'
    have := x_child_eq I hx hxr hux hc
    omega
  have hSrc : FSrc M x r SV (x - 1) := ⟨by omega, hH, ChgX.supg (by rw [hux]; simp), hbase, hnc, he2l⟩
  rcases flow_sib I hx hxr he2r hux SV SA hRU hRC hRB hnr (x - r) r rfl (Or.inl rfl) (by omega) l hl hlx
      (fun j' hj' hlj' hj'x => absurd (anc_between hlA j' (le_of_lt hlj') (by omega))
        (not_anc_sib hl hj' (by omega))) (x - 1) hEnd hSrc with h | ⟨h, _⟩
  · exact h.2
  · exact absurd rfl h

end

end Ytosk.V3Main.SeedPF
