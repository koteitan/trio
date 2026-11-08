/-
**The flow with a general source (2026-11-08).**

`flow_sib` (V3SVFlowM) with
- a source `s` that is the root of the subtree ending at `e` (not only its last column): the walk stops at `s`;
- the row-0 parent `p` of `x` may be `r` (sv) or the source `s` (C1, `s = q`);
- `EndAtX`: the end `e` may be followed by `x` itself (in C1, `x` is a descendant of the children of `r`).
The children of the strict ancestors of the source (above `r`) are below `x` (`FSrc2`, last field).
-/
import Ytosk.V3FlowG

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- `e` is the last column of the subtree of `w` below `x`. -/
def EndAtX (M : Mat) (x w e : Nat) : Prop :=
  w ≤ e ∧ (∀ t, w ≤ t → t ≤ e → Anc0 M w t) ∧ (e + 1 = x ∨ ¬ Anc0 M w (e + 1))

theorem endAtX_last {M : Mat} {x w l e : Nat} (hl : l ∈ children M w) (hlx : l < x)
    (hmax : ∀ c ∈ children M w, c < x → c ≤ l) (he : EndAtX M x w e) (hex : e < x) (heM : e < M.length) :
    EndAtX M x l e := by
  obtain ⟨hwe, hall, hnot⟩ := he
  have hlA := anc0_of_child hl
  have hwl := (mem_children hl).1
  have hle : l ≤ e := by
    by_contra h
    rcases hnot with h1 | h1
    · omega
    · exact h1 (anc_between hlA (e + 1) (by omega) (by omega))
  refine ⟨hle, fun t hlt hte => ?_, ?_⟩
  · have hwt := hall t (by omega) hte
    obtain ⟨c, hc, hct⟩ := child_toward hwt (by omega) (by omega)
    have hcl := hmax c hc (by have := hct.le; omega)
    rcases Nat.eq_or_lt_of_le hcl with rfl | hlt'
    · exact hct
    · exact absurd (anc_between hct l (by omega) (by omega)) (not_anc_sib hc hl (by omega))
  · rcases hnot with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (fun hA => h1 (Anc0.trans hlA hA))

theorem endAtX_sib {M : Mat} {x w s j : Nat} (hs : s ∈ children M w) (hj : j ∈ children M w) (hsj : s < j)
    (hnb : ∀ c ∈ children M w, ¬ (s < c ∧ c < j)) : EndAtX M x s (j - 1) := by
  obtain ⟨h1, h2, h3⟩ := endAt_sib hs hj hsj hnb
  exact ⟨h1, h2, Or.inr h3⟩

/-- The last child of a strict ancestor of the source is an ancestor of the source. -/
theorem last_toward {M : Mat} {k l s e : Nat} (hl : l ∈ children M k) (hle : Anc0 M l e) (hks : Anc0 M k s)
    (hks' : k ≠ s) (hse : Anc0 M s e) : Anc0 M l s := by
  rcases anc0_total hle hse with h | h
  · exact h
  · by_cases hsl : s = l
    · rw [hsl]; exact Anc0.refl l
    · exfalso
      have hsk : Anc0 M s k := anc0_of_par_ne h hsl (mem_children_iff.mp hl).2
      exact hks' (anc0_antisymm hks hsk)

/-- The source of a segment of the flow: `s`, the root of the subtree ending at `e`. -/
def FSrc2 (M : Mat) (x r p : Nat) (SV : Nat → Prop) (s e : Nat) : Prop :=
  s < x ∧ e < x ∧ HighD M r s ∧ ChgX M x false s ∧ SV s ∧ EndAtX M x s e ∧ CL (M.take x) s = [] ∧
  (∀ w, par M 0 s = some w → col M s ≠ bump M w ∧ (s = p → ¬ Counted (M.take x) w s)) ∧
  (∀ k, Anc0 M k s → k ≠ s → r < k → ∀ c ∈ children M k, c < x)

section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk)
  {x r p : Nat} (hx : x + 1 = M.length) (hxp : par M 0 x = some p) (he2r : entry M 2 r = 0)
  (hux : ∀ c, upg M (x - 1) = some c → c = x)
include I hx hxp he2r hux

/-- **The walk with a general source.** -/
theorem flow_sib2 (SV SA : Nat → Prop)
    (hRU : ∀ i j, upg M i = some j → j < x → HighD M r j → SV j → SV i)
    (hRC : ∀ w j, w < x → j ∈ children M w → j < x → Counted (M.take x) w j →
      (∀ j' ∈ children M w, j < j' → j' < x → ¬ Counted (M.take x) w j') → HighD M r j →
      (FPV M x SV j ∨ FPA M x SA j) → SA w)
    (hRB : ∀ w j k, w < x → HighD M r w → w ≠ p → j ∈ children M w → col M j = bump M w →
      (∀ j' ∈ children M w, j < j' → j' < x → col M j' ≠ bump M w) → j ≠ p → k ∈ children M j →
      (∀ k' ∈ children M j, k' ≤ k) → HighD M r k → (FPV M x SV k ∨ FPA M x SA k) → SV w)
    (hnr : ∀ j ∈ children M r, j < x → HighD M r j → upg M r ≠ some j) :
    ∀ n w, x - w = n → (w = r ∨ HighD M r w) → w < x →
      ∀ j, j ∈ children M w → j < x →
      (∀ j' ∈ children M w, j < j' → j' < x → col M j' ≠ bump M w ∧ ¬ Counted (M.take x) w j') →
      ∀ s e, EndAtX M x j e → Anc0 M j s → FSrc2 M x r p SV s e →
        FPA M x SA w ∨ (w ≠ r ∧ FPV M x SV w) := by
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
  have hxc : x ∈ children M p := mem_children_iff.mpr ⟨by omega, hxp⟩
  -- the result for proper descendants of `w` that are ancestors of the source
  have G : ∀ k, w < k → k < x → HighD M r k → ∀ s e, EndAtX M x k e → Anc0 M k s →
      FSrc2 M x r p SV s e → FPV M x SV k ∨ FPA M x SA k := by
    intro k hwk hkx hk s e hke hks hse
    by_cases hks' : k = s
    · subst hks'
      exact Or.inl ⟨hse.2.2.2.1, hse.2.2.2.2.1, hse.2.2.2.2.2.2.1⟩
    · have hkch := hse.2.2.2.2.2.2.2.2 k hks hks' (by omega)
      have hsM : s < M.length := by have := hse.1; omega
      obtain ⟨c0, hc0, _⟩ := child_toward hks hks' hsM
      obtain ⟨l, hl, hlmax⟩ := last_child hc0
      have hlx : l < x := hkch l hl
      have hle := endAtX_last hl hlx (fun c hc _ => hlmax c hc) hke hse.2.1 (by have := hse.2.1; omega)
      have hse' : Anc0 M s e := (hse.2.2.2.2.2.1).2.1 e (hse.2.2.2.2.2.1).1 le_rfl
      have hls := last_toward hl (hle.2.1 e hle.1 le_rfl) hks hks' hse'
      rcases ihn (x - k) (by omega) k rfl (Or.inr hk) hkx l hl hlx
          (fun j' hj' hlj' _ => absurd (hlmax j' hj') (by omega)) s e hle hls hse with h | ⟨_, h⟩
      · exact Or.inr h
      · exact Or.inl h
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ihj =>
  intro hj hjx hlater s e hje hjs hse
  obtain ⟨hsx, hex, hsH, hsC, hsSV, hsE, hsCL, hsNB, hsch⟩ := hse
  have hse0 : FSrc2 M x r p SV s e := ⟨hsx, hex, hsH, hsC, hsSV, hsE, hsCL, hsNB, hsch⟩
  have hwj := (mem_children hj).1
  have hjr : j ≠ r := by omega
  have hjH : HighD M r j := highD_of_anc hsH (Anc0.trans hAw (anc0_of_child hj)) hjs hjr
  have hsAe : Anc0 M s e := hsE.2.1 e hsE.1 le_rfl
  have hsM : s < M.length := by omega
  -- a strict ancestor of the source above `r` has its children below `x`, so it is not `p`
  have hnp : ∀ k, Anc0 M k s → k ≠ s → r < k → k ≠ p := by
    intro k hks hks' hrk hkp
    have := hsch k hks hks' hrk x (by rw [hkp]; exact hxc)
    omega
  by_cases hbj : col M j = bump M w
  · ---- `j` is a bump child of `w`
    have hwr : w ≠ r := by
      rintro rfl; have := I.be _ j hj hbj; omega
    have hwH : HighD M r w := hw.resolve_left hwr
    have hjs' : j ≠ s := by
      rintro rfl; exact (hsNB w (mem_children_iff.mp hj).2).1 hbj
    have hjch := hsch j hjs hjs' (by omega)
    obtain ⟨c0, hc0, _⟩ := child_toward hjs hjs' hsM
    obtain ⟨k, hk, hkmax⟩ := last_child hc0
    have hkx : k < x := hjch k hk
    have hke := endAtX_last hk hkx (fun c hc _ => hkmax c hc) hje hex (by omega)
    have hks := last_toward hk (hke.2.1 e hke.1 le_rfl) hjs hjs' hsAe
    have hjk := (mem_children hk).1
    have hkH : HighD M r k :=
      highD_of_anc hsH (Anc0.trans (Anc0.trans hAw (anc0_of_child hj)) (anc0_of_child hk)) hks (by omega)
    have hGk := G k (by omega) hkx hkH s e hke hks hse0
    have he1w : entry M 1 w ≠ 0 := by
      have := hwH.2.2 w hwH.1 (Anc0.refl w) hwr; omega
    have he2w : entry M 2 w ≠ 0 := by have := I.be w j hj hbj; omega
    have hchg : ChgX M x false w := ChgX.vbump he1w he2w hj hbj hk (chgT_of hGk)
    have hwp : w ≠ p := hnp w (Anc0.trans (anc0_of_child hj) hjs) (by have := hjs.le; omega) (by omega)
    have hjp : j ≠ p := hnp j hjs hjs' (by omega)
    have hSV := hRB w j k hwx hwH hwp hj hbj (fun j' hj' hjj' hj'x => (hlater j' hj' hjj' hj'x).1)
      hjp hk hkmax hkH hGk
    have hTop := (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hchg).1 rfl hwx
    exact Or.inr ⟨hwr, hchg, hSV, cl_nil_of hTop.2.1⟩
  by_cases hcj : Counted (M.take x) w j
  · ---- `j` is counted
    have hjp : j ≠ p := by
      intro hjp
      by_cases hjs' : j = s
      · subst hjs'
        exact (hsNB w (mem_children_iff.mp hj).2).2 hjp hcj
      · exact hnp j hjs hjs' (by omega) hjp
    have hGj := G j hwj hjx hjH s e hje hjs hse0
    have hSA := hRC w j hwx hj hjx hcj (fun j' hj' hjj' hj'x => (hlater j' hj' hjj' hj'x).2) hjH hGj
    have hcM : Counted M w j := (cnt_eqNG hx hxp hux hwx hjx hjp).mp hcj
    exact Or.inl ⟨ChgX.ochild hj hcM.1 hcM.2 (chgT_of hGj), hSA⟩
  ---- `j` is upgraded
  have hiu : ∃ i, i + 1 < x ∧ upg M i = some j := by
    have h : isUpg (M.take x) j = true := by
      by_contra hn
      apply hcj
      exact ⟨by rw [col_take M hjx, bump_take M hwx]; exact hbj, fun h' => hn h'.1⟩
    exact (isUpg_take M (by omega) j).mp h
  obtain ⟨i, hix, hui⟩ := hiu
  have he2j : 1 ≤ entry M 2 j := upg_target_e2 hui
  -- `v(j)` changes and grows
  have hjV : ChgX M x false j ∧ SV j := by
    by_cases hjs' : j = s
    · subst hjs'; exact ⟨hsC, hsSV⟩
    have hjp : j ≠ p := hnp j hjs hjs' (by omega)
    have htop : topped M j = true := (u_nodeG hx hxp hjx hjp hbj hcj hwx).2
    have hjch := hsch j hjs hjs' (by omega)
    obtain ⟨c1, hc1, _⟩ := child_toward hjs hjs' hsM
    have hchb : ∃ b, b ∈ children M j ∧ (∀ c ∈ children M j, c ≤ b) ∧ col M b = bump M j := by
      unfold topped at htop
      cases hl : (children M j).getLast? with
      | none =>
        exfalso
        have hnil : children M j = [] := List.getLast?_eq_none_iff.mp hl
        rw [hnil] at hc1; simp at hc1
      | some b =>
        rw [hl] at htop
        have hbm : b ∈ children M j := List.mem_of_getLast? hl
        refine ⟨b, hbm, fun c hc => ?_, by simpa using htop⟩
        rcases List.getLast?_eq_some_iff.mp hl with ⟨l', hl'⟩
        have hs := children_sorted M j
        rw [hl'] at hs hc
        rcases List.mem_append.mp hc with hc' | hc'
        · exact le_of_lt ((List.pairwise_append.mp hs).2.2 c hc' b (by simp))
        · simp at hc'; omega
    obtain ⟨b, hb, hbmax, hbb⟩ := hchb
    have hbx : b < x := hjch b hb
    have hbe := endAtX_last hb hbx (fun c hc _ => hbmax c hc) hje hex (by omega)
    have hbs := last_toward hb (hbe.2.1 e hbe.1 le_rfl) hjs hjs' hsAe
    have hbs' : b ≠ s := by
      rintro rfl; exact (hsNB j (mem_children_iff.mp hb).2).1 hbb
    have hjb := (mem_children hb).1
    have hbch := hsch b hbs hbs' (by omega)
    obtain ⟨c0, hc0, _⟩ := child_toward hbs hbs' hsM
    obtain ⟨k, hk, hkmax⟩ := last_child hc0
    have hkx : k < x := hbch k hk
    have hke := endAtX_last hk hkx (fun c hc _ => hkmax c hc) hbe hex (by omega)
    have hks := last_toward hk (hke.2.1 e hke.1 le_rfl) hbs hbs' hsAe
    have hbk := (mem_children hk).1
    have hkH : HighD M r k :=
      highD_of_anc hsH (Anc0.trans (Anc0.trans (Anc0.trans hAw (anc0_of_child hj)) (anc0_of_child hb))
        (anc0_of_child hk)) hks (by omega)
    have hGk := G k (by omega) hkx hkH s e hke hks hse0
    have he1j : entry M 1 j ≠ 0 := by
      have := hjH.2.2 j hjH.1 (Anc0.refl j) hjr; omega
    have he2j' : entry M 2 j ≠ 0 := by have := I.be j b hb hbb; omega
    have hbp : b ≠ p := hnp b hbs hbs' (by omega)
    exact ⟨ChgX.vbump he1j he2j' hb hbb hk (chgT_of hGk),
      hRB j b k hjx hjH hjp hb hbb (fun j' hj' hbj' _ => absurd (hbmax j' hj') (by omega)) hbp hk hkmax hkH hGk⟩
  obtain ⟨hchgj, hSVj⟩ := hjV
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
      rintro rfl; exact hnr j hj hjx hjH hui
    refine Or.inr ⟨hwr, hchgi, hSVi, cl_nil_of (fun c hc hcc => ?_)⟩
    rw [children_take] at hc
    obtain ⟨hcm, hcx⟩ := List.mem_filter.mp hc
    have hcx' : c < x := by simpa using hcx
    have hic := (mem_children hcm).1
    rcases Nat.eq_or_lt_of_le (show j ≤ c by omega) with rfl | hjc
    · exact hcj hcc
    · exact (hlater c hcm hjc hcx').2 hcc
  ---- the previous sibling `t`; its subtree ends at the upgrader `j − 1`
  have hwj1 : w + 1 < j := by omega
  obtain ⟨t, ht, htj, hnb⟩ := prev_child hj hwj1
  have hes := endAtX_sib (x := x) ht hj htj hnb
  have hes0 := endAt_sib ht hj htj hnb
  have hi1 : i = j - 1 := by omega
  have htx : t < x := by omega
  have hwt := (mem_children ht).1
  have hAti : Anc0 M t (j - 1) := hes.2.1 (j - 1) hes.1 le_rfl
  have hsub : ∀ c, Anc0 M t c → c < j := by
    intro c hc
    by_contra h
    exact hes0.2.2 (by rw [show j - 1 + 1 = j by omega]; exact anc_between hc j (by omega) (by omega))
  have hiH : HighD M r (j - 1) := by
    refine ⟨Anc0.trans (Anc0.trans hAw (anc0_of_child ht)) hAti, by omega, ?_⟩
    intro q hrq hqi hqr
    have hwi : Anc0 M w (j - 1) := Anc0.trans (anc0_of_child ht) hAti
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
  have hnoc : ∀ c, c ∈ children M (j - 1) → False := end_no_child hes0 htj (by omega)
  have hSrc : FSrc2 M x r p SV (j - 1) (j - 1) := by
    refine ⟨by omega, by omega, hiH, hi1 ▸ hchgi, hi1 ▸ hSVi,
      ⟨le_rfl, fun t' h1 h2 => by rw [show t' = j - 1 by omega]; exact Anc0.refl _,
        Or.inr (fun hA => hes0.2.2 (Anc0.trans hAti hA))⟩,
      cl_nil_of (fun c hc _ => by rw [children_take] at hc; exact hnoc c (List.mem_filter.mp hc).1),
      fun w' _ => ⟨fun hb => ?_, fun hjp => ?_⟩, ?_⟩
    · have : entry M 2 (j - 1) = (col M (j - 1)).2.2 := rfl
      rw [hb] at this; simp [bump] at this; rw [← hi1] at this; omega
    · exact absurd (by rw [hjp]; exact hxc) (hnoc x)
    · intro k hk hk' hrk c hc
      rcases anc0_total hk hAti with hkt | htk
      · by_cases hkt' : k = t
        · subst hkt'
          exact lt_trans (hsub c (anc0_of_child hc)) hjx
        · have hkw : Anc0 M k w := anc0_of_par_ne hkt hkt' (mem_children_iff.mp ht).2
          exact hsch k (Anc0.trans hkw (Anc0.trans (anc0_of_child hj) hjs))
            (by have := hkw.le; have := hjs.le; omega) hrk c hc
      · exact lt_trans (hsub c (Anc0.trans htk (anc0_of_child hc))) hjx
  refine ihj t htj ht htx (fun j' hj' htj' hj'x => ?_) (j - 1) (j - 1) hes hAti hSrc
  rcases Nat.eq_or_lt_of_le (show j ≤ j' by by_contra h; exact hnb j' hj' ⟨htj', by omega⟩) with rfl | hjj'
  · exact ⟨hbj, hcj⟩
  · exact hlater j' hj' hjj' hj'x

/-- **The flow reaches `r`** from a source `s` whose subtree ends at `x − 1`. -/
theorem flow_top2 (SV SA : Nat → Prop) {s : Nat} (hsrc : FSrc2 M x r p SV s (x - 1))
    (hrs : r ≠ s)
    (hRU : ∀ i j, upg M i = some j → j < x → HighD M r j → SV j → SV i)
    (hRC : ∀ w j, w < x → j ∈ children M w → j < x → Counted (M.take x) w j →
      (∀ j' ∈ children M w, j < j' → j' < x → ¬ Counted (M.take x) w j') → HighD M r j →
      (FPV M x SV j ∨ FPA M x SA j) → SA w)
    (hRB : ∀ w j k, w < x → HighD M r w → w ≠ p → j ∈ children M w → col M j = bump M w →
      (∀ j' ∈ children M w, j < j' → j' < x → col M j' ≠ bump M w) → j ≠ p → k ∈ children M j →
      (∀ k' ∈ children M j, k' ≤ k) → HighD M r k → (FPV M x SV k ∨ FPA M x SA k) → SV w)
    (hnr : ∀ j ∈ children M r, j < x → HighD M r j → upg M r ≠ some j) : SA r := by
  have hsH := hsrc.2.2.1
  have hrs' := hsH.1
  have hsx := hsrc.1
  have hAse : Anc0 M s (x - 1) := (hsrc.2.2.2.2.2.1).2.1 (x - 1) (hsrc.2.2.2.2.2.1).1 le_rfl
  have hAr : Anc0 M r (x - 1) := Anc0.trans hrs' hAse
  have hrx1 : r < x - 1 := by have := hrs'.le; have := hAse.le; omega
  obtain ⟨l, hl, hlA⟩ := child_toward hAr (by omega) (by omega)
  have hlx : l < x := by have := hlA.le; omega
  have hEnd : EndAtX M x l (x - 1) := ⟨hlA.le, fun t ht1 ht2 => anc_between hlA t ht1 ht2,
    Or.inl (by omega)⟩
  have hls' : Anc0 M l s := by
    rcases anc0_total hlA hAse with h | h
    · exact h
    · by_cases hsl : s = l
      · rw [hsl]; exact Anc0.refl l
      · exfalso
        have hsr : Anc0 M s r := anc0_of_par_ne h hsl (mem_children_iff.mp hl).2
        exact hrs (anc0_antisymm hrs' hsr)
  rcases flow_sib2 I hx hxp he2r hux SV SA hRU hRC hRB hnr (x - r) r rfl (Or.inl rfl) (by omega) l hl hlx
      (fun j' hj' hlj' hj'x => absurd (anc_between hlA j' (le_of_lt hlj') (by omega))
        (not_anc_sib hl hj' (by omega))) s (x - 1) hEnd hls' hsrc with h | ⟨h, _⟩
  · exact h.2
  · exact absurd rfl h

end

end Ytosk.V3Main.SeedPF
