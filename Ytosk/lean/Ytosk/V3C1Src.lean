/-
**t = 2, C1: the source of the flow for the C strict field (2026-11-08).**

In the C case (`q ≠ r`, `CL_M(r)` does not end with `q`): `q` is the last child of `r`, uncounted in `M` and in
`M.take x`, and `x` is its bump child (`c_q_facts`, from the proof of `cl_C_any`). With `upg(x − 1) = none` (C1),
`v_T(q) = qnS` (`c_vqP_of_un`), and `σ_{V,qnS}` raises it strictly: `f(V + δ) = qnS + σδ` (`c1_src_sv`). The
change of `v(q)` is `ChgX.snb`. So `q` is a source of the flow (`c1_src`, `FSrc2`) whose subtree ends at `x − 1`.
-/
import Ytosk.V3FlowG2

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The column `q` in the C case.** -/
theorem c_q_facts {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some q)
    (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q]) :
    par M 0 q = some r ∧ ¬ Counted (M.take (r + L)) r q ∧ col M (r + L) = bump M q := by
  have hx : r + L + 1 = M.length := hlen
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hpq : par M 0 q = some r := par0_q_t2 hM hS I hlen hr hq hqr
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hqM : q ∈ children M r := mem_children_iff.mpr ⟨by omega, hpq⟩
  have hxr : r + L ∉ children M r := fun h => by
    have := (mem_children_iff.mp h).2; rw [hq] at this; cases this; exact hqr rfl
  have hmax : ∀ d ∈ children M r, d ≤ q := by
    intro d hd
    by_contra hlt
    have hdl := (mem_children hd).2
    have hdx : d ≠ r + L := fun e => hxr (e ▸ hd)
    have hpd := (mem_children_iff.mp hd).2
    have h1 := ((par0_spec M).mp hpd).2.2 q (by omega) (by omega)
    have h2 := ((par0_spec M).mp hq).2.1
    have h3 := ((par0_spec M).mp hq).2.2 d (by omega) (by omega)
    omega
  have hsplit := split_last_max _ _ (children_sorted M r) hqM hmax
  have hnq : ¬ Counted M r q := by
    intro hc
    apply hncl
    refine ⟨((children M r).filter (fun d => decide (d < q))).filter (fun d => decide (Counted M r d)), ?_⟩
    unfold CL; rw [hsplit, List.filter_append]; simp [hc]
  have he2r : entry M 2 r = 0 := (par2_facts I.z2 (by omega) hr).1
  have hqb : col M q ≠ bump M r := fun h => by have := I.be r q hqM h; omega
  have hUT : isUpg M q = true ∧ topped M q = true := by
    by_contra h; exact hnq ⟨hqb, h⟩
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have hchq := children_split_x hx hxq
  have hxb : col M (r + L) = bump M q := by
    have hTp := hUT.2
    unfold topped at hTp
    rw [hchq] at hTp
    simpa using hTp
  refine ⟨hpq, ?_, hxb⟩
  rintro ⟨hb, hu⟩
  rw [col_take M hqx, bump_take M (by omega)] at hb
  apply hu
  refine ⟨?_, ?_⟩
  · unfold isUpg
    have hU := hUT.1
    unfold isUpg at hU
    rw [List.any_eq_true] at hU ⊢
    obtain ⟨k, hk, hkq⟩ := hU
    have hkq' : upg M k = some q := by simpa using hkq
    have hk1 : k + 1 < r + L := by
      have hkl := List.mem_range.mp hk
      rcases Nat.lt_or_ge (k + 1) (r + L) with h | h
      · exact h
      · exfalso
        rcases Nat.lt_or_ge k (r + L) with h' | h'
        · rw [show k = r + L - 1 by omega] at hkq'
          have := I.uat (r + L - 1) q hkq' (by omega)
          have hTp := hUT.2
          rw [this] at hTp; cases hTp
        · rw [show k = r + L by omega, upg_last_none hx] at hkq'; cases hkq'
    exact ⟨k, List.mem_range.mpr (by rw [List.length_take]; omega), by rw [upg_take M hk1]; simp [hkq']⟩
  · have he2 : entry M 2 q = 1 := by
      have hU := hUT.1
      unfold isUpg at hU
      rw [List.any_eq_true] at hU
      obtain ⟨k, _, hkq⟩ := hU
      have := upg_target_e2 (show upg M k = some q by simpa using hkq); have := I.z2 q; omega
    have hall := all_bump_of_last I.r0p I.z2 I.sd I.z1 he2 hchq hxb
    unfold topped
    rw [children_take]
    cases hl : ((children M q).filter (fun c => decide (c < r + L))).getLast? with
    | none => rfl
    | some ℓ =>
      have hℓ := List.mem_filter.mp (List.mem_of_getLast? hl)
      have hℓx : ℓ < r + L := by simpa using hℓ.2
      simp only [decide_eq_true_eq]
      rw [col_take M hℓx, bump_take M hqx]
      exact hall ℓ hℓ.1

/-- **`v_T(q) = qnS` grows under `σ_{V,qnS}`.** -/
theorem c1_src_sv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) {r L q : Nat}
    (hrM : r < M.length) :
    qnS M ρ r L q < shf (ρ.v r) (qnS M ρ r L q) (qnS M ρ r L q) := by
  have hV : isOT (ρ.v r) = true := I.good.ot_v r hrM
  have hW : isOT (qnS M ρ r L q) = true := qnS_ot I hrM L q
  have hVW : ρ.v r < qnS M ρ r L q := qnS_gt M ρ r L q
  have hX : isOT (sumN (one :: ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))) = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ht; exact isOT_bumpTerm I.good q b
  have hω := isOT_omega hX
  have key : shf (ρ.v r) (qnS M ρ r L q) (add (ρ.v r) (omega (sumN (one ::
      ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))))) =
      add (qnS M ρ r L q) (sh (ρ.v r) (qnS M ρ r L q) (omega (sumN (one ::
        ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))))) := by
    rw [shf_add hV hW hVW hV hω (le_refl _), shf_self]
  obtain ⟨_, s, y, hsy⟩ := single_omega (isOT_sh hV hW hVW hX)
  calc qnS M ρ r L q < add (qnS M ρ r L q) (sh (ρ.v r) (qnS M ρ r L q) (omega (sumN (one ::
        ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))))) := by
        rw [sh_omega hV hW hVW hX, hsy]; exact lt_add_principal s y _
    _ = shf (ρ.v r) (qnS M ρ r L q) (add (ρ.v r) (omega (sumN (one ::
        ((children M q).filter (fun d => decide (d < r + L))).map (bumpTerm M ρ q))))) := key.symm
    _ = shf (ρ.v r) (qnS M ρ r L q) (qnS M ρ r L q) := rfl

/-- **The C strict field from the rules of the flow** (C1: `upg(x − 1) = none`). The source is `q`. -/
theorem c1_strict_of_rules {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hq : par M 0 (r + L) = some q) (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q])
    (hun : upg M (r + L - 1) = none) {τ : Valn} (hτ : Cons (M.take (r + L)) τ)
    (hRU : ∀ i j, upg M i = some j → j < r + L → HighD M r j →
      τ.v j < shf (ρ.v r) (qnS M ρ r L q) (τ.v j) → τ.v i < shf (ρ.v r) (qnS M ρ r L q) (τ.v i))
    (hRC : ∀ w j, w < r + L → j ∈ children M w → j < r + L → Counted (M.take (r + L)) w j →
      (∀ j' ∈ children M w, j < j' → j' < r + L → ¬ Counted (M.take (r + L)) w j') → HighD M r j →
      (FPV M (r + L) (fun d => τ.v d < shf (ρ.v r) (qnS M ρ r L q) (τ.v d)) j ∨
        FPA M (r + L) (fun d => argT (M.take (r + L)) τ d <
          sh (ρ.v r) (qnS M ρ r L q) (argT (M.take (r + L)) τ d)) j) →
      argT (M.take (r + L)) τ w < sh (ρ.v r) (qnS M ρ r L q) (argT (M.take (r + L)) τ w))
    (hRB : ∀ w j k, w < r + L → HighD M r w → w ≠ q → j ∈ children M w → col M j = bump M w →
      (∀ j' ∈ children M w, j < j' → j' < r + L → col M j' ≠ bump M w) → j ≠ q → k ∈ children M j →
      (∀ k' ∈ children M j, k' ≤ k) → HighD M r k →
      (FPV M (r + L) (fun d => τ.v d < shf (ρ.v r) (qnS M ρ r L q) (τ.v d)) k ∨
        FPA M (r + L) (fun d => argT (M.take (r + L)) τ d <
          sh (ρ.v r) (qnS M ρ r L q) (argT (M.take (r + L)) τ d)) k) →
      τ.v w < shf (ρ.v r) (qnS M ρ r L q) (τ.v w))
    (hnr : ∀ j ∈ children M r, j < r + L → HighD M r j → upg M r ≠ some j) :
    t2X1 M r L τ < sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) := by
  have hx : r + L + 1 = M.length := hlen
  obtain ⟨hpq, hnqT, hxb⟩ := c_q_facts hM hS I hlen hr hq hqr hncl
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hrq : r < q := par_lt M 0 _ _ hpq
  have hrM : r < M.length := by omega
  have he2r : entry M 2 r = 0 := (par2_facts I.z2 (by omega) hr).1
  have hxq : r + L ∈ children M q := mem_children_iff.mpr ⟨by omega, hq⟩
  have hqM : q ∈ children M r := mem_children_iff.mpr ⟨by omega, hpq⟩
  have hux : ∀ c, upg M (r + L - 1) = some c → c = r + L := by
    intro c hc; rw [hun] at hc; cases hc
  -- the row-1 entry of `q` is that of `x`, above that of `r`
  have he1q : entry M 1 r < entry M 1 q := by
    have h1 := par1_entry_lt (par1_x_r (by omega) I.z2 I.z1 hr)
    have : entry M 1 (r + L) = entry M 1 q := by
      have : entry M 1 (r + L) = (col M (r + L)).2.1 := rfl; rw [this, hxb]; rfl
    omega
  have hqH : HighD M r q := by
    refine ⟨anc0_of_par M 0 r q hpq, by omega, fun q' hrq' hq'q hq'r => ?_⟩
    by_cases hq' : q' = q
    · rw [hq']; exact he1q
    · exfalso
      have := anc0_of_par_ne hq'q hq' hpq
      exact hq'r (anc0_antisymm this hrq')
  have he2q : entry M 2 q ≠ 0 := by have := I.be q (r + L) hxq hxb; omega
  have hchg : ChgX M (r + L) false q := ChgX.snb (by omega) he2q hxq hxb
  have hTop := (chg_struct hx I.r0p I.z2 I.sd I.z1 I.uat I.uab hchg).1 rfl hqx
  have hsrc : FSrc2 M (r + L) r q (fun d => τ.v d < shf (ρ.v r) (qnS M ρ r L q) (τ.v d)) q (r + L - 1) := by
    refine ⟨hqx, by omega, hqH, hchg, ?_, ⟨by omega, fun t h1 h2 => anc_between (anc0_of_child hxq) t h1 (by omega),
      Or.inl (by omega)⟩, cl_nil_of hTop.2.1, fun w hw => ?_, fun k hk hk' hrk => ?_⟩
    · show τ.v q < shf (ρ.v r) (qnS M ρ r L q) (τ.v q)
      rw [c_vqP_of_un hM hS I hlen hr hq hqr hun τ hτ]
      exact c1_src_sv I hrM
    · rw [hpq] at hw; cases hw
      exact ⟨fun h => by have := I.be r q hqM h; omega, fun _ => hnqT⟩
    · exfalso
      have := (anc0_of_par_ne hk hk' hpq).le
      omega
  exact flow_top2 I hx hq he2r hux _ _ hsrc (by omega) hRU hRC hRB hnr

#print axioms c1_strict_of_rules

end Ytosk.V3Main.SeedPF
