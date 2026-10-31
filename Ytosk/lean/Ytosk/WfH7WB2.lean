/-
**HUAC は Bad2 の x − 1 でだけ要る（2026-10-31, WfH7W）。**

HUAC（上げ先が祖先の列の成分の支配）は一般には偽（`HUACFalse.not_HUAC`）。トップの 2 つの残り
`T0BadSeedsH7W`・`T2QNDomBad` が HUAC を呼ぶのは、全部 Bad2 の行列の最後から 2 番目の列 n = x − 1 が祖先へ
上げるときだけである（t0 の欄 1・欄 2、qn の単純な形）。ただ t0 の欄 2 の「失われた最後の葉」の場合
（`seed_sum_lhd` → `lost_tail_dom`）は、直前の兄弟 c での成分の支配 v(P₁ n) → v(c) を使う。

- `HUACB2`: Bad2 の M で n + 2 = |M|、n が祖先 k < n へ上げるなら、v(P₁ n) の成分は v(n) の成分か 0 以下。
  HUAC の反例（32 列）は Bad2 でない（n の親 p が bump 子でない）。
- `H7WTail`: t0 の Bad2 の場面で、r が g の bump 子、M.take x での r の子が K0 ++ [c, x − 1]、x − 1 が祖先へ上げる
  とき、v(P₁(x − 1)) の成分は v(c) の成分か 0 以下。
- `t0BadSeedsH7W_of_B2 : HDropU → HUACB2 → H7WTail → T0BadSeedsH7W`
- `t2QNDomBad_of_B2 : HUACB2 → T2QNDomBad2 → T2QNDomBad`
-/
import Ytosk.WfH10bChain
import Ytosk.V3QNDomS

namespace Ytosk.WfH7W

open T

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **Residual: HUAC at the second-to-last column of a `Bad2` matrix** (2026-10-31). The general `HUAC` is false
(`HUACFalse.not_HUAC`, whose column `n = 30` has a parent that is not a bump child, so the matrix is not `Bad2`). -/
def HUACB2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ n, n + 2 = M.length → ∀ k, upg M n = some k → k < n →
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z])

/-- **Residual: the lost last leaf of a bump child in the `t = 0` `Bad2` seeds** (2026-10-31): the components of
`v(P₁(x − 1))` are bounded by those of `v(c)` for the preceding sibling `c` (measured: `P₁ c = P₁(x − 1)` and
`v(c) = v(x − 1)` in every such frame). -/
def H7WTail : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ x, x + 1 = M.length → entry M 1 x = 0 →
    ∀ g r, r ∈ children M g → col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → x ∈ children M r →
    ∀ K0 c m k, children (M.take x) r = K0 ++ [c, x - 1] → upg M (x - 1) = some k → k < x - 1 →
      par M 1 (x - 1) = some m → ∀ u, Dom (comps u (ρ.v m)) (comps u (ρ.v c) ++ [z])

open T0SeedSum in
theorem lost_tail_domT {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3V2 M ρ rk)
    {x g r n : Nat} {K : List Nat}
    (hx : x + 1 = M.length) (hnx : n + 1 = x)
    (hr : r ∈ children M g) (hrb : col M r = bump M g)
    (hxCh : x ∈ children M r) (hK : children (M.take x) r = K ++ [n]) (hne : K ≠ [])
    (hp : (K.map ρ.o ++ [ρ.o n]).Pairwise (fun a b => b ≤ a))
    {k : Nat} (hu : upg M n = some k) (hkn : k < n)
    (hT3 : ∀ K0 c m, children (M.take x) r = K0 ++ [c, n] → par M 1 n = some m →
      ∀ u, Dom (comps u (ρ.v m)) (comps u (ρ.v c) ++ [z])) :
    ∀ u, Dom (comps u ((drop1 M x rk).o n)) (comps u (sumN (K.map ρ.o)) ++ [z]) := by
  have S := sInv_std hM hS
  obtain ⟨SX, SJ⟩ := sInvXJ_std hM hS
  obtain ⟨m, hm, _, _, _⟩ := upg_spec hu
  have hleaf := (lost_upg_take hM hS I hx hnx hu).2
  rw [hm] at hleaf
  simp only [vOpt] at hleaf
  rw [hleaf]
  obtain ⟨K0, c, hK0⟩ : ∃ K0 c, K = K0 ++ [c] := by
    rcases List.eq_nil_or_concat K with he | ⟨l, c, he⟩
    · exact False.elim (hne he)
    · exact ⟨l, c, by simpa only [List.concat_eq_append] using he⟩
  have hfull : children M r = K0 ++ c :: n :: [x] := by
    rw [children_split_x hx hxCh, ← children_take, hK, hK0]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hcM : c ∈ children M r := by rw [hfull]; simp
  have hnM : n ∈ children M r := by rw [hfull]; simp
  have hcn : c < n := by
    have hs := children_sorted M r
    rw [hfull] at hs
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 n (by simp)
  have he0c := S.r0p c r (mem_children_iff.mp hcM).2
  have he0n := S.r0p n r (mem_children_iff.mp hnM).2
  have he1 : entry M 1 n ≤ entry M 1 c := by
    have hsd := S.sibDec r K0 [x] c n hfull
    unfold colLe at hsd
    change entry M 0 n < entry M 0 c ∨
      (entry M 0 n = entry M 0 c ∧ (entry M 1 n < entry M 1 c ∨
      (entry M 1 n = entry M 1 c ∧ entry M 2 n ≤ entry M 2 c))) at hsd
    omega
  have hdm := hT3 K0 c m (by rw [hK, hK0]; simp) hm
  have hcM' := (mem_children hcM).2
  have hd : ∀ u, Dom (comps u (psi (add (ρ.v m) one) z z)) (comps u (ρ.o c) ++ [z]) := by
    obtain ⟨y, hy⟩ := o_psi_sub I.cons hcM'
    rw [sf_ot (I.good.ot_v c hcM')] at hy
    rw [hy]
    exact HUACPath.comp_dom_trans (HUACPath.lost_leaf_comp_dom hdm)
      (HUACPath.index_comp_dom (I.good.ot_v c hcM'))
  apply HUACPath.comp_dom_trans hd
  have hss : ∀ t ∈ K.map ρ.o, Single t := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    have hiM : i ∈ children M r := by rw [children_split_x hx hxCh, ← children_take, hK]; simp [hi]
    exact single_o I.cons I.good (mem_children hiM).2
  have hpl := (List.pairwise_append.mp hp).1
  rw [hK0, List.map_append, List.map_singleton] at hss hpl ⊢
  rw [sumN_snoc_dec hss hpl]
  intro u d hd
  refine ⟨d, List.mem_append_left _ ?_, le_refl _⟩
  rw [comps_app]
  exact List.mem_append_right _ hd

open T0SeedSum in
theorem seed_sum_lhdT {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3V2 M ρ rk) {x g r : Nat}
    (hx : x + 1 = M.length) (hr : r ∈ children M g) (hrb : col M r = bump M g)
    (hg1 : entry M 1 g ≠ 0) (hg2 : entry M 2 g ≠ 0)
    (hxCh : x ∈ children M r) (hrn : r ≠ x - 1)
    (hnlost : ¬ (children (M.take x) r = [x - 1] ∧
      ∃ k, upg M (x - 1) = some k ∧ k < x - 1))
    (hT : Cons (M.take x) (drop1 M x rk)) (hRT : Rk (M.take x) rk)
    (hdrop : ∀ i, i < x → PO ρ (drop1 M x rk) i ∧ PV M ρ (drop1 M x rk) i)
    (hT3 : ∀ K0 c m k, children (M.take x) r = K0 ++ [c, x - 1] → upg M (x - 1) = some k → k < x - 1 →
      par M 1 (x - 1) = some m → ∀ u, Dom (comps u (ρ.v m)) (comps u (ρ.v c) ++ [z])) :
    LhdE (omega (sumN ((children (M.take x) r).map (drop1 M x rk).o)))
      (omega (sumN ((children (M.take x) r).map ρ.o))) := by
  let τ := drop1 M x rk
  have S := sInv_std hM hS
  obtain ⟨SX, SJ⟩ := sInvXJ_std hM hS
  have hrx := (mem_children hxCh).1
  have hrc : r + 1 ∈ children (M.take x) r := by
    refine mem_children_iff.mpr ⟨by simp only [List.length_take]; omega, ?_⟩
    rw [par_take M 0 (r + 1) (by omega)]
    exact child_succ (Anc0.step (mem_children_iff.mp hxCh).2 (Anc0.refl r)) (by omega)
  have hne : children (M.take x) r ≠ [] := by intro he; rw [he] at hrc; simp at hrc
  obtain ⟨K, d, hK⟩ : ∃ K d, children (M.take x) r = K ++ [d] := by
    rcases List.eq_nil_or_concat (children (M.take x) r) with he | ⟨K, d, he⟩
    · exact False.elim (hne he)
    · exact ⟨K, d, by simpa only [List.concat_eq_append] using he⟩
  have hdT : d ∈ children (M.take x) r := by rw [hK]; simp
  have hdx : d < x := by
    have := (mem_children hdT).2
    simp only [List.length_take] at this
    omega
  have hdM : d ∈ children M r := by
    rw [children_take, List.mem_filter] at hdT
    exact hdT.1
  have hlast : (children (M.take x) r).getLast? = some d := by rw [hK]; simp
  have hprefix : K.map τ.o = K.map ρ.o := by
    apply List.map_congr_left
    intro c hc
    have hcT : c ∈ children (M.take x) r := by rw [hK]; simp [hc]
    have hcM : c ∈ children M r := by
      rw [children_take, List.mem_filter] at hcT
      exact hcT.1
    have hcd : c < d := by
      have hs := children_sorted (M.take x) r
      rw [hK] at hs
      exact (List.pairwise_append.mp hs).2.2 c hc d (by simp)
    exact earlier_o_stable S I.cons I.good hx (by rw [e2_of_col hrb]; decide) hcM hdT hcd hT hRT
  have hfull : children M r = (K ++ [d]) ++ [x] := by
    rw [children_split_x hx hxCh, ← children_take, hK]
  have hp : (K.map ρ.o ++ [ρ.o d]).Pairwise (fun a b => b ≤ a) := by
    have h := I.kd g hg1 hg2 r hr hrb
    rw [hfull, List.map_append, List.map_append, List.map_singleton, List.map_singleton] at h
    exact (List.pairwise_append.mp h).1
  have hs : ∀ t ∈ K.map ρ.o ++ [ρ.o d], Single t := by
    intro t ht
    have ht' : t ∈ (children M r).map ρ.o := by rw [hfull, List.map_append, List.map_append, List.map_singleton]; exact List.mem_append_left _ ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht'
    exact single_o I.cons I.good (mem_children hi).2
  have hs' : Single (τ.o d) := (hdrop d hdx).1.2
  have hle : τ.o d ≤ ρ.o d := (hdrop d hdx).1.le
  have hstable : ¬ (d = x - 1 ∧ ∃ k, upg M d = some k ∧ k < d) → τ.v d = ρ.v d := by
    intro hnl
    exact last_child_v_stable S SX.loc.2.2.2 SJ I.cons I.good hx hr hrb hxCh hlast hnl hT hRT
  rw [hK, List.map_append, List.map_append, List.map_singleton, List.map_singleton, hprefix]
  by_cases hKn : K = []
  · have hv : τ.v d = ρ.v d := hstable (by
      rintro ⟨hd, k, hu, hk⟩
      apply hnlost
      subst d
      exact ⟨by simpa only [hKn, List.nil_append] using hK, k, hu, hk⟩)
    have hstrong := T0SeedOutside.po_strong_of_v_eq I.cons I.good hT hdx (by omega)
      (hdrop d hdx).2.2 hv (hdrop d hdx).1
    obtain ⟨y', hy'⟩ := o_psi_sub hT (show d < (M.take x).length by simp only [List.length_take]; omega)
    obtain ⟨y, hy⟩ := o_psi_sub I.cons (show d < M.length by omega)
    rw [sf_ot (hdrop d hdx).2.2, hv] at hy'
    rw [sf_ot (I.good.ot_v d (by omega))] at hy
    simp only [hKn, List.map_nil, List.nil_append]
    have hsold : Single (ρ.o d) := hs _ (by simp)
    rw [sumN_singleton hs', sumN_singleton hsold]
    change LhdE (τ.o d) (ρ.o d) at hstrong
    change τ.o d = _ at hy'
    rw [hy', hy] at hstrong ⊢
    have hotnew := hs'.1
    have hotold := hsold.1
    rw [hy'] at hotnew
    rw [hy] at hotold
    exact omega_single_same hstrong hotnew hotold
  · apply omega_sum_last hs hs' hp hle (by simpa using hKn)
    by_cases hnl : ¬ (d = x - 1 ∧ ∃ k, upg M d = some k ∧ k < d)
    · exact Or.inl (T0SeedOutside.po_strong_of_v_eq I.cons I.good hT hdx (by omega)
        (hdrop d hdx).2.2 (hstable hnl) (hdrop d hdx).1)
    · push Not at hnl
      obtain ⟨hd, k, hu, hkd⟩ := hnl
      subst hd
      exact Or.inr (lost_tail_domT hM hS I hx (by omega) hr hrb hxCh hK hKn hp hu hkd
        (fun K0 c m hK' hm => hT3 K0 c m k hK' hu hkd hm))

theorem t0BadSeedsH7W_of_B2 (hDU : HDropU) (hB2 : HUACB2) (hTail : H7WTail) : T0BadSeedsH7W := by
  intro M ρ rk hM hS hB I r L hlen hL hp he1
  have S := sInv_std hM hS
  obtain ⟨SX, SJ⟩ := sInvXJ_std hM hS
  obtain ⟨R, _⟩ := hDU M ρ rk hM hS (by intro h; subst h; simp at hlen) I
  have hx : (r + L) + 1 = M.length := hlen
  have hcnt := counted_take_last (M := M) (show 1 ≤ M.length by omega)
    S.r0p S.z2 S.sibDec S.z1c S.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRT : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hT := cons_of_rk hRT
  rw [show M.length - 1 = r + L by omega] at R
  have hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV M ρ (drop1 M (r + L) rk) i :=
    drop_all_hardB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hT hRT I.vs R.vst I.fc I.fo
      R.hard (bump_dropB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hT hRT I.kd I.td R.ab R.ws) R.ua
  refine ⟨fun g pp hg hpp h1p h2p hgb => ?_, fun g hg hrx hrb h1g h2g => ?_⟩
  · by_cases hs : L = 1 ∧ ∃ k, upg M r = some k ∧ k < r
    · obtain ⟨hL1, k, hk, hkr⟩ := hs
      subst hL1
      right
      intro w' hw' u _ e he
      obtain ⟨_, ho⟩ := lost_upg_take hM hS I (x := r + 1) (by omega) rfl hk
      rw [ho] at hw'
      simp only [psi.injEq] at hw'
      rw [← hw'.1] at he
      rcases dom_add_one (hB2 M ρ rk hM hS hB I r (by omega) k hk hkr) u e he with h | ⟨d, hd, hed⟩
      · exact ⟨z, List.mem_cons_self .., by rw [h]⟩
      · exact ⟨d, List.mem_cons_of_mem _ hd, hed⟩
    · left
      apply T0SeedOutside.seed_lhd_outside S SX.loc.2.2.2 SJ I.cons I.good hx hp hg hpp hgb he1 ?_ hT hRT hdrop
      rintro ⟨hr, k, hk, hkr⟩
      exact hs ⟨by omega, k, hk, hkr⟩
  · by_cases hs : children (M.take (r + L)) r = [r + L - 1] ∧ ∃ k, upg M (r + L - 1) = some k ∧ k < r + L - 1
    · obtain ⟨hch, k, hk, hkx⟩ := hs
      right
      have S := sInv_std hM hS
      obtain ⟨hv', ho'⟩ := lost_upg_take hM hS I (x := r + L) (r := r + L - 1) (by omega) (by omega) hk
      -- `x − 1` has no children in `M` (`x` is a child of `r ≠ x − 1`)
      have hchM : children M (r + L - 1) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro c hc
        have hcl := mem_children hc
        have hcx : c = r + L := by omega
        have hpc := (mem_children_iff.mp hc).2
        rw [hcx, hp] at hpc
        exact hrx (Option.some.inj hpc)
      have hvot : isOT (ρ.v (r + L - 1)) = true := I.good.ot_v _ (by omega)
      have hoM := o_nochild I.cons (by omega) hchM hvot
      have hVot : isOT (add (vOpt ρ (par M 1 (r + L - 1))) one) = true :=
        isOT_add (vOpt_ot I.good (by omega)) isOT_one
      have hw0 : add (vOpt ρ (par M 1 (r + L - 1))) one ≠ z := by
        intro h
        have := congrArg last h
        rw [show one = psi z z z from rfl, last_add_W ⟨z, z, rfl⟩] at this
        cases this
      have hvz : ρ.v (r + L - 1) ≠ z := v_ne_z_of_e1 I.cons (by omega) (upg_e12 hk).1
      rw [hch]
      simp only [List.map_cons, List.map_nil]
      rw [sumN_singleton (single_o I.cons I.good (by omega)), hoM, omega_psi_zz hvz (isOT_psi_zz hvot)]
      intro s b' hsb u e he
      simp only [psi.injEq] at hsb
      obtain ⟨rfl, rfl, -⟩ := hsb
      rw [sumN_singleton ⟨by rw [ho']; exact isOT_psi_zz hVot, _, _, ho'⟩, ho',
        omega_psi_zz hw0 (isOT_psi_zz hVot)] at he
      rcases comps_psi_zz he with h | he
      · exact ⟨z, List.mem_cons_self .., by rw [h]⟩
      rcases dom_add_one (hB2 M ρ rk hM hS hB I (r + L - 1) (by omega) k hk hkx) u e he with h | ⟨d, hd, hed⟩
      · exact ⟨z, List.mem_cons_self .., by rw [h]⟩
      · exact ⟨d, by simp [hd], hed⟩
    · left
      have hrM : r ∈ children M g := mem_children_iff.mpr ⟨by have := par_lt M 0 (r + L) r hp; omega, hg⟩
      have hxM : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
      exact seed_sum_lhdT hM hS I hx hrM hrb h1g h2g hxM hrx hs hT hRT hdrop
        (fun K0 c m k hK hu hk hm => hTail M ρ rk hM hS hB I (r + L) hx he1 g r hrM hrb h1g h2g hxM K0 c m k hK hu hk hm)

theorem qnDom_simpleB2 (hB2 : HUACB2) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) (hB : Bad2 M)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hq : par M 0 (r + L) = some q) (hqr : q ≠ r)
    {p k : Nat} (hchq : (children M q).filter (fun c => decide (c < r + L)) = [p])
    (hchp : children M p = [r + L - 1]) (hpb : col M p = bump M q) (hk : upg M (r + L - 1) = some k)
    (hkx : k < r + L - 1) {τ : Valn} (hτ : Cons (M.take (r + L)) τ) {ωT : T}
    (hvq : τ.v q = add (ρ.v r) ωT) (hωT : ∃ a b, ωT = psi a b z) :
    ∀ u, Dom (comps u ωT) (comps u (qnS M ρ r L q) ++ [z]) := by
  have S := C.S
  have I := C.I
  have hqx : q < r + L := par_lt M 0 _ _ hq
  have hpM : p ∈ children M q := (List.mem_filter.mp (by rw [hchq]; simp : p ∈ (children M q).filter _)).1
  have hpx : p < r + L := by
    have := (List.mem_filter.mp (by rw [hchq]; simp : p ∈ (children M q).filter _)).2; simpa using this
  have hxm1p : r + L - 1 ∈ children M p := by rw [hchp]; simp
  have hpx1 : p < r + L - 1 := (mem_children hxm1p).1
  have hx1 : r + L - 1 + 1 = r + L := by omega
  -- the drop valuation and `τ`
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hag := agree_of_cons hC1 hτ hRk1
  have hlT : (M.take (r + L)).length = r + L := by rw [List.length_take]; omega
  have hdrop := C.hdrop
  rw [show M.length - 1 = r + L by omega] at hdrop
  have hG1 := good3_take (show r + L + 1 = M.length by omega) S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good
    hC1 hRk1 hdrop
  have hGτ := good3_congr hG1 hag
  obtain ⟨hv', ho'⟩ := lost_upg_take C.std C.ne I (x := r + L) (r := r + L - 1) (by omega) hx1 hk
  set w := add (vOpt ρ (par M 1 (r + L - 1))) one with hw
  have hwot : isOT w = true := isOT_add (vOpt_ot I.good (by omega)) isOT_one
  have hw0 : w ≠ z := by
    intro h
    have := congrArg last h
    rw [hw, show one = psi z z z from rfl, last_add_W ⟨z, z, rfl⟩] at this
    cases this
  have hoτ : τ.o (r + L - 1) = psi w z z := by rw [← (hag _ (by omega)).1, ho']
  -- `ω_T = ψ_w(0)`
  have he2q : entry M 2 q = 1 := S.bumpE2 q p hpM hpb
  have he1q : entry M 1 q ≠ 0 := fun h => by have := S.r12 q h; omega
  have hchT : children (M.take (r + L)) q = [p] := by rw [children_take, hchq]
  have hchTp : children (M.take (r + L)) p = [r + L - 1] := by
    rw [children_take, hchp]; simp; omega
  have hbT : bumpTerm (M.take (r + L)) τ q p = omega (sumN [psi w z z]) := by
    unfold bumpTerm
    rw [col_take M hpx, bump_take M hqx, if_pos hpb, hchTp]
    simp [hoτ]
  have hqT : q < (M.take (r + L)).length := by omega
  have hvqT : τ.v q = add (vOpt τ (par (M.take (r + L)) 1 q)) (psi w z z) := by
    rw [(hτ q hqT).2]; unfold vRhs
    rw [entry_take M 1 hqx, entry_take M 2 hqx, if_neg he1q, if_neg (by omega), hchT]
    simp only [List.map_cons, List.map_nil]
    rw [hbT, bumpSum_psi_zz hw0 (isOT_psi_zz hwot)]
    exact sf_ot (isOT_add (vOpt_ot hGτ hqT) (isOT_psi_zz hwot))
  have hωTe : ωT = psi w z z := by
    obtain ⟨a, b, rfl⟩ := hωT
    have h1 := congrArg last hvq
    rw [hvqT, last_add_W ⟨_, _, rfl⟩, last_add_W ⟨_, _, rfl⟩] at h1
    exact h1.symm
  -- `s′ = V + ψ_{v(x−1)}(0)`
  have hchM : children M (r + L - 1) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    have hcl := mem_children hc
    have hcx : c = r + L := by omega
    have hpc := (mem_children_iff.mp hc).2
    rw [hcx, hq] at hpc
    have := Option.some.inj hpc
    have := (mem_children hpM).1
    omega
  set a := ρ.v (r + L - 1) with ha
  have haot : isOT a = true := I.good.ot_v _ (by omega)
  have ha0 : a ≠ z := v_ne_z_of_e1 I.cons (by omega) (upg_e12 hk).1
  have hoM : ρ.o (r + L - 1) = psi a z z := o_nochild I.cons (by omega) hchM haot
  have hqnS : qnS M ρ r L q = add (ρ.v r) (psi a z z) := by
    unfold qnS; rw [hchq]
    simp only [List.map_cons, List.map_nil]
    unfold bumpTerm
    rw [if_pos hpb, hchp]
    simp only [List.map_cons, List.map_nil]
    rw [hoM, bumpSum_psi_zz ha0 (isOT_psi_zz haot)]
  have hwa : w ≤ a := by rw [← hv']; exact (hdrop (r + L - 1) (by omega)).2.le
  -- the components
  intro u e he
  rw [hωTe] at he
  obtain ⟨hwu, he⟩ := comps_psi_zz' he
  have hz : z ∈ comps u (qnS M ρ r L q) ++ [z] := List.mem_append_right _ (List.mem_singleton_self _)
  rcases he with he | he
  · exact ⟨z, hz, by rw [he]⟩
  rcases dom_add_one (hB2 M ρ rk C.std C.ne hB I (r + L - 1) (by omega) k hk hkx) u e he with h | ⟨d, hd, hed⟩
  · exact ⟨z, hz, by rw [h]⟩
  refine ⟨d, List.mem_append_left _ ?_, hed⟩
  have hau : ¬ a < u := fun h => hwu (lt_of_le_of_lt hwa h)
  rw [hqnS]
  obtain ⟨P, hP, _⟩ := add_eq_app_prefix (ρ.v r) (psi a z z)
  rw [hP, comps_app]
  exact List.mem_append_right _ (mem_comps_psi_zz hau hd)

/-- **`T2QNDomBad` from `HUACB2` and the non-simple shapes** (no general `HUAC`). -/
theorem t2QNDomBad_of_B2 (hB2 : HUACB2) (h : T2QNDomBad2) : T2QNDomBad := by
  intro M ρ rk C hB hz h2 r L q hlen hr hq hqr Lc hCL τ hτ hE ωT hvq hωT
  by_cases hs : ∃ p k, (children M q).filter (fun c => decide (c < r + L)) = [p] ∧ children M p = [r + L - 1] ∧
      col M p = bump M q ∧ upg M (r + L - 1) = some k ∧ k < r + L - 1
  · obtain ⟨p, k, hchq, hchp, hpb, hk, hkx⟩ := hs
    exact qnDom_simpleB2 hB2 C hB hlen hq hqr hchq hchp hpb hk hkx hτ hvq hωT
  · exact h M ρ rk C hB hz h2 r L q hlen hr hq hqr Lc hCL hs τ hτ hE ωT hvq hωT

end Ytosk.WfH7W
