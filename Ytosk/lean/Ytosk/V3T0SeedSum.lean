/-
The unchanged sibling prefix closes a weak last child in the Bad2 seed sum.
-/
import Ytosk.V3T0SeedOutside
import Ytosk.V3HUACPath

namespace Ytosk.T0SeedSum

open T

/-- A dominating unchanged prefix carries weak tail components through omega. -/
theorem omega_prefix_dom {A b' b : T} (hA : A ≠ z) (hle : b' ≤ b)
    (hnew : isOT (app A b') = true) (hold : isOT (app A b) = true)
    (hdom : ∀ u, Dom (comps u b') (comps u A ++ [z])) :
    LhdE (omega (app A b')) (omega (app A b)) := by
  rcases (le_iff _ _).mp hle with hlt | rfl
  swap
  · exact Or.inl rfl
  have hl : LhdE (app A b') (app A b) := Or.inr (HUACPath.lhd_common_prefix hlt hdom)
  have hrel : BRelS (app A b') (app A b) := by
    cases A with
    | z => exact False.elim (hA rfl)
    | psi s y c =>
      simp only [app_psi] at hl ⊢
      by_cases hE : psi s y (app c b) < E0
      · exact Or.inl ⟨hl, hE⟩
      · exact Or.inr (Or.inl ⟨hl, fun h' => hE (lt_E0_rest h'), _, _, _, _, _, rfl, rfl⟩)
  exact brelS_lhdE (brelS_omega hnew hold hrel)

/-- A strong last child passes through omega under a common nonzero prefix. -/
theorem omega_prefix_strong {A b' b : T} (hA : A ≠ z) (hrel : LhdE b' b)
    (hnew : isOT (app A b') = true) (hold : isOT (app A b) = true) :
    LhdE (omega (app A b')) (omega (app A b)) := by
  apply brelS_lhdE
  apply brelS_omega hnew hold
  simpa only [app_z_right] using brelS_app_same hA hrel z

/-- At a singleton child with an unchanged index, the psi shape supplies BRelS. -/
theorem omega_single_same {s y' y : T} (hrel : LhdE (psi s y' z) (psi s y z))
    (hnew : isOT (psi s y' z) = true) (hold : isOT (psi s y z) = true) :
    LhdE (omega (psi s y' z)) (omega (psi s y z)) := by
  apply brelS_lhdE
  apply brelS_omega hnew hold
  simpa using brelS_single_same z hrel hnew

/-- All siblings strictly before a remaining child are unchanged. -/
theorem earlier_o_stable {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat}
    (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) {x r c d : Nat}
    (hx : x + 1 = M.length) (hr2 : entry M 2 r ≠ 0)
    (hc : c ∈ children M r) (hd : d ∈ children (M.take x) r) (hcd : c < d)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) : τ.o c = ρ.o c := by
  have hdx : d < x := by
    have := (mem_children hd).2
    simp only [List.length_take] at this
    omega
  apply (chg_off hx hC hG hT hRT c (by omega)).1
  intro hchg
  exact chg_only_last hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hr2 hc hd hcd hchg (Anc0.refl c)

/-- A last remaining child has unchanged index unless it is the lost upgrade itself. -/
theorem last_child_v_stable {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat}
    (S : SInv M) (hBL : BumpLeaf M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {x g r d : Nat}
    (hx : x + 1 = M.length) (hr : r ∈ children M g) (hrb : col M r = bump M g)
    (hxCh : x ∈ children M r) (hlast : (children (M.take x) r).getLast? = some d)
    (hnlost : ¬ (d = x - 1 ∧ ∃ k, upg M d = some k ∧ k < d))
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) : τ.v d = ρ.v d := by
  have hdT := List.mem_of_getLast? hlast
  have hdx : d < x := by
    have := (mem_children hdT).2
    simp only [List.length_take] at this
    omega
  have hdM : d ∈ children M r := by
    rw [children_take, List.mem_filter] at hdT
    exact hdT.1
  have hd2 := HUACPath.zero_child_before_later hBL hJ hr hrb hdM hxCh hdx
  by_cases he : d = x - 1
  · have hu : upg M d = none := by
      cases hu : upg M d with
      | none => rfl
      | some k =>
        obtain ⟨_, _, _, _, heq | ⟨_, hk⟩⟩ := upg_spec hu
        · have hnext : upg M d = some (d + 1) := by simpa only [heq] using hu
          have hArc : Anc0 M r x := Anc0.step (mem_children_iff.mp hxCh).2 (Anc0.refl r)
          exact False.elim (HUACPath.no_next_child S (e2_of_col hrb) hdM hdx hArc hnext)
        · exact False.elim (hnlost ⟨he, k, hu, hk⟩)
    exact T0SeedOutside.v_stable_zero_no_upg S hC hG hx hdx hd2 hu hT hRT
  · have hrx : r < x := (mem_children hxCh).1
    have hArc : Anc0 M r (x - 1) :=
      anc_between (Anc0.step (mem_children_iff.mp hxCh).2 (Anc0.refl r)) (x - 1) (by omega) (by omega)
    have hAd : Anc0 (M.take x) d (x - 1) :=
      anc0_last_child hlast (anc0_to_take hArc (by omega)) (by omega) (by simp only [List.length_take]; omega)
    have hc : d + 1 ∈ children (M.take x) d :=
      mem_children_iff.mpr ⟨by simp only [List.length_take]; omega,
        child_succ hAd (by omega)⟩
    exact T0SeedOutside.v_stable_zero_child S hC hG hx hdx hd2 hT hRT hc

/-- Keep a decreasing prefix and replace only its final summand. -/
theorem omega_sum_last {l : List T} {b' b : T}
    (hs : ∀ t ∈ l ++ [b], Single t) (hs' : Single b')
    (hp : (l ++ [b]).Pairwise (fun a b => b ≤ a)) (hle : b' ≤ b)
    (hne : l ≠ [])
    (htail : LhdE b' b ∨ ∀ u, Dom (comps u b') (comps u (sumN l) ++ [z])) :
    LhdE (omega (sumN (l ++ [b']))) (omega (sumN (l ++ [b]))) := by
  have hsl : ∀ t ∈ l, Single t := fun t ht => hs t (List.mem_append_left _ ht)
  obtain ⟨hpl, _, hcross⟩ := List.pairwise_append.mp hp
  have hp' : (l ++ [b']).Pairwise (fun a b => b ≤ a) := by
    apply List.pairwise_append.mpr
    refine ⟨hpl, by simp, ?_⟩
    intro a ha t ht
    simp only [List.mem_singleton] at ht
    subst t
    exact le_trans hle (hcross a ha b (by simp))
  have hsnew : ∀ t ∈ l ++ [b'], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsl t ht
    · simp only [List.mem_singleton] at ht
      subst t
      exact hs'
  have hot := isOT_sumN (l ++ [b]) (fun t ht => (hs t ht).1)
  have hot' := isOT_sumN (l ++ [b']) (fun t ht => (hsnew t ht).1)
  rw [sumN_snoc_dec hs hp] at hot ⊢
  rw [sumN_snoc_dec hsnew hp'] at hot' ⊢
  have hA := sumN_ne_z hsl hpl hne
  rcases htail with htail | htail
  · exact omega_prefix_strong hA htail hot' hot
  · exact omega_prefix_dom hA hle hot' hot htail

/-- An unchanged earlier sibling supplies all components of a lost final leaf. -/
theorem lost_tail_dom (hU : HUAC) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3V2 M ρ rk)
    {x g r n : Nat} {K : List Nat}
    (hx : x + 1 = M.length) (hnx : n + 1 = x)
    (hr : r ∈ children M g) (hrb : col M r = bump M g)
    (hxCh : x ∈ children M r) (hK : children (M.take x) r = K ++ [n]) (hne : K ≠ [])
    (hp : (K.map ρ.o ++ [ρ.o n]).Pairwise (fun a b => b ≤ a))
    (hu : ∃ k, upg M n = some k) :
    ∀ u, Dom (comps u ((drop1 M x rk).o n)) (comps u (sumN (K.map ρ.o)) ++ [z]) := by
  have S := sInv_std hM hS
  obtain ⟨SX, SJ⟩ := sInvXJ_std hM hS
  obtain ⟨k, hu⟩ := hu
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
  have hd := HUACPath.earlier_sibling_leaf_dom hU hM hS S SX.loc.2.2.2 SJ
    I.cons I.rank I.good hr hrb hcM hnM hxCh hcn (by omega) hm he1
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

/-- The bump-child sum is strong outside a singleton lost upgrade. -/
theorem seed_sum_lhd (hU : HUAC) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3V2 M ρ rk) {x g r : Nat}
    (hx : x + 1 = M.length) (hr : r ∈ children M g) (hrb : col M r = bump M g)
    (hg1 : entry M 1 g ≠ 0) (hg2 : entry M 2 g ≠ 0)
    (hxCh : x ∈ children M r) (hrn : r ≠ x - 1)
    (hnlost : ¬ (children (M.take x) r = [x - 1] ∧
      ∃ k, upg M (x - 1) = some k ∧ k < x - 1))
    (hT : Cons (M.take x) (drop1 M x rk)) (hRT : Rk (M.take x) rk)
    (hdrop : ∀ i, i < x → PO ρ (drop1 M x rk) i ∧ PV M ρ (drop1 M x rk) i) :
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
      obtain ⟨hd, k, hu, _⟩ := hnl
      exact Or.inr (lost_tail_dom hU hM hS I hx (by omega) hr hrb hxCh hK hKn hp ⟨k, hu⟩)

/-- Only the preceding-upgrade exclusion remains from H8. -/
def T0BadSeedsH10 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ g, par M 0 r = some g → r ≠ r + L - 1 → r - 1 ≠ g → Counted M g r → topped (M.take (r + L)) r = true →
      upg M (r - 1) ≠ some r

/-- HUAC and the already available drop conclusion eliminate H9's sum field. -/
theorem t0BadSeedsH9_of (hDU : HDropU) (hU : HUAC) (h10 : T0BadSeedsH10) :
    T0SeedOutside.T0BadSeedsH9 := by
  intro M ρ rk hM hS hB I r L hlen hL hp he1
  refine ⟨?_, h10 M ρ rk hM hS hB I r L hlen hL hp he1⟩
  intro g hg hrn hrb hg1 hg2 hnlost
  have S := sInv_std hM hS
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
  left
  apply seed_sum_lhd hU hM hS I hx ?_ hrb hg1 hg2 ?_ hrn hnlost hT hRT hdrop
  · exact mem_children_iff.mpr ⟨by have := par_lt M 0 (r + L) r hp; omega, hg⟩
  · exact mem_children_iff.mpr ⟨by omega, hp⟩

end Ytosk.T0SeedSum
