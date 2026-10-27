/-
HUAC along a row-1 path of row-2-zero columns, with no upgrade to the next column.
-/
import Ytosk.V3HUAC

namespace Ytosk.HUACPath

open T

/-- Component domination with zero adjoined is transitive. -/
theorem comp_dom_trans {A B C : T}
    (hAB : ∀ u, Dom (comps u A) (comps u B ++ [z]))
    (hBC : ∀ u, Dom (comps u B) (comps u C ++ [z])) :
    ∀ u, Dom (comps u A) (comps u C ++ [z]) := by
  intro u g hg
  obtain ⟨d, hd, hgd⟩ := hAB u g hg
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨e, he, hde⟩ := hBC u d hd
    exact ⟨e, he, le_trans hgd hde⟩
  · simp only [List.mem_singleton] at hd
    exact ⟨z, List.mem_append_right _ (by simp), by simpa [hd] using hgd⟩

/-- HUAC or addition of one handles one row-1 edge at a row-2-zero column. -/
theorem parent_comp_dom (hU : HUAC) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (hC : Cons M ρ) (hR : Rk M rk) (hG : Good3 M ρ)
    {c p : Nat} (hc : c < M.length) (hp : par M 1 c = some p)
    (h2 : entry M 2 c = 0) (hn : upg M c ≠ some (c + 1)) :
    ∀ u, Dom (comps u (ρ.v p)) (comps u (ρ.v c) ++ [z]) := by
  cases hu : upg M c with
  | some k =>
    obtain ⟨_, _, _, _, he | ⟨_, hk⟩⟩ := upg_spec hu
    · exact False.elim (hn (by rw [he] at hu; exact hu))
    · simpa only [hp, vOpt] using hU M ρ rk hM hS hC hR hG c k hu hk
  | none =>
    have h1 : entry M 1 c ≠ 0 := by have := par1_entry_lt hp; omega
    have hpc := par_lt M 1 c p hp
    have hv : ρ.v c = app (ρ.v p) one := by
      rw [(hC c hc).2]
      unfold vRhs
      rw [if_neg h1, if_pos h2, hu, hp]
      simp only [vOpt]
      rw [sf_ot (isOT_add (hG.ot_v p (by omega)) isOT_one), add_one_eq_app]
    intro u g hg
    refine ⟨g, List.mem_append_left _ ?_, le_refl _⟩
    rw [hv, comps_app]
    exact List.mem_append_left _ hg

/-- All strict row-1 ancestors have row 2 zero and cannot upgrade to their next column.
Thus only the endpoint needs these hypotheses. -/
theorem comp_dom_path (hU : HUAC) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (S : SInv M)
    (hC : Cons M ρ) (hR : Rk M rk) (hG : Good3 M ρ) :
    ∀ n p c, c < n → TRIO.le1 M p c → entry M 2 c = 0 → upg M c ≠ some (c + 1) →
      ∀ u, Dom (comps u (ρ.v p)) (comps u (ρ.v c) ++ [z])
  | 0, _, _, hc, _, _, _ => False.elim (Nat.not_lt_zero _ hc)
  | n + 1, p, c, hcn, hpc, h2, hn => by
    by_cases heq : c = p
    · subst p
      exact fun u g hg => ⟨g, List.mem_append_left _ hg, le_refl _⟩
    obtain ⟨m, hm, hpm⟩ := le1_par1_down hpc heq
    have hmc := par_lt M 1 c m hm
    have hcM : c < M.length := hpc.2.1
    have hm2 : entry M 2 m = 0 := by
      by_contra h
      have he : entry M 2 m = 1 := by have := S.z2 m; omega
      exact no_par1_of_e2 S.z1c hcM he hm
    have hmn : upg M m ≠ some (m + 1) := by
      intro hu
      have := leaf_of_upg_next S.r0p hu c (anc0_of_par M 1 m c hm)
      omega
    exact comp_dom_trans
      (comp_dom_path hU hM hS S hC hR hG n p m (by omega) hpm hm2 hmn)
      (parent_comp_dom hU hM hS hC hR hG hcM hm h2 hn)

/-- A prefix whose components dominate the new tail supplies the whole interval witness. -/
theorem lhd_common_prefix {A b' b : T} (hlt : b' < b)
    (hdom : ∀ u, Dom (comps u b') (comps u A ++ [z])) :
    Lhd z (app A b') (app A b) := by
  refine ⟨app_lt_app_left A hlt, fun u c h1 h2 g hg => ?_⟩
  obtain ⟨c0, rfl, _, _⟩ := between_app h1 h2
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · refine ⟨g, List.mem_append_left _ ?_, le_refl _⟩
    rw [comps_app]
    exact List.mem_append_left _ hg
  · obtain ⟨d, hd, hgd⟩ := hdom u g hg
    refine ⟨d, ?_, hgd⟩
    rcases List.mem_append.mp hd with hd | hd
    · exact List.mem_append_left _ (by rw [comps_app]; exact List.mem_append_left _ hd)
    · exact List.mem_append_right _ hd

/-- A child of a row-2-one parent, still followed by another descendant, cannot upgrade to its next column. -/
theorem no_next_child {M : Mat} (S : SInv M) {r c x : Nat}
    (hr2 : entry M 2 r = 1) (hc : c ∈ children M r)
    (hcx : c < x) (hrx : Anc0 M r x) : upg M c ≠ some (c + 1) := by
  intro hu
  obtain ⟨m, hm, hmk, _, _⟩ := upg_spec hu
  obtain ⟨m', hm', hmk0⟩ := upg_target_par0 S.r0p hu
  rw [hm] at hm'; cases hm'
  have hrc := (mem_children hc).1
  have hAc : Anc0 M m c := anc0_of_par M 1 m c hm
  have hAmr : Anc0 M m r := anc0_par hAc (by have := par_lt M 1 c m hm; omega)
    (mem_children_iff.mp hc).2
  have hmr : m < r := by
    have hle := hAmr.le
    have h1 := par1_entry_lt hm
    have h2 := S.z1c r c hr2 hc
    by_contra h
    have : m = r := by omega
    subst m
    omega
  have hArc : Anc0 M r (c + 1) := anc_between hrx (c + 1) (by omega) (by omega)
  have := (anc0_par hArc (by omega) hmk0).le
  omega

/-- Children before a later child of a bump column all have row 2 zero. -/
theorem zero_child_before_later {M : Mat} (hBL : BumpLeaf M) (hJ : RowJ M)
    {g r c x : Nat} (hr : r ∈ children M g) (hrb : col M r = bump M g)
    (hc : c ∈ children M r) (hx : x ∈ children M r) (hcx : c < x) : entry M 2 c = 0 := by
  by_contra h2
  have h1 := hJ c r h2 (mem_children_iff.mp hc).2
  have he1 : entry M 1 r = entry M 1 g := e1_of_col hrb
  obtain ⟨_, _, hclast, _⟩ := hBL g r c hr hrb hc (by omega)
  have := last_le (children_sorted M r) hclast x hx
  omega

/-- An earlier sibling of a lost leaf carries all components of that leaf's row-1 parent. -/
theorem earlier_sibling_parent_dom (hU : HUAC) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (S : SInv M) (hBL : BumpLeaf M) (hJ : RowJ M)
    (hC : Cons M ρ) (hR : Rk M rk) (hG : Good3 M ρ)
    {g r c n m x : Nat} (hr : r ∈ children M g) (hrb : col M r = bump M g)
    (hc : c ∈ children M r) (hn : n ∈ children M r) (hx : x ∈ children M r)
    (hcn : c < n) (hnx : n < x) (hm : par M 1 n = some m)
    (he1 : entry M 1 n ≤ entry M 1 c) :
    ∀ u, Dom (comps u (ρ.v m)) (comps u (ρ.v c) ++ [z]) := by
  have hcM := (mem_children hc).2
  have hnM := (mem_children hn).2
  have hmn := par_lt M 1 n m hm
  have hAmr : Anc0 M m r := anc0_par (anc0_of_par M 1 m n hm) (by omega)
    (mem_children_iff.mp hn).2
  have hmn1 : TRIO.le1 M m n :=
    le1_par1_up ⟨by omega, by omega, Relation.ReflTransGen.refl⟩ hm hnM
  have hmc1 := guard_sib hAmr (mem_children_iff.mp hc).2 (mem_children_iff.mp hn).2 hcM hnM hmn1 he1
  have hc2 := zero_child_before_later hBL hJ hr hrb hc hx (by omega)
  have hr2 : entry M 2 r = 1 := e2_of_col hrb
  have hArc : Anc0 M r x := Anc0.step (mem_children_iff.mp hx).2 (Anc0.refl r)
  exact comp_dom_path hU hM hS S hC hR hG M.length m c hcM hmc1 hc2
    (no_next_child S hr2 hc (by omega) hArc)

/-- Components of a standard subscript occur in its psi node whenever they are nonempty. -/
theorem index_comp_dom {v y : T} (hv : isOT v = true) :
    ∀ u, Dom (comps u v) (comps u (psi v y z) ++ [z]) := by
  intro u g hg
  by_cases hlt : v < u
  · have hnil : comps u v = [] := comps_eq_nil_of_lev (fun q hq =>
      lt_trans (lev_lt_of_summand hv hq) hlt)
    rw [hnil] at hg
    simp at hg
  · exact ⟨g, List.mem_append_left _ (comps_psi_mem_of hlt (Or.inr (Or.inr (Or.inl hg)))), le_refl _⟩

/-- A lost-upgrade leaf inherits component domination of its old row-1 parent. -/
theorem lost_leaf_comp_dom {A B : T}
    (h : ∀ u, Dom (comps u A) (comps u B ++ [z])) :
    ∀ u, Dom (comps u (psi (add A one) z z)) (comps u B ++ [z]) := by
  intro u g hg
  rcases comps_psi_zz hg with hgz | hg
  · exact ⟨z, List.mem_append_right _ (by simp), by simp [hgz]⟩
  · rcases dom_add_one h u g hg with hgz | ⟨d, hd, hgd⟩
    · exact ⟨z, List.mem_append_right _ (by simp), by simp [hgz]⟩
    · exact ⟨d, List.mem_append_left _ hd, hgd⟩

/-- The actual old o of an earlier sibling dominates the lost leaf. -/
theorem earlier_sibling_leaf_dom (hU : HUAC) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (S : SInv M) (hBL : BumpLeaf M) (hJ : RowJ M)
    (hC : Cons M ρ) (hR : Rk M rk) (hG : Good3 M ρ)
    {g r c n m x : Nat} (hr : r ∈ children M g) (hrb : col M r = bump M g)
    (hc : c ∈ children M r) (hn : n ∈ children M r) (hx : x ∈ children M r)
    (hcn : c < n) (hnx : n < x) (hm : par M 1 n = some m)
    (he1 : entry M 1 n ≤ entry M 1 c) :
    ∀ u, Dom (comps u (psi (add (ρ.v m) one) z z)) (comps u (ρ.o c) ++ [z]) := by
  have hd := earlier_sibling_parent_dom hU hM hS S hBL hJ hC hR hG hr hrb hc hn hx hcn hnx hm he1
  have hcM := (mem_children hc).2
  obtain ⟨y, hy⟩ := o_psi_sub hC hcM
  rw [sf_ot (hG.ot_v c hcM)] at hy
  rw [hy]
  exact comp_dom_trans (lost_leaf_comp_dom hd) (index_comp_dom (hG.ot_v c hcM))

end Ytosk.HUACPath
