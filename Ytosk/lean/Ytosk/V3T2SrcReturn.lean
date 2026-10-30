/- An actual ancestor upgrade transfers back to an ancestor with the
same row-1 value and parent. No condition on the later next column is
needed: candidate targets have one fixed row-0 depth. -/
import Ytosk.V3T2SrcOrigins

namespace Ytosk.T2SrcReturn
open T

private theorem find_unique {l : List Nat} {p : Nat → Bool} {k : Nat}
    (hm : k ∈ l) (hk : p k = true) (hu : ∀ r ∈ l, p r = true → r = k) :
    l.find? p = some k := by
  induction l with
  | nil => simp at hm
  | cons a l ih =>
    cases ha : p a with
    | true =>
      have he := hu a (by simp) ha
      simp only [List.find?_cons, he, hk]
    | false =>
      have hml : k ∈ l := by
        rcases List.mem_cons.mp hm with he | he
        · rw [he, ha] at hk; cases hk
        · exact he
      simp only [List.find?_cons, ha]
      exact ih hml (fun r hr => hu r (List.mem_cons_of_mem _ hr))

/-- The ancestor upgrade of a returning descendant is also the ancestor's
upgrade. The ancestor has a protected next column in its own subtree. -/
theorem upgrade_back {M : Mat} (hR0 : R0P M) {a c k : Nat}
    (ha2 : entry M 2 a = 0) (hac : Anc0 M a c) (haclt : a < c)
    (hc1 : entry M 1 c = entry M 1 a) (hp : par M 1 c = par M 1 a)
    (hu : upg M c = some k) (hkc : k < c) : upg M a = some k := by
  obtain ⟨p, hcp, hkp, hcol, hcase⟩ := upg_spec hu
  have hpa : par M 1 a = some p := hp.symm.trans hcp
  obtain ⟨p', hcp', hkp0⟩ := upg_target_par0 hR0 hu
  rw [hcp] at hcp'; cases hcp'
  have hpc := par_lt M 1 a p hpa
  have hAkc : Anc0 M k c := by
    rcases hcase with he | ⟨hA, _⟩
    · omega
    · exact hA
  have hak : a ≠ k := by
    intro he
    have hz := e2_of_col hcol
    rw [← he, ha2] at hz
    omega
  have hAka : Anc0 M k a := by
    rcases anc0_total hAkc hac with h | h
    · exact h
    · have hh := anc0_par h hak hkp0
      have := hh.le
      omega
  have hka : k < a := by have := hAka.le; omega
  have hAnext := child_succ hac (Nat.ne_of_lt haclt)
  have hanext0 := hR0 (a + 1) a hAnext
  have hka0 := anc0_e0_lt hAka (Nat.ne_of_lt hka)
  have hpa0 := anc0_e0_lt (anc0_of_par M 1 p a hpa) (Nat.ne_of_lt hpc)
  have hcN := upg_succ_lt hu
  have ha1 := par1_entry_lt hpa
  have hnext : ¬ (par M 1 (a + 1) = some p ∧
      col M (a + 1) = (entry M 0 p + 1, entry M 1 a, entry M 2 p + 1)) := by
    rintro ⟨_, he⟩
    have hh := e0_of_col he
    omega
  rw [hc1] at hcol
  unfold upg
  rw [if_neg (by omega), hpa]
  simp only
  rw [if_neg hnext, upgClimb_find]
  apply find_unique (mem_ancL_of_anc hAka (Nat.ne_of_lt hka))
  · exact decide_eq_true ⟨hkp, hcol, by omega⟩
  · intro r hr hpr
    have hpred : par M 1 r = some p ∧
        col M r = (entry M 0 p + 1, entry M 1 a, entry M 2 p + 1) ∧
        entry M 0 r < entry M 0 (a + 1) := of_decide_eq_true hpr
    have hr0 := e0_of_col hpred.2.1
    have hk0 := e0_of_col hcol
    exact anc0_eq_of_e0 (anc0_of_mem_ancL hr) hAka (by omega)

/-- Cons turns the transferred upgrade and common parent into the exact
old value equality, even if the descendant's next column exits the copy. -/
theorem value_back {M : Mat} {ρ : Valn} (S : SInv M) (hC : Cons M ρ)
    {a c k : Nat} (ha2 : entry M 2 a = 0) (hac : Anc0 M a c) (haclt : a < c)
    (hc1 : entry M 1 c = entry M 1 a) (hp : par M 1 c = par M 1 a)
    (hu : upg M c = some k) (hkc : k < c) : ρ.v c = ρ.v a := by
  have hau := upgrade_back S.r0p ha2 hac haclt hc1 hp hu hkc
  have hcN : c < M.length := by have := upg_succ_lt hu; omega
  have haN : a < M.length := by omega
  have hc2 : entry M 2 c = 0 := by have := S.z2 c; have := (upg_e12 hu).2; omega
  exact WfHUACDeep.value_eq_of_same_rhs hC hcN haN hc1 hc2 ha2 hp (hu.trans hau.symm)


/-- The lost child returns to the old value at the same row on the
parent chain, even when the last column exits that ancestor's subtree. -/
theorem lost_value_return {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) (hB : Bad2 M)
    {x a m i j : Nat} (hx : x + 1 = M.length) (hx2 : entry M 2 x = 1)
    (ha : par M 0 x ≠ some (x - 1) ∨ par M 1 x ≠ some (x - 1))
    (hT : Cons (M.take x) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hc : x - 1 ∈ children M j) (hA : WfHUACDeep.Up1 M a m)
    (hc1 : entry M 1 (x - 1) = entry M 1 a) : ρ.v (x - 1) = ρ.v a := by
  obtain ⟨_, k, p, g, hu, hkc, hp, hg, hpb, hleaf, ho, hoT⟩ :=
    T2SrcLeaf.source_leaf_shapes C hB hx hx2 ha hT
  have him : i < M.length := Nat.lt_trans (mem_children hj).1 (mem_children hj).2
  have hm2 : entry M 2 m = 0 := by
    by_contra hn
    exact no_par1_of_e2 C.S.z1c him (by have := C.S.z2 m; omega) hm1
  have ha2 := WfHUACDeep.up1_e2 C.S hA hm2
  have hAc : Anc0 M a (x - 1) := (WfHUACDeep.up1_anc0 hA).trans
    ((anc0_of_par M 0 m i hmi).trans
      ((anc0_of_par M 0 i j (mem_children_iff.mp hj).2).trans
        (anc0_of_par M 0 j (x - 1) (mem_children_iff.mp hc).2)))
  have haclt : a < x - 1 := by
    have ham := WfHUACDeep.up1_le hA
    have hmi' := par_lt M 0 i m hmi
    have hij := (mem_children hj).1
    have hjc := (mem_children hc).1
    omega
  have hpar := T2SrcQuiet.par1_deep_return hmi hm1 hj hb hc hA hc1
  exact value_back C.S C.I.cons ha2 hAc haclt hc1 hpar hu hkc

/-- An origin of a source-parent summand upgrades to a strict ancestor. -/
theorem origin_is_ancestor {M : Mat} (S : SInv M) {i m b k : Nat}
    (hi : i < M.length) (hm : par M 1 i = some m) (h : WfHUACDeep.Up1 M b m)
    (hu : upg M b = some k) : k < b ∧ Anc0 M k b := by
  obtain ⟨w, hwN, hp⟩ := T2SrcOrigins.chain_parent_has_child hi hm h
  have hbw := par_lt M 1 w b hp
  obtain ⟨_, _, _, _, he | ⟨hA, hkb⟩⟩ := upg_spec hu
  · have hn : upg M b = some (b + 1) := by simpa only [he] using hu
    have hh := leaf_of_upg_next S.r0p hn w (anc0_of_par M 1 b w hp)
    omega
  · exact ⟨hkb, hA⟩

/-- Every old target bump grandchild is the value of an ancestor on the
same source-parent chain. This is the deep return theorem at its real
upgrade, rather than an assumed copy shape. -/
theorem target_grandchild_value {M : Mat} {ρ : Valn}
    (hX : SInvX M) (hJ : RowJ M) (hC : Cons M ρ)
    {i m b k j d : Nat} (hi : i < M.length) (hm : par M 1 i = some m)
    (hbm : WfHUACDeep.Up1 M b m) (hu : upg M b = some k)
    (hj : j ∈ children M k) (hb : col M j = bump M k) (hd : d ∈ children M j) :
    ∃ a, WfHUACDeep.Up1 M a m ∧ entry M 1 a = entry M 1 d ∧ ρ.v d = ρ.v a := by
  have S := hX.toSInv
  obtain ⟨hkb, hAkb⟩ := origin_is_ancestor S hi hm hbm hu
  have hmN : m < M.length := Nat.lt_trans (par_lt M 1 i m hm) hi
  have hbN : b < M.length := by have := WfHUACDeep.up1_le hbm; omega
  have hm2 : entry M 2 m = 0 := by
    by_contra hn
    exact no_par1_of_e2 S.z1c hi (by have := S.z2 m; omega) hm
  have hb2 := WfHUACDeep.up1_e2 S hbm hm2
  obtain ⟨p, hbp, hkp0⟩ := upg_target_par0 S.r0p hu
  have hpN : p < M.length := Nat.lt_trans (par_lt M 1 b p hbp) hbN
  have hp2 : entry M 2 p = 0 := by
    by_contra hn
    exact no_par1_of_e2 S.z1c hbN (by have := S.z2 p; omega) hbp
  have htop := S.uat b k hu (by omega)
  have hdrow : entry M 1 d ≤ entry M 1 p := by
    have hr1 := hX.r1s k p hkp0
    by_contra hn
    obtain ⟨_, _, _, hlast⟩ := hX.loc.2.2.2 k j d hj hb hd (by omega)
    simp only [topped, hlast, hb, decide_true] at htop
    contradiction
  obtain ⟨a, hAp, harow⟩ := T2SrcQuiet.parent_at_row hX hdrow
  have hd2 := T2SrcQuiet.bump_grandchild_e2_zero hX hJ hj hb hd
  have ha2 := WfHUACDeep.up1_e2 S hAp hp2
  have hGAb : GA M b k := ⟨hAkb, fun _ j0 hj0 hb0 => S.uab b k hu (by omega) j0 hj0 hb0⟩
  have hk2 : entry M 2 k ≠ 0 := by have := upg_target_e2 hu; omega
  have hGBd : GB M b d := ⟨k, j, hGAb, hk2, hj, hb,
    anc0_of_par M 0 j d (mem_children_iff.mp hd).2⟩
  have hdb : d < b := gb_lt S hbN hb2 hGBd d (Anc0.refl d)
  obtain ⟨hpar, hup⟩ := WfHUACDeep.deep_return S hbN hu hkb hkp0 hj hb hd hdb hAp harow.symm hd2 ha2
  have haN : a < M.length := by have := WfHUACDeep.up1_le hAp; omega
  have hval := WfHUACDeep.value_eq_of_same_rhs hC (mem_children hd).2 haN harow.symm hd2 ha2 hpar hup
  exact ⟨a, WfHUACDeep.up1_trans hAp (WfHUACDeep.up1_trans (.step hbp (.refl _)) hbm), harow, hval⟩


/-- The deterministic row-1 parent chain is linearly ordered by ancestry. -/
theorem chain_comparable {M : Mat} {a b m : Nat}
    (hA : WfHUACDeep.Up1 M a m) (hB : WfHUACDeep.Up1 M b m) :
    WfHUACDeep.Up1 M a b ∨ WfHUACDeep.Up1 M b a := by
  induction hA generalizing b with
  | refl => exact Or.inr hB
  | @step m p hp tail ih =>
    cases hB with
    | refl => exact Or.inl (.step hp tail)
    | step hpB tailB =>
      rw [hp] at hpB
      cases hpB
      exact ih tailB

theorem chain_strict_row {M : Mat} {a b : Nat}
    (h : WfHUACDeep.Up1 M a b) (hne : a ≠ b) : entry M 1 a < entry M 1 b := by
  cases h with
  | refl => exact False.elim (hne rfl)
  | step hp tail =>
    have hle := WfHUACDeep.up1_e1_le tail
    have hlt := par1_entry_lt hp
    omega

/-- Row order selects the ancestry direction on one row-1 chain. -/
theorem chain_by_row {M : Mat} {a b m : Nat}
    (hA : WfHUACDeep.Up1 M a m) (hB : WfHUACDeep.Up1 M b m)
    (hrow : entry M 1 a ≤ entry M 1 b) : WfHUACDeep.Up1 M a b := by
  rcases chain_comparable hA hB with h | h
  · exact h
  · by_cases he : a = b
    · subst b; exact .refl _
    · have hh := chain_strict_row h (Ne.symm he)
      omega

theorem chain_value_le {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
    {a b : Nat} (h : WfHUACDeep.Up1 M a b) (hb : b < M.length) : ρ.v a ≤ ρ.v b := by
  revert hb
  induction h with
  | refl => intro _; exact le_refl _
  | @step b p hp tail ih =>
    intro hb
    have hpN : p < M.length := Nat.lt_trans (par_lt M 1 b p hp) hb
    have h1 : entry M 1 b ≠ 0 := by have := par1_entry_lt hp; omega
    exact le_trans (ih hpN) (v_par1_le hC hG hb h1 hp)

/-- A strict ancestor on the row-1 chain is at or above the immediate parent. -/
theorem chain_parent_tail {M : Mat} {a b : Nat}
    (h : WfHUACDeep.Up1 M a b) (hne : a ≠ b) :
    ∃ p, par M 1 b = some p ∧ WfHUACDeep.Up1 M a p := by
  cases h with
  | refl => exact False.elim (hne rfl)
  | step hp tail => exact ⟨_, hp, tail⟩


/-- An old target child cannot have its o-value strictly between the new
and old lost-child values. Both indices are values on one parent chain. -/
theorem old_target_child_gap {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) (hB : Bad2 M)
    {x m i j b k j0 d : Nat} (hx : x + 1 = M.length) (hx2 : entry M 2 x = 1)
    (ha : par M 0 x ≠ some (x - 1) ∨ par M 1 x ≠ some (x - 1))
    (hT : Cons (M.take x) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i) (hc : x - 1 ∈ children M j)
    (hrow : entry M 1 (x - 1) ≤ entry M 1 m)
    (hbm : WfHUACDeep.Up1 M b m) (hu : upg M b = some k)
    (hj0 : j0 ∈ children M k) (hb0 : col M j0 = bump M k) (hd : d ∈ children M j0) :
    ρ.o d < τ.o (x - 1) ∨ ρ.o (x - 1) ≤ ρ.o d := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
  obtain ⟨a, hA, harow⟩ := T2SrcQuiet.parent_at_row hX hrow
  have hca := lost_value_return C hB hx hx2 ha hT hmi hm1 hj hb hc hA harow.symm
  have hpar := T2SrcQuiet.par1_deep_return hmi hm1 hj hb hc hA harow.symm
  obtain ⟨_, k', p', g', hu', hkc', hp', hg', hpb', hleaf, ho, hoT⟩ :=
    T2SrcLeaf.source_leaf_shapes C hB hx hx2 ha hT
  have hiN : i < M.length := Nat.lt_trans (mem_children hj).1 (mem_children hj).2
  obtain ⟨ad, hAd, hadrow, hvd⟩ := target_grandchild_value hX hJ C.I.cons hiN hm1 hbm hu hj0 hb0 hd
  obtain ⟨y, hy⟩ := o_psi_sub C.I.cons (mem_children hd).2
  rw [sf_ot (C.I.good.ot_v d (mem_children hd).2)] at hy
  have hmN := Nat.lt_trans (par_lt M 1 i m hm1) hiN
  have haN : a < M.length := by have := WfHUACDeep.up1_le hA; omega
  have hadN : ad < M.length := by have := WfHUACDeep.up1_le hAd; omega
  by_cases hlow : entry M 1 d < entry M 1 (x - 1)
  · left
    have hpath := chain_by_row hAd hA (by omega)
    have hne : ad ≠ a := by intro he; rw [he] at hadrow; omega
    obtain ⟨p, hpa, hadp⟩ := chain_parent_tail hpath hne
    have hpN := Nat.lt_trans (par_lt M 1 a p hpa) haN
    have hval := chain_value_le C.I.cons C.I.good hadp hpN
    have hidx : ρ.v ad < add (ρ.v p) one := lt_of_le_of_lt hval (lt_add_principal z z _)
    rw [hy, hvd, hoT, hpar, hpa]
    exact psi_lt_psi_z_iff.mpr (Or.inl hidx)
  · right
    have hpath := chain_by_row hA hAd (by omega)
    have hval := chain_value_le C.I.cons C.I.good hpath hadN
    rw [ho, hca, hy, hvd]
    exact psi_le_psi_any hval


/-- The earlier-branch witness is impossible when the changing child is
the lost penultimate leaf. Apply the replacement parser to its G sum. -/
theorem lost_branch_not_between {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) (hB : Bad2 M)
    {r L m i j b k j0 : Nat} (hx : r + L + 1 = M.length)
    (hr : par M 2 (r + L) = some r) (hx2 : entry M 2 (r + L) = 1)
    (ha : par M 0 (r + L) ≠ some (r + L - 1) ∨ par M 1 (r + L) ≠ some (r + L - 1))
    (hT : Cons (M.take (r + L)) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hc : r + L - 1 ∈ children M j) (hce : τ.o (r + L - 1) ≠ ρ.o (r + L - 1))
    (hrow : entry M 1 (r + L - 1) ≤ entry M 1 m)
    (hbm : WfHUACDeep.Up1 M b m) (hu : upg M b = some k)
    (hj0 : j0 ∈ children M k) (hb0 : col M j0 = bump M k)
    (hLower : ¬ bumpTerm M ρ k j0 < bumpTerm (M.take (r + L)) τ i j)
    (hUpper : bumpTerm M ρ k j0 < bumpTerm M ρ i j) : False := by
  classical
  have hGT : Good3 (M.take (r + L)) τ := by
    have he : M.length - 1 = r + L := by omega
    rw [← he] at hT ⊢
    exact good3_take_any (Inv3W.ofV2 C.S C.I) C.toW (by omega) hT
  have hRT : Rk (M.take (r + L)) rk := rk_take (by omega) C.I.rank
    (by have := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
        simpa only [show M.length - 1 = r + L from by omega] using this)
  have hcx : r + L - 1 < r + L := by have := par_lt M 2 (r + L) r hr; omega
  have hjx : j < r + L := Nat.lt_trans (mem_children hc).1 hcx
  have hix : i < r + L := Nat.lt_trans (mem_children hj).1 hjx
  have hnx := T2SrcLeaf.last_not_child_of_bump C hx hr hj hb
  obtain ⟨K, hK, hKT, hfix, hOldSum, hNewSum⟩ := T2SrcLeaf.changed_bump_child_last C.S
    C.I.cons C.I.good hx hb hnx hc hce hT hRT hGT
  have hbT : col (M.take (r + L)) j = bump (M.take (r + L)) i := by
    rw [col_take M hjx, bump_take M hix, hb]
  let G0 := sumN ((children M j0).map ρ.o)
  let G := sumN ((children M j).map ρ.o)
  let G' := sumN ((children (M.take (r + L)) j).map τ.o)
  have h0 : isOT G0 = true := isOT_sumN _ (by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact C.I.good.ot_o d (mem_children hd).2)
  have hG : isOT G = true := isOT_sumN _ (by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact C.I.good.ot_o d (mem_children hd).2)
  have hG' : isOT G' = true := isOT_sumN _ (by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hGT.ot_o d (mem_children hd).2)
  have hbG : bumpTerm M ρ k j0 = omega G0 := by simp only [bumpTerm, if_pos hb0]; rfl
  have hbOld : bumpTerm M ρ i j = omega G := by simp only [bumpTerm, if_pos hb]; rfl
  have hbNew : bumpTerm (M.take (r + L)) τ i j = omega G' := by
    simp only [bumpTerm, if_pos hbT]; rfl
  rw [hbG, hbOld] at hUpper
  rw [hbG, hbNew] at hLower
  have hold : G0 < G := T2SrcRounding.omega_lt_reflect h0 hG hUpper
  have hnew : ¬ G0 < G' := fun h => hLower (omega_lt_omega h0 hG' h)
  obtain ⟨_, ku, p, g, hup, hku, hp, hg, hpb, hleaf, ho, hoT⟩ :=
    T2SrcLeaf.source_leaf_shapes C hB hx hx2 ha hT
  change G0 < sumN ((children M j).map ρ.o) at hold
  rw [hOldSum, ho] at hold
  change ¬ G0 < sumN ((children (M.take (r + L)) j).map τ.o) at hnew
  rw [hNewSum, hoT] at hnew
  obtain ⟨s, hs, hsn, hso⟩ := T2SrcRounding.summand_in_replacement_window
    (sumN (K.map ρ.o)) G0 hnew hold
  have hsing : ∀ t ∈ (children M j0).map ρ.o, Single t := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact single_o C.I.cons C.I.good (mem_children hd).2
  have hslist := summands_sumN_sub hsing s hs
  obtain ⟨d, hd, he⟩ := List.mem_map.mp hslist
  have hgap := old_target_child_gap C hB hx hx2 ha hT hmi hm1 hj hb hc hrow hbm hu hj0 hb0 hd
  rw [he] at hgap
  rcases hgap with hgap | hgap
  · exact hsn (by rwa [hoT] at hgap)
  · exact not_lt_of_ge hgap (by simpa only [ho] using hso)


/-- In case (a), every actual failure must use a changing child strictly
before x-1. The lost-leaf case has been eliminated without any new guard. -/
theorem source_failed_nonlost {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) (hB : Bad2 M)
    {r L i : Nat} (hx : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hx2 : entry M 2 (r + L) = 1)
    (ha : par M 0 (r + L) ≠ some (r + L - 1) ∨ par M 1 (r + L) ≠ some (r + L - 1))
    (hi : i < r + L) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hT : Cons (M.take (r + L)) τ) (hf : WfT2Abs.DropFail M ρ τ (r + L) i) :
    ∃ m j c, par M 0 i = some m ∧ par M 1 i = some m ∧
      j ∈ children M i ∧ col M j = bump M i ∧ c ∈ children M j ∧
      c < r + L - 1 ∧ τ.o c ≠ ρ.o c := by
  obtain ⟨m, j, c, b, k, j0, hmi, hm1, hj, hb, hc, hcx, hce, hbm, hu, hki,
    hj0, hb0, hj0i, hLower, hUpper⟩ := T2SrcOrigins.source_failed_earlier_bump C hx hr hi h1 h2 hT hf
  by_cases he : c = r + L - 1
  · subst c
    have hGT : Good3 (M.take (r + L)) τ := by
      have he : M.length - 1 = r + L := by omega
      rw [← he] at hT ⊢
      exact good3_take_any (Inv3W.ofV2 C.S C.I) C.toW (by omega) hT
    have hRT : Rk (M.take (r + L)) rk := rk_take (by omega) C.I.rank
      (by have := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
          simpa only [show M.length - 1 = r + L from by omega] using this)
    have hrow := T2SrcQuiet.failed_drop_grandchild_row_le C.S C.I.cons C.I.good
      hx hT hRT hGT hmi hm1 hj hb hc hcx hf
    exact False.elim (lost_branch_not_between C hB hx hr hx2 ha hT hmi hm1 hj hb hc hce hrow
      hbm hu hj0 hb0 hLower hUpper)
  · exact ⟨m, j, c, hmi, hm1, hj, hb, hc, by omega, hce⟩

/-- Under a row-2-positive source, an existing lost grandchild forces any
changing bump-grandchild call to be that last column. -/
theorem changed_child_is_lost {M : Mat} {ρ τ : Valn}
    {rkT : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {x i j j' c : Nat} (hx : x + 1 = M.length) (h2 : entry M 2 i ≠ 0)
    (hj : j ∈ children M i) (hb : col M j = bump M i) (hcLast : x - 1 ∈ children M j)
    (hj' : j' ∈ children M i) (hc : c ∈ children M j') (hcx : c < x)
    (hce : τ.o c ≠ ρ.o c) (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) :
    c = x - 1 := by
  have hlastx : x - 1 < x := by have := (mem_children hcLast).1; omega
  have hjx : j < x := Nat.lt_trans (mem_children hcLast).1 hlastx
  have hjT : j ∈ children (M.take x) i := mem_take_children hj hjx
  have hch : ChgX M x true c := by
    by_contra hn
    exact hce ((chg_off hx hC hG hT hRT c hcx).1 hn)
  have he : j' = j := by
    rcases lt_trichotomy j' j with hlt | he | hgt
    · exact False.elim (chg_only_last hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab
        h2 hj' hjT hlt hch (anc0_of_par M 0 j' c (mem_children_iff.mp hc).2))
    · exact he
    · have hless := kid_lt_x (mem_children_iff.mp hj).2 (mem_children_iff.mp hj').2 hgt
        (mem_children_iff.mp hcLast).2
      have hjc := (mem_children hc).1
      omega
  subst j'
  by_contra hn
  have hcl : c < x - 1 := by omega
  have hj2 : entry M 2 j ≠ 0 := by have := e2_of_col hb; omega
  exact hce (T0SeedSum.earlier_o_stable S hC hG hx hj2 hc
    (mem_take_children hcLast hlastx) hcl hT hRT)

/-- The full lost-grandchild part of (a), for every consistent prefix
valuation, follows from the existing context. -/
theorem not_dropFail_of_lost_grandchild {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) (hB : Bad2 M)
    {r L i j : Nat} (hx : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hx2 : entry M 2 (r + L) = 1)
    (ha : par M 0 (r + L) ≠ some (r + L - 1) ∨ par M 1 (r + L) ≠ some (r + L - 1))
    (hi : i < r + L) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hT : Cons (M.take (r + L)) τ)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hcLast : r + L - 1 ∈ children M j) : ¬ WfT2Abs.DropFail M ρ τ (r + L) i := by
  intro hf
  obtain ⟨m, j', c, _, _, hj', _, hc, hcl, hce⟩ := source_failed_nonlost C hB hx hr hx2 ha hi h1 h2 hT hf
  have hRT : Rk (M.take (r + L)) rk := rk_take (by omega) C.I.rank
    (by have := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
        simpa only [show M.length - 1 = r + L from by omega] using this)
  have he := changed_child_is_lost C.S C.I.cons C.I.good hx h2 hj hb hcLast hj' hc
    (by omega) hce hT hRT
  omega

end Ytosk.T2SrcReturn
