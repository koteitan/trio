/-
An unchanged return child bounds the parent value in the T2 source sum.
The certificate contains only row/parent/child facts. No HUAC hypothesis or
new global residual is assumed.
-/
import Ytosk.V3T2SrcLeaf
import Ytosk.V3HUACCopy
import Ytosk.V3VAnc

namespace Ytosk.T2SrcPrefix
open T

/-- A return child strictly before a later sibling has the value of the
row-0/row-1 parent of i. Its next column remains inside the branch, so the
upgrade search agrees with that parent's search. -/
theorem earlier_return_value {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) {m i j d c : Nat}
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hd : d ∈ children M j) (hc : c ∈ children M j) (hdc : d < c)
    (hd1 : entry M 1 d = entry M 1 m)
    (hm2 : entry M 2 m = 0) (hd2 : entry M 2 d = 0) : ρ.v d = ρ.v m := by
  have hjp := (mem_children_iff.mp hj).2
  have hdp := (mem_children_iff.mp hd).2
  have hmlt := par_lt M 0 i m hmi
  have hij := (mem_children hj).1
  have hjd := (mem_children hd).1
  have hcN := (mem_children hc).2
  have him : i < M.length := by omega
  have hmnext : par M 0 (m + 1) = some m :=
    child_succ (anc0_of_par M 0 m i hmi) (Nat.ne_of_lt hmlt)
  have hmd : entry M 0 m < entry M 0 (m + 1) := by
    have := S.r0p (m + 1) m hmnext
    omega
  have hAjc := anc0_of_par M 0 j c (mem_children_iff.mp hc).2
  have hAdnext : Anc0 M j (d + 1) := anc_between hAjc (d + 1) (by omega) (by omega)
  have hcd : entry M 0 m < entry M 0 (d + 1) := by
    have := anc0_e0_lt hAdnext (by omega)
    have := S.r0p i m hmi
    have := S.r0p j i hjp
    omega
  have hp := HUACCopy.par1_return hmi hjp hdp (par1_entry_lt hm1) (e1_of_col hb) hd1
  have hu := HUACCopy.upg_return hmi hjp hdp (par1_entry_lt hm1) (e1_of_col hb) hd1
    hm2 hd2 (by omega) (by omega) hmd hcd
  rw [(hC d (by omega)).2, (hC m (by omega)).2]
  unfold vRhs
  rw [hd1, hd2, hm2, hp, hu]
  simp only [ite_true]

/-- The same return child is unchanged by the last-column drop, because
it has a later remaining sibling. Its o-value gives a strict bound on the
parent value, and hence on the new sum G_T. -/
theorem parent_lt_new_sum_of_earlier_return {M : Mat} {ρ τ : Valn}
    {rkT : Bool → Nat → Nat} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {x m i j d c : Nat}
    (hx : x + 1 = M.length)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) (hGT : Good3 (M.take x) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hd : d ∈ children M j) (hc : c ∈ children (M.take x) j) (hdc : d < c)
    (hd1 : entry M 1 d = entry M 1 m)
    (hm2 : entry M 2 m = 0) (hd2 : entry M 2 d = 0) :
    vOpt ρ (par M 1 i) < sumN ((children (M.take x) j).map τ.o) := by
  have hcM := (mem_children_take hc).2
  have hcx := (mem_children_take hc).1
  have hdx : d < x := by omega
  have hj2 : entry M 2 j ≠ 0 := by
    change (col M j).2.2 ≠ 0
    rw [hb]
    simp [bump]
  have hv := earlier_return_value S hC hmi hm1 hj hb hd hcM hdc hd1 hm2 hd2
  have ho := T0SeedSum.earlier_o_stable S hC hG hx hj2 hd hc hdc hT hRT
  have hdT : d ∈ children (M.take x) j := by
    rw [children_take, List.mem_filter]
    exact ⟨hd, by simpa using hdx⟩
  have hlt : ρ.v m < τ.o d := by
    obtain ⟨y, hy⟩ := o_psi_sub hC (mem_children hd).2
    rw [ho, ← hv, hy, sf_ot (hG.ot_v d (mem_children hd).2)]
    exact sub_lt _ _ _
  have hOT : ∀ t ∈ (children (M.take x) j).map τ.o, isOT t = true := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
    exact hGT.ot_o e (mem_children he).2
  rw [hm1]
  exact lt_of_lt_of_le hlt (T2SrcLeaf.mem_le_sumN hOT (List.mem_map.mpr ⟨d, hdT, rfl⟩))

/-- A structural return witness in the unchanged prefix rules out the
source absorption failure outright, at every cutoff. -/
theorem not_dropFail_of_earlier_return {M : Mat} {ρ τ : Valn}
    {rkT : Bool → Nat → Nat} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {x m i j d c : Nat}
    (hx : x + 1 = M.length)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) (hGT : Good3 (M.take x) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hd : d ∈ children M j) (hc : c ∈ children (M.take x) j) (hdc : d < c)
    (hd1 : entry M 1 d = entry M 1 m)
    (hm2 : entry M 2 m = 0) (hd2 : entry M 2 d = 0) :
    ¬ WfT2Abs.DropFail M ρ τ x i := by
  have hlt := parent_lt_new_sum_of_earlier_return S hC hG hx hT hRT hGT
    hmi hm1 hj hb hd hc hdc hd1 hm2 hd2
  have hjx : j < x := Nat.lt_trans (mem_children hc).1 (mem_children_take hc).1
  have hix : i < x := Nat.lt_trans (mem_children hj).1 hjx
  have hjT : j ∈ children (M.take x) i := by
    rw [children_take, List.mem_filter]
    exact ⟨hj, by simpa using hjx⟩
  have hbT : col (M.take x) j = bump (M.take x) i := by
    rw [col_take M hjx, bump_take M hix, hb]
  have hle := T2SrcLeaf.child_sum_le_bumpW hGT hjT hbT
  have hpW := lt_of_lt_of_le hlt hle
  intro hf
  apply hf
  intro q hq _ hnT _
  exact False.elim (hnT (lt_of_le_of_lt
    (le_trans (summands_le_head (vOpt_ot hG (by omega)) q hq) (head_le_self _)) hpW))

/-- The return equality only needs the next column to stay in the branch;
the return child itself need not have a later sibling. -/
theorem return_value_of_next {M : Mat} {ρ : Valn} (hR0 : R0P M)
    (hC : Cons M ρ) {m i j c : Nat}
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hjp : par M 0 j = some i) (hb1 : entry M 1 j = entry M 1 i)
    (hcp : par M 0 c = some j) (hcN : c + 1 < M.length)
    (hc1 : entry M 1 c = entry M 1 m)
    (hm2 : entry M 2 m = 0) (hc2 : entry M 2 c = 0)
    (hnext : entry M 0 m < entry M 0 (c + 1)) : ρ.v c = ρ.v m := by
  have hmlt := par_lt M 0 i m hmi
  have hij := par_lt M 0 j i hjp
  have hjc := par_lt M 0 c j hcp
  have hmnext := child_succ (anc0_of_par M 0 m i hmi) (Nat.ne_of_lt hmlt)
  have hmd : entry M 0 m < entry M 0 (m + 1) := by
    have := hR0 (m + 1) m hmnext
    omega
  have hp := HUACCopy.par1_return hmi hjp hcp (par1_entry_lt hm1) hb1 hc1
  have hu := HUACCopy.upg_return hmi hjp hcp (par1_entry_lt hm1) hb1 hc1
    hm2 hc2 (by omega) hcN hmd hnext
  rw [(hC c (by omega)).2, (hC m (by omega)).2]
  unfold vRhs
  rw [hc1, hc2, hm2, hp, hu]
  simp only [ite_true]

/-- A non-lost return keeps the old parent value even if its o-value
changes, since its own upgrade and its parent's protected value agree. -/
theorem nonlost_return_value {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat}
    (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) {x m i j c : Nat}
    (hx : x + 1 = M.length) (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i) (hc : c ∈ children M j)
    (hcN : c + 1 < x) (hc1 : entry M 1 c = entry M 1 m)
    (hm2 : entry M 2 m = 0) (hc2 : entry M 2 c = 0)
    (hnext : entry M 0 m < entry M 0 (c + 1)) : τ.v c = ρ.v m := by
  have hmlt := par_lt M 0 i m hmi
  have hij := (mem_children hj).1
  have hjc := (mem_children hc).1
  have hmT : m < x := by omega
  have hiT : i < x := by omega
  have hjT : j < x := by omega
  have hcT : c < x := by omega
  have hret : τ.v c = τ.v m := by
    apply return_value_of_next (R0P_take S.r0p x) hT
      (by rw [par_take M 0 i hiT]; exact hmi)
      (by rw [par_take M 1 i hiT]; exact hm1)
      (by rw [par_take M 0 j hjT]; exact (mem_children_iff.mp hj).2)
      (by rw [entry_take M 1 hjT, entry_take M 1 hiT]; exact e1_of_col hb)
      (by rw [par_take M 0 c hcT]; exact (mem_children_iff.mp hc).2)
      (by simp only [List.length_take]; omega)
      (by rw [entry_take M 1 hcT, entry_take M 1 hmT]; exact hc1)
      (by rw [entry_take M 2 hmT]; exact hm2)
      (by rw [entry_take M 2 hcT]; exact hc2)
      (by rw [entry_take M 0 hmT, entry_take M 0 hcN]; exact hnext)
  have hiChild : i ∈ children (M.take x) m :=
    mem_children_iff.mpr ⟨by simp only [List.length_take]; omega, by rw [par_take M 0 i hiT]; exact hmi⟩
  exact hret.trans (T0SeedOutside.v_stable_zero_child S hC hG hx hmT hm2 hT hRT hiChild)

/-- A child whose new index dominates the old parent value leaves no
source absorption window. Used with the proved structural return equality. -/
theorem not_dropFail_of_parent_le_child {M : Mat} {ρ τ : Valn}
    (hG : Good3 M ρ) {x i j c : Nat} (hi : i < x) (hx : x ≤ M.length)
    (hT : Cons (M.take x) τ) (hGT : Good3 (M.take x) τ)
    (hj : j ∈ children (M.take x) i) (hb : col (M.take x) j = bump (M.take x) i)
    (hc : c ∈ children (M.take x) j)
    (hV : vOpt ρ (par M 1 i) ≤ τ.v c) : ¬ WfT2Abs.DropFail M ρ τ x i := by
  obtain ⟨y, hy⟩ := o_psi_sub hT (mem_children hc).2
  rw [sf_ot (hGT.ot_v c (mem_children hc).2)] at hy
  have hpO : vOpt ρ (par M 1 i) < τ.o c := by
    rw [hy]
    exact lt_of_le_of_lt hV (sub_lt _ _ _)
  have hGo : ∀ t ∈ (children (M.take x) j).map τ.o, isOT t = true := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hGT.ot_o d (mem_children hd).2
  have hsum := T2SrcLeaf.mem_le_sumN hGo (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hpW := lt_of_lt_of_le hpO (le_trans hsum (T2SrcLeaf.child_sum_le_bumpW hGT hj hb))
  intro hf
  apply hf
  intro q hq _ hnT _
  exact False.elim (hnT (lt_of_le_of_lt
    (le_trans (summands_le_head (vOpt_ot hG (by omega)) q hq) (head_le_self _)) hpW))

/-- The other structural certificate is a row-1 path from the protected
parent to the new child. Ordinary value monotonicity suffices here. -/
theorem not_dropFail_of_row1_descendant {M : Mat} {ρ τ : Valn}
    {rkT : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {x m i j c : Nat} (hx : x + 1 = M.length) (hi : i < x)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) (hGT : Good3 (M.take x) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children (M.take x) i) (hb : col (M.take x) j = bump (M.take x) i)
    (hc : c ∈ children (M.take x) j) (hpath : TRIO.le1 (M.take x) m c) :
    ¬ WfT2Abs.DropFail M ρ τ x i := by
  have hmiLt := par_lt M 0 i m hmi
  have hmT : m < x := by omega
  have hm2 : entry M 2 m = 0 := by
    have hz := S.z2 m
    by_contra h
    exact no_par1_of_e2 S.z1c (by omega) (by omega) hm1
  have hiChild : i ∈ children (M.take x) m :=
    mem_children_iff.mpr ⟨by simp only [List.length_take]; omega,
      by rw [par_take M 0 i hi]; exact hmi⟩
  have hv := T0SeedOutside.v_stable_zero_child S hC hG hx hmT hm2 hT hRT hiChild
  have hle := v_le_of_le1 (vMono1_of hT hGT) (c + 1) m c (Nat.lt_succ_self c) hpath
  apply not_dropFail_of_parent_le_child hG hi (by omega) hT hGT hj hb hc
  rw [hm1]
  change ρ.v m ≤ τ.v c
  rw [← hv]
  exact hle

end Ytosk.T2SrcPrefix
