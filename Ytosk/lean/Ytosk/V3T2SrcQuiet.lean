/- A lower return can pass through several row-1 parents whose upgrades
are absent. These local certificates do not assert a new matrix invariant. -/
import Ytosk.V3T2SrcIndex
import Ytosk.WfHUACDeep

namespace Ytosk.T2SrcQuiet
open T

/-- Row-1 parent steps at which the value uses the increment one. -/
inductive QuietParents (M : Mat) : Nat → Nat → Prop
  | refl (a : Nat) : QuietParents M a a
  | step {m p a : Nat} (hp : par M 1 m = some p) (hu : upg M m = none)
      (tail : QuietParents M a p) : QuietParents M a m

theorem quiet_up1 {M : Mat} {a m : Nat} (h : QuietParents M a m) :
    WfHUACDeep.Up1 M a m := by
  induction h with
  | refl => exact .refl _
  | step hp _ _ ih => exact .step hp ih

/-- Adding one at a column with no upgrade cannot raise its leading index. -/
theorem no_upgrade_index_le {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {m : Nat} (hm : m < M.length)
    (hu : upg M m = none) (hm2 : entry M 2 m = 0) :
    lev (ρ.v m) ≤ lev (vOpt ρ (par M 1 m)) := by
  by_cases h10 : entry M 1 m = 0
  · rw [v_z_of_e1 hC hm h10]
    exact z_le _
  · have hv := (hC m hm).2
    unfold vRhs at hv
    rw [if_neg h10, if_pos hm2, hu] at hv
    change ρ.v m = sf (add (vOpt ρ (par M 1 m)) one) at hv
    rw [sf_ot (isOT_add (vOpt_ot hG hm) isOT_one)] at hv
    rw [hv]
    rcases lev_add_cases (vOpt ρ (par M 1 m)) one with he | he
    · rw [he]
    · rw [he]
      exact z_le _

/-- A chain of absent upgrades preserves the index bound at its upper end.
The starting column is a row-1 parent, so next-column upgrades are excluded. -/
theorem quiet_parent_index_le {M : Mat} {ρ : Valn} (hX : SInvX M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {a m : Nat} (h : QuietParents M a m)
    {i : Nat} (hi : i < M.length) (hm : par M 1 i = some m) :
    lev (ρ.v m) ≤ vOpt ρ (par M 1 a) := by
  induction h generalizing i with
  | refl a => exact T2SrcIndex.row1_parent_index_le hX hJ hC hG hi hm
  | @step m p a hp hu tail ih =>
    have hmi := par_lt M 1 i m hm
    have hmN : m < M.length := by omega
    have hm2 : entry M 2 m = 0 := by
      by_contra hn
      exact no_par1_of_e2 hX.toSInv.z1c hi (by have := hX.toSInv.z2 m; omega) hm
    have hb := no_upgrade_index_le hC hG hmN hu hm2
    rw [hp] at hb
    exact le_trans hb (ih hmN hp)

/-- The row-1 search skips the entire chain above the lower return row. -/
theorem par1_deep_return {M : Mat} {a m i j c : Nat}
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hc : c ∈ children M j) (h : WfHUACDeep.Up1 M a m)
    (hc1 : entry M 1 c = entry M 1 a) : par M 1 c = par M 1 a := by
  have hmk := par1_entry_lt hm1
  have ham := WfHUACDeep.up1_e1_le h
  obtain ⟨S, hS, hSp⟩ := WfHUACDeep.up1_split h
  have hancc : ancL M c = j :: i :: (S ++ a :: ancL M a) := by
    rw [ancL_eq (mem_children_iff.mp hc).2, ancL_eq (mem_children_iff.mp hj).2,
      ancL_eq hmi, hS]
  rw [par1_find M c, hancc, hc1, par1_find M a]
  simp only [List.find?_cons]
  have hj1 := e1_of_col hb
  have hj' : ¬ entry M 1 j < entry M 1 a := by omega
  have hi' : ¬ entry M 1 i < entry M 1 a := by omega
  simp only [decide_eq_false hj', decide_eq_false hi']
  rw [WfHUACDeep.find_skip (fun s hs => decide_eq_false (by have := hSp s hs; omega))]
  simp

/-- A lost return to a lower row still dominates the old parent, provided
all intervening row-1 parents use the increment one. -/
theorem not_dropFail_of_lost_quiet_return {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) (hB : Bad2 M)
    {x a m i j : Nat} (hx : x + 1 = M.length) (hx2 : entry M 2 x = 1)
    (ha : par M 0 x ≠ some (x - 1) ∨ par M 1 x ≠ some (x - 1))
    (hT : Cons (M.take x) τ) (hGT : Good3 (M.take x) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hc : x - 1 ∈ children M j) (hq : QuietParents M a m)
    (hc1 : entry M 1 (x - 1) = entry M 1 a) :
    ¬ WfT2Abs.DropFail M ρ τ x i := by
  obtain ⟨_, k, p, g, hu, hkn, hp, hg, hpb, hleaf, ho, hoT⟩ :=
    T2SrcLeaf.source_leaf_shapes C hB hx hx2 ha hT
  have hpos : 0 < x := by
    obtain ⟨b, hb, _⟩ := upg_spec hu
    have := par_lt M 1 (x - 1) b hb
    omega
  have hcx : x - 1 < x := by omega
  have hjx : j < x := Nat.lt_trans (mem_children hc).1 hcx
  have hix : i < x := Nat.lt_trans (mem_children hj).1 hjx
  obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
  have hidx := quiet_parent_index_le hX hJ C.I.cons C.I.good hq (by omega) hm1
  have hpc := par1_deep_return hmi hm1 hj hb hc (quiet_up1 hq) hc1
  have hltidx : lev (ρ.v m) < add (vOpt ρ (par M 1 a)) one :=
    lt_of_le_of_lt hidx (lt_add_principal z z _)
  have hpO : ρ.v m < τ.o (x - 1) := by
    rw [hoT, hpc]
    cases hv : ρ.v m with
    | z => exact z_lt_psi _ _ _
    | psi b d e =>
      rw [hv] at hltidx
      exact psi_lt_psi_z_iff.mpr (Or.inl hltidx)
  have hcT : x - 1 ∈ children (M.take x) j := by
    rw [children_take, List.mem_filter]
    exact ⟨hc, by simpa using hcx⟩
  have hGo : ∀ t ∈ (children (M.take x) j).map τ.o, isOT t = true := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hGT.ot_o d (mem_children hd).2
  have hsum := T2SrcLeaf.mem_le_sumN hGo (List.mem_map.mpr ⟨x - 1, hcT, rfl⟩)
  have hjT : j ∈ children (M.take x) i := by
    rw [children_take, List.mem_filter]
    exact ⟨hj, by simpa using hjx⟩
  have hbT : col (M.take x) j = bump (M.take x) i := by
    rw [col_take M hjx, bump_take M hix, hb]
  have hpW := lt_of_lt_of_le hpO (le_trans hsum (T2SrcLeaf.child_sum_le_bumpW hGT hjT hbT))
  intro hf
  apply hf
  intro q hq _ hnT _
  rw [hm1] at hq
  exact False.elim (hnT (lt_of_le_of_lt
    (le_trans (summands_le_head (C.I.good.ot_v m (by have := par_lt M 0 i m hmi; omega)) q hq)
      (head_le_self _)) hpW))


/-- Removing only a final bump leaf cannot cause a source absorption failure.
The interval between consecutive omega powers has a single principal term. -/
theorem not_dropFail_of_omega_step {M : Mat} {ρ τ : Valn} {x i : Nat} {S : T}
    (hS : isOT S = true) (hM : bumpW M ρ i = omega (succ S))
    (hT : bumpW (M.take x) τ i = omega S) :
    ¬ WfT2Abs.DropFail M ρ τ x i := by
  intro hf
  apply hf
  intro q hq _ hnT hlt
  rw [hT] at hnT
  rw [hM] at hlt ⊢
  obtain ⟨s, b, h1, h2⟩ := omega_succ_form hS
  have he : q = omega S := by
    rw [h1] at hnT
    rw [show succ S = app S one from rfl, h2] at hlt
    have hq' := single_between (mem_summands hq) hnT hlt
    exact hq'.trans h1.symm
  rw [he]
  exact lhd_omega_succ hS

/-- If every surviving bump term agrees, deleting the last column is either
an equality or the consecutive-omega case. No assumption on its parent is used. -/
theorem not_dropFail_of_surviving_terms_eq {M : Mat} {ρ τ : Valn}
    {x i : Nat} (hx : x + 1 = M.length)
    (hGT : Good3 (M.take x) τ)
    (he : ∀ j ∈ children (M.take x) i,
      bumpTerm M ρ i j = bumpTerm (M.take x) τ i j) :
    ¬ WfT2Abs.DropFail M ρ τ x i := by
  let P := sumN (one :: (children (M.take x) i).map (bumpTerm (M.take x) τ i))
  have hP : isOT P = true := isOT_bumpP hGT i
  have hT : bumpW (M.take x) τ i = omega P := rfl
  have hmap : (children (M.take x) i).map (bumpTerm M ρ i) =
      (children (M.take x) i).map (bumpTerm (M.take x) τ i) :=
    List.map_congr_left he
  by_cases hxi : x ∈ children M i
  · have hb := T2SrcLeaf.bumpTerm_last (ρ := ρ) (i := i) hx
    have hM : bumpW M ρ i = omega (add P (bumpTerm M ρ i x)) := by
      unfold bumpW
      rw [children_split_x hx hxi, ← children_take, List.map_append, List.map_singleton,
        ← List.cons_append, sumN_snoc, hmap]
      have hbOT : isOT (bumpTerm M ρ i x) = true := by
        rw [hb]
        split <;> rfl
      rw [sf_ot (isOT_add hP hbOT)]
    by_cases hxb : col M x = bump M i
    · rw [hb, if_pos hxb, add_one_eq_succ hP] at hM
      exact not_dropFail_of_omega_step hP hM hT
    · rw [hb, if_neg hxb, add_z_right] at hM
      intro hf
      apply hf
      intro q _ _ hnT hlt
      rw [hM, ← hT] at hlt
      exact False.elim (hnT hlt)
  · have hch : children M i = children (M.take x) i := by
      symm
      rw [children_take, List.filter_eq_self]
      intro j hj
      have hN := (mem_children hj).2
      have hne : j ≠ x := fun h => hxi (h ▸ hj)
      simpa using (show j < x by omega)
    have hM : bumpW M ρ i = bumpW (M.take x) τ i := by
      unfold bumpW
      rw [hch, hmap]
    intro hf
    apply hf
    intro q _ _ hnT hlt
    exact False.elim (hnT (hM ▸ hlt))


/-- A genuine failed absorption changes an already present bump branch.
The extra last-column contribution alone was discharged above. -/
theorem changed_branch_of_dropFail {M : Mat} {ρ τ : Valn} {x i : Nat}
    (hx : x + 1 = M.length) (hGT : Good3 (M.take x) τ)
    (hf : WfT2Abs.DropFail M ρ τ x i) :
    ∃ j ∈ children (M.take x) i,
      bumpTerm M ρ i j ≠ bumpTerm (M.take x) τ i j := by
  classical
  by_contra hn
  apply not_dropFail_of_surviving_terms_eq hx hGT _ hf
  intro j hj
  by_contra hne
  exact hn ⟨j, hj, hne⟩

/-- The failed source window has one last changing branch and one last
changing child. The parent used by the value is the row-0 parent as well.
All these certificates follow from the existing step context. -/
theorem failed_drop_branch {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) {r L i : Nat}
    (hx : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hi : i < r + L) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hT : Cons (M.take (r + L)) τ) (hf : WfT2Abs.DropFail M ρ τ (r + L) i) :
    ∃ m j c K B, par M 0 i = some m ∧ par M 1 i = some m ∧
      j ∈ children M i ∧ col M j = bump M i ∧
      c ∈ children M j ∧ c < r + L ∧ τ.o c ≠ ρ.o c ∧
      children (M.take (r + L)) i = B ++ [j] ∧
      (∀ d ∈ B, bumpTerm (M.take (r + L)) τ i d = bumpTerm M ρ i d) ∧
      children M j = K ++ [c] ∧ children (M.take (r + L)) j = K ++ [c] ∧
      (∀ d ∈ K, τ.o d = ρ.o d) := by
  classical
  have hGT : Good3 (M.take (r + L)) τ := by
    have he : M.length - 1 = r + L := by omega
    rw [← he] at hT ⊢
    exact good3_take_any (Inv3W.ofV2 C.S C.I) C.toW (by omega) hT
  have hRT : Rk (M.take (r + L)) rk := rk_take (by omega) C.I.rank
    (by have := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
        simpa only [show M.length - 1 = r + L from by omega] using this)
  obtain ⟨j, hjT, hne⟩ := changed_branch_of_dropFail hx hGT hf
  obtain ⟨hjx, hj⟩ := mem_children_take hjT
  have hb : col M j = bump M i := by
    by_contra hnb
    apply hne
    unfold bumpTerm
    rw [col_take M hjx, bump_take M hi, if_neg hnb, if_neg hnb]
  have hnx := T2SrcLeaf.last_not_child_of_bump C hx hr hj hb
  have hch : children (M.take (r + L)) j = children M j := by
    rw [children_take, children_filter_x hx hnx]
  have hex : ∃ c ∈ children M j, τ.o c ≠ ρ.o c := by
    by_contra hno
    apply hne
    unfold bumpTerm
    rw [col_take M hjx, bump_take M hi, if_pos hb, if_pos hb, hch]
    congr 2
    apply List.map_congr_left
    intro c hc
    by_contra hne'
    exact hno ⟨c, hc, Ne.symm hne'⟩
  obtain ⟨c, hc, hce⟩ := hex
  have hcx : c < r + L := by
    have := (mem_children hc).2
    have hn : c ≠ r + L := fun he => hnx (he ▸ hc)
    omega
  obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
  obtain ⟨m, hmi, hm1⟩ := T2SrcIndex.own_parent_of_bump_child hX hJ h1 h2 hj hb
  obtain ⟨K, hK, hKT, hfix, _, _⟩ := T2SrcLeaf.changed_bump_child_last C.S
    C.I.cons C.I.good hx hb hnx hc hce hT hRT hGT
  obtain ⟨B, hB, hfixB⟩ := T2SrcLeaf.changed_branch_last C.S C.I.cons C.I.good
    hx h2 hj hc hcx hce (fun d hd hbd => T2SrcLeaf.last_not_child_of_bump C hx hr hd hbd) hT hRT
  exact ⟨m, j, c, K, B, hmi, hm1, hj, hb, hc, hcx, hce, hB, hfixB, hK, hKT, hfix⟩


/-- Above the parent's row, a bump grandchild has that parent as its
row-1 parent. Z1C leaves no intermediate row to search. -/
theorem par1_of_high_grandchild {M : Mat} (S : SInv M) {m i j c : Nat}
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hc : c ∈ children M j) (hh : entry M 1 m < entry M 1 c) :
    par M 1 c = some m := by
  have hij := e1_of_col hb
  have hj2 : entry M 2 j = 1 := e2_of_col hb
  have hci := S.z1c j c hj2 hc
  have him := par1_entry_lt hm1
  rw [par1_find M c, ancL_eq (mem_children_iff.mp hc).2,
    ancL_eq (mem_children_iff.mp hj).2, ancL_eq hmi]
  simp only [List.find?_cons]
  have hj' : ¬ entry M 1 j < entry M 1 c := by omega
  have hi' : ¬ entry M 1 i < entry M 1 c := by omega
  simp only [decide_eq_false hj', decide_eq_false hi', decide_eq_true hh]

/-- A surviving child above m's row bounds the protected value of m.
It can never be the last changing child of a failed source window. -/
theorem not_dropFail_of_high_grandchild {M : Mat} {ρ τ : Valn}
    {rkT : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {x m i j c : Nat} (hx : x + 1 = M.length)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) (hGT : Good3 (M.take x) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hc : c ∈ children M j) (hcx : c < x) (hh : entry M 1 m < entry M 1 c) :
    ¬ WfT2Abs.DropFail M ρ τ x i := by
  have hjx : j < x := Nat.lt_trans (mem_children hc).1 hcx
  have hix : i < x := Nat.lt_trans (mem_children hj).1 hjx
  have hmx : m < x := Nat.lt_trans (par_lt M 0 i m hmi) hix
  have hjT : j ∈ children (M.take x) i := mem_take_children hj hjx
  have hcT : c ∈ children (M.take x) j := mem_take_children hc hcx
  have hbT : col (M.take x) j = bump (M.take x) i := by
    rw [col_take M hjx, bump_take M hix, hb]
  have hpc : par (M.take x) 1 c = some m := by
    rw [par_take M 1 c hcx]
    exact par1_of_high_grandchild S hmi hm1 hj hb hc hh
  have hmT : m < (M.take x).length := by rw [lenT hx]; exact hmx
  have hcN : c < (M.take x).length := by rw [lenT hx]; exact hcx
  have hpath : TRIO.le1 (M.take x) m c :=
    le1_par1_up ⟨hmT, hmT, Relation.ReflTransGen.refl⟩ hpc hcN
  exact T2SrcPrefix.not_dropFail_of_row1_descendant S hC hG hx hix hT hRT hGT
    hmi hm1 hjT hbT hcT hpath


/-- All grandchildren through a bump child have row 2 zero. If row 2 were
positive, RowJ and Z1C would put it at the bump child's row, where BumpLeaf
already forces row 2 zero. -/
theorem bump_grandchild_e2_zero {M : Mat} (hX : SInvX M) (hJ : RowJ M)
    {i j c : Nat} (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hc : c ∈ children M j) : entry M 2 c = 0 := by
  by_contra hn
  have hrow := hJ c j hn (mem_children_iff.mp hc).2
  have hj1 := e1_of_col hb
  have hz := (hX.loc.2.2.2 i j c hj hb hc (by omega)).1
  exact hn hz

/-- At a failed source window there is no surviving grandchild above the
old parent's row. This is a consequence, not an extra hypothesis. -/
theorem failed_drop_grandchild_row_le {M : Mat} {ρ τ : Valn}
    {rkT : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {x m i j c : Nat} (hx : x + 1 = M.length)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) (hGT : Good3 (M.take x) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hc : c ∈ children M j) (hcx : c < x)
    (hf : WfT2Abs.DropFail M ρ τ x i) : entry M 1 c ≤ entry M 1 m := by
  by_contra hn
  exact not_dropFail_of_high_grandchild S hC hG hx hT hRT hGT
    hmi hm1 hj hb hc hcx (by omega) hf


/-- A failed window has no earlier grandchild returning to or above m's
row. Both the equal-row copy and the higher-row monotonicity case are
already closed by the value comparisons. -/
theorem failed_drop_earlier_row_lt {M : Mat} {ρ τ : Valn}
    {rkT : Bool → Nat → Nat} (hX : SInvX M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ)
    {x m i j c d : Nat} (hx : x + 1 = M.length)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) (hGT : Good3 (M.take x) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hc : c ∈ children M j) (hcx : c < x)
    (hd : d ∈ children M j) (hdc : d < c)
    (hf : WfT2Abs.DropFail M ρ τ x i) : entry M 1 d < entry M 1 m := by
  have hdx : d < x := by omega
  have hle := failed_drop_grandchild_row_le hX.toSInv hC hG hx hT hRT hGT
    hmi hm1 hj hb hd hdx hf
  by_contra hn
  have he : entry M 1 d = entry M 1 m := by omega
  have hiN : i < M.length := Nat.lt_trans (mem_children hj).1 (mem_children hj).2
  have hm2 : entry M 2 m = 0 := by
    by_contra h
    exact no_par1_of_e2 hX.toSInv.z1c hiN (by have := hX.toSInv.z2 m; omega) hm1
  have hd2 := bump_grandchild_e2_zero hX hJ hj hb hd
  exact T2SrcPrefix.not_dropFail_of_earlier_return hX.toSInv hC hG hx hT hRT hGT
    hmi hm1 hj hb hd (mem_take_children hc hcx) hdc he hm2 hd2 hf


/-- R1S makes every row-1 parent step lower row 1 by exactly one. -/
theorem par1_height_step {M : Mat} (hR1 : R1S M) {m p : Nat}
    (hp : par M 1 m = some p) : entry M 1 m = entry M 1 p + 1 := by
  have hpm := par_lt M 1 m p hp
  obtain ⟨d, hd, hdm⟩ := anc0_child (anc0_of_par M 1 p m hp) (Nat.ne_of_lt hpm)
  have hrow := par1_between hp d hdm (par_lt M 0 d p hd)
  have hstep := hR1 d p hd
  have hlt := par1_entry_lt hp
  omega

/-- Every lower row is represented on the row-1 parent chain. -/
theorem parent_at_row {M : Mat} (hX : SInvX M) {m h : Nat}
    (hh : h ≤ entry M 1 m) :
    ∃ a, WfHUACDeep.Up1 M a m ∧ entry M 1 a = h := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases he : h = entry M 1 m
    · exact ⟨m, .refl _, he.symm⟩
    · have hpos : 0 < entry M 1 m := by omega
      obtain ⟨p, hp⟩ := par1_exists hX.e00 hX.r01 hpos
      have hs := par1_height_step hX.r1s hp
      obtain ⟨a, ha, har⟩ := ih p (par_lt M 1 m p hp) (by omega)
      exact ⟨a, .step hp ha, har⟩


/-- A row-1 chain is quiet, or it contains an actual upgrade before the
chosen return row. No claim about standard shape is hidden in this split. -/
theorem quiet_or_upgraded_parent {M : Mat} {a m : Nat} (h : WfHUACDeep.Up1 M a m) :
    QuietParents M a m ∨ ∃ b, WfHUACDeep.Up1 M b m ∧
      entry M 1 a < entry M 1 b ∧ upg M b ≠ none := by
  induction h with
  | refl => exact Or.inl (.refl _)
  | @step m p hp tail ih =>
    by_cases hu : upg M m = none
    · rcases ih with hq | ⟨b, hbm, hrow, hb⟩
      · exact Or.inl (.step hp hu hq)
      · exact Or.inr ⟨b, .step hp hbm, hrow, hb⟩
    · have hrow := par1_entry_lt hp
      have hle := WfHUACDeep.up1_e1_le tail
      exact Or.inr ⟨m, .refl _, by omega, hu⟩

/-- In the lost-child case, a failed window must cross a genuine upgrade
on the parent's row-1 chain above the return row. The entirely quiet case
has been proved impossible, including arbitrarily long chains. -/
theorem failed_lost_has_upgraded_parent {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) (hB : Bad2 M)
    {x m i j : Nat} (hx : x + 1 = M.length) (hx2 : entry M 2 x = 1)
    (ha : par M 0 x ≠ some (x - 1) ∨ par M 1 x ≠ some (x - 1))
    (hT : Cons (M.take x) τ) (hGT : Good3 (M.take x) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hc : x - 1 ∈ children M j)
    (hrow : entry M 1 (x - 1) ≤ entry M 1 m)
    (hf : WfT2Abs.DropFail M ρ τ x i) :
    ∃ b, WfHUACDeep.Up1 M b m ∧
      entry M 1 (x - 1) < entry M 1 b ∧ upg M b ≠ none := by
  obtain ⟨hX, _⟩ := sInvXJ_std C.std C.ne
  obtain ⟨a, hA, har⟩ := parent_at_row hX hrow
  rcases quiet_or_upgraded_parent hA with hq | ⟨b, hbM, hbl, hbu⟩
  · exact False.elim (not_dropFail_of_lost_quiet_return C hB hx hx2 ha hT hGT
      hmi hm1 hj hb hc hq har.symm hf)
  · exact ⟨b, hbM, by omega, hbu⟩

end Ytosk.T2SrcQuiet
