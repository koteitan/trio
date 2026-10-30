/- Localize the proved guard comparison to the next column only. -/
import Ytosk.V3T2SrcPrefix

namespace Ytosk.T2SrcIndex
open T Classical

/-- A row-2-nonzero column with a bump child has its row-0 parent as
row-1 parent. Otherwise it is itself a bump child and BumpLeaf rules out
its row-2-one bump child. -/
theorem own_parent_of_bump_child {M : Mat} (hX : SInvX M) (hJ : RowJ M)
    {i j : Nat} (hi1 : entry M 1 i ≠ 0) (hi2 : entry M 2 i ≠ 0)
    (hj : j ∈ children M i) (hb : col M j = bump M i) :
    ∃ m, par M 0 i = some m ∧ par M 1 i = some m := by
  have S := hX.toSInv
  obtain ⟨a, ha⟩ := par1_exists S.e00 S.r01 (show 0 < entry M 1 i by omega)
  obtain ⟨p, hp⟩ := par0_of_anc (anc0_of_par M 1 a i ha) (Nat.ne_of_lt (par_lt M 1 i a ha))
  have hle := hJ i p hi2 hp
  have hlt : entry M 1 p < entry M 1 i := by
    by_contra h
    have he : entry M 1 i = entry M 1 p := by omega
    have hi21 : entry M 2 i = 1 := by have := S.z2 i; omega
    have hib : col M i = bump M p := by
      rw [col_eq_entries, S.r0p i p hp, he, hi21]
      rfl
    have hiM : i < M.length := Nat.lt_trans (mem_children hj).1 (mem_children hj).2
    have hiChild : i ∈ children M p := mem_children_iff.mpr ⟨hiM, hp⟩
    have hz := (hX.loc.2.2.2 p i j hiChild hib hj (by rw [e1_of_col hb]; exact hle)).1
    have ho := e2_of_col hb
    omega
  exact ⟨p, hp, par1_of_child hp hlt⟩

theorem v_le_unguarded_local {G : Mat} {ρ : Valn} (hC : Cons G ρ) (hG : Good3 G ρ) (hR0 : R0P G) (hJ : RowJ G) (hBE : BumpE2 G) (hUAB : UAB G) (hZ2 : Z2 G)
    (hR01 : R01 G) (h00 : entry G 0 0 = 0) {r d : Nat} (he2r : entry G 2 r = 0)
    (hsub : d + 1 < G.length → Anc0 G r (d + 1)) (hrd : Anc0 G r d) (hdr : d ≠ r)
    (hdl : d < G.length)
    (hwin : ∀ y, Anc0 G r y → Anc0 G y d → y ≠ r → y ≠ d → entry G 1 r < entry G 1 y)
    (hng : ¬ TRIO.le1 G r d) : ρ.v d ≤ ρ.v r := by
  have hrdlt : r < d := by have := hrd.le; omega
  by_cases h1d : entry G 1 d = 0
  · rw [v_z_of_e1 hC hdl h1d]; exact z_le _
  obtain ⟨m, hm⟩ := par1_exists h00 hR01 (show 0 < entry G 1 d by omega)
  obtain ⟨hmd, hmdlt, he1md, hbetd⟩ := par1_facts hm
  have hrl : r < G.length := by omega
  have hle1rr : TRIO.le1 G r r := ⟨hrl, hrl, Relation.ReflTransGen.refl⟩
  -- `P_1(d)` is a proper ancestor of `r`
  have hmr : Anc0 G m r ∧ m ≠ r := by
    rcases anc0_total hmd hrd with h | h
    · refine ⟨h, fun hmr => hng ?_⟩
      rw [hmr] at hm
      exact le1_par1_up hle1rr hm hdl
    · exfalso
      by_cases hmr : m = r
      · rw [hmr] at hm; exact hng (le1_par1_up hle1rr hm hdl)
      · have hml : m < G.length := by omega
        have hgm : TRIO.le1 G r m := by
          apply (le1_window hml h).mpr
          intro y hy1 hy2 hy3
          by_cases hym : y = m
          · rw [hym]; exact hwin m h hmd hmr (by omega)
          · exact hwin y hy1 (Anc0.trans hy2 hmd) hy3 (by have := hy2.le; omega)
        exact hng (le1_par1_up hgm hm hdl)
  obtain ⟨hmr1, hmr2⟩ := hmr
  have hmrlt : m < r := by have := hmr1.le; omega
  -- `e2(d) = 0`
  have he2d : entry G 2 d = 0 := by
    by_contra h2d
    obtain ⟨p, hp, hrp⟩ := anc0_par_exists hrd (Ne.symm hdr)
    have hJd := hJ d p h2d hp
    have hpd := par_lt G 0 d p hp
    by_cases hpr : p = r
    · rw [hpr] at hp hJd
      have he1dr : entry G 1 d ≤ entry G 1 r := hbetd r hmr1 hrd (Ne.symm hmr2) (by omega)
      have h0d := hR0 d r hp
      have h2d1 : entry G 2 d = 1 := by have := hZ2 d; omega
      have hdb : col G d = bump G r := by
        rw [col_eq_entries, h0d, h2d1, show entry G 1 d = entry G 1 r by omega]; rfl
      have := hBE r d (mem_children_iff.mpr ⟨hdl, hp⟩) hdb
      omega
    · have h1 := hwin p hrp (Anc0.step hp (Anc0.refl p)) hpr (by omega)
      have he1dr : entry G 1 d ≤ entry G 1 r := hbetd r hmr1 hrd (Ne.symm hmr2) (by omega)
      omega
  -- `d + 1` is not a child of `m`
  have hnext : d + 1 < G.length → par G 0 (d + 1) ≠ some m := by
    intro hd1 h
    have := (anc0_par (hsub hd1) (by omega) h).le
    omega
  -- along the row-1 chain of `r` down to `m`
  have key : ∀ c, Anc0 G m c → c ≠ m → Anc0 G c r → ρ.v d ≤ ρ.v c := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      intro hmc hcm hcr
      have hcd : Anc0 G c d := Anc0.trans hcr hrd
      have hcdlt : c < d := by have := hcr.le; omega
      have he1c : entry G 1 d ≤ entry G 1 c := hbetd c hmc hcd hcm (by omega)
      have hcl : c < G.length := by omega
      obtain ⟨c', hc'⟩ := par1_exists h00 hR01 (show 0 < entry G 1 c by omega)
      obtain ⟨hc'c, hc'lt, he1c', hbetc⟩ := par1_facts hc'
      have hmc' : Anc0 G m c' := by
        rcases anc0_total hmc hc'c with h | h
        · exact h
        · by_cases hc'm : c' = m
          · rw [hc'm]; exact Anc0.refl m
          · exfalso
            have := hbetc m h hmc (Ne.symm hc'm) (Ne.symm hcm)
            omega
      by_cases hc'm : c' = m
      · rw [hc'm] at hc'
        exact v_le_same_par1 hC hG hR0 hJ hBE hUAB hZ2 hc' hm hcd (by omega) he1c he2d hdl hnext
      · have h1 := ih c' hc'lt hmc' hc'm (Anc0.trans hc'c hcr)
        exact le_trans h1 (v_par1_le hC hG hcl (by omega) hc')
  exact key r hmr1 (Ne.symm hmr2) (Anc0.refl r)


/-- A grandchild returning to or below the old parent's row has no larger
value, provided its next column stays inside the branch. -/
theorem lower_return_value_le {M : Mat} {ρ : Valn}
    (S : SInv M) (hJ : RowJ M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {m k j c : Nat} (hkm : par M 0 k = some m) (hkm1 : par M 1 k = some m)
    (hjk : par M 0 j = some k) (hj1 : entry M 1 j = entry M 1 k)
    (hcj : par M 0 c = some j) (hcN : c < M.length)
    (hm2 : entry M 2 m = 0) (hc1 : entry M 1 c ≤ entry M 1 m)
    (hnext : c + 1 < M.length → entry M 0 m < entry M 0 (c + 1)) :
    ρ.v c ≤ ρ.v m := by
  have hmc : Anc0 M m c :=
    (anc0_of_par M 0 m k hkm).trans
      ((anc0_of_par M 0 k j hjk).trans (anc0_of_par M 0 j c hcj))
  have hmklt := par_lt M 0 k m hkm
  have hkjlt := par_lt M 0 j k hjk
  have hjclt := par_lt M 0 c j hcj
  have hmk1 := par1_entry_lt hkm1
  apply v_le_unguarded_local hC hG S.r0p hJ S.bumpE2 S.uab S.z2 S.r01 S.e00 hm2
    (fun hn => anc0_next hmc (hnext hn)) hmc (by omega) hcN
  · intro y hmy hyc hym hycne
    have hyj := anc0_par hyc hycne hcj
    by_cases hyje : y = j
    · rw [hyje, hj1]; exact hmk1
    · have hyk := anc0_par hyj hyje hjk
      by_cases hyke : y = k
      · rw [hyke]; exact hmk1
      · have hym' := anc0_par hyk hyke hkm
        exact False.elim (hym (le_antisymm hym'.le hmy.le))
  · intro hle
    have := (le1_window hcN hmc).mp hle c hmc (Anc0.refl c) (by omega)
    omega

/-- At an untopped row-1 child, every bump grandchild returns below the
parent's row. A later non-bump child keeps its next column inside the branch. -/
theorem bump_kid_le_parent {M : Mat} {ρ : Valn} (hX : SInvX M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {m k j c : Nat}
    (hkm : par M 0 k = some m) (hkm1 : par M 1 k = some m)
    (htop : topped M k = false)
    (hj : j ∈ children M k) (hb : col M j = bump M k)
    (hc : c ∈ children M j) : ρ.v c ≤ ρ.v m := by
  have S := hX.toSInv
  have hjp := (mem_children_iff.mp hj).2
  have hcp := (mem_children_iff.mp hc).2
  have hmk := par_lt M 0 k m hkm
  have hkj := (mem_children hj).1
  have hjc := (mem_children hc).1
  have hcN := (mem_children hc).2
  have hkN : k < M.length := by omega
  have hm2 : entry M 2 m = 0 := by
    have hz := S.z2 m
    by_contra h
    have hm21 : entry M 2 m = 1 := by omega
    exact no_par1_of_e2 S.z1c hkN hm21 hkm1
  have hc1 : entry M 1 c ≤ entry M 1 m := by
    have hr1 := hX.r1s k m hkm
    by_contra h
    obtain ⟨_, _, _, hlast⟩ := hX.loc.2.2.2 k j c hj hb hc (by omega)
    simp only [topped, hlast, hb, decide_true] at htop
    contradiction
  have hlast_exists : ∃ l, (children M k).getLast? = some l := by
    cases he : (children M k).getLast? with
    | none =>
      have heq := List.getLast?_eq_none_iff.mp he
      rw [heq] at hj
      simp at hj
    | some l => exact ⟨l, rfl⟩
  obtain ⟨l, hl⟩ := hlast_exists
  have hlM := List.mem_of_getLast? hl
  have hlp := (mem_children_iff.mp hlM).2
  have hjle := last_le (children_sorted M k) hl j hj
  have hjl : j < l := by
    by_contra h
    have he : j = l := by omega
    rw [← he] at hl
    simp only [topped, hl, hb, decide_true] at htop
    contradiction
  have hcl : c < l := kid_lt_x hjp hlp hjl hcp
  have hAml := (anc0_of_par M 0 m k hkm).trans (anc0_of_par M 0 k l hlp)
  apply lower_return_value_le S hJ hC hG hkm hkm1 hjp (e1_of_col hb) hcp hcN hm2 hc1
  intro _
  have ha : Anc0 M m (c + 1) := anc_between hAml (c + 1) (by omega) (by omega)
  exact anc0_e0_lt ha (by omega)

/-- The bump term's leading index is bounded by the old parent value.
Only untoppedness of the target is needed, not HUAC. -/
theorem bump_index_le_parent {M : Mat} {ρ : Valn} (hX : SInvX M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {m k : Nat}
    (hkm : par M 0 k = some m) (hkm1 : par M 1 k = some m)
    (htop : topped M k = false) : lev (bumpW M ρ k) ≤ ρ.v m := by
  apply le_trans (lev_omega_le _) (not_lt.mp (not_lt_lev_sumN _ ?_))
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact ⟨isOT_one, not_lt_z _⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    refine ⟨isOT_bumpTerm hG k j, ?_⟩
    unfold bumpTerm
    split
    · rename_i hb
      intro hf
      apply not_lt_lev_sumN _ ?_ (lt_of_lt_of_le hf (lev_omega_le _))
      intro s hs
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
      have hcN := (mem_children hc).2
      refine ⟨hG.ot_o c hcN, ?_⟩
      obtain ⟨y, hy⟩ := o_psi_sub hC hcN
      rw [hy, sf_ot (hG.ot_v c hcN)]
      exact not_lt_of_ge (bump_kid_le_parent hX hJ hC hG hkm hkm1 htop hj hb hc)
    · exact not_lt_z _

/-- The leading index of an ancestor-upgraded value is no larger than
its row-1 parent's value. This is an ordinary order bound, not component
domination; it remains valid in the known HUAC counterexamples. -/
theorem ancestor_value_index_le {M : Mat} {ρ : Valn} (hX : SInvX M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {n k : Nat}
    (hn : n < M.length) (hu : upg M n = some k) (hkn : k < n) :
    lev (ρ.v n) ≤ vOpt ρ (par M 1 n) := by
  have S := hX.toSInv
  obtain ⟨m, hm, hkm⟩ := upg_target_par0 S.r0p hu
  obtain ⟨m', hm', hkm1, _, _⟩ := upg_spec hu
  rw [hm] at hm'
  cases hm'
  obtain ⟨h1, h2⟩ := upg_e12 hu
  have h20 : entry M 2 n = 0 := by have := S.z2 n; omega
  have hv := v_upg_eq hC hn h1 h20 hu (vOpt_ot hG hn)
    (fun j _ _ c hc => hG.ot_o c (mem_children hc).2)
  obtain ⟨_, _, _, _, hk, _⟩ := upg_target_val hC hG hn hu
  rw [hv, hk]
  have hb := bump_index_le_parent hX hJ hC hG hkm hkm1 (S.uat n k hu (by omega))
  rw [hm]
  change lev (add (ρ.v m) (bumpW M ρ k)) ≤ ρ.v m
  rcases lev_add_cases (ρ.v m) (bumpW M ρ k) with he | he
  · rw [he]
    cases hv : ρ.v m with
    | z => exact le_refl _
    | psi a b c => exact le_of_lt (sub_lt a b c)
  · rw [he]
    exact hb

/-- A row-1 parent cannot upgrade to its next column. Its value therefore
has leading index no larger than the value of its own row-1 parent. -/
theorem row1_parent_index_le {M : Mat} {ρ : Valn} (hX : SInvX M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {i m : Nat}
    (hi : i < M.length) (hm : par M 1 i = some m) :
    lev (ρ.v m) ≤ vOpt ρ (par M 1 m) := by
  have S := hX.toSInv
  have hmi := par_lt M 1 i m hm
  have hmN : m < M.length := by omega
  have hn : upg M m ≠ some (m + 1) := by
    intro hu
    have := leaf_of_upg_next S.r0p hu i (anc0_of_par M 1 m i hm)
    omega
  have hm2 : entry M 2 m = 0 := by
    have hz := S.z2 m
    by_contra h
    exact no_par1_of_e2 S.z1c hi (by omega) hm
  cases hu : upg M m with
  | some k =>
    obtain ⟨_, _, _, _, he | ⟨_, hkm⟩⟩ := upg_spec hu
    · exact False.elim (hn (by simpa only [he] using hu))
    · exact ancestor_value_index_le hX hJ hC hG hmN hu hkm
  | none =>
    by_cases h10 : entry M 1 m = 0
    · rw [v_z_of_e1 hC hmN h10]
      exact z_le _
    · have hv := (hC m hmN).2
      unfold vRhs at hv
      rw [if_neg h10, if_pos hm2, hu] at hv
      change ρ.v m = sf (add (vOpt ρ (par M 1 m)) one) at hv
      rw [sf_ot (isOT_add (vOpt_ot hG hmN) isOT_one)] at hv
      rw [hv]
      rcases lev_add_cases (vOpt ρ (par M 1 m)) one with he | he
      · rw [he]
        cases hv : vOpt ρ (par M 1 m) with
        | z => exact le_refl _
        | psi a b c => exact le_of_lt (sub_lt a b c)
      · rw [he]
        exact z_le _

/-- The lost final child, when it returns to m's row, bounds the old
parent value after losing its upgrade: its new index is V+one, whereas
the old parent's leading index is at most V. -/
theorem not_dropFail_of_lost_return {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) (hB : Bad2 M)
    {x m i j : Nat} (hx : x + 1 = M.length) (hx2 : entry M 2 x = 1)
    (ha : par M 0 x ≠ some (x - 1) ∨ par M 1 x ≠ some (x - 1))
    (hT : Cons (M.take x) τ) (hGT : Good3 (M.take x) τ)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i)
    (hc : x - 1 ∈ children M j) (hc1 : entry M 1 (x - 1) = entry M 1 m) :
    ¬ WfT2Abs.DropFail M ρ τ x i := by
  obtain ⟨_, k, p, g, hu, hkn, hp, hg, hpb, hleaf, ho, hoT⟩ :=
    T2SrcLeaf.source_leaf_shapes C hB hx hx2 ha hT
  have hpos : 0 < x := by
    obtain ⟨a, ha, _⟩ := upg_spec hu
    have := par_lt M 1 (x - 1) a ha
    omega
  have hcx : x - 1 < x := by omega
  have hjx : j < x := Nat.lt_trans (mem_children hc).1 hcx
  have hix : i < x := Nat.lt_trans (mem_children hj).1 hjx
  obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
  have hidx := row1_parent_index_le hX hJ C.I.cons C.I.good (by omega) hm1
  have hpc := HUACCopy.par1_return hmi (mem_children_iff.mp hj).2
    (mem_children_iff.mp hc).2 (par1_entry_lt hm1) (e1_of_col hb) hc1
  have hltidx : lev (ρ.v m) < add (vOpt ρ (par M 1 m)) one :=
    lt_of_le_of_lt hidx (lt_add_principal z z _)
  have hpO : ρ.v m < τ.o (x - 1) := by
    rw [hoT, hpc]
    cases hv : ρ.v m with
    | z => exact z_lt_psi _ _ _
    | psi a b c =>
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

end Ytosk.T2SrcIndex
