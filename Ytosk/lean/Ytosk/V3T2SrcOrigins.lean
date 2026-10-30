/- The principal summands of a row-1-parent value come from actual
upgrade increments on its parent chain, except for copies of one. -/
import Ytosk.V3T2SrcRounding
import Ytosk.V3PhiGapT2P

namespace Ytosk.T2SrcOrigins
open T
open WfHUACDeep

/-- Every summand other than one has an actual origin on the row-1 chain.
This uses the value equations, without component domination or HUAC. -/
theorem row1_value_origin {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) : ∀ m, m < M.length → entry M 2 m = 0 →
    ∀ q ∈ summands (ρ.v m), q = one ∨
      ∃ b k, Up1 M b m ∧ upg M b = some k ∧ q = bumpW M ρ k := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hm2 q hq
    by_cases hm1 : entry M 1 m = 0
    · rw [v_z_of_e1 hC hm hm1] at hq
      simp only [summands, List.not_mem_nil] at hq
    · obtain ⟨p, hp⟩ := par1_exists S.e00 S.r01 (show 0 < entry M 1 m by omega)
      have hpm := par_lt M 1 m p hp
      have hpN : p < M.length := by omega
      have hp2 : entry M 2 p = 0 := by
        by_contra hn
        exact no_par1_of_e2 S.z1c hm (by have := S.z2 p; omega) hp
      have lift (hq' : q ∈ summands (ρ.v p)) : q = one ∨
          ∃ b k, Up1 M b m ∧ upg M b = some k ∧ q = bumpW M ρ k := by
        rcases ih p hpm hpN hp2 q hq' with he | ⟨b, k, hb, hu, he⟩
        · exact Or.inl he
        · exact Or.inr ⟨b, k, .step hp hb, hu, he⟩
      cases hu : upg M m with
      | none =>
        have hv := (hC m hm).2
        unfold vRhs at hv
        rw [if_neg hm1, if_pos hm2, hu, hp] at hv
        change ρ.v m = sf (add (ρ.v p) one) at hv
        rw [sf_ot (isOT_add (hG.ot_v p hpN) isOT_one)] at hv
        rw [hv] at hq
        rcases summands_add_single (ρ.v p) q hq with he | ⟨hq', _⟩
        · exact Or.inl he
        · exact lift hq'
      | some k =>
        have hv := HUACSupport.value_at_target S hC hG hm hu
        obtain ⟨s, y, hW⟩ := omega_psi_form (sumN (one :: (children M k).map (bumpTerm M ρ k)))
        change bumpW M ρ k = psi s y z at hW
        rw [hv, hp, hW] at hq
        rcases summands_add_single (ρ.v p) q hq with he | ⟨hq', _⟩
        · exact Or.inr ⟨m, k, .refl _, hu, he.trans hW.symm⟩
        · exact lift hq'

/-- At the source parent, every large summand is the omega power of the
bump exponent of an actual upgrade on that parent's chain. -/
theorem source_summand_origin {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {i m : Nat}
    (hi : i < M.length) (hm : par M 1 i = some m) {q : T}
    (hq : q ∈ summands (vOpt ρ (par M 1 i))) (hq2 : ¬ q < psi z two z) :
    ∃ b k, Up1 M b m ∧ upg M b = some k ∧
      q = omega (sumN (one :: (children M k).map (bumpTerm M ρ k))) := by
  have hmN : m < M.length := Nat.lt_trans (par_lt M 1 i m hm) hi
  have hm2 : entry M 2 m = 0 := by
    by_contra hn
    exact no_par1_of_e2 S.z1c hi (by have := S.z2 m; omega) hm
  rw [hm] at hq
  rcases row1_value_origin S hC hG m hmN hm2 q hq with he | ⟨b, k, hb, hu, he⟩
  · exact False.elim (hq2 (he ▸ (by decide : one < psi z two z)))
  · exact ⟨b, k, hb, hu, he⟩


/-- Every ancestor on the row-1 chain is itself a row-1 parent of a
column in the matrix. -/
theorem chain_parent_has_child {M : Mat} {i m b : Nat}
    (hi : i < M.length) (hm : par M 1 i = some m) (h : Up1 M b m) :
    ∃ w, w < M.length ∧ par M 1 w = some b := by
  induction h generalizing i with
  | refl => exact ⟨i, hi, hm⟩
  | @step m p hp tail ih =>
    have hmN : m < M.length := Nat.lt_trans (par_lt M 1 i m hm) hi
    exact ih hmN hp

/-- The target giving a source-parent summand is strictly before the
source column. It cannot be a next-column upgrade. -/
theorem origin_target_lt_source {M : Mat} (S : SInv M) {i m b k : Nat}
    (hi : i < M.length) (hm : par M 1 i = some m) (h : Up1 M b m)
    (hu : upg M b = some k) : k < i := by
  obtain ⟨w, hwN, hp⟩ := chain_parent_has_child hi hm h
  have hbw := par_lt M 1 w b hp
  have hbmi := up1_le h
  have hmi := par_lt M 1 i m hm
  obtain ⟨_, _, _, _, hnext | ⟨_, hkb⟩⟩ := upg_spec hu
  · have hn : upg M b = some (b + 1) := by simpa only [hnext] using hu
    have hh := leaf_of_upg_next S.r0p hn w (anc0_of_par M 1 b w hp)
    omega
  · omega

/-- A genuinely failed double-omega source window has a cutoff witness
in an earlier upgrade exponent. The optional final one contributes only
the consecutive-omega boundary, which is already Lhd. -/
theorem failed_window_descends {M : Mat} {ρ τ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {x i m : Nat} {Q G G' : T}
    (hi : i < M.length) (hm : par M 1 i = some m)
    (hQ : isOT Q = true) (hG0 : isOT G = true) (hG1 : isOT G' = true)
    (hNew : bumpW (M.take x) τ i = omega (add Q (omega G')))
    (hOld : bumpW M ρ i = omega (add Q (omega G)) ∨
      bumpW M ρ i = omega (succ (add Q (omega G))))
    (hf : WfT2Abs.DropFail M ρ τ x i) :
    ∃ b k r, Up1 M b m ∧ upg M b = some k ∧ k < i ∧
      r ∈ summands (sumN (one :: (children M k).map (bumpTerm M ρ k))) ∧
      ¬ r < omega G' ∧ r < omega G := by
  classical
  have hbad : ∃ q, q ∈ summands (vOpt ρ (par M 1 i)) ∧ ¬ q < psi z two z ∧
      ¬ q < bumpW (M.take x) τ i ∧ q < bumpW M ρ i ∧ ¬ Lhd z q (bumpW M ρ i) := by
    by_contra hn
    apply hf
    intro q hq hq2 hnT hqM
    by_contra hnl
    exact hn ⟨q, hq, hq2, hnT, hqM, hnl⟩
  obtain ⟨q, hq, hq2, hnT, hqM, hnl⟩ := hbad
  obtain ⟨b, k, hb, hu, he⟩ := source_summand_origin S hC hG hi hm hq hq2
  let P := sumN (one :: (children M k).map (bumpTerm M ρ k))
  have hP : isOT P = true := isOT_bumpP hG k
  change q = omega P at he
  have hn : ¬ P < add Q (omega G') := by
    intro hp
    apply hnT
    rw [he, hNew]
    exact omega_lt_omega hP (isOT_add hQ (isOT_omega hG1)) hp
  have hold : P < add Q (omega G) := by
    rcases hOld with hOld | hOld
    · rw [he, hOld] at hqM
      exact T2SrcRounding.omega_lt_reflect hP (isOT_add hQ (isOT_omega hG0)) hqM
    · rw [he, hOld] at hqM
      have hle := lt_succ_iff.mp (T2SrcRounding.omega_lt_reflect hP
        (isOT_succ (isOT_add hQ (isOT_omega hG0))) hqM)
      rcases (le_iff _ _).mp hle with hlt | heq
      · exact hlt
      · exact False.elim (hnl (by
          rw [he, heq, hOld]
          exact lhd_omega_succ (isOT_add hQ (isOT_omega hG0))))
  obtain ⟨s, y, hB⟩ := omega_psi_form G
  obtain ⟨s', y', hB'⟩ := omega_psi_form G'
  simp only [hB, hB'] at hn hold
  obtain ⟨r, hr, hnew, hold'⟩ := T2SrcRounding.summand_in_replacement_window Q P hn hold
  refine ⟨b, k, r, hb, hu, origin_target_lt_source S hi hm hb hu, hr, ?_, ?_⟩
  · simpa only [hB'] using hnew
  · simpa only [hB] using hold'


/-- The real failed drop supplies the common-prefix decomposition itself.
The remaining witness is in the exponent of an earlier upgrade target;
no extra term-shape hypothesis is assumed here. -/
theorem source_failed_descends {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) {r L i : Nat}
    (hx : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hi : i < r + L) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hT : Cons (M.take (r + L)) τ) (hf : WfT2Abs.DropFail M ρ τ (r + L) i) :
    ∃ m j c b k d, par M 0 i = some m ∧ par M 1 i = some m ∧
      j ∈ children M i ∧ col M j = bump M i ∧
      c ∈ children M j ∧ c < r + L ∧ τ.o c ≠ ρ.o c ∧
      Up1 M b m ∧ upg M b = some k ∧ k < i ∧
      d ∈ summands (sumN (one :: (children M k).map (bumpTerm M ρ k))) ∧
      ¬ d < bumpTerm (M.take (r + L)) τ i j ∧ d < bumpTerm M ρ i j := by
  classical
  obtain ⟨m, j, c, K, B, hmi, hm1, hj, hb, hc, hcx, hce, hBranches, hfixB,
    hKids, hKidsT, hfixK⟩ := T2SrcQuiet.failed_drop_branch C hx hr hi h1 h2 hT hf
  have hGT : Good3 (M.take (r + L)) τ := by
    have he : M.length - 1 = r + L := by omega
    rw [← he] at hT ⊢
    exact good3_take_any (Inv3W.ofV2 C.S C.I) C.toW (by omega) hT
  let Q := sumN (one :: B.map (bumpTerm M ρ i))
  let G := sumN ((children M j).map ρ.o)
  let G' := sumN ((children (M.take (r + L)) j).map τ.o)
  have hQ : isOT Q = true := by
    apply isOT_sumN
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm C.I.good i d
  have hG0 : isOT G = true := isOT_sumN _ (by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact C.I.good.ot_o d (mem_children hd).2)
  have hG1 : isOT G' = true := isOT_sumN _ (by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hGT.ot_o d (mem_children hd).2)
  have hjx : j < r + L := Nat.lt_trans (mem_children hc).1 hcx
  have hBM : bumpTerm M ρ i j = omega G := by simp only [bumpTerm, if_pos hb]; rfl
  have hBT : bumpTerm (M.take (r + L)) τ i j = omega G' := by
    unfold bumpTerm
    rw [col_take M hjx, bump_take M hi, if_pos hb]
  obtain ⟨hPN, hPM⟩ := T2SrcLeaf.bump_sums_of_last_branch C.I.good hGT hx hBranches hfixB
  change sumN (one :: (children (M.take (r + L)) i).map (bumpTerm (M.take (r + L)) τ i)) =
    add Q (bumpTerm (M.take (r + L)) τ i j) at hPN
  change sumN (one :: (children M i).map (bumpTerm M ρ i)) =
    (if r + L ∈ children M i then add (add Q (bumpTerm M ρ i j)) (bumpTerm M ρ i (r + L))
    else add Q (bumpTerm M ρ i j)) at hPM
  have hNew : bumpW (M.take (r + L)) τ i = omega (add Q (omega G')) := by
    unfold bumpW
    rw [hPN, hBT]
  have hOld : bumpW M ρ i = omega (add Q (omega G)) ∨
      bumpW M ρ i = omega (succ (add Q (omega G))) := by
    unfold bumpW
    rw [hPM, hBM]
    by_cases hxi : r + L ∈ children M i
    · rw [if_pos hxi, T2SrcLeaf.bumpTerm_last hx]
      by_cases hxb : col M (r + L) = bump M i
      · right
        rw [if_pos hxb, add_one_eq_succ (isOT_add hQ (isOT_omega hG0))]
      · left
        rw [if_neg hxb, add_z_right]
    · left
      rw [if_neg hxi]
  obtain ⟨b, k, d, hbm, hu, hki, hd, hdn, hdo⟩ := failed_window_descends C.S
    C.I.cons C.I.good (by omega) hm1 hQ hG0 hG1 hNew hOld hf
  exact ⟨m, j, c, b, k, d, hmi, hm1, hj, hb, hc, hcx, hce, hbm, hu, hki, hd,
    by simpa only [hBT] using hdn, by simpa only [hBM] using hdo⟩


/-- Non-unit summands of a bump exponent are actual bump-child terms. -/
theorem bump_exponent_summand {M : Mat} {ρ : Valn} (hG : Good3 M ρ) {k : Nat} {r : T}
    (hr : r ∈ summands (sumN (one :: (children M k).map (bumpTerm M ρ k))))
    (hr1 : r ≠ one) : ∃ j, j ∈ children M k ∧ col M j = bump M k ∧ r = bumpTerm M ρ k j := by
  classical
  let l := one :: (children M k).map (bumpTerm M ρ k)
  have hOT : ∀ t ∈ l, isOT t = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact isOT_one
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
      exact isOT_bumpTerm hG k j
  have hs : ∀ t ∈ nzs l, Single t := by
    intro t ht
    obtain ⟨htl, hne⟩ := List.mem_filter.mp ht
    have hne' : t ≠ z := of_decide_eq_true hne
    rcases List.mem_cons.mp htl with rfl | htl
    · exact ⟨isOT_one, z, z, rfl⟩
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp htl
      by_cases hb : col M j = bump M k
      · unfold bumpTerm
        rw [if_pos hb]
        exact single_omega (isOT_sumN _ (by
          intro t ht
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
          exact hG.ot_o d (mem_children hd).2))
      · exact False.elim (hne' (by simp only [bumpTerm, if_neg hb]))
  change r ∈ summands (sumN l) at hr
  rw [sumN_nzs hOT] at hr
  have hrn := summands_sumN_sub hs r hr
  obtain ⟨hrl, hrnz⟩ := List.mem_filter.mp hrn
  have hr0 : r ≠ z := of_decide_eq_true hrnz
  rcases List.mem_cons.mp hrl with he | hrl
  · exact False.elim (hr1 he)
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp hrl
    have hb : col M j = bump M k := by
      by_contra hn
      exact hr0 (he.symm.trans (by simp only [bumpTerm, if_neg hn]))
    exact ⟨j, hj, hb, he.symm⟩

/-- Bump children of the target are all before the upgrading parent.
UAB puts the parent on a non-bump branch, and bump children come first. -/
theorem origin_bump_child_lt_source {M : Mat} (S : SInv M) {i m b k j : Nat}
    (hi : i < M.length) (hm : par M 1 i = some m) (h : Up1 M b m)
    (hu : upg M b = some k) (hj : j ∈ children M k) (hjb : col M j = bump M k) : j < i := by
  obtain ⟨w, hwN, hp⟩ := chain_parent_has_child hi hm h
  have hbw := par_lt M 1 w b hp
  have hbmi := up1_le h
  have hmi := par_lt M 1 i m hm
  have hnext : k ≠ b + 1 := by
    intro he
    have hn : upg M b = some (b + 1) := by simpa only [he] using hu
    have hh := leaf_of_upg_next S.r0p hn w (anc0_of_par M 1 b w hp)
    omega
  obtain ⟨a, ha, hk1, hcol, hcase⟩ := upg_spec hu
  rcases hcase with he | ⟨hAkb, hkb⟩
  · exact False.elim (hnext he)
  · obtain ⟨d, hdk, hAdb⟩ := anc0_child hAkb (Nat.ne_of_lt hkb)
    have hdM : d < M.length := by have := hAdb.le; omega
    have hd : d ∈ children M k := mem_children_iff.mpr ⟨hdM, hdk⟩
    have hnb : col M d ≠ bump M k := by
      intro he
      exact S.uab b k hu hnext d hd he hAdb
    have hk2 : entry M 2 k ≠ 0 := by have := e2_of_col hcol; omega
    have hjd := bump_lt_nonbump S hk2 hj hjb hd hnb
    have hdb := hAdb.le
    omega


/-- A nonempty bump branch is strictly above one. -/
theorem one_lt_nonempty_bump {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
    {i j c : Nat} (hb : col M j = bump M i) (hc : c ∈ children M j) :
    one < bumpTerm M ρ i j := by
  obtain ⟨y, hy⟩ := o_psi_sub hC (mem_children hc).2
  have hc0 : ρ.o c ≠ z := by rw [hy]; simp
  have hterms : ∀ t ∈ (children M j).map ρ.o, isOT t = true := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hG.ot_o d (mem_children hd).2
  have hmem := T2SrcLeaf.mem_le_sumN hterms (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hsum : one ≤ sumN ((children M j).map ρ.o) := le_trans (one_le_of_ne_z hc0) hmem
  have hω := omega_le_omega isOT_one (isOT_sumN _ hterms) hsum
  have hone : one < omega one := by decide
  unfold bumpTerm
  rw [if_pos hb]
  exact lt_of_lt_of_le hone hω

/-- The real failed drop yields an actual earlier bump branch between
the new and old changing branch terms. Both the branch and its target
are before the current source column. -/
theorem source_failed_earlier_bump {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) {r L i : Nat}
    (hx : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hi : i < r + L) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hT : Cons (M.take (r + L)) τ) (hf : WfT2Abs.DropFail M ρ τ (r + L) i) :
    ∃ m j c b k j0, par M 0 i = some m ∧ par M 1 i = some m ∧
      j ∈ children M i ∧ col M j = bump M i ∧
      c ∈ children M j ∧ c < r + L ∧ τ.o c ≠ ρ.o c ∧
      Up1 M b m ∧ upg M b = some k ∧ k < i ∧
      j0 ∈ children M k ∧ col M j0 = bump M k ∧ j0 < i ∧
      ¬ bumpTerm M ρ k j0 < bumpTerm (M.take (r + L)) τ i j ∧
      bumpTerm M ρ k j0 < bumpTerm M ρ i j := by
  obtain ⟨m, j, c, b, k, d, hmi, hm1, hj, hb, hc, hcx, hce, hbm, hu, hki, hd, hdn, hdo⟩ :=
    source_failed_descends C hx hr hi h1 h2 hT hf
  have hGT : Good3 (M.take (r + L)) τ := by
    have he : M.length - 1 = r + L := by omega
    rw [← he] at hT ⊢
    exact good3_take_any (Inv3W.ofV2 C.S C.I) C.toW (by omega) hT
  have hjx : j < r + L := Nat.lt_trans (mem_children hc).1 hcx
  have hbT : col (M.take (r + L)) j = bump (M.take (r + L)) i := by
    rw [col_take M hjx, bump_take M hi, hb]
  have hcT : c ∈ children (M.take (r + L)) j := mem_take_children hc hcx
  have hd1 : d ≠ one := by
    intro he
    rw [he] at hdn
    exact hdn (one_lt_nonempty_bump hT hGT hbT hcT)
  obtain ⟨j0, hj0, hb0, he⟩ := bump_exponent_summand C.I.good hd hd1
  have hj0i := origin_bump_child_lt_source C.S (by omega) hm1 hbm hu hj0 hb0
  rw [he] at hdn hdo
  exact ⟨m, j, c, b, k, j0, hmi, hm1, hj, hb, hc, hcx, hce, hbm, hu, hki,
    hj0, hb0, hj0i, hdn, hdo⟩

end Ytosk.T2SrcOrigins
