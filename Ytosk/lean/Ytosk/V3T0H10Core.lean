/-
The exact structural input still needed for H10.
U3 has been checked on all 20 probe sets. The implication from U3 to H10
uses no value comparison: a row-1-zero parent makes absorption empty.
The proposed universal U3 is false on 68 graft/expansion frames (bms standard,
below SRO). All 68 still have strong absorption: their parent values are
finite naturals 1, 2 or 3. No U3 theorem or top-level replacement is asserted.
-/
import Ytosk.V3T0SeedSum
import Ytosk.V3S1Std
import Core

namespace Ytosk.T0H10Core
open T

/-- The H10 frame without Bad2 or valuation assumptions. -/
structure Frame (M : Mat) (r L g : Nat) : Prop where
  len : r + L + 1 = M.length
  pos : 0 < L
  parent : par M 0 (r + L) = some r
  row1 : entry M 1 (r + L) = 0
  grandparent : par M 0 r = some g
  nonlast : r ≠ r + L - 1
  separated : r - 1 ≠ g
  counted : Counted M g r
  topped : Ytosk.topped (M.take (r + L)) r = true

/-- U3's conclusion, with both upgrades as explicit inputs.
This is a proof interface, not an additional assumption of the top theorem. -/
def ParentZeroAt (M : Mat) (r L : Nat) : Prop :=
  upg M (r - 1) = some r → ∀ k, upg M (r + L - 1) = some k →
    ∃ p, par M 1 (r + L - 1) = some p ∧ entry M 1 p = 0

/-- A zero row-1 parent leaves no summands for the strong absorption test. -/
theorem strong_of_parent_zero {M : Mat} {ρ : Valn} (hC : Cons M ρ)
    {x p : Nat} (hx : x ≤ M.length) (hp : par M 1 (x - 1) = some p) (he : entry M 1 p = 0) :
    UpgAbsX M x ρ := by
  have hpN : p < M.length := by
    have := par_lt M 1 (x - 1) p hp
    omega
  have hv : vOpt ρ (par M 1 (x - 1)) = z := by
    rw [hp]
    exact v_z_of_e1 hC hpN he
  intro i k W hix hu hW hW0 q hq
  have hi : i = x - 1 := by omega
  subst i
  rw [hv] at hq
  simp only [summands, List.not_mem_nil] at hq

/-- Finite natural parent values also make absorption strong.
This covers the 68 measured counterexamples to the overstrong U3 proposal. -/
theorem strong_of_finite_parent {M : Mat} {ρ : Valn} {x : Nat}
    (hfinite : ∀ q ∈ summands (vOpt ρ (par M 1 (x - 1))), q = one) :
    UpgAbsX M x ρ := by
  intro i k W hix _ _ _ q hq hlt
  have hi : i = x - 1 := by omega
  subst i
  have hq1 := hfinite q hq
  subst q
  exact lhd_one hlt

/-- Hypothetical bridge from U3 to H10. The universal premise is refuted in
V3T0H10U3Counterexample and is not an assumption of the top theorem. -/
theorem h10_of_parent_zero
    (hU3 : ∀ M, Std M → M ≠ SRO → ∀ r L g, Frame M r L g → ParentZeroAt M r L) :
    T0SeedSum.T0BadSeedsH10 := by
  intro M ρ rk hM hNe hBad I r L hlen hL hp he g hg hr hn hc ht hu
  have hf : Frame M r L g := ⟨hlen, hL, hp, he, hg, hr, hn, hc, ht⟩
  have hlength : M.length - 1 = r + L := by omega
  have hlength' : M.length - 2 = r + L - 1 := by omega
  obtain ⟨⟨k, hk⟩, p, b, hp', hb, hcol, hbad⟩ := hBad
  rw [hlength'] at hk
  obtain ⟨q, hq, hq1⟩ := hU3 M hM hNe r L g hf hu k hk
  rcases hbad with hbad | hbad
  · obtain ⟨_, σ, hσ, hnot⟩ := hbad
    rw [hlength] at hnot
    exact hnot (strong_of_parent_zero hσ (by omega) hq hq1)
  · have hne := hbad.2.1
    rw [hlength] at hne
    exact hne he

/-- Toppedness forces the final upgrade to land strictly before the copy root.
This uses only the existing structural invariant, not Core or value bounds. -/
theorem target_before_root {M : Mat} {r L g k : Nat} (S : SInv M)
    (F : Frame M r L g) (hu : upg M (r + L - 1) = some k) :
    k < r ∧ Anc0 M k r := by
  have hlen := F.len
  have hL := F.pos
  have hnlast := F.nonlast
  have hrx : r < r + L - 1 := by omega
  have hx : r + L < M.length := by omega
  obtain ⟨m, hm, hmk, hcol, hnext | ⟨hAk, hkn⟩⟩ := upg_spec hu
  · have he : entry M 1 k = entry M 1 (r + L - 1) := e1_of_col hcol
    have hpos := par1_entry_lt hm
    have heq : k = r + L := by omega
    rw [heq, F.row1] at he
    omega
  · have hAr : Anc0 M r (r + L - 1) :=
      anc_between (anc0_of_par M 0 r (r + L) F.parent) _ (by omega) (by omega)
    have hne : k ≠ (r + L - 1) + 1 := by omega
    have hd := upg_climb_e0 hu hne
    have hdr := S.r0p (r + L) r F.parent
    have hkr : k ≠ r := by
      intro heq
      subst k
      have hu' : upg M (r + (L - 1)) = some r := by
        simpa only [show r + (L - 1) = r + L - 1 from by omega] using hu
      have hnot := upg_r_not_topped F.len F.parent S.r0p S.z2 S.sibDec S.z1c S.uab
        (q := L - 1) (by omega) (by omega) hu'
      rw [F.topped] at hnot
      cases hnot
    have hAkr : Anc0 M k r := by
      rcases anc0_total hAk hAr with h | h
      · exact h
      · have hlt := anc0_e0_lt h (Ne.symm hkr)
        have heq : (r + L - 1) + 1 = r + L := by omega
        rw [heq] at hd
        omega
    exact ⟨lt_of_le_of_ne hAkr.le hkr, hAkr⟩

/-- The row-1 parent sought by U3 is a strict ancestor of g. -/
theorem source_parent_before_grandparent {M : Mat} {r L g k : Nat} (S : SInv M)
    (F : Frame M r L g) (hu : upg M (r + L - 1) = some k) :
    ∃ p, par M 1 (r + L - 1) = some p ∧ p < g ∧ Anc0 M p g := by
  obtain ⟨hkr, hAkr⟩ := target_before_root S F hu
  obtain ⟨p, hp, hpk⟩ := upg_target_par0 S.r0p hu
  have hpklt := par_lt M 0 k p hpk
  have hAkg : Anc0 M k g := anc0_par hAkr (by omega) F.grandparent
  have hApk : Anc0 M p k := anc0_of_par M 0 p k hpk
  exact ⟨p, hp, by have := hAkg.le; omega, hApk.trans hAkg⟩

/-- The final source cannot have row 1 above g: its row-1 parent
has already been skipped before reaching g. -/
theorem source_row_le_grandparent {M : Mat} {r L g k : Nat} (S : SInv M)
    (F : Frame M r L g) (hu : upg M (r + L - 1) = some k) :
    entry M 1 (r + L - 1) ≤ entry M 1 g := by
  obtain ⟨p, hp, hpg, _⟩ := source_parent_before_grandparent S F hu
  have hlen := F.len
  have hL := F.pos
  have hnlast := F.nonlast
  have hAr : Anc0 M r (r + L - 1) :=
    anc_between (anc0_of_par M 0 r (r + L) F.parent) _ (by omega) (by omega)
  exact par1_between hp g ((anc0_of_par M 0 g r F.grandparent).trans hAr) hpg

/-- The small-grandparent case closes structurally, without Core or S1.
All 33 measured nonvacuous U3 frames have entry1(g)=1. -/
theorem parent_zero_of_small_grandparent {M : Mat} {r L g : Nat} (S : SInv M)
    (F : Frame M r L g) (hg : entry M 1 g ≤ 1) : ParentZeroAt M r L := by
  intro _ k hu
  obtain ⟨p, hp, _, _⟩ := source_parent_before_grandparent S F hu
  have hs := source_row_le_grandparent S F hu
  have hp1 := par1_entry_lt hp
  exact ⟨p, hp, by omega⟩

/-- The actual remaining H10 field, restricted to entry1(g) at least two.
The U3 conclusion is not assumed here; standard U3 counterexamples still
have strong absorption and hence do not satisfy Bad2. -/
def T0BadSeedsH10Big : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ r L,
    r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ g, par M 0 r = some g → 2 ≤ entry M 1 g →
      r ≠ r + L - 1 → r - 1 ≠ g → Counted M g r → topped (M.take (r + L)) r = true →
        upg M (r - 1) ≠ some r

/-- A pointwise parent-zero certificate contradicts Bad2 in this frame. -/
theorem no_upgrade_of_parent_zero {M : Mat} {r L g : Nat}
    (F : Frame M r L g) (hBad : Bad2 M) (hP : ParentZeroAt M r L) :
    upg M (r - 1) ≠ some r := by
  intro hu
  have hlen := F.len
  have hlength : M.length - 1 = r + L := by omega
  have hlength' : M.length - 2 = r + L - 1 := by omega
  obtain ⟨⟨k, hk⟩, p, b, hp', hb, hcol, hbad⟩ := hBad
  rw [hlength'] at hk
  obtain ⟨q, hq, hq1⟩ := hP hu k hk
  rcases hbad with hbad | hbad
  · obtain ⟨_, σ, hσ, hnot⟩ := hbad
    rw [hlength] at hnot
    exact hnot (strong_of_parent_zero hσ (by omega) hq hq1)
  · have hne := hbad.2.1
    rw [hlength] at hne
    exact hne F.row1

/-- Only the large-grandparent case needs a residual. The small case is a theorem. -/
theorem h10_of_big (hBig : T0BadSeedsH10Big) : T0SeedSum.T0BadSeedsH10 := by
  intro M ρ rk hM hNe hBad I r L hlen hL hp he g hg hr hn hc ht
  by_cases hbig : 2 ≤ entry M 1 g
  · exact hBig M ρ rk hM hNe hBad I r L hlen hL hp he g hg hbig hr hn hc ht
  · have F : Frame M r L g := ⟨hlen, hL, hp, he, hg, hr, hn, hc, ht⟩
    exact no_upgrade_of_parent_zero F hBad
      (parent_zero_of_small_grandparent (sInv_std hM hNe) F (by omega))

/-- The restricted residual follows immediately from the former one. -/
theorem h10_big_of_h10 (h : T0SeedSum.T0BadSeedsH10) : T0BadSeedsH10Big := by
  intro M ρ rk hM hNe hBad I r L hlen hL hp he g hg _ hr hn hc ht
  exact h M ρ rk hM hNe hBad I r L hlen hL hp he g hg hr hn hc ht

/-- The Core comparison at P1(g),g is above the final source parent. -/
theorem core_parent_above_source_parent {M : Mat} {r L g k p : Nat} (S : SInv M)
    (F : Frame M r L g) (hu : upg M (r + L - 1) = some k)
    (hp : par M 1 (r + L - 1) = some p) :
    ∃ a, par M 1 g = some a ∧ p ≤ a ∧ Anc0 M p a ∧ entry M 2 a = 0 := by
  obtain ⟨p', hp', hpg, hApg⟩ := source_parent_before_grandparent S F hu
  rw [hp] at hp'
  cases hp'
  have hrow := source_row_le_grandparent S F hu
  have hpos := par1_entry_lt hp
  obtain ⟨a, ha, hpa, hApa⟩ := par1_near hApg (by omega) (by omega)
  have hgM : g < M.length := by
    have hg := par_lt M 0 r g F.grandparent
    have hlen := F.len
    have hL := F.pos
    omega
  have ha0 : entry M 2 a = 0 := by
    by_contra h
    have ha1 : entry M 2 a = 1 := by have := S.z2 a; omega
    exact no_par1_of_e2 S.z1c hgM ha1 ha
  exact ⟨a, ha, hpa, hApa, ha0⟩

/-- The next upgrade identifies the root's parent in both rows and fixes row 2. -/
theorem next_root_shape {M : Mat} {r L g : Nat} (S : SInv M)
    (F : Frame M r L g) (hu : upg M (r - 1) = some r) :
    par M 1 (r - 1) = some g ∧ par M 1 r = some g ∧
      entry M 2 g = 0 ∧ entry M 2 r = 1 := by
  obtain ⟨g', hp, hpg⟩ := upg_target_par0 S.r0p hu
  rw [F.grandparent] at hpg
  cases hpg
  obtain ⟨m, hm, hmr, hcol, _⟩ := upg_spec hu
  rw [hp] at hm
  cases hm
  have he2 := e2_of_col hcol
  have hr2 := S.z2 r
  exact ⟨hp, hmr, by omega, by omega⟩

/-- Core's two columns have equal zero row 2 and positive row-0/row-1 offsets. -/
theorem core_pair_shape {M : Mat} {r L g k p : Nat} (S : SInv M)
    (F : Frame M r L g) (hu0 : upg M (r - 1) = some r)
    (hu : upg M (r + L - 1) = some k) (hp : par M 1 (r + L - 1) = some p) :
    ∃ a d f, par M 1 g = some a ∧ entry M 2 a = 0 ∧ 0 < d ∧ 0 < f ∧
      col M g = (entry M 0 a + d, entry M 1 a + f, 0) := by
  obtain ⟨a, ha, _, _, ha2⟩ := core_parent_above_source_parent S F hu hp
  have ha1 := par1_entry_lt ha
  have hag := par_lt M 1 g a ha
  have ha0 := anc0_e0_lt (anc0_of_par M 1 a g ha) (by omega)
  have hg2 := (next_root_shape S F hu0).2.2.1
  refine ⟨a, entry M 0 g - entry M 0 a, entry M 1 g - entry M 1 a, ha, ha2,
    by omega, by omega, ?_⟩
  rw [col_eq_entries, hg2]
  congr 2 <;> omega

/-- The strict spine hypothesis of Core follows from the actual row-1 parent.
The decomposition is only a positional way of naming the two columns. -/
theorem spine_of_parent_split {G A R : Mat} {p q : Nat × Nat × Nat}
    (hp : par ((G ++ (p :: A)) ++ q :: R) 1 (G.length + 1 + A.length) = some G.length) :
    TRIO.SpineOK A q.1 (p.2.1 + 1) := by
  let P := (G ++ (p :: A)) ++ [q]
  have htake : (((G ++ (p :: A)) ++ q :: R).take (G.length + 1 + A.length + 1)) = P := by
    have take_one (Q : Mat) : (Q ++ q :: R).take (Q.length + 1) = Q ++ [q] := by
      rw [List.take_append, List.take_of_length_le (by omega)]
      simp
    simpa only [P, List.length_append, List.length_cons, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using take_one (G ++ p :: A)
  have hpP : par P 1 (G.length + 1 + A.length) = some G.length := by
    rw [← htake, par_take _ 1 _ (by omega)]
    exact hp
  have hroot : G.length < P.length := by simp [P]
  have hlast : G.length + 1 + A.length < P.length := by simp only [P, List.length_append, List.length_cons]; omega
  have hle := le1_par1_up (TRIO.le1_refl hroot) hpP hlast
  have hh : TRIO.le1 P G.length (G ++ (p :: A)).length := by
    simpa only [List.length_append, List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hle
  exact TRIO.spineOK_strict_of_le1 hh

/-- Core at two actual parent/child positions requires no separate spine premise. -/
theorem core_bound_of_parent_split {M X A B A2 Z : Mat} {u w z e f : Nat}
    (hCore : TRIO.ArgDomCoreOn M)
    (hM : M = (X ++ (u, w, z) :: (A ++ (u + e, w + f, z) :: (B ++ A2))) ++ Z)
    (hpar : par M 1 (X.length + 1 + A.length) = some X.length)
    (he : 0 < e) (hz : f = 0 ∨ z = 0)
    (hA : ∀ t ∈ A, u < t.1) (hB : ∀ t ∈ B, u + e < t.1)
    (hA2 : ∀ t ∈ A2, u < t.1)
    (hA2head : A2 = [] ∨ (A2.headI).1 ≤ u + e)
    (hZhead : Z = [] ∨ (Z.headI).1 ≤ u) :
    TRIO.sle B (TRIO.hshift w e f (A ++ (u + e, w + f, z) :: (B ++ A2))) := by
  have hp : par ((X ++ ((u, w, z) :: A)) ++ (u + e, w + f, z) :: (B ++ A2 ++ Z))
      1 (X.length + 1 + A.length) = some X.length := by
    rw [hM] at hpar
    simpa only [List.append_assoc, List.cons_append] using hpar
  exact hCore hM he hz hA hB hA2 hA2head hZhead (spine_of_parent_split hp)

/-- S1 orders a later sibling against any earlier sibling, not only adjacent ones. -/
theorem sibling_subtree_bound {M : Mat} (hS : S1 M) (p : Nat) :
    ∀ (l : List Nat) (pre : List Nat) (a : Nat), children M p = pre ++ a :: l →
      ∀ b ∈ l, TRIO.sle (subT M b) (subT M a) := by
  intro l
  induction l with
  | nil => intro pre a h b hb; simp at hb
  | cons c l ih =>
    intro pre a h b hb
    have hac : TRIO.sle (subT M c) (subT M a) := by
      have hnot : ¬ TRIO.seqlex (subT M a) (subT M c) := by
        intro hlt
        have hb := (seqLtB_iff_seqlex _ _).mpr hlt
        rw [hS p pre l a c h] at hb
        cases hb
      rcases TRIO.seqlex_total (subT M c) (subT M a) with he | hca | hac
      · exact Or.inl he
      · exact Or.inr hca
      · exact False.elim (hnot hac)
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hac
    · have htail : children M p = (pre ++ [a]) ++ c :: l := by
        simpa only [List.append_assoc, List.singleton_append] using h
      exact TRIO.sle_trans (ih (pre ++ [a]) c htail b hb) hac

/-- R1S makes every actual row-1 parent edge a unit step.
This rules out the lifted full-Core counterexamples with skipped row-1 values. -/
theorem par1_row_eq_succ {M : Mat} (hR1 : R1S M) {c p : Nat}
    (hp : par M 1 c = some p) : entry M 1 c = entry M 1 p + 1 := by
  have hpc := par_lt M 1 c p hp
  have hA : Anc0 M p c := anc0_of_par M 1 p c hp
  obtain ⟨d, hdp, hAdc⟩ := anc0_child hA (by omega)
  have hpd := par_lt M 0 d p hdp
  have hlow := par1_between hp d hAdc hpd
  have hupp := hR1 d p hdp
  have hlt := par1_entry_lt hp
  omega

/-- With the R1S input supplied by Std, Core at P1(g),g has row-1 shift exactly one. -/
theorem core_pair_unit_shift {M : Mat} {r L g k p : Nat} (S : SInv M) (hR1 : R1S M)
    (F : Frame M r L g) (hu0 : upg M (r - 1) = some r)
    (hu : upg M (r + L - 1) = some k) (hp : par M 1 (r + L - 1) = some p) :
    ∃ a d, par M 1 g = some a ∧ entry M 2 a = 0 ∧ 0 < d ∧
      col M g = (entry M 0 a + d, entry M 1 a + 1, 0) := by
  obtain ⟨a, d, f, ha, ha2, hd, hf, hcol⟩ := core_pair_shape S F hu0 hu hp
  have hunit := par1_row_eq_succ hR1 ha
  have hrow := e1_of_col hcol
  have hfeq : f = 1 := by omega
  subst f
  exact ⟨a, d, ha, ha2, hd, hcol⟩

/-- The proved standard-form input available for the remaining structural proof. -/
theorem core_of_std {M : Mat} (hM : Std M) (hne : M ≠ []) : TRIO.ArgDomCoreOn M :=
  TRIO.argDomCoreOn_ST_TS ((std_stts hM).resolve_left hne)

end Ytosk.T0H10Core
