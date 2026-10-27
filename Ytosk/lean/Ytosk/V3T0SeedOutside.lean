/-
Stable subscript equations for the non-lost t=0 seed (2026-10-27).
-/
import Ytosk.V3HUAC
import Ytosk.V3RootPath

namespace Ytosk.T0SeedOutside

open T

/-- A row-2-zero changing column cannot keep a row-0 child in the prefix. -/
theorem topC_no_child_zero {M : Mat} (S : SInv M) {x i c : Nat}
    (hx : x ≤ M.length) (hi : i < x) (h2 : entry M 2 i = 0)
    (hTop : TopC M x i) (hc : c ∈ children (M.take x) i) : False := by
  classical
  have hcM : c ∈ children M i := by
    rw [children_take, List.mem_filter] at hc
    exact hc.1
  have hcx : c < x := by
    have := (mem_children hc).2
    simp only [List.length_take] at this
    omega
  have hcp : par M 0 c = some i := (mem_children_iff.mp hcM).2
  have hnb : col (M.take x) c ≠ bump (M.take x) i := by
    rw [col_take M hcx, bump_take M hi]
    intro h
    have := S.bumpE2 i c hcM h
    omega
  have hnc := hTop.2.1 c hc
  have hU : isUpg (M.take x) c = true := by
    by_contra h
    exact hnc ⟨hnb, fun h' => h h'.1⟩
  obtain ⟨j, hjx, hj⟩ := (isUpg_take M hx c).mp hU
  obtain ⟨p, hp, hpc⟩ := upg_target_par0 S.r0p hj
  obtain ⟨p', hp', hpc', _, _⟩ := upg_spec hj
  rw [hp] at hp'; cases hp'
  rw [hcp] at hpc; cases hpc
  exact hTop.2.2 c hcx hpc'

/-- A row-2-zero column with an earlier child has an unchanged subscript on a drop. -/
theorem v_stable_zero_child {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat}
    (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) {x i c : Nat}
    (hx : x + 1 = M.length) (hi : i < x) (h2 : entry M 2 i = 0)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT)
    (hc : c ∈ children (M.take x) i) : τ.v i = ρ.v i := by
  apply (chg_off hx hC hG hT hRT i hi).2
  intro hchg
  exact topC_no_child_zero S (by omega) hi h2
    ((chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hchg).1 rfl hi) hc

/-- A non-leaf below a bump child necessarily has row 2 zero. -/
theorem zero_below_bump_of_child {M : Mat} (hBL : BumpLeaf M) (hJ : RowJ M)
    {pp g r x : Nat} (hg : g ∈ children M pp) (hgb : col M g = bump M pp)
    (hr : r ∈ children M g) (hx : x ∈ children M r) : entry M 2 r = 0 := by
  by_contra h2
  have hlow := hJ r g h2 (mem_children_iff.mp hr).2
  have he : entry M 1 g = entry M 1 pp := e1_of_col hgb
  have hleaf := (hBL pp g r hg hgb hr (by omega)).2.1
  rw [hleaf] at hx
  simp at hx

/-- Equal subscripts remove the weak alternative of PO. -/
theorem po_strong_of_v_eq {M : Mat} {ρ τ : Valn} {x i : Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hT : Cons (M.take x) τ)
    (hi : i < x) (hx : x ≤ M.length) (hot : isOT (τ.v i) = true)
    (hv : τ.v i = ρ.v i) (hPO : PO ρ τ i) : LhdE (τ.o i) (ρ.o i) := by
  rcases hPO.1 with h | ⟨⟨w', w, X, hw', hw, hlt, _⟩, _⟩
  · exact h
  · have hiT : i < (M.take x).length := by simp only [List.length_take]; omega
    obtain ⟨y', hy'⟩ := o_psi_sub hT hiT
    obtain ⟨y, hy⟩ := o_psi_sub hC (show i < M.length by omega)
    rw [hy', sf_ot hot] at hw'
    rw [hy, sf_ot (hG.ot_v i (by omega))] at hw
    have he' := hw'
    have he := hw
    simp only [psi.injEq] at he' he
    have : w' = w := by rw [← he'.1, ← he.1, hv]
    rw [this] at hlt
    exact False.elim (lt_irrefl' _ hlt)

/-- A row-1 parent of a remaining column has unchanged value. -/
theorem vOpt_par1_stable {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat}
    (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) {x i : Nat}
    (hx : x + 1 = M.length) (hi : i < x)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) :
    vOpt τ (par M 1 i) = vOpt ρ (par M 1 i) := by
  cases hp : par M 1 i with
  | none => rfl
  | some p =>
    show τ.v p = ρ.v p
    have hpi := par_lt M 1 i p hp
    apply (chg_off hx hC hG hT hRT p (by omega)).2
    intro hchg
    exact (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hchg).1 rfl (by omega)
      |>.2.2 i hi hp

/-- A row-2-zero column without an upgrade has unchanged value. -/
theorem v_stable_zero_no_upg {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat}
    (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) {x i : Nat}
    (hx : x + 1 = M.length) (hi : i < x) (h2 : entry M 2 i = 0)
    (hu : upg M i = none) (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) :
    τ.v i = ρ.v i := by
  have hiT : i < (M.take x).length := by simp only [List.length_take]; omega
  have hUT : upg (M.take x) i = none := by
    by_cases hix : i + 1 < x
    · rw [upg_take M hix, hu]
    · exact upg_last_none (by simp only [List.length_take]; omega)
  have hV := vOpt_par1_stable S hC hG hx hi hT hRT
  rw [(hT i hiT).2, (hC i (by omega)).2]
  unfold vRhs
  rw [entry_take M 1 hi, entry_take M 2 hi, par_take M 1 i hi]
  by_cases h1 : entry M 1 i = 0
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2, hUT, hu, hV]

/-- Outside the lost ancestor-upgrade case, the seed below a bump has unchanged index. -/
theorem seed_v_stable {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat}
    (S : SInv M) (hBL : BumpLeaf M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {x r g pp : Nat}
    (hx : x + 1 = M.length) (hp : par M 0 x = some r)
    (hg : par M 0 r = some g) (hpp : par M 0 g = some pp)
    (hgb : col M g = bump M pp)
    (hnlost : ¬ (r = x - 1 ∧ ∃ k, upg M r = some k ∧ k < r))
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT) : τ.v r = ρ.v r := by
  have hrx := par_lt M 0 x r hp
  have hgr := par_lt M 0 r g hg
  have hpg := par_lt M 0 g pp hpp
  have hxCh : x ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
  have hrCh : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
  have hgCh : g ∈ children M pp := mem_children_iff.mpr ⟨by omega, hpp⟩
  have h2 := zero_below_bump_of_child hBL hJ hgCh hgb hrCh hxCh
  by_cases hlast : r = x - 1
  · have hu : upg M r = none := by
      cases hu : upg M r with
      | none => rfl
      | some k =>
        obtain ⟨_, _, _, _, he | ⟨_, hk⟩⟩ := upg_spec hu
        · have hnext : upg M r = some (r + 1) := by rw [he] at hu; exact hu
          have := leaf_of_upg_next S.r0p hnext x (Anc0.step hp (Anc0.refl r))
          omega
        · exact False.elim (hnlost ⟨hlast, k, hu, hk⟩)
    exact v_stable_zero_no_upg S hC hG hx hrx h2 hu hT hRT
  · have hc : r + 1 ∈ children (M.take x) r := by
      refine mem_children_iff.mpr ⟨by simp only [List.length_take]; omega, ?_⟩
      rw [par_take M 0 (r + 1) (by omega)]
      exact child_succ (Anc0.step hp (Anc0.refl r)) (by omega)
    exact v_stable_zero_child S hC hG hx hrx h2 hT hRT hc

/-- The strong first seed conclusion outside the lost ancestor-upgrade case.
The only drop input is its already available conclusion PO/PV. -/
theorem seed_lhd_outside {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat}
    (S : SInv M) (hBL : BumpLeaf M) (hJ : RowJ M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {x r g pp : Nat}
    (hx : x + 1 = M.length) (hp : par M 0 x = some r)
    (hg : par M 0 r = some g) (hpp : par M 0 g = some pp)
    (hgb : col M g = bump M pp) (hx1 : entry M 1 x = 0)
    (hnlost : ¬ (r = x - 1 ∧ ∃ k, upg M r = some k ∧ k < r))
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT)
    (hdrop : ∀ i, i < x → PO ρ τ i ∧ PV M ρ τ i) : Lhd z (τ.o r) (ρ.o r) := by
  have hrx := par_lt M 0 x r hp
  have h2 : entry M 2 x = 0 := S.r12 x hx1
  have hxCh : x ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
  have hCnt : Counted M r x := by
    refine ⟨?_, ?_⟩
    · intro h
      have := e2_of_col h
      omega
    · rw [not_isUpg_e2z h2]
      simp
  have hxCL : x ∈ CL M r := by
    unfold CL
    exact List.mem_filter.mpr ⟨hxCh, by simpa using hCnt⟩
  have hlast : ∀ d ∈ CL M r, d ≤ x := by
    intro d hd
    have hdc : d ∈ children M r := (List.mem_filter.mp hd).1
    have := (mem_children hdc).2
    omega
  have hstrict : τ.o r < ρ.o r :=
    o_strict_frame hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hC hG hT hRT hdrop
      hrx hxCL hlast (fun h => False.elim (Nat.lt_irrefl x h))
  have hv := seed_v_stable S hBL hJ hC hG hx hp hg hpp hgb hnlost hT hRT
  exact lhd_of_lhdE_lt
    (po_strong_of_v_eq hC hG hT hrx (by omega) (hdrop r hrx).2.2 hv (hdrop r hrx).1) hstrict

/-- The two still open fields of H8: the bump sum and the preceding upgrade. -/
def T0BadSeedsH9 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Bad2 M → Inv3V2 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    (∀ g, par M 0 r = some g → r ≠ r + L - 1 → col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 →
      ¬ (children (M.take (r + L)) r = [r + L - 1] ∧ ∃ k, upg M (r + L - 1) = some k ∧ k < r + L - 1) →
      LhdE (omega (sumN ((children (M.take (r + L)) r).map (drop1 M (r + L) rk).o)))
          (omega (sumN ((children (M.take (r + L)) r).map ρ.o))) ∨
        ∀ s b', omega (sumN ((children (M.take (r + L)) r).map ρ.o)) = psi s b' z →
          ∀ u, ∀ e ∈ comps u (omega (sumN ((children (M.take (r + L)) r).map (drop1 M (r + L) rk).o))),
            ∃ d ∈ z :: b' :: (comps u b' ++ comps u s), e ≤ d) ∧
    (∀ g, par M 0 r = some g → r ≠ r + L - 1 → r - 1 ≠ g → Counted M g r → topped (M.take (r + L)) r = true →
      upg M (r - 1) ≠ some r)

/-- H8's first field follows from the existing drop hypothesis; H9 keeps only fields 2 and 3. -/
theorem t0BadSeedsH8_of (hDU : HDropU) (h9 : T0BadSeedsH9) : T0BadSeedsH8 := by
  intro M ρ rk hM hS hB I r L hlen hL hp he1
  obtain ⟨h2, h3⟩ := h9 M ρ rk hM hS hB I r L hlen hL hp he1
  refine ⟨?_, h2, h3⟩
  intro hnlost g pp hg hpp _ _ hgb
  have S := sInv_std hM hS
  obtain ⟨SX, SJ⟩ := sInvXJ_std hM hS
  obtain ⟨R, _⟩ := hDU M ρ rk hM hS (by intro h; subst h; simp at hlen) I
  have hx : (r + L) + 1 = M.length := hlen
  have hcnt := counted_take_last (M := M) (show 1 ≤ M.length by omega)
    S.r0p S.z2 S.sibDec S.z1c S.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRT : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hT := cons_of_rk hRT
  have he : M.length - 1 = r + L := by omega
  rw [he] at R
  have hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV M ρ (drop1 M (r + L) rk) i :=
    drop_all_hardB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hT hRT I.vs R.vst I.fc I.fo
      R.hard (bump_dropB hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hT hRT I.kd I.td R.ab R.ws) R.ua
  left
  apply seed_lhd_outside S SX.loc.2.2.2 SJ I.cons I.good hx hp hg hpp hgb he1 ?_ hT hRT hdrop
  rintro ⟨hr, k, hk, hkr⟩
  exact hnlost ⟨by omega, k, hk, hkr⟩

end Ytosk.T0SeedOutside
