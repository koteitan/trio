/-
**WfCofH1 (2026-11-01): `HRootD` and `HNotSucc` without hypotheses.**

- `hRootD`   : a standard `A ≠ SRO` with nonzero last column has its bad root (`parLast_of` and the structural
  invariants `sInv_std`).
- `hNotSucc` : the value of a standard `A ≠ SRO` with nonzero last column is not a successor. The last root `Rt`
  (a `(0,0,0)` column after which every column is nonzero) has the child `Rt + 1`, which is counted
  (`R12` excludes the bump `(1,0,1)`, `UAT` excludes "upgraded and topped"), so `o(Rt) = sf(ψ_0(S))` with `S ≠ 0`.
  Its last summand is `ψ_0(B)` with `B ≠ 0`, which survives `sf` and the sum of the roots (`NS`), and
  `cof ψ_0(B) ∈ {ω, Ω_{μ+1}}`, never `succ`.
-/
import Ytosk.WfCofL4
import Ytosk.V3InvExpand
import Ytosk.V3StructT1
import Ytosk.V3T0F
import Ytosk.V3StepVG
import Ytosk.V3BumpDrop

namespace Ytosk.WfCofH1

open T Ytosk

set_option linter.unusedSectionVars false

/-! ## HRootD -/

theorem lastTy_eq (A : Mat) : lastTy A = TRIO.srow A (A.length - 1) := rfl

/-- **The bad root exists** (structural). -/
theorem hRootD : HRootD := by
  intro A tA a b μ ⟨hA, hS, _, hz, _, _⟩
  have I := sInv_std hA hS
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  exact ⟨r, by rw [BRoot, lastTy_eq]; exact hr⟩

/-! ## Terms whose last summand is `ψ_0(B)`, `B ≠ 0` -/

/-- The last summand is `ψ_0(B)` with `B ≠ 0`. -/
def NS (t : T) : Prop := ∃ B, B ≠ z ∧ last t = psi z B z

theorem last_psi_of_ne {a b w : T} (hw : w ≠ z) : last (psi a b w) = last w := by
  cases w with
  | z => exact absurd rfl hw
  | psi => rfl

theorem last_add_of_ne : ∀ (A : T) {y : T}, y ≠ z → last (add A y) = last y
  | z, _, _ => rfl
  | psi a b c, y, hy => by
    cases y with
    | z => exact absurd rfl hy
    | psi d e f =>
      simp only [add]
      split
      · rfl
      · rw [last_psi_of_ne (add_ne_z_right c (by simp))]
        exact last_add_of_ne c (by simp)

theorem NS.ne_z {t : T} (h : NS t) : t ≠ z := by
  rintro rfl; obtain ⟨B, _, hB⟩ := h; simp [last] at hB

theorem NS_add (A : T) {y : T} (h : NS y) : NS (add A y) := by
  have hne := h.ne_z
  obtain ⟨B, hB, hl⟩ := h
  exact ⟨B, hB, by rw [last_add_of_ne A hne, hl]⟩

theorem sub_psi_z {s y : T} (hy : y ≠ z) : sub (psi s y z) (psi s z z) = psi s y z := by
  cases y with
  | z => exact absurd rfl hy
  | psi p q w => simp [sub, lt]

theorem lt_z_right (b : T) : lt b z = false := by cases b <;> rfl

/-- `sp` keeps a nonzero argument. -/
theorem sp_ns (a : T) : ∀ (x b : T), (b ≠ z ∨ x ≠ z) → ∃ B, B ≠ z ∧ sp a b x = psi a B z
  | z, b, h => ⟨b, h.resolve_right (fun h' => h' rfl), by simp [sp]⟩
  | psi s y c, b, _ => by
    unfold sp
    split
    · rename_i hlt
      apply sp_ns a c
      left
      have hy : y ≠ z := by
        rintro rfl; rw [lt_z_right] at hlt; simp at hlt
      by_cases ht : cut (add s one) y = z
      · simp only [ht]
        rw [sub_psi_z hy]
        simp [add]
      · exact add_ne_z_left _ ht
    · exact sp_ns a c _ (Or.inl (add_ne_z_right _ (by simp)))

theorem sf_z' : sf z = z := by simp [sf]

theorem NS_sf : ∀ {t : T}, NS t → NS (sf t)
  | z, h => absurd rfl h.ne_z
  | psi a b c, h => by
    obtain ⟨B, hB, hl⟩ := h
    by_cases hc : c = z
    · subst hc
      simp only [last] at hl
      obtain ⟨rfl, rfl, -⟩ := T.psi.inj hl
      simp only [sf]
      rw [add_z_right]
      obtain ⟨B', hB', he⟩ := sp_ns z (sf b) z (Or.inr (sf_ne_z hB))
      exact ⟨B', hB', by rw [he]; rfl⟩
    · rw [last_psi_of_ne hc] at hl
      have ih := NS_sf (t := c) ⟨B, hB, hl⟩
      simp only [sf]
      exact NS_add _ ih

theorem NS_cof {t : T} (h : NS t) : cof t ≠ .succ := by
  obtain ⟨B, hB, hl⟩ := h
  rw [← cof_last_g t, hl]
  intro hc
  unfold cof at hc
  rw [if_neg hB] at hc
  by_cases hsb : isSucc B = true
  · rw [if_pos hsb] at hc; cases hc
  · rw [if_neg hsb] at hc
    rcases hcb : cof B with _ | _ | _ | μ
    · rw [hcb] at hc; cases hc
    · exact hsb ((cof_props B).2 hcb)
    · rw [hcb] at hc; cases hc
    · rw [hcb] at hc
      simp only [lt_z_right] at hc
      cases hc

/-! ## sums -/

theorem foldl_ne_z : ∀ (l : List T) (acc : T), (acc ≠ z ∨ ∃ y ∈ l, y ≠ z) →
    l.foldl (fun a b => sf (add a b)) acc ≠ z
  | [], acc, h => by
    rcases h with h | ⟨y, hy, _⟩
    · exact h
    · cases hy
  | y :: l, acc, h => by
    simp only [List.foldl_cons]
    apply foldl_ne_z l
    by_cases hy : y ≠ z
    · exact Or.inl (sf_ne_z (add_ne_z_right _ hy))
    · rcases h with h | ⟨w, hw, hwz⟩
      · exact Or.inl (sf_ne_z (add_ne_z_left _ h))
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact absurd hwz hy
        · exact Or.inr ⟨w, hw, hwz⟩

theorem sumN_ne_z {l : List T} {y : T} (hy : y ∈ l) (hz : y ≠ z) : sumN l ≠ z :=
  foldl_ne_z l z (Or.inr ⟨y, hy, hz⟩)

/-! ## HNotSucc -/

theorem par0_after_root {M : Mat} {R : Nat} (h0 : entry M 0 R = 0) (hp : entry M 0 (R + 1) ≠ 0) :
    par M 0 (R + 1) = some R := by
  have hlt : entry M 0 R < entry M 0 (R + 1) := by omega
  simp [par, prev, climb, hlt]

theorem upg_none_of_e1 {M : Mat} {n : Nat} (h : entry M 1 n = 0) : upg M n = none := by
  unfold upg; rw [if_pos (Or.inl h)]

theorem isUpg_exists {M : Mat} {c : Nat} (h : isUpg M c = true) : ∃ k, upg M k = some c := by
  unfold isUpg at h
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
  exact ⟨k, by simpa using hk⟩

/-- **The value of a standard matrix with nonzero last column is not a successor.** -/
theorem hNotSucc : HNotSucc := by
  intro A hA hS hE hz tA hv
  obtain ⟨ρ, rk, hC, _, rfl⟩ := hv
  have I := sInv_std hA hS
  have hlen : 0 < A.length := List.length_pos_of_ne_nil hE
  obtain ⟨Rt, hRA, hR0, hRl⟩ := root_t1 I.r01 I.r12 I.e00 (A.length - 1)
  have hRle := hRA.le
  have hRx : Rt < A.length - 1 := by
    rcases Nat.lt_or_ge Rt (A.length - 1) with h | h
    · exact h
    · exfalso; exact hz (by rw [show A.length - 1 = Rt by omega]; exact hR0)
  have he0 : entry A 0 Rt = 0 := e0_of_col hR0
  have he1 : entry A 1 Rt = 0 := e1_of_col hR0
  have he2 : entry A 2 Rt = 0 := e2_of_col hR0
  -- the first child `Rt + 1`
  have hc0 : entry A 0 (Rt + 1) ≠ 0 := hRl (Rt + 1) (by omega) (by omega)
  have hpc : par A 0 (Rt + 1) = some Rt := par0_after_root he0 hc0
  have hcmem : Rt + 1 ∈ children A Rt := mem_children_iff.mpr ⟨by omega, hpc⟩
  have hcnt : cnt A ρ Rt (Rt + 1) = ρ.o (Rt + 1) := by
    unfold cnt
    have hnb : col A (Rt + 1) ≠ bump A Rt := by
      intro hb
      have hb' : col A (Rt + 1) = (1, 0, 1) := by
        rw [hb]; unfold bump; rw [he0, he1]
      have h1 := e1_of_col hb'
      have h2 := e2_of_col hb'
      have := I.r12 (Rt + 1) h1
      omega
    rw [if_neg hnb]
    have hnu : ¬ (isUpg A (Rt + 1) = true ∧ topped A (Rt + 1) = true) := by
      rintro ⟨hu, ht⟩
      obtain ⟨k, hk⟩ := isUpg_exists hu
      by_cases hkc : Rt + 1 = k + 1
      · have : k = Rt := by omega
        subst this
        rw [upg_none_of_e1 he1] at hk; cases hk
      · rw [I.uat k (Rt + 1) hk hkc] at ht; cases ht
    rw [if_neg hnu]
  have hone : ρ.o (Rt + 1) ≠ z := by
    obtain ⟨s, y, hsy⟩ := o_psi_form hC (i := Rt + 1) (by omega)
    rw [hsy]; simp
  have hSne : sumN ((children A Rt).map (cnt A ρ Rt)) ≠ z :=
    sumN_ne_z (List.mem_map.mpr ⟨Rt + 1, hcmem, hcnt⟩) hone
  have hvR : ρ.v Rt = z := by
    rw [(hC Rt (by omega)).2]; simp [vRhs, he1]
  have hoR : NS (ρ.o Rt) := by
    rw [(hC Rt (by omega)).1]
    unfold oRhs
    rw [hvR]
    exact NS_sf ⟨_, hSne, rfl⟩
  -- the sum of the roots
  have key : ∀ m, Rt + 1 ≤ m → m ≤ A.length →
      NS (sumN ((List.range m).map fun i => if col A i = (0, 0, 0) then ρ.o i else z)) := by
    intro m hm1 hm2
    induction m, hm1 using Nat.le_induction with
    | base =>
      rw [List.range_succ, List.map_append, List.map_singleton, sumN_snoc]
      simp only [if_pos hR0]
      exact NS_sf (NS_add _ hoR)
    | succ m hm ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, sumN_snoc]
      have hcm : col A m ≠ (0, 0, 0) := by
        intro h0
        exact hRl m (by omega) (by omega) (e0_of_col h0)
      simp only [if_neg hcm, add_z_right]
      exact NS_sf (ih (by omega))
  exact NS_cof (key A.length (by omega) (le_refl _))

end Ytosk.WfCofH1
