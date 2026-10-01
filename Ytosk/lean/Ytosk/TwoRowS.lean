/-
**2 行・t = 1 の経路の値の形。**

x から根への経路で、r より下（r と x の間と x）の値は cof が Ω_{μ+1}（μ = v(r)）、r の値は ψ_μ(b)（cof b = Ω_{μ+1}）、
r 以上の値は対角化の点（ψ_{a′}(b)、引き上げで a′ が上に動く）を持つ。
-/
import Ytosk.TwoRowA

namespace Ytosk

open T

/-! ## 祖先と climb の鎖 -/

theorem anc0_of_rtg {M : Mat} {a b : Nat} (h : Relation.ReflTransGen (StepRel (par M 0)) a b) :
    Anc0 M a b := by
  induction h with
  | refl => exact Anc0.refl _
  | tail _ h2 ih => exact Anc0.step h2 ih

theorem rtg_of_anc0 {M : Mat} {a b : Nat} (h : Anc0 M a b) :
    Relation.ReflTransGen (StepRel (par M 0)) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | step hp _ ih => exact Relation.ReflTransGen.tail ih hp

/-- **Between the row-1 parent and the column, row 1 is at least the column's.** -/
theorem par1_between {M : Mat} {x r : Nat} (hr : par M 1 x = some r) :
    ∀ p, Anc0 M p x → r < p → entry M 1 x ≤ entry M 1 p := by
  intro p hp hrp
  rcases Nat.eq_or_lt_of_le hp.le with heq | hlt
  · rw [heq]
  have hr' : climb (par M 0) (fun q => decide (entry M 1 q < entry M 1 x)) (x + 1) (par M 0 x) = some r := hr
  clear hr
  cases hq : par M 0 x with
  | none => rw [hq] at hr'; simp [climb] at hr'
  | some q0 =>
    rw [hq] at hr'
    have hq0 := par_lt M 0 x q0 hq
    have := (climb_chain_iff (par M 0) _ (par_lt M 0) r (x + 1) q0 (by omega)).mp hr'
    have hpq : Anc0 M p q0 := anc0_par hp (by omega) hq
    have h3 := this.2.2 p (rtg_of_anc0 hpq) hrp
    simp at h3; omega

/-! ## 項の小補題 -/

theorem init_succ : ∀ ν : T, init (succ ν) = ν
  | z => rfl
  | psi a b c => by
    show init (psi a b (app c one)) = psi a b c
    have hne : app c one ≠ z := fun h => by exact absurd (app_eq_z h).2 (by simp [one])
    cases hc : app c one with
    | z => exact absurd hc hne
    | psi d e f =>
      show psi a b (init (psi d e f)) = psi a b c
      rw [← hc]; congr 1; exact init_succ c

theorem cof_leaf (ν : T) : cof (psi (succ ν) z z) = .big ν := by
  have hs : isSucc (succ ν) = true := isSucc_succ ν
  have hne : succ ν ≠ z := by
    intro h; rw [h] at hs; simp [isSucc, last, one] at hs
  simp only [cof, if_neg hne, hs, if_true, init_succ]

theorem nT_succ (k : Nat) : nT (k + 1) = succ (nT k) := by
  show sf (add (nT k) one) = _
  rw [sf_ot (isOT_add (isOT_nT k) isOT_one), add_one_eq_succ (isOT_nT k)]

theorem lt_nT : ∀ {k l : Nat}, k < l → nT k < nT l := by
  intro k l h
  induction l with
  | zero => omega
  | succ l ih =>
    rw [nT_succ]
    rcases Nat.lt_or_ge k l with h' | h'
    · exact lt_trans (ih h') (lt_succ_self _)
    · have : k = l := by omega
      subst this; exact lt_succ_self _

theorem DiagAt.not_succ {a b μ : T} {t : T} (h : DiagAt a b μ t) : isSucc t = false := by
  induction h with
  | here hb _ _ =>
    simp only [isSucc, last, beq_eq_false_iff_ne]
    intro h; simp [one] at h; exact hb h.2
  | rest _ ih => rw [isSucc_psi_rest _ _ _ (by simp)]; exact ih
  | arg hb _ _ _ =>
    simp only [isSucc, last, beq_eq_false_iff_ne]
    intro h; simp [one] at h; exact hb h.2
  | sub ha _ _ _ =>
    simp only [isSucc, last, beq_eq_false_iff_ne]
    intro h; simp [one] at h; exact ha h

/-- The node over a path child, as `ψ_a` of one `sp` step. -/
theorem o2r_frame {M : Mat} {x : Nat} (hG : Good2 M) (hx : x + 1 = M.length) {h p : Nat}
    (hpA : Anc0 M p x) (hp : par M 0 p = some h) :
    o2r M h = psi (vr M h) (spArg (vr M h) (bst M h p) (o2r M p)) z := by
  have hpc := par_lt M 0 p h hp
  have hle := children_le_of_anc_last hpA hx hp
  have hcmem : p ∈ children M h := mem_children_iff.mpr ⟨by have := hpA.le; omega, hp⟩
  have hsplit := split_last_max _ p (children_sorted M h) hcmem hle
  set C := (children M h).filter (fun d => decide (d < p)) with hCdef
  have hdM := hG.dec h
  simp only [hsplit, List.map_append, List.map_cons, List.map_nil] at hdM
  have hsumM : sumN ((children M h).map (o2r M)) = app (sumN (C.map (o2r M))) (o2r M p) := by
    simp only [hsplit, List.map_append, List.map_cons, List.map_nil]
    refine sumN_snoc_dec ?_ hdM
    intro t ht'
    rcases List.mem_append.mp ht' with ht' | ht'
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht'; exact single_o2r hG i
    · rw [List.mem_singleton] at ht'; subst ht'; exact single_o2r hG p
  rw [o2r_spArg (isOT_vr hG.f1 h) (sumN_children hG h).1, hsumM, spArg_app, hCdef]; rfl

theorem spArg_single (a b s y : T) : spArg a b (psi s y z) = step a b s y z := rfl

end Ytosk
