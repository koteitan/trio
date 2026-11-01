/- DQC with a bounded bad-leaf step. This definition alone asserts no
matrix invariant and is not wired into a top theorem. No DV premise is
needed for the three basic order/OT lemmas because leaf carries its bounds
and the standard-form certificate explicitly. -/
import Ytosk.WfQrH6

namespace Ytosk
open T WfQrH6

inductive DQX (η : T) : Bool → T → T → T → Prop
  | mk {B l lN lS Q s y : T} : l = psi s y z → DQX η false l lN lS →
      (∀ q ∈ summands Q, lN ≤ q ∧ q < l) → isOT Q = true →
      DQX η true (app B l) (app B (app Q lN)) (app B lS)
  | base {l : T} : fsD l η < l → isOT (fsD l η) = true → DQX η false l (fsD l η) (fsD l η)
  | sub {a aN aS : T} : DQX η true a aN aS → DQX η false (psi a z z) (psi aN z z) (psi aS z z)
  | arg {a b bN bS : T} : DQX η true b bN bS → isOT (psi a bS z) = true →
      (∀ g ∈ comps a bN, g ∉ comps a bS → g < bS) →
      DQX η false (psi a b z) (psi a bN z) (psi a bS z)
  | leaf {l q : T} : fsD l η ≤ q → q < l → isOT q = true → DQX η false l q q

theorem DQX.toLt {η : T} : ∀ {k : Bool} {t tN tS : T}, DQX η k t tN tS → tN < t := by
  intro k t tN tS h
  induction h with
  | @mk B l lN lS Q s y hl _ hQ _ ih =>
    apply app_lt_app_left B
    subst hl
    cases hQc : Q with
    | z => simpa using ih
    | psi a b c =>
      simp only [app_psi]
      apply lt_of_head_lt
      exact (hQ (psi a b z) (by rw [hQc]; simp [summands])).2
  | base h _ => exact h
  | sub _ ih => rw [psi_lt_psi_z_iff]; exact Or.inl ih
  | arg _ _ _ ih => rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, ih⟩)

  | leaf _ hlt _ => exact hlt

theorem DQX.strip_le {η : T} : ∀ {k : Bool} {t tN tS : T}, DQX η k t tN tS → tS ≤ tN := by
  intro k t tN tS h
  induction h with
  | mk _ _ hQ _ ih => exact app_le_app_left' _ (le_trans ih (le_app_Q (fun q hq => (hQ q hq).1)))
  | base _ _ => exact le_refl _
  | sub _ ih =>
    rcases lt_or_eq_of_le ih with h | h
    · exact le_of_lt (by rw [psi_lt_psi_z_iff]; exact Or.inl h)
    · rw [h]
  | arg _ _ _ ih =>
    rcases lt_or_eq_of_le ih with h | h
    · exact le_of_lt (by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h⟩)
    · rw [h]

  | leaf _ _ _ => exact le_refl _

theorem DQX.ot {η : T} : ∀ {k : Bool} {t tN tS : T}, DQX η k t tN tS → isOT t = true → isOT tN = true := by
  intro k t tN tS h
  induction h with
  | @mk B l lN lS Q s y hl d hQ hQot ih =>
    intro ht
    have hB := isOT_app_left ht
    have hl' := isOT_app_right ht
    have hlN := ih hl'
    have hlNl : lN < l := DQX.toLt d
    have hQN : isOT (app Q lN) = true :=
      isOT_app_of hQot hlN (fun q hq => le_trans (head_le_self lN) (hQ q hq).1)
    have hhead : head (app Q lN) < l := by
      cases hQc : Q with
      | z => simpa [app] using lt_of_le_of_lt (head_le_self lN) hlNl
      | psi a1 b1 c1 =>
        have := (hQ (psi a1 b1 z) (by rw [hQc]; simp [summands])).2
        simpa [app, head] using this
    refine isOT_app_of hB hQN (fun q hq => ?_)
    subst hl
    exact le_of_lt (lt_of_lt_of_le hhead (WfQrL3.last_le_summands ht q hq))
  | base _ hot => intro _; exact hot
  | sub _ ih =>
    intro ht
    exact WfQrL10.isOT_om (ih (isOT_sub ht))
  | @arg a b bN bS d hS hC ih =>
    intro ht
    have hbN := ih (isOT_arg ht)
    have hle := DQX.strip_le d
    rw [isOT_psi_iff]
    refine ⟨isOT_sub ht, hbN, rfl, by simpa [head] using z_le (psi a bN z), fun g hg => ?_⟩
    by_cases hgS : g ∈ comps a bS
    · exact lt_of_lt_of_le (comps_lt hS g hgS) hle
    · exact lt_of_lt_of_le (hC g hg hgS) hle

  | leaf _ _ hot => intro _; exact hot

theorem DQX.ofDQC {η : T} {k : Bool} {t tN tS : T} (h : WfQrH6.DQC η k t tN tS) :
    DQX η k t tN tS := by
  induction h with
  | mk hl _ hQ hOT ih => exact DQX.mk hl ih hQ hOT
  | base hlt hot => exact DQX.base hlt hot
  | sub _ ih => exact DQX.sub ih
  | arg _ hOT hC ih => exact DQX.arg ih hOT hC

end Ytosk
