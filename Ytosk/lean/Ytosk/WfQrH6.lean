/-
**WfQrH6 (2026-11-01): C_strip, the standard form of `DQ` values.**
`DQC η k t tN tS` is `DQ η k t tN` carrying the stripped term `tS` (every re-exposed `Q` removed) and, at each
argument level `ψ_a(b) → ψ_a(b_N)`, the condition C_strip of tmp/wf/WfQrL/compq.py: every component of `b_N`
that is not a component of `b_S` is `< b_S`; together with the standard form of `ψ_a(b_S)` (the value with all `Q`
removed), the standard form of `Q` and of the base values.  `DQC.ot`: a `DQC` image of a standard term is standard.
`DQC.toDQ` forgets the annotation; `DQC.strip_le`: `t_S ≤ t_N`.
-/
import Ytosk.WfQrL3
import Ytosk.WfQrL10

namespace Ytosk.WfQrH6
open T Ytosk

/-- `DQ` with the stripped term and the C_strip annotation. -/
inductive DQC (η : T) : Bool → T → T → T → Prop
  | mk {B l lN lS Q s y : T} : l = psi s y z → DQC η false l lN lS →
      (∀ q ∈ summands Q, lN ≤ q ∧ q < l) → isOT Q = true →
      DQC η true (app B l) (app B (app Q lN)) (app B lS)
  | base {l : T} : fsD l η < l → isOT (fsD l η) = true → DQC η false l (fsD l η) (fsD l η)
  | sub {a aN aS : T} : DQC η true a aN aS → DQC η false (psi a z z) (psi aN z z) (psi aS z z)
  | arg {a b bN bS : T} : DQC η true b bN bS → isOT (psi a bS z) = true →
      (∀ g ∈ comps a bN, g ∉ comps a bS → g < bS) →
      DQC η false (psi a b z) (psi a bN z) (psi a bS z)

theorem DQC.toDQ {η : T} : ∀ {k : Bool} {t tN tS : T}, DQC η k t tN tS → DQ η k t tN := by
  intro k t tN tS h
  induction h with
  | mk hl _ hQ _ ih => exact DQ.mk hl ih hQ
  | base hlt _ => exact DQ.base hlt
  | sub _ ih => exact DQ.sub ih
  | arg _ _ _ ih => exact DQ.arg ih

theorem psi_le_rest (a b X : T) : psi a b z ≤ psi a b X := by
  cases X with
  | z => exact le_refl _
  | psi a1 b1 c1 =>
    apply le_of_lt
    rw [T.psi_lt_psi]; right; right; exact ⟨rfl, rfl, T.z_lt_psi _ _ _⟩

/-- `lN ≤ Q ++ lN` when the first summand of `Q` is `≥ lN`. -/
theorem le_app_Q : ∀ {Q lN : T}, (∀ q ∈ summands Q, lN ≤ q) → lN ≤ app Q lN
  | z, lN, _ => by simp [app]
  | psi _ _ _, z, _ => z_le _
  | psi a b c, psi a' b' c', h => by
    have h1 : psi a' b' c' ≤ psi a b z := h (psi a b z) (by simp [summands])
    simp only [app_psi]
    rcases lt_or_eq_of_le h1 with hlt | heq
    · apply le_of_lt
      rw [T.psi_lt_psi] at hlt ⊢
      rcases hlt with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, h'⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl ⟨rfl, h'⟩)
      · exact absurd h' (T.not_lt_z _)
    · obtain ⟨rfl, rfl, rfl⟩ := T.psi.inj heq
      exact psi_le_rest _ _ _

theorem app_le_app_left' (B : T) {x y : T} (h : x ≤ y) : app B x ≤ app B y := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (app_lt_app_left B h)
  · exact le_refl _

/-- **The stripped term is below the new term.** -/
theorem DQC.strip_le {η : T} : ∀ {k : Bool} {t tN tS : T}, DQC η k t tN tS → tS ≤ tN := by
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

/-- **C_strip gives the standard form**: a `DQC` image of a standard term is standard. -/
theorem DQC.ot {η : T} : ∀ {k : Bool} {t tN tS : T}, DQC η k t tN tS → isOT t = true → isOT tN = true := by
  intro k t tN tS h
  induction h with
  | @mk B l lN lS Q s y hl d hQ hQot ih =>
    intro ht
    have hB := isOT_app_left ht
    have hl' := isOT_app_right ht
    have hlN := ih hl'
    have hlNl : lN < l := (DQC.toDQ d).lt
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
    have hle := DQC.strip_le d
    rw [isOT_psi_iff]
    refine ⟨isOT_sub ht, hbN, rfl, by simpa [head] using z_le (psi a bN z), fun g hg => ?_⟩
    by_cases hgS : g ∈ comps a bS
    · exact lt_of_lt_of_le (comps_lt hS g hgS) hle
    · exact lt_of_lt_of_le (hC g hg hgS) hle

/-- **The standard-form conjuncts of `hLocE` from C_strip** (`o` values on `D`: single and standard; `v` values on
`D`: standard), given a `DQC` annotation of the change at each call. -/
theorem std_of_DQC {M N : Mat} {x : Nat} {ρ σ : Valn} (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hCN : Cons N σ) (hxN : x < N.length)
    (ho : ∀ c, c ≤ x → DepX M x true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS)
    (hv : ∀ i, i < x → DepX M x false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) :
    (∀ c, c ≤ x → DepX M x true c → Single (σ.o c) ∧ isOT (σ.o c) = true) ∧
    (∀ i, i < x → DepX M x false i → isOT (σ.v i) = true) := by
  refine ⟨fun c hc hd => ?_, fun i hi hd => ?_⟩
  · obtain ⟨η, tS, h⟩ := ho c hc hd
    have hot := h.ot (hG.ot_o c (by omega))
    exact ⟨⟨hot, o_psi_form hCN (by omega)⟩, hot⟩
  · obtain ⟨η, tS, h⟩ := hv i hi hd
    exact h.ot (hG.ot_v i (by omega))

end Ytosk.WfQrH6
