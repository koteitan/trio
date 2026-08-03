/-
Final.lean: トリオ数列（BM4, z<2 断片）停止性の組み立て。

共終性 `trio_cofinality` は無条件（Core.lean）。残る仮定は `Wset.TowerOK`
（ガード付きコピー塔）と `Wset.TbOper`（`tbAll` が一手展開で保たれる）の二つ。
-/
import Wset
import Reduction

namespace TRIO

open Three

/-- Transport well-foundedness from the `ST_TS`-restricted relation on trio
sequences to `Rnf` on the term side. -/
theorem acc_Rnf_of_acc_TS :
    ∀ {M : TrioSeq},
      Acc (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b) M →
      ST_TS M → Acc Rnf (translate M) := by
  intro M hacc
  induction hacc with
  | intro M0 _ ih =>
    intro hM0
    refine Acc.intro _ (fun v hv => ?_)
    obtain ⟨hlt, -, hvNF⟩ := hv
    obtain ⟨N, hN, rfl⟩ := hvNF
    exact ih N ⟨hN, hM0, hlt⟩ hN

theorem wf_Rnf_of_wf_TS
    (h : WellFounded
      (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b)) :
    WellFounded Rnf := by
  refine ⟨fun u => ?_⟩
  by_cases hu : u ∈ NF
  · obtain ⟨M, hM, rfl⟩ := hu
    exact acc_Rnf_of_acc_TS (h.apply M) hM
  · exact Acc.intro _ (fun v hv => absurd hv.2.1 hu)

/-- Well-foundedness of `olt` restricted to standard forms. -/
theorem wf_olt_ST_TS_holds (h2 : Wset.TowerGraft2) (he : Wset.TowerExp) :
    WellFounded
      (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b) :=
  Wset.wf_olt_ST_TS_of_cofinality (Wset.towerOK_of h2 he)
    (fun hM hN h => trio_cofinality hM hN h)

/-- Well-foundedness of `Rnf` (the term-side order on the `translate` image). -/
theorem wf_Rnf_holds (h2 : Wset.TowerGraft2) (he : Wset.TowerExp) :
    WellFounded Rnf :=
  wf_Rnf_of_wf_TS (wf_olt_ST_TS_holds h2 he)

/-- **Trio sequences terminate.**  The one-step expansion relation on standard
forms is well-founded — modulo the two remaining tower cores. -/
theorem TRIO_terminates (h2 : Wset.TowerGraft2) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  step_terminates (wf_Rnf_holds h2 he)

/-- **No infinite expansion sequence.** -/
theorem no_infinite_expansion_holds (h2 : Wset.TowerGraft2) (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion (wf_Rnf_holds h2 he)

end TRIO
