/-
Final.lean: トリオ数列（BM4, z<2 断片）停止性の組み立て。

共終性 `trio_cofinality` は無条件（Core.lean）。残る仮定は `Wset.TowerOK`
（ガード付きコピー塔）と `Wset.TbOper`（`tbAll` が一手展開で保たれる）の二つ。
-/
import Wset
import Reduction
import Gamma
import Lind

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
  Wset.wf_olt_ST_TS_of_cofinality (S := Wset.Wstar) Set.Subset.rfl
    (Wset.Wstar_closed (Wset.towerOK_of h2 he))
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


/-! ## 新しいトラック: 2 本の文脈核から停止性まで

`Wstar2s`（接頭辞閉包）で A2' を回すと装備が帰納法自身から出るので、
`GraftAll` は `CoreCtxSuffixLift` / `CorePlantCtxLift` の 2 本だけに依存する。 -/

/-- **Well-foundedness of `olt` on standard forms, from the two context
cores.** -/
theorem wf_olt_ST_TS_of_cores (hsl : CoreCtxSuffixLift) (hp : CorePlantCtxLift) :
    WellFounded
      (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b) :=
  Wset.wf_olt_ST_TS_of_cofinality (S := Wset.Wstar2s) Wset.Wstar2s_le_Wstar
    (fun u0 R hR => Wstar2s_closed_of_graftAll (graftAll_of_cores hsl hp) u0 R hR)
    (fun hM hN h => trio_cofinality hM hN h)

/-- **Trio sequences terminate**, modulo the two *context* cores
`CoreCtxSuffixLift` and `CorePlantCtxLift` — no tower core, no equipment gap. -/
theorem TRIO_terminates_of_cores (hsl : CoreCtxSuffixLift)
    (hp : CorePlantCtxLift) : WellFounded stepRel :=
  step_terminates (wf_Rnf_of_wf_TS (wf_olt_ST_TS_of_cores hsl hp))

/-- **No infinite expansion sequence**, from the two context cores. -/
theorem no_infinite_expansion_of_cores (hsl : CoreCtxSuffixLift)
    (hp : CorePlantCtxLift) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion (wf_Rnf_of_wf_TS (wf_olt_ST_TS_of_cores hsl hp))

/-- **Well-foundedness from one `GX`-core plus the `W`-level infix
equipment.** -/
theorem wf_olt_ST_TS_of_plant (hie : InfEquip) (hp : CorePlantCtxLift) :
    WellFounded
      (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b) :=
  Wset.wf_olt_ST_TS_of_cofinality (S := Wset.Wstar2s) Wset.Wstar2s_le_Wstar
    (fun u0 R hR => Wstar2s_closed_of_graftAll (graftAll_of_plant hie hp) u0 R hR)
    (fun hM hN h => trio_cofinality hM hN h)

/-- **Trio sequences terminate**, modulo ONE `GX`-level core
(`CorePlantCtxLift`) and one pure `W`-level equipment statement
(`InfEquip`, the context's re-based infixes are themselves equipped). -/
theorem TRIO_terminates_of_plant (hie : InfEquip) (hp : CorePlantCtxLift) :
    WellFounded stepRel :=
  step_terminates (wf_Rnf_of_wf_TS (wf_olt_ST_TS_of_plant hie hp))

/-- **Trio sequences terminate**, modulo the LIFT-FREE `GX` core
(`CorePlantCtx0`: the planted peel of an equipped context is in `GX`) plus the
`W`-level infix equipment (`InfEquip`).  `corePlantCtxLift_of_plant0` absorbs
the ambient lift into the context (`ltail`), so no lift quantifier survives in
either residue. -/
theorem TRIO_terminates_of_plant0 (hie : InfEquip) (hp : CorePlantCtx0) :
    WellFounded stepRel :=
  TRIO_terminates_of_plant hie (corePlantCtxLift_of_plant0 hp)

/-- **Trio sequences terminate**, modulo the ONE-COLUMN core `CoreSingleton`
(`[(0,b,c)] ∈ GX`) plus `InfEquip`.  The length induction (`Lind.lean`) rebuilds
every based sequence from one-column blocks by `gx_graft`, so the whole `GX`
side of the campaign rests on this single family. -/
theorem TRIO_terminates_of_singleton (hie : InfEquip) (hs : CoreSingleton) :
    WellFounded stepRel :=
  TRIO_terminates_of_plant0 hie (corePlantCtx0_of_singleton hs)

/-- **No infinite expansion sequence**, from the lift-free core. -/
theorem no_infinite_expansion_of_plant0 (hie : InfEquip) (hp : CorePlantCtx0) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion
    (wf_Rnf_of_wf_TS (wf_olt_ST_TS_of_plant hie (corePlantCtxLift_of_plant0 hp)))

/-- **No infinite expansion sequence**, from the one-column core. -/
theorem no_infinite_expansion_of_singleton (hie : InfEquip) (hs : CoreSingleton) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_plant0 hie (corePlantCtx0_of_singleton hs)

/-! ### ★ 残核の最終形: `GX` を含まない 2 本の `W` レベル命題

`CoreCap` = 装備つき文脈の**末尾列の添字を任意に差し替えても `W` package**、
`InfEquip` = 文脈の窓の再基底化中置が再び装備。どちらも `GX` を含まない。 -/

/-- **Trio sequences terminate**, modulo two pure `W`-level statements:
`CoreCap` (re-capping an equipped context's last column) and `InfEquip`. -/
theorem TRIO_terminates_of_cap (hie : InfEquip) (hc : CoreCap) :
    WellFounded stepRel :=
  TRIO_terminates_of_singleton hie (coreSingleton_of_cap hc)

/-- **No infinite expansion sequence**, from the two `W`-level statements. -/
theorem no_infinite_expansion_of_cap (hie : InfEquip) (hc : CoreCap) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_singleton hie (coreSingleton_of_cap hc)

end TRIO
