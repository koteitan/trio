/-
Final.lean: トリオ数列（BM4, z<2 断片）停止性の組み立て。

共終性 `trio_cofinality` は無条件（Core.lean）。残る仮定は `Wset.TowerOK`
（ガード付きコピー塔）と `Wset.TbOper`（`tbAll` が一手展開で保たれる）の二つ。
-/
import Wset
import Reduction
import Gamma
import Lind
import Wtower2

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

/-! ### ★ (WL) 経由: リフト無しトラックで行 2 塔核が消える

`towerGraft2_of_liftStage` により、`LiftStage`（= (WL): 根リフトは段を
ちょうど `2d` 上げる）から `TowerGraft2` が出る。⟹ 残核は `TowerExp` だけ。 -/

/-- **Trio sequences terminate**, modulo the stage law `(WL)` and the
successor-route tower core `TowerExp` — no `Wstar2`, no `GraftAll`, no `GX`. -/
theorem TRIO_terminates_of_liftStage (hWL : LiftStage) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  TRIO_terminates (towerGraft2_of_liftStage hWL) he

/-- **No infinite expansion sequence**, from `(WL)` and `TowerExp`. -/
theorem no_infinite_expansion_of_liftStage (hWL : LiftStage) (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_holds (towerGraft2_of_liftStage hWL) he



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

/-! ### ⛔ 旧 `InfEquip` 経路は撤去（`InfEquip` は偽: `Infcex.not_infEquip`）

`InfEquip` は結論に `entry M 2 p ≤ 1` を含むが、これは `argOK`（行 0 の条件）
からも装備 `CtxOK` からも出ない（反例 `M = [(1,0,2),(2,0,0)]`）。したがって
`InfEquip` を仮定していた頂点定理はすべて空虚なので削除した。
代わりに、**単元核 `CoreSingleton` ひとつ**から 2 本の文脈核が直接出る
（`Lind.corePlantCtxLift_of_core` / `Lind.coreCtxSuffixLift_of_core`）。 -/

/-- **Well-foundedness of `olt` on standard forms, from the ONE-COLUMN core.**
Both context cores are `GX`-membership of *based* sequences, which the length
induction supplies from `[(0,b,c)] ∈ GX` alone. -/
theorem wf_olt_ST_TS_of_core (hs : CoreSingleton) :
    WellFounded
      (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b) :=
  wf_olt_ST_TS_of_cores (coreCtxSuffixLift_of_core hs) (corePlantCtxLift_of_core hs)

/-- **Trio sequences terminate**, modulo the single one-column core
`CoreSingleton` (`[(0,b,c)] ∈ GX`). -/
theorem TRIO_terminates_of_core (hs : CoreSingleton) : WellFounded stepRel :=
  step_terminates (wf_Rnf_of_wf_TS (wf_olt_ST_TS_of_core hs))

/-- **No infinite expansion sequence**, from the one-column core. -/
theorem no_infinite_expansion_of_core (hs : CoreSingleton) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion (wf_Rnf_of_wf_TS (wf_olt_ST_TS_of_core hs))

/-! ### ★ 残核の最終形: `GX` を含まない 1 本の `W` レベル命題

`CoreCap` = 装備つき文脈の**末尾列の添字を任意に差し替えても `W` package**。 -/

/-- **Trio sequences terminate**, modulo ONE pure `W`-level statement:
`CoreCap` (re-capping an equipped context's last column). -/
theorem TRIO_terminates_of_cap (hc : CoreCap) : WellFounded stepRel :=
  TRIO_terminates_of_core (coreSingleton_of_cap hc)

/-- **No infinite expansion sequence**, from the cap statement. -/
theorem no_infinite_expansion_of_cap (hc : CoreCap) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_core (coreSingleton_of_cap hc)

end TRIO
