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

/-- **Trio sequences terminate**, modulo the PARENTED residue of the stage law
and `TowerExp`.  `liftStage_of_parented` discharges every parentless branch of
`Aop` (including all of clause 3) by `lift_oper_of_noParent`. -/
theorem TRIO_terminates_of_parented (hP : LiftStageParented) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  TRIO_terminates_of_liftStage (liftStage_of_parented hP) he

/-- **No infinite expansion sequence**, from the parented residue. -/
theorem no_infinite_expansion_of_parented (hP : LiftStageParented)
    (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_liftStage (liftStage_of_parented hP) he

/-- **Trio sequences terminate, modulo the row-1 graft tower alone.**  Three of
the four `(WL)` branches are proved (`lspOn_pos`, `lspOn_srow2`, `lspOn_srow0`),
so the whole stage law now rests on the single class
`badPar X = 0 ∧ srow X (|X| - 1) = 1` — the same phenomenon as `TowerExp`. -/
theorem TRIO_terminates_of_srow1
    (hs1 : LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 1))
    (he : Wset.TowerExp) : WellFounded stepRel :=
  TRIO_terminates_of_parented (liftStageParented_of_srow1 hs1) he

/-- **No infinite expansion sequence**, from the row-1 graft tower alone. -/
theorem no_infinite_expansion_of_srow1
    (hs1 : LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 1))
    (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_parented (liftStageParented_of_srow1 hs1) he

/-- **Trio sequences terminate, modulo the shifted copy tower `(TOW)`.**  The
last `(WL)` branch is the row-1 collapse at the root, whose expansion IS the
row-0-shifted copy tower of the peel (`oper_of_srow1_par0`); the clause-2
hypothesis supplies the peel itself at `n = 1`.  So the whole stage law reduces
to a `W`-closure with no lift in it. -/
theorem TRIO_terminates_of_tower (htow : ShiftTowerClosed) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  TRIO_terminates_of_parented (liftStageParented_of_tower htow) he

/-- **No infinite expansion sequence**, from `(TOW)` and `TowerExp`. -/
theorem no_infinite_expansion_of_tower (htow : ShiftTowerClosed)
    (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_parented (liftStageParented_of_tower htow) he

/-- **Trio sequences terminate, modulo `(TOW)` and the ROW-2 half of
`TowerExp`.**  The row-1 half of `TowerExp` is the same shifted copy tower
(`towerExp1_of_tower`), so the whole proof now rests on exactly two statements:
the shifted copy tower `(TOW)`, and the guarded (row-1-ascending) tower of a
row-2 collapse arriving through clause 2. -/
theorem TRIO_terminates_of_tow (htow : ShiftTowerClosed) (h2 : TowerExp2) :
    WellFounded stepRel :=
  TRIO_terminates_of_tower htow (towerExp_of_tower htow h2)

/-- **No infinite expansion sequence**, from `(TOW)` and `TowerExp2`. -/
theorem no_infinite_expansion_of_tow (htow : ShiftTowerClosed)
    (h2 : TowerExp2) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_tower htow (towerExp_of_tower htow h2)

/-- **Trio sequences terminate, modulo `(CAT)` and `TowerExp2`.**  `(CAT)` is
the hypothesis-free strengthening of `Wset.W_add`: `W u` closed under plain
concatenation.  Probe `tools/probe_cat.py`: 372290 pairs, 0 violations. -/
theorem TRIO_terminates_of_cat (hcat : WCat) (h2 : TowerExp2) :
    WellFounded stepRel :=
  TRIO_terminates_of_tow (shiftTowerClosed_of_cat hcat) h2

/-- **No infinite expansion sequence**, from `(CAT)` and `TowerExp2`. -/
theorem no_infinite_expansion_of_cat (hcat : WCat) (h2 : TowerExp2) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_tow (shiftTowerClosed_of_cat hcat) h2

/-- **★ Trio sequences terminate, modulo `(CAT)` and the LOW half of the row-2
tower.**  `TowerExp`'s `m < a` half is `(CAT)`-strength (`towerExp_of_cat`): the
appended column is then a `W a` member on its own.  What is left is the row-2
collapse with `a ≤ m`, i.e. exactly the case where the orphan's level exceeds
the target stage and the column is harmless only because it finds a parent.
That is where the pair-sequence content sits (its `|R| = 1`, `z = 0` base is the
pair diagonal `[(k*d0, v + k*d1, 0)]`). -/
theorem TRIO_terminates_of_cat_low (hcat : WCat) (h2 : TowerExp2Low) :
    WellFounded stepRel :=
  TRIO_terminates_of_tower (shiftTowerClosed_of_cat hcat) (towerExp_of_cat hcat h2)

/-- **No infinite expansion sequence**, from `(CAT)` and the low row-2 tower. -/
theorem no_infinite_expansion_of_cat_low (hcat : WCat) (h2 : TowerExp2Low) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_tower (shiftTowerClosed_of_cat hcat)
    (towerExp_of_cat hcat h2)

/-- **★★ Trio sequences terminate, modulo `(CAT)` and the row-2 tower at the
root's OWN stage.**  This is the tightest form of the residue: `TowerExp2Root`
has no `a` quantifier at all (`W_mono` supplies every `a ≥ 2v+z`, and
`tower1_le` forces `2v+z ≤ m`), so what is open is exactly

> a row-2 collapse `p_{v,z}(R)` whose argument arrived through the SUCCESSOR
> clause lands in `W (2v+z)`.

`(CAT)` — `W u` is closed under concatenation — carries everything else. -/
theorem TRIO_terminates_of_cat_root (hcat : WCat) (h2 : TowerExp2Root) :
    WellFounded stepRel :=
  TRIO_terminates_of_cat_low hcat (towerExp2Low_of_root h2)

/-- **No infinite expansion sequence**, from `(CAT)` and the root-stage tower. -/
theorem no_infinite_expansion_of_cat_root (hcat : WCat) (h2 : TowerExp2Root) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_cat_low hcat (towerExp2Low_of_root h2)

/-- **★ Trio sequences terminate, modulo `(SNOC)` ALONE.**  `(SNOC)` is the
atomic form of the whole residue: *appending one column that finds a parent does
not raise the stage*.

* Every `Aop` clause of `(CAT)` reduces to it (`wcat_of_snoc`), using the
  `rsum`-free append identity `Xbar.oper_append_inner` for the parented case and
  `graft B [] = B.dropLast` for the orphan case; `(CAT)` gives `(TOW)`, hence the
  whole stage law `(WL)`.
* `TowerExp` — both halves, including the row-2 one that `(CAT)` provably could
  not reach — is *literally* a snoc (`towerExp_of_snoc`): `domT R m` makes
  `R⟦1⟧ = R.dropLast`, so the clause-2 datum puts `p_{v,z}(R.dropLast)` in
  `W a`, and `R`'s trailing orphan is the one column appended.

Probe `tools/probe_snoc.py`: 14455 instances, 0 violations. -/
theorem TRIO_terminates_of_snoc (hsn : WSnoc) : WellFounded stepRel :=
  TRIO_terminates_of_tower (shiftTowerClosed_of_cat (wcat_of_snoc hsn))
    (towerExp_of_snoc hsn)

/-- **No infinite expansion sequence**, from `(SNOC)` alone. -/
theorem no_infinite_expansion_of_snoc (hsn : WSnoc) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_tower (shiftTowerClosed_of_cat (wcat_of_snoc hsn))
    (towerExp_of_snoc hsn)



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
