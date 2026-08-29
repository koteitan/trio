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
import L53Subst
import L105Cap

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

/-- **★★★★★ 停止性は `TowerOK` ただ 1 本から出る**（課題 L70）。

`TowerGraft2` / `TowerExp` を経由せず `Wstar_closed` に直に渡した形。
`Wstar` 路線（2 行の完成証明と同じ道筋）では、共終性 `trio_cofinality` は無条件、
`Wstar` の閉性は `Wstar_closed` が `TowerOK` だけを要求する。

⟹ **3 行 z<2 の停止性 ＝ `TowerOK`。** そして課題 L64 / L69 のとおり

    `srow = 1` の枝 … `towerOK1_of_clause3`（`L53Subst.lean`）で**証明ずみ**
    `srow = 2` の枝 … 親は**必ず根**（`Wset.parent_cons_eq_zero` `:2762`）
                      ⟹ `z < c`（`L53.tower2_zr` `:2380`）
                      ⟹ **段は無条件に収まる**（`L53.tower2_stage_fits'` `:2406`。
                         docstring「段はいつでもちょうど収まる」。`c` にも `z` にも制限なし）
                      ⟹ **残核は段ではなく `LiftTie`**
                         （`L53.towerOK2_of_clause3` `:2432` の唯一の仮定）

⚠ 2026-08-30 訂正（SESSION §140）。ここには 2 度、誤った注記が入っていた。

    (旧 1)「`srow = 2, z = 1` は起きない（`tower2_root_z_zero`）」
           ⟹ `tower2_root_z_zero` の前提は `entry R 2 (|R|-1) = 1`、
              すなわち **`c = 1` に限った言明**。しかも**死んだコード**
              （`tower2_z_zero_of_parent` からしか呼ばれず、そちらは誰も呼ばない）。
              生きている鎖 `towerOK2_of_clause3` は最初から `c` について一般。

    (旧 2)「`srow = 2, 親が根でない` … 残核。`z = 1` かつ `c = 1` のときだけ起きる」
           ⟹ **誤り**。`domT R m` があれば `parent_cons_eq_zero` が親 = 根を
              **無条件に**与えるので、`TowerOK2` の設定に「親が根でない」枝は**存在しない**。
              team-lead が `TowerOK` の設定（`domT` あり）と `CoreCap` の snoc 残核
              （`domT` が成り立たず `j0 >= 1` が起きる側）を混同して書き込んだもの。 -/
theorem wf_olt_ST_TS_of_towerOK (htow : Wset.TowerOK) :
    WellFounded
      (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b) :=
  Wset.wf_olt_ST_TS_of_cofinality (S := Wset.Wstar) Set.Subset.rfl
    (Wset.Wstar_closed htow)
    (fun hM hN h => trio_cofinality hM hN h)

/-- **★★★★★ トリオ数列は停止する、`TowerOK` を仮定して。** -/
theorem TRIO_terminates_of_towerOK (htow : Wset.TowerOK) : WellFounded stepRel :=
  step_terminates (wf_Rnf_of_wf_TS (wf_olt_ST_TS_of_towerOK htow))

/-- **無限展開列は無い**、`TowerOK` から。 -/
theorem no_infinite_expansion_of_towerOK (htow : Wset.TowerOK) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion (wf_Rnf_of_wf_TS (wf_olt_ST_TS_of_towerOK htow))

/-- **Trio sequences terminate**, modulo the stage law `(WL)` and the
successor-route tower core `TowerExp` — no `Wstar2`, no `GraftAll`, no `GX`. -/
theorem TRIO_terminates_of_liftStage (hWL : LiftStage) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  TRIO_terminates (towerGraft2_of_liftStage hWL) he

/-- **No infinite expansion sequence**, from `(WL)` and `TowerExp`. -/
theorem no_infinite_expansion_of_liftStage (hWL : LiftStage) (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_holds (towerGraft2_of_liftStage hWL) he

/-- **★★★ Trio sequences terminate, modulo `(ROW1MONO)` and `TowerExp`.**
`(ROW1MONO)` says only that `W a` is closed under LOWERING row 1 — no lift, no
mask, no cone in the statement.  `Lift1 X d` is the uniform shift
`shiftr01 0 d X` with row 1 lowered at the columns outside the root cone, and
the uniform shift is proved (`Wslift.ulift_mem_W`), so this bypasses the
index-mask vs value-mask obstruction that `TieFree` and the row-1 window both
ran into. -/
theorem TRIO_terminates_of_row1mono (hM : Row1Mono) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  TRIO_terminates_of_liftStage (liftStage_of_row1mono hM) he

/-- **No infinite expansion sequence**, from `(ROW1MONO)` and `TowerExp`. -/
theorem no_infinite_expansion_of_row1mono (hM : Row1Mono) (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_liftStage (liftStage_of_row1mono hM) he

/-! ### ★★★★★ 課題 L84: 持ち上げ核は「行 1 のタイがある根」だけになった

`L53.liftStage_of_noTie`（仮定ゼロ）が**無タイの全 `v`** を覆うので、`(WL)` のうち
本当に要るのは `L53.LiftTie` ——「根の行 1 と等しい列が引数にある場合」だけ。
H11 の全数（`TowerOK2` の場面 70557 件）:

    狭義                 62476 (88.5%)   `L53.liftStage_of_strict`    ✅ 仮定ゼロ
    無タイだが狭義でない  1950 ( 2.8%)   `L53.liftStage_of_noTie`     ✅ 仮定ゼロ
    タイだが `TieFree`     (  6.1%)      `L53.liftTie_case_tieFree`   ✅ 既存定理
    **残りのタイ                          `L53.LiftTie`               ← 核**

シート 4482 行の側では `TowerOK2` / タイは **24 節点（0.5%）**。
さらに `L53.liftTie_of_row1down` で核は `Row1DownLocal`（`Row1Mono` の**局所版**、
`L53.row1DownLocal_of_row1mono` で `Row1Mono` より弱いことが証明ずみ）へ移る。 -/

/-- **★★★★★ Trio 数列は停止する、`LiftTie` と `TowerExp` を仮定すれば。**
`LiftStage`（全部の根での `(WL)`）より**真に小さい核**: タイのある根だけ。 -/
theorem TRIO_terminates_of_liftTie (hlt : L53.LiftTie) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  TRIO_terminates_of_towerOK (L53.towerOK_of_liftTie hlt he)

/-- **無限展開列は無い**、`LiftTie` と `TowerExp` から。 -/
theorem no_infinite_expansion_of_liftTie (hlt : L53.LiftTie) (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_towerOK (L53.towerOK_of_liftTie hlt he)

/-! ### ★★★★★ 課題 L115: 持ち上げ核の段は **自己段だけ**で足りる

`L53.towerOK2_of_clause3`（`L53Subst.lean:2432`）が `L53.liftStage_cons`（`:2344`）を
呼ぶのは **1 か所だけ**で、そこでの段は塔の帰納 `key` が自己段で回っているため
**常に `2v+z`**（`ih : ((0,v,z) :: graft R …) ∈ W (2*v+z)`）。
⟹ `L53.LiftTie` の `∀ m` は使われていない。

    `L105.LiftTieSelf`（`L105Cap.lean:1335`）… 段を `m = 2v+z` に固定した `LiftTie`
    `L105.liftTieSelf_of_liftTie`（`:1340`）  … `LiftTie ⟹ LiftTieSelf`
    `L105.towerOK_of_liftTieSelf`（`:1396`）  … `LiftTieSelf ＋ TowerExp ⟹ TowerOK`

`X ∈ W m` から `X ∈ W (lev X 0)` は出ない（`Wset.W_mono` は逆向き）ので、
**逆は言えない ＝ 真の弱化**。しかも `Wstar` の元はすべて `Wself`
（`L53.Wstar_iff_Wself`、`L53Subst.lean:3001`）なので、**狙う場所とちょうど一致**する。 -/

/-- **★★★★★ Trio 数列は停止する、`LiftTieSelf` と `TowerExp` を仮定すれば。**
`TRIO_terminates_of_liftTie` より**真に弱い**仮定（段が自己段に固定）。 -/
theorem TRIO_terminates_of_liftTieSelf (hlt : L105.LiftTieSelf)
    (he : Wset.TowerExp) : WellFounded stepRel :=
  TRIO_terminates_of_towerOK (L105.towerOK_of_liftTieSelf hlt he)

/-- **無限展開列は無い**、`LiftTieSelf` と `TowerExp` から。 -/
theorem no_infinite_expansion_of_liftTieSelf (hlt : L105.LiftTieSelf)
    (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_towerOK (L105.towerOK_of_liftTieSelf hlt he)

/-- 位置づけ: `LiftTie` 経路はこれを経由して再現できる。 -/
theorem TRIO_terminates_of_liftTie' (hlt : L53.LiftTie) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  TRIO_terminates_of_liftTieSelf (L105.liftTieSelf_of_liftTie hlt) he

/-! ### ★★★★★ 課題 L115-1: 持ち上げ核は **`d = 1` の 1 文**まで細った

`LiftTieSelf` からさらに 2 枝落ちる（`L105Cap.lean` §26 / §28、どちらも緑）:

    `∀ d` が消える  … `Wset.Lift1_Lift1`（`Wset.lean:1230`）＋
                      `Wset.lift_cons`（`:3656`）で `d` の帰納が回る:
                      `Lift1 X (d+1) = Lift1 ((0,v+1,z) :: ltail v z R 1) d` で、
                      `Lift1 X 1 ∈ W (2v+z+2) = W (2(v+1)+z)` は**また自己段**
                      （`Wset.argOK_ltail`（`:3716`）で `argOK` も保たれる）
    `TieFree` の枝  … `L53.liftTie_case_tieFree`（`L53Subst.lean:2615`、実測 6.1%）

⟹ **`L105.LiftTieCore`**（`L105Cap.lean` §29）: **3 量化（`v z R`）／ 4 前提**

    `argOK R` / **タイあり** `∃ p ∈ R, p.2.1 = v` /
    **`¬ (1 ≤ v ∧ TieFree ((0,v,z) :: R))`** / **自己段** `((0,v,z) :: R) ∈ W (2v+z)`
    ⟹ `Lift1 ((0,v,z) :: R) 1 ∈ W (2v+z+2)`

上の表（`Final.lean:152`）の 88.5% ＋ 2.8% ＋ 6.1% が全部**仮定ゼロ定理**で落ち、
残るのは「**タイかつ `¬TieFree`**」だけ。しかも持ち上げ量は **1** に固定。 -/

/-- **★★★★★ Trio 数列は停止する、`LiftTieCore` と `TowerExp` を仮定すれば。**
`TRIO_terminates_of_liftTieSelf` よりさらに弱い（`d = 1` ＋ `TieFree` 除外）。 -/
theorem TRIO_terminates_of_liftTieCore (h : L105.LiftTieCore) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  TRIO_terminates_of_towerOK (L105.towerOK_of_liftTieCore h he)

/-- **無限展開列は無い**、`LiftTieCore` と `TowerExp` から。 -/
theorem no_infinite_expansion_of_liftTieCore (h : L105.LiftTieCore)
    (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_towerOK (L105.towerOK_of_liftTieCore h he)

/-! ### ⚠ 課題 L112/L113 の判定: **「仮定 1 本」は見かけだった**

`L105.coreCap_iff_graftAll`（`L105Cap.lean` §25、緑）:

    **`CoreCap` ⟺ `Wset.GraftAll`**（`Wset.lean:4085`）

`Lind.graft_singleton_eq_cap`（`Lind.lean:169`）が `graft M [(0,b,c)] = cap M b c` を
与え、`GraftAll` の装備仮定は `Gamma.CtxOK`（`Gamma.lean:153`）の定義そのものなので、
**`CoreCap` は `GraftAll` の「`y` が 1 列」の場合そのもの**である。

そして `TRIO_terminates_of_cap` の鎖の中で `TowerExp` に相当する債務は
**`Wset.liftTowerExp2_of_graftAll`（`Wset.lean:4211`）**として `GraftAll` から出ている
（`Lcone.Wstar2s_closed_of_graftAll`（`Lcone.lean:687`）が
`Wset.Wstar2s_closed`（`Wset.lean:4347`）に渡す 3 本のうちの 1 本）。

⟹ **`CoreCap` は `TowerExp` を避けているのではなく、内側に畳んでいる。**
「仮定 1 本」は本数の指標にすぎず、`CoreCap` ＝ `CoreSingleton` ＝ `GraftAll` は
**同じ命題の 3 つの名前**である。 -/

/-- **核が「より弱い方」へ動いた履歴**（課題 L83）。`Row1DownLocal` は
`L53.row1DownLocal_of_row1mono` で `Row1Mono` から出るので、真に弱い。 -/
theorem TRIO_terminates_of_row1down (h1 : L53.Row1DownLocal)
    (h0 : L53.Row1DownRoot0) (he : Wset.TowerExp) : WellFounded stepRel :=
  TRIO_terminates_of_liftTie (L53.liftTie_of_row1down h1 h0) he

/-! ### ★★★★★ 課題 L86: 核は「閾値の off-by-one」1 つに畳まれた

`Lcone.le1_zero_iff` は「根が行 0 で狭義最浅なら `le1 X 0 j` ⟺ **根以外の**行 0
祖先がすべて `entry X 1 0` より上」と言う。`coneV X w j` は**根を含む**祖先が
`w` より上。⟹ 根を判定から外した錐 `L53.coneVR` を入れると、両方が**同じ族**になる:

    `mlift X w d` = `L53.mliftR X w d`（`w < v0`）  … `Wslift.mlift_mem_W` で**証明ずみ**
    `Lift1 X d`   = `L53.mliftR X v0 d`             … 欲しいもの

**⟹ 核 ＝ `L53.mliftR_mem_W_of_lt` を `w < v0` から `w = v0` へ 1 段伸ばすこと。**
`TieFree` / `Row1Mono` / `WConvex` / `Row1DownLocal` / `Row1DownRoot0` が全部これに
畳まれ、`v0 = 0` の場合分けも消える（`mliftR` は閾値に `v0 - 1` を使わない）。 -/

/-- **★★★★★ Trio 数列は停止する、`MliftR` と `TowerExp` を仮定すれば。**
今日の到達点の最終形: 持ち上げ側の核は**閾値の 1 段**だけ。 -/
theorem TRIO_terminates_of_mliftR (h : L53.MliftR) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  TRIO_terminates_of_liftTie (L53.liftTie_of_mliftR h) he

/-- **無限展開列は無い**、`MliftR` と `TowerExp` から。 -/
theorem no_infinite_expansion_of_mliftR (h : L53.MliftR) (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_liftTie (L53.liftTie_of_mliftR h) he

/-- **★★★★★ 核ちょうど 2 本の形**: 持ち上げは `MliftR`（閾値の 1 段）、
節 2 は `GraftFromExp`（連結 = `WCat` / `WSnoc`）。どちらも既存の証明ずみ定理の
**1 段の一般化**。 -/
theorem TRIO_terminates_of_mliftR_graft (h : L53.MliftR) (hg : L53.GraftFromExp) :
    WellFounded stepRel :=
  TRIO_terminates_of_towerOK (L53.towerOK_of_mliftR_graft h hg)

/-- **★★★★ Trio sequences terminate, modulo `(WCONVEX)` and `TowerExp`.**
`(WCONVEX)` is strictly weaker in shape than `(ROW1MONO)`: it may assume a
witness BELOW as well as above.  That is exactly what the (WL) induction
supplies — the lower end is the induction hypothesis and the upper end is free
from `(ULIFT)` — and the two sandwich halves that connect them are now proved
(`Le1_Lift1_oper`, `Le1_oper_Lift1_shiftr01`), so nothing about masks, cones,
ties or `oper` survives in the hypothesis. -/
theorem TRIO_terminates_of_wconvex (hc : WConvex) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  TRIO_terminates_of_liftStage (liftStage_of_wconvex' hc) he

/-- **No infinite expansion sequence**, from `(WCONVEX)` and `TowerExp`. -/
theorem no_infinite_expansion_of_wconvex (hc : WConvex) (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_liftStage (liftStage_of_wconvex' hc) he

/-- **⚠ 参考: `(ROW0FREE)` は定理と同値**（進展ではなく警告のための記録）。
行 1 で効いた「証明済みの上界 ＋ 単調性」の手は行 0 では使えない: 深さを全部 0 に
潰した列は `nextrel0` が空で全列が孤児なので**無条件に `W`**（`flat_mem_W`）。
よって「行 1・行 2 が同じなら行 0 は効かない」を仮定した瞬間に停止性そのものに
なる。行 0 の単調性や (DEPTHORD) を補題として使おうとしないこと。 -/
theorem TRIO_terminates_of_row0free (h : Row0Free) : WellFounded stepRel :=
  step_terminates (wf_Rnf_of_wf_TS
    (Wset.wf_of_cofinality_and_membership
      (fun hM hN hlt => trio_cofinality hM hN hlt)
      (fun M _ => ⟨Wset.lev M 0, mem_W_of_row0free h M⟩)))

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
theorem TRIO_terminates_of_tower (htow : ShiftTowerClosedS) (he : Wset.TowerExp) :
    WellFounded stepRel :=
  TRIO_terminates_of_parented (liftStageParented_of_tower htow) he

/-- **No infinite expansion sequence**, from `(TOW)` and `TowerExp`. -/
theorem no_infinite_expansion_of_tower (htow : ShiftTowerClosedS)
    (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_parented (liftStageParented_of_tower htow) he

/-- **Trio sequences terminate, modulo `(TOW)` and the ROW-2 half of
`TowerExp`.**  The row-1 half of `TowerExp` is the same shifted copy tower
(`towerExp1_of_tower`), so the whole proof now rests on exactly two statements:
the shifted copy tower `(TOW)`, and the guarded (row-1-ascending) tower of a
row-2 collapse arriving through clause 2. -/
theorem TRIO_terminates_of_tow (htow : ShiftTowerClosedS) (h2 : TowerExp2) :
    WellFounded stepRel :=
  TRIO_terminates_of_tower htow (towerExp_of_tower htow h2)

/-- **No infinite expansion sequence**, from `(TOW)` and `TowerExp2`. -/
theorem no_infinite_expansion_of_tow (htow : ShiftTowerClosedS)
    (h2 : TowerExp2) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_tower htow (towerExp_of_tower htow h2)

/-- **Trio sequences terminate, modulo `(CAT)` and `TowerExp2`.**  `(CAT)` is
the hypothesis-free strengthening of `Wset.W_add`: `W u` closed under plain
concatenation.  Probe `tools/probe_cat.py`: 372290 pairs, 0 violations. -/
theorem TRIO_terminates_of_cat (hcat : WCat) (h2 : TowerExp2) :
    WellFounded stepRel :=
  TRIO_terminates_of_tow (shiftTowerClosedS_of_closed (shiftTowerClosed_of_cat hcat)) h2

/-- **No infinite expansion sequence**, from `(CAT)` and `TowerExp2`. -/
theorem no_infinite_expansion_of_cat (hcat : WCat) (h2 : TowerExp2) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_tow (shiftTowerClosedS_of_closed (shiftTowerClosed_of_cat hcat)) h2

/-- **★ Trio sequences terminate, modulo `(CAT)` and the LOW half of the row-2
tower.**  `TowerExp`'s `m < a` half is `(CAT)`-strength (`towerExp_of_cat`): the
appended column is then a `W a` member on its own.  What is left is the row-2
collapse with `a ≤ m`, i.e. exactly the case where the orphan's level exceeds
the target stage and the column is harmless only because it finds a parent.
That is where the pair-sequence content sits (its `|R| = 1`, `z = 0` base is the
pair diagonal `[(k*d0, v + k*d1, 0)]`). -/
theorem TRIO_terminates_of_cat_low (hcat : WCat) (h2 : TowerExp2Low) :
    WellFounded stepRel :=
  TRIO_terminates_of_tower (shiftTowerClosedS_of_closed (shiftTowerClosed_of_cat hcat)) (towerExp_of_cat hcat h2)

/-- **No infinite expansion sequence**, from `(CAT)` and the low row-2 tower. -/
theorem no_infinite_expansion_of_cat_low (hcat : WCat) (h2 : TowerExp2Low) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_tower (shiftTowerClosedS_of_closed (shiftTowerClosed_of_cat hcat))
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

/-- **★★★ Trio sequences terminate, modulo `(CAT)` and `(SUBST)`.**  Both are
pure `W`-closure statements, and the pair-sequence theorem is already discharged
(it lives in the `|R| = 1` base of the row-2 tower, proved by
`PairBridge.diag_mem_W` / `diag1_mem_W`).

* `(CAT)` — `W u` is closed under concatenation; it carries `(TOW)`, hence the
  whole stage law `(WL)`, and the `m < a` half of `TowerExp`.
* `(SUBST)` — substituting under each column of a `W u` member a block rooted at
  that column and lying in `W` of that column's own level keeps the stage; it
  closes the row-2 tower via `towerExp2Root_of_subst`.

Probes: `tools/probe_cat.py` 372290 pairs 0 violations,
`tools/probe_subst.py` 38403 decided instances 0 violations. -/
theorem TRIO_terminates_of_cat_subst (hcat : WCat) (hsub : SubstClosed) :
    WellFounded stepRel :=
  TRIO_terminates_of_cat_root hcat
    (towerExp2Root_of_subst hsub
      (liftStage_of_parented
        (liftStageParented_of_tower (shiftTowerClosedS_of_closed (shiftTowerClosed_of_cat hcat)))))

/-- **No infinite expansion sequence**, from `(CAT)` and `(SUBST)`. -/
theorem no_infinite_expansion_of_cat_subst (hcat : WCat) (hsub : SubstClosed) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_cat_root hcat
    (towerExp2Root_of_subst hsub
      (liftStage_of_parented
        (liftStageParented_of_tower (shiftTowerClosedS_of_closed (shiftTowerClosed_of_cat hcat)))))

/-- **★★ Trio sequences terminate, modulo `(CAT)` and `(SUBST1)`.**

`(SUBST1)` is `(SUBST)` for a SINGLE block: the substitutions under the host's
columns are independent, so doing them left to right (`substClosed_of_subst1`)
recovers the full statement.  It is the better core — one block, no `flatMap`,
and no chain condition on the host.

Probes: `tools/probe_cat.py` 372290 pairs 0 violations,
`tools/probe_subst1.py` 62151 instances 0 violations. -/
theorem TRIO_terminates_of_cat_subst1 (hcat : WCat) (hs : Subst1) :
    WellFounded stepRel :=
  TRIO_terminates_of_cat_subst hcat (substClosed_of_subst1 hs)

/-- **No infinite expansion sequence**, from `(CAT)` and `(SUBST1)`. -/
theorem no_infinite_expansion_of_cat_subst1 (hcat : WCat) (hs : Subst1) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_cat_subst hcat (substClosed_of_subst1 hs)

/-- **★★★ Trio sequences terminate, modulo `(SUBST1g)` ALONE.**

`(SUBST1g)` is the whole residue in one statement:

    S ∈ W u,  p < |S|,  C ∈ W (lev S p),  entry C 0 0 = entry S 0 p,
    every other column of C strictly deeper
    ⟹ S.take p ++ C ++ S.drop (p+1) ∈ W u

i.e. `Aop`'s clause 3 (graft a `W m` block onto the LAST column, `m = lev - 1`)
liberalised in exactly two places: any position, and the block's stage raised
from `lev - 1` to `lev`.

`(CAT)` is gone.  Its two consumers are both `(SUBST)`:

* `(TOW)` — the shifted copy tower is `(SUBST)` over the constant diagonal
  `[(x0 + k*e, b, c)]_{k<n}` at level `2b+c = u` (`shiftTowerClosedS_of_substG`),
  which carries the stage law `(WL)`;
* `TowerExp`'s `m < a` half — the two-column host `[(0,v,z), t] ∈ W a`
  (`two_col_mem_W`, itself the pair theorem) has exactly the two levels the peel
  and the trailing column need (`cons_mem_W_of_substG`).

Probe `tools/probe_subst1g.py`: 210201 instances, 0 violations. -/
theorem TRIO_terminates_of_subst1g (hs : Subst1g) : WellFounded stepRel := by
  have hgG : SubstClosedG := substClosedG_of_subst1g hs
  have htowS : ShiftTowerClosedS := shiftTowerClosedS_of_substG hgG
  have hWL : LiftStage := liftStage_of_parented (liftStageParented_of_tower htowS)
  have h2 : TowerExp2Low :=
    towerExp2Low_of_root
      (towerExp2Root_of_subst (substClosed_of_substClosedG hgG) hWL)
  exact TRIO_terminates_of_tower htowS (towerExp_of_substG hgG htowS h2)

/-- **No infinite expansion sequence**, from `(SUBST1g)` alone. -/
theorem no_infinite_expansion_of_subst1g (hs : Subst1g) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) := by
  have hgG : SubstClosedG := substClosedG_of_subst1g hs
  have htowS : ShiftTowerClosedS := shiftTowerClosedS_of_substG hgG
  have hWL : LiftStage := liftStage_of_parented (liftStageParented_of_tower htowS)
  have h2 : TowerExp2Low :=
    towerExp2Low_of_root
      (towerExp2Root_of_subst (substClosed_of_substClosedG hgG) hWL)
  exact no_infinite_expansion_of_tower htowS (towerExp_of_substG hgG htowS h2)

/-- **★★★★ Trio sequences terminate, modulo the REVIVAL case alone.**

`subst1g_of_revive` runs the induction on the host's `W` datum over the
prefix-closed substitution property and closes everything except one shape.
Writing `D = S.drop (p+1)` and `R` for the substituted sequence:

* **mirror** — `D` has ≥ 2 columns and its trailing column has a parent inside
  `D`: `Xbar.oper_append_inner` (no `rsum`) mirrors `oper` across the
  substitution and the datum at `S⟦n⟧` is the goal;
* **orphan** — `D ≠ []` and `R`'s trailing column has no parent in `R` either:
  `oper` peels, and the peel is the substitution on the PREFIX `S.dropLast`,
  which the prefix package supplies;
* clause 1 is immediate (`C ∈ W 0 ⊆ W u`).

What survives is `Subst1gRevive`: the block sits at the very end (`D = []`), or
`R`'s trailing column HAS a parent although it is an orphan inside `D` — i.e.
**the context revives a dead orphan**.  That single shape now carries the whole
termination theorem. -/
theorem TRIO_terminates_of_revive (hrev : Subst1gRevive) : WellFounded stepRel :=
  TRIO_terminates_of_subst1g (subst1g_of_revive hrev)

/-- **No infinite expansion sequence**, from the revival case alone. -/
theorem no_infinite_expansion_of_revive (hrev : Subst1gRevive) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_subst1g (subst1g_of_revive hrev)

/-- **★★★★★ Trio sequences terminate, modulo a residue with NO STAGE in it.**

`Wset.W_root_stage` (new) says the stage of a `W`-member is exactly its root's
level, so together with `lev_root_le_of_mem_W`

    M ∈ W u  ↔  M ∈ Wself ∧ lev M 0 ≤ u

— the whole indexed family collapses to one set plus a root-level side
condition.  Since a substitution never raises the root level, the stage
quantifier drops out of the core, and what carries the entire termination
theorem is a single stage-free statement: *a `Wself` member stays in `Wself`
when a `Wself` block is grafted under one of its columns, in the one case where
the context revives a column that is an orphan inside its own block.* -/
theorem TRIO_terminates_of_revive_self (h : Subst1gReviveSelf) :
    WellFounded stepRel :=
  TRIO_terminates_of_revive (subst1gRevive_of_self h)

/-- **No infinite expansion sequence**, from the stage-free residue. -/
theorem no_infinite_expansion_of_revive_self (h : Subst1gReviveSelf) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_revive (subst1gRevive_of_self h)

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

**Measurement.**  ⚠ The old figure (`tools/probe_snoc.py`: 14455 instances,
0 violations) measured *nothing*: its `inW` omits clause 3 of `Aop`, so on
decided inputs it collapses to `lev S[0] ≤ a`, and `(C ++ [p])[0] = C[0]`
makes the implication a tautology.  Only 408 of its 5068 matrices had a
certified `C ∈ W u`.

The sound figure is `tools/dbms/r49.py`: **≈111000 instances, 0
counterexamples, both sides certified** — `Wlo C = true` certifies `C ∈ W u`
and `Wup (C ++ [p]) u = false` certifies `C ++ [p] ∉ W u`.  Cross-checked
against the independent refuter `tools/refute.py` (the contrapositive of
`TRIO.L47.W3`) on 4580 instances with 0 disagreements.

⚠ `WSnoc` does **not** close under expansion to any fixed depth (the depth
needed grows with `n`), so the measurement reads "no counterexample found",
never "proved".

⚠⚠ **Do not read `WSnoc` as "short, therefore promising"** (task L47).  Its
own proof is circular: `C ++ [p] ∈ W u` can only be shown by clause 2
(`TRIO.L47.wsnoc_clause2_iff` — clause 1 dies on `C ≠ []`, clause 3 on
`domT`'s `¬ hasParent`), and

    (C ++ [p])⟦n⟧ = C.take r ++ shTower (C.drop r) δ n

where `r` is `p`'s parent.  For `r ≥ 1` a length induction closes it, but
`r = 0` leaves `shTower C δ n ∈ W u`, which is `ShiftTowerClosed` verbatim —
and `WSnoc → WCat → ShiftTowerClosed` (`wcat_of_snoc`,
`shiftTowerClosed_of_cat`).  `r = 0` really happens: **9.65%** of 200299
pairs whose `C` is certified by `zeroRow2_mem_Wself` (row 2 ≡ 0), e.g.
`C = (1,0,0)(5,4,0)`, `p = (6,2,0)`.

So `WSnoc` is a *shorter statement* than `Subst1gReviveSelf`, not a *weaker*
one: it is the same knot. -/
theorem TRIO_terminates_of_snoc (hsn : WSnoc) : WellFounded stepRel :=
  TRIO_terminates_of_tower (shiftTowerClosedS_of_closed (shiftTowerClosed_of_cat (wcat_of_snoc hsn)))
    (towerExp_of_snoc hsn)

/-- **No infinite expansion sequence**, from `(SNOC)` alone. -/
theorem no_infinite_expansion_of_snoc (hsn : WSnoc) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_of_tower (shiftTowerClosedS_of_closed (shiftTowerClosed_of_cat (wcat_of_snoc hsn)))
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
