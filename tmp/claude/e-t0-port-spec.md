# E: t = 0 の偽の入力 hAbs（T0AbsW）を AbsWNxU 版に替える（trio-claude → trio-codex、2026-11-02）

T0AbsW M r L ρ := ∀ n ≥ 2, ∀ σ, Cons (gexp M r L 0 0 n) σ → AbsWN M (gexp …) r ρ σ は 39 列の標準形で偽
（V3T0AbsFalse）。その枠は BadAbsShape に入り、ゆるみは悪い列 i だけ（tmp/claude/abs_slack_20261101.json の t0 の 2 枠）。
t = 2 と同じ道具で直す。鎖の一覧は tmp/codex/t0_absw_chain_20261101.md（D2）。

## 新しい入力
def T0AbsWU M r L ρ := ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → AbsWNxU M (TRIO.gexp M r L 0 0 n) r ρ σ
∧ NotBumpKidXU M (TRIO.gexp M r L 0 0 n) r ρ σ
（NotBumpKidXU が t = 0 で構造から出るなら外してよい。まず入れておき、後で測る）
T0AbsW.toU: 古い入力から新しい入力（AbsWN.toX → AbsWNx.toU、NotBumpKidX.of_absWN → notBumpKidXU_of）。

## 手本
t = 2 で同じ直しをした差分が手本:
- エンジン: V3DepRWU.deps_lhd_otW_RU → WfT2X1.deps_lhd_otX → WfT2X1U.deps_lhd_otXU。変えた場所は 4 つ:
  (1) bump 型の列の v（AbsAt ∨ Bd、Bd なら v_bump_lhdV で許容 v(P1 i)）、
  (2) 数える子のない列の o を v から（o_noarg_lhdV）、
  (3) 最後の数える子が Bd の親の o（bad_frame、許容が親でなければ bad_frameG）、
  (4) vupg が Bd を読む（hBdUp で Bd を運ぶ）。
- 結論の型: Lhd z を PX（Lhd z ∨ (Bd i ∧ Lhd (vOpt ρ (par M 1 i)))）に。PX.lt で < は出る。
- 悪い集合は Bd := BdXU M N ρ σ r i（bnd = r）、仮定は bdxu_absX・bdxu_up・bdxu_F・bdxu_cl・notBumpKidXU_of。

## 手順（新しいファイルに U 版を作る。既存は変えない）
1. t0_dep_lhdU（V3T0D.lean 773 行 t0_dep_lhd の写し）と t0_dep_otSU（V3T0DepS.lean 96 行 t0_dep_otS の写し）:
   hAbs : AbsWN … を (hAbsX : ∀ i < r, e1 ≠ 0 → e2 ≠ 0 → AbsAt ∨ Bd i) (hBdUp) (hBdF) (hBdCL) (hBdK) に替え、
   結論の Lhd z (valB σ b i) (valB ρ b i) を PX 形に。上の (1)〜(4) を写す。
2. t0_coreG2U（WfDrL4.lean 4042）: 中の hdl : σ.o d ≤ ρ.o d は PX からの < で作る（le_of_lt）。
3. T0DFU（V3T0TopR.lean 49 の T0DF の Lhd z 欄を PX 形に）、t0_otdG2U（WfDrL4.lean 4264）。
4. 読む側: t0_carrierV3 の hdl（107-108 行）は PX からの <。t0VSD_atC2（V3T0ConsumersV3.lean 119-143）は 142 行で
   変わった v c の Lhd z を使う → ここが唯一 ◁ を本当に使う所。まず止まって、そのゴールと周りを私に送る
   （t = 2 では vs_changed_boundVG で直した。同じ形なら同じ補題で済む）。
5. t0DF_of_seed_inputsU, t0_carrierV3U, expCore0_of_seedsU（V3T0CarrierV3.lean）を hAbs : T0AtV3 T0AbsWU で。
6. 入口 V3TranslationAllUV3.lean: V3TranslationAbsUV3 の hAbs を hAbsU : T0AtV3 (fun M ρ r L => T0AbsWU M r L ρ) に
   替えた desc3 / translation_order / translation_surj（名前の末尾 UU）。
7. 健全性: V3T0AbsFalse の 39 列の行列で、新しい入力の該当の枠（n = 2, i = 34）で BadAbsShape と BdXU が成り立つ
   ことを decide で（V3AbsUpgSanity と同じ流儀）。

## 決まり
- 既存のファイルは変えない。roots に足す前に、もうあるかを確かめる。
- git は使わない。区切りごとに、ファイル一覧・単体と全体ビルドの exit・公理・コミットメッセージ案を chm で送る。
- 詰まったら、ファイル・定理・ゴールを送って止まる（C3 のときの止まり方でよい）。
- 長いジョブはバックグラウンドで（AGENTS.md）。
