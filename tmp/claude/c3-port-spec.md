# C3: t = 2 の鎖を BdXU で写す（trio-claude → trio-codex、2026-11-01）

目的: 入口の偽の入力 hBX : T2AtV3 T2BelowAtV3（中身は AbsWNx、41 列の標準形で偽: V3T2AbsXFalse）を、
広い入力 AbsWNxU（V3AbsUpgShape.lean）に替えた入口を作る。

## もうあるもの（すべて緑・コミット済み）
- V3AbsUpgLemma: lhd_psi_disG, o_frame_lhdVG
- WfT2X1U: bad_frameG, deps_lhd_otXU（hBdS の代わりに hBdUp・hBdF をとる。hBdK はそのまま）
- V3AbsUpgShape: UpgAbsShape, AbsWNxU, AbsWNx.toU, BdU, BdXU, bdxu_absX, bdxu_up, bdxu_F, bdxu_cl,
  NotBumpKidXU, notBumpKidXU_of

## 手順
1. 鎖を確かめる: T2BelowAtV3（V3T2BelowV3.lean）と V3T2RootV3 から下って、deps_lhd_otX・BdX・bdx_absX・
   bdx_shape・NotBumpKidX・AbsWNx・hBdS を使う定理を全部挙げる（候補: WfT2X2, WfT2X3, WfT2X4, WfT2R4,
   WfT2R7〜R9, V3T2BelowV3, V3T2RootV3, V3T2CarrierV3）。一覧を tmp/codex/c3_chain.md に書く。
2. 各ファイル F について、新しいファイル F + "U"（例 WfT2X2U.lean）に必要な定理だけを写し、名前に U を付ける。
   置き換えの規則:
   - deps_lhd_otX → deps_lhd_otXU。引数 hBdS（bdx_shape など）の位置に `bdxu_up bdxu_F` の 2 つを渡す。
   - Bd := BdX … → Bd := BdXU …。bdx_absX h → bdxu_absX h。bdx_shape → 使わない。
   - AbsWNx → AbsWNxU。NotBumpKidX → NotBumpKidXU（もとの NotBumpKidX h から notBumpKidXU_of h）。
   - 定理の仮定 (hBdS : ∀ i, Bd i → BadAbsShape …) は、(hBdUp …) (hBdF …) (hBdCL : ∀ i, Bd i → CL M i = [] ∧ CL N i = [])
     の 3 つに替える。BadAbsShape から CL = [] だけを取り出している所（WfT2X2.not_bd_of_cl など）は hBdCL を使う。
   - WfT2X2 の good_below_ofX の 135 行目付近（最後の数える子 c が Bd の枝）は、WfT2X1U.deps_lhd_otXU の
     同じ枝と同じ直し方: hBdF i c hBdc hcCL から CL と形を取り、par M 1 c = some i なら bad_frame、
     そうでなければ bad_frameG（許容 vOpt ρ (par M 1 c)）。WfT2X1U.lean の該当箇所をそのまま手本にする。
3. 最後に入口を作る（新しいファイル V3TranslationAbsUV3.lean）:
   - def T2BelowAtV3U: T2BelowAtV3 の AbsWNx を AbsWNxU に、NotBumpKidX を NotBumpKidXU に替えたもの
     （T2BelowResX の U 版 T2BelowResXU を経由してよい）。
   - theorem T2BelowAtV3.toU: 古い入力から新しい入力（AbsWNx.toU と notBumpKidXU_of）。
   - expOut2_of_inputsU, desc3_of_enginesV3U, translation_order_of_enginesV3U, translation_surj_of_enginesV3U:
     V3TranslationInputsV3 / V3TranslationStepV3 と同じで hBX を hBXU : T2AtV3 T2BelowAtV3U に替えたもの。
     （hQR は V3TranslationStepV3 の Step 型を使う版を優先）
4. 健全性（任意だが大事）: V3T2AbsXFalse の 41 列の行列で、i = 37 で UpgAbsShape が成り立つことを
   decide で示す（m = 31, c = 36, p = 32）。σ は V3T2AbsXFalse と同じ値づけ。

## 決まり
- 既存のファイルは変えない。新しいファイルを lakefile の roots に足す。
- 区切りごとに: ファイル一覧・単体と全体ビルドの exit・公理（[propext, Classical.choice, Quot.sound] 以下）・
  コミットメッセージ案を chm で trio-claude に送る。git は使わない。
- 詰まったら、どのファイルのどの定理のどのゴールかを送って止まる。形の定義（UpgAbsShape など）は変えずに、
  まず trio-claude に相談する。

## 改訂（2026-11-02 01:50、codex の指摘を受けて）
codex の指摘のとおり、good_below_ofX の結論 FrameShapeX の 4 つ目の形は子の ◁ の許容を v(i) に固定しているので、
上げの形（許容 v(P1 c) ≠ v(i)）では作れない。結論の形を広げる。

もうあるもの（7f39d412、V3AbsUpgFrame.lean）:
- FrameShape5: 4 つ目の形の許容を任意の V にし、(∀ u, ∀ g ∈ comps u V, g < σ.o c) を足したもの。
- FrameShapeXU := FrameShapeX ∨ FrameShape5、FrameShapeX.toU。
- WfT2X.vs_changed_boundVG: vs_changed_boundV の許容一般版（qVSF_of_shapeX の 5 つ目の形で使う）。

C3 の追加の規則:
- 鎖の中の結論・仮定の FrameShapeX は FrameShapeXU に替える。
- good_below_ofXU の bad-final-child の枝: hBdF の左（par M 1 c = some i）は今までどおり FrameShapeX の 4 つ目
  （Or.inl）。右（成分の上界）は FrameShape5（Or.inr）で、V := vOpt ρ (par M 1 c)、子の ◁ は IH の PX の右の枝
  （v・o とも許容 vOpt ρ (par M 1 c)。左の枝なら lhd_mono_eta）、上界は hBdF、Lhd z (σ.o i) (ρ.o i) は bad_frameG。
- 読む側の U 版（WfT2X5・X6・X7・R1 の該当定理）: rcases hS with hS | h5。左は既存の X 版をそのまま呼ぶ。
  右（FrameShape5）は 4 つ目の形の証明の写しで、
  - shape4_split はそのまま使える（構造の欄は同じ）。
  - clField_of_shapeX / clField_of_shapeSX: hQlowV の代わりに
    hQlowVG : ∀ V a Lv s s', Q a Lv (psi s z z) → Lhd V (psi s' z z) (psi s z z) →
      (∀ u, ∀ g ∈ comps u V, g < psi s' z z) → isOT (psi s' z z) = true → Q a Lv (psi s' z z)
    をとる。QFC・QFCo・QVRAt・QFO の hQlowVG は WfT2X7 の qFC_lowV などと同じ証明（◁ を使っていない）。
  - qVSF_of_shapeX の右: vs_changed_boundV を vs_changed_boundVG（hsm は上界の u := ρ.v i）に替える。
  - frame_of_shapeX・rw_frame_of_shapeX・pathLv_of_shapeXR: 右は 4 つ目の形と同じ証明（◁ を使わない）。
