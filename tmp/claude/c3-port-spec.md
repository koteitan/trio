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
