# WfT2X: t = 2 の Bad2 の道を AbsWNx で作り直す（2026-11-01）

WfAbsW の「次」の 1〜3 と 4 の半分、5 の入口を Lean で緑にした（WfT2X1〜8、すべて緑、build 1232 jobs）。

## 不変条件
呼び出し (b, i) の主張を
  PX b i := (σ(b,i) ◁ ρ(b,i)  ∨  (Bd i ∧ σ(b,i) ◁_{v(P₁ i)} ρ(b,i)))  ∧  σ(b,i) は標準形
にした（WfT2X1 `PX`）。Bd は悪い列の集合で、仮定は
- hAbsX: i < bnd, e₁ i ≠ 0, e₂ i ≠ 0 ⇒ AbsAt i ∨ Bd i
- hBdS: Bd i ⇒ BadAbsShape i
- hBdK: Bd i, P₀ i = m, P₀ m = p ⇒ col m ≠ bump p（m は bump 子でない）

## Lean（新しいファイルだけ）
- WfT2X1 `deps_lhd_otX`: deps_lhd_otW_RU の写し。
  - v の bump 枠: AbsAt なら v_bump_lhdW（◁）、でなければ Bd i で v_bump_lhdV（◁_{v(P₁ i)}）。
  - o を v から: 悪い列は o = ψ_{v}(0) なので o_noarg_lhdV。RClaimU・REr は引数 0 でただ。
  - o の枠で最後の数える子 c が悪い列: `bad_frame`（o_frame_lhdV に標準形・RClaimU（rc_nnU）・REr を足した形。
    Good3 N は使わない）。親 m の o は ◁ で下がる。
  - vupg は悪い列を読まない（BadAbsShape の「i へ上げない」）。vbump の k は悪い列でない（hBdK）。
- WfT2X2 `good_below_ofX`・`t2_assembleOTX`: 結論の FrameShape を FrameShapeX に（悪い親では第 4 の場合）。
- WfT2X3 `t2_sv_belowX`・`t2_qr_belowX`・`t2_qn_belowX`: hAbs : AbsWN を AbsWNx ∧ NotBumpKidX に。
  Bd := BdX（i < bnd ∧ e₁ ≠ 0 ∧ e₂ ≠ 0 ∧ ¬AbsAt ∧ BadAbsShape）。種の hSeed は IH を使っていなかったので写すだけ。
- WfT2X4 `T2BelowResX`・`T2BelowXSX`・`t2BelowXS_ofX`・`hExp_t2_resX`、旧 ⇒ 新 `T2BelowRes.toX`
  （AbsWN ⇒ AbsWNx、AbsWN の下で NotBumpKidX は空虚 `NotBumpKidX.of_absWN`）。
- WfT2X5 FrameShapeX の読み手: `shape4_split`、`frame_of_shapeX`（VRAPre）、`rw_frame_of_shapeX`（VRASeed）、
  `clField_of_shapeX`（FO の骨組み）、`clField_of_shapeSX`（VSR の骨組み）。後の 2 つは hQlowV が要る。
- WfT2X6 `vs_changed_boundV`（添字が ◁_a で下がる版。段 a では comps a a = [] なので許容は効かない）、
  `qVSF_of_shapeX`（VSF）。
- WfT2X7 hQlowV の実例: `qFC_lowV`・`qFCo_lowV`・`qVRAt_lowV`（引数 0 の子は書き換えない）、`qFO_lowV`（最後の子を読まない）。
- WfT2X8 `T2BelowRV2X`（T2BelowRV2 の AbsWN 欄を AbsWNx ∧ NotBumpKidX に）、`t2BelowXResV2X_of`、
  `T2BelowRV2.toX`・`T2BelowXResV2.toX`。

## 測定（probe_nbk.py、run_nbk.sh、nbk.log、n = 2, 3、i < x の bump 型の列すべて）
AbsAt が偽の列で BadAbsShape と NotBumpKid（m = P₀ i が P₀ m の bump 子でない）:
| 集合 | 行列 | AbsAt 真 | AbsAt 偽 | うち shape ∧ NotBumpKid |
|---|---:|---:|---:|---:|
| graft36 | 100 | 3955 | 21 | 21 |
| graft36b | 3461 | 139096 | 256 | 256 |
| graft36c | 11451 | 470832 | 544 | 544 |
| graftM36 | 24596 | 2447221 | 25 | 25 |
| graftM36x | 9914 | 891930 | 80 | 80 |
他の t = 2 の集合（graftBb2St・b2grow1/2・cbadext・ext2b2・shapegrow・graft4/5・graftBb2・Cprime、WfAbsW/absx_sets.log）
は AbsAt が偽の列が 0 なので NotBumpKidX は空虚に真。
接ぎ木での攻撃: graft36b・36c・graftM36x がそれぞれ 36 列の行列に 1〜3 列接いだ族で、例外 0。

## FrameShape の 7 つの読み手と第 4 の場合
第 4 の場合: v(i) 不変、CL_M i = CL_N i = Lc ++ [c]、Lc の o 不変、c は M・N とも引数 0、
o(c)・v(c) は ◁_{v(i)} でしか下がらない、o(i) は ◁。
| 読み手 | 性質 | 第 4 の場合に要るもの | 状態 |
|---|---|---|---|
| V3T2VRAPre `frame_of_shape` | 書き換える枠は M でも書き換える | なし（c は引数 0 で書き換えない、Lc の枠は M と同じ） | `frame_of_shapeX` 緑 |
| V3T2VRASeed `rw_frame_of_shape`・`pathLv_of_shape` | 同上（段の道） | なし | `rw_frame_of_shapeX` 緑（pathLv は X 版の読み替えが残り） |
| V3T2VSF `qVSF_of_shape` | VSmallF の枠 | 添字の ◁_{v(i)} での vs_changed_bound | `vs_changed_boundV`・`qVSF_of_shapeX` 緑 |
| V3ExpT2FO `clField_of_shape`（骨組み clField_expand_t2） | 枠の性質 Q 一般 | hQlowV（ψ_{s}(0) を ◁_a で ψ_{s′}(0) に下げても Q）と N の子の標準形 | `clField_of_shapeX` 緑。QFO は `qFO_lowV` |
| V3T2VSR `clField_of_shapeS`（骨組み clField_expand_t2S/t2SK） | 同上 | 同上 | `clField_of_shapeSX` 緑 |
| V3T2FC（QFCo を VSR/RwClCopy の骨組みで） | FrameClosed | hQlowV for QFCo | `qFCo_lowV` 緑 |
| V3T2VRA（QVRAt を clField_of_shapeS で） | VSmallRAll（段 u） | hQlowV for QVRAt | `qVRAt_lowV` 緑 |

## 残り
1. 骨組み clField_expand_t2（FO）・clField_expand_t2S（VSR）・clField_expand_t2SK（RwClCopy）と
   qVSF の骨組み（VSF）・VRA・VRAPre・VRASeed・VRASV・FDCopy・ExpT2BD・ExpT2RP の、t2BelowXS_of を
   t2BelowXS_ofX に、FrameShape の読み手を X 版に替えた写し（hB : T2BelowXResAt → T2BelowXResAtX、
   hQlowV を足す）。どれも上の X 版の補題を差し込むだけの見込み。
2. トップの hBX : T2BelowXResV2 を T2BelowXResV2X に（`t2BelowXResV2X_of` で T2BelowRV2X から）。
   T2BelowRV2X の新しい欄は AbsWNx（WfAbsW で全集合・接ぎ木で例外 0）と NotBumpKidX（上の表）。
3. NotBumpKidX を構造の議論で証明する（m = P₀ i = P₁ i で i が m の最後の数える子のとき m が bump 子なら
   i は bump 枠の k になり、bump 項の G が下がる形と矛盾するはず）。
