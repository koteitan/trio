# WfAbsW: Bad2・t = 2 の AbsWN M M[n] を外す設計（2026-10-31）

## 結論
- AbsWN M M[n] の使い道は 1 か所だけ: D の伝播エンジン（V3DepRWU `deps_lhd_otW_RU`、V3ExpT2AO の `t2_assembleOT`
  経由の V3DepOTW、V3DepLhd の 4 本）で、種でない bump 型の v の呼び出し i に `v_bump_lhdW` を当てて
  σ.v i ◁ ρ.v i（Lhd z）を出すところ。
- 36 列の行列（WfSrcC3Cex）の M[2] では、この ◁ の結論そのものが偽: v(32) と o(32) は ◁ で下がらない
  （`WfAbsWCex.not_lhd_v`・`not_lhd_o`）。下がるのは許容 V = v(P₁ 32) = v(31) つきの ◁_V で、親 m = 31 の
  o(31) で ◁ に戻る。
- そのため T2BelowXS（`t2BelowXS_of` の結論、T2BelowXResV2 のすべての使い道が読む）の欄 FrameShape も偽:
  m = 31 は種の列でなく、最後の数える子 32 が ◁ で下がらない（`WfAbsWCex.not_frameShape`）。
  したがって hBX : T2BelowXResV2 は（文脈 StepCtxT2 が M で成り立つ限り）偽。Python ではこの M で Inv3V2 の欄は
  M・M[2] ですべて真なので、偽なのは途中の不変条件だけ。

## 使う側の地図
T2BelowRV2.AbsWN → t2BelowXResV2_of → T2BelowXResAt（T2BelowRes の第 4 欄）→ t2BelowXS_of（V3ExpT2BA）
→ t2_sv_below（V3ExpT2SB）・t2_qr_below（V3ExpT2QB）・t2_qn_below（V3ExpT2NB）→ deps_lhd_otW_RU（V3DepRWU:541）
・t2_assembleOT（V3ExpT2AO → V3DepOTW:323）で v_bump_lhdW。
T2BelowXResV2（hBX）の使い手（t2SeedPreShapeC_of・t2VRASeedSVC_of・t2VRAPre_of・t2FDCopyRes_of_path・expT2V2_of・
r2V2_of・hExp_t2_inv3V2 …）はすべて t2BelowXS_of を通る。T2BelowXS の FrameShape を読むのは
V3T2FC・V3T2VSR・V3T2VSF・V3ExpT2FO・V3T2VRA・V3T2VRAPre・V3T2VRASeed。

## 測定（probe_fail.py・probe_absx.py、n = 2, 3、i < x のすべての列）
| 集合 | 行列 | AbsAt が成り立つ列 | AbsAt が偽の列 | 偽の列で BadAbsShape |
|---|---:|---:|---:|---:|
| graft36（cex36 に 1 列接ぐ） | 100 | 3955 | 21 | 21 |
| graft36b（2 列接ぐ） | 3461 | 139096 | 256 | 256 |
| graft36c（graft36b の 250 個にさらに 1 列） | 11451 | 470832 | 544 | 544 |
| graftBb2St | 5384 | 174598 | 0 | — |
| b2grow1 / b2grow2 | 1879 / 3131 | 101922 / 234886 | 0 | — |
| cbadext | 3447 | 115042 | 0 | — |
| ext2b2 | 2609 | 94812 | 0 | — |
| shapegrow | 299 | 12020 | 0 | — |
| graft4 / graft5（WfB2S） | 3147 / 3493 | 143898 / 134008 | 0 | — |
| graftBb2 | 13854 | 450910 | 0 | — |
| Cprime | 103956 | 1794116 | 0 | — |

偽の列ではいつも: v(i) は ◁ で下がらないが ◁_V（V = v(P₁ i)）で下がる、o(i) も ◁_V、o(m) は ◁、
m は bump 子でない（i はどの bump 枠の k でもない）、i・m は種の列（q, r, x − 1, P₀ q）でない。
◁ が偽の呼び出しはこれ以外では i = q（種の列、既存の扱い）だけ（sets1.log・graft36b.log）。

## 新しい欄（Lean、緑）
- `WfAbsW.AbsAt M N ρ σ i`: AbsWN の i での中身。
- `WfAbsW.BadAbsShape M N ρ σ i`: m = P₀ i = P₁ i、CL_M i = CL_N i = []、CL_M m = CL_N m = Lc ++ [i]、
  Lc の o と v(m) は変わらない、i へ上げる列はない。
- `WfAbsW.AbsWNx M N bnd ρ σ := ∀ i < bnd, e₁ i ≠ 0 → e₂ i ≠ 0 → AbsAt i ∨ BadAbsShape i`。`AbsWN.toX`。
- 36 列の行列: `WfAbsWCex.not_absAt`（i = 32 で AbsAt が偽）と `bad_shape`（BadAbsShape が真）。

## 道具（WfAbsWEta、緑）
- `lhd_mono_eta`・`lhd_of_compsSub`・`lhd_sub_eta`（ψ_{a′}(0) ◁_η ψ_a(0)）・`lhd_psi_dis`（b′ ◁_V b ⇒ ψ_V(b′) ◁ ψ_V(b)）・
  `lhd_add_eta`（X + w′ ◁_η X ⊕ w、X の成分が η の成分なら吸収の仮定なし）。
- `v_bump_lhdV`: bump 型の v の枠で AbsWN なしに σ.v i ◁_{v(P₁ i)} ρ.v i。
- `o_frame_lhdV`: 親の o の枠で最後の数える子が引数 0 かつ ◁_{v(i)} なら σ.o i ◁ ρ.o i。
- `bad_parent_lhd`・`bump_col_of_absWNx`: AbsWNx の各列で「v(i) ◁」か「o(m) ◁ ∧ v(i), o(i) ◁_{v(m)}」。
- `WfAbsWFrame.FrameShapeX`（FrameShape ∨ 悪い親の第 4 の場合）と `frameShapeX_of_bad`。

## 残り（エンジンの作り直し）
1. `deps_lhd_otW_RU`（V3DepRWU）と V3DepOTW の写しで、不変条件を
   P(b, i) := Lhd z ∨ (i が悪い列 ∧ Lhd_{v(P₁ i)}) に替える。使う所: ov（`o_noarg_lhdV`）、ochild（親 m で `o_frame_lhdV`）、
   vbump の IH は k が悪くないこと（測定: m は bump 子でない）、vupg（BadAbsShape の「i へ上げない」）。
   悪い呼び出しの isOT・RClaimU・REr の出力は除く（W と同じ扱い）。hAbs を AbsWNx に。
2. `good_below_of`（V3ExpT2BX）を悪い列つきに: 悪い列で FrameShape の代わりに親で FrameShapeX。
3. 3 つのエンジン t2_sv_below・t2_qr_below・t2_qn_below と t2BelowXS_of を AbsWNx・FrameShapeX で写す。
4. FrameShape の 7 つの使い手（上の地図）に第 4 の場合を足す（VSmallF・FrameClosed・FrameOT・VRA の枠の議論を
   v_N(c) = V + W′ の形で）。
5. トップの残りを T2BelowRV2 の AbsWN 欄を AbsWNx にした形にする（AbsWN.toX で古い形から出る）。
