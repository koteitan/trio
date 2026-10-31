# WfT2R: t = 2 の Bad2 の道のつなぎ替え（2026-11-01）

最上位を `T2BelowXResV2X` の上で組み直した（WfT2R1〜9、すべて緑、build 1105 jobs、公理は propext・Classical.choice・Quot.sound のみ）。

## 結果
- `trio_terminates_main_V2_curYR`（WfT2R9）: 今のトップ `trio_terminates_main_V2_cur` の
  `hTB2 : T2BadRes` を `hQD : T2QNDomBad2`（T2BadRes の第 2 成分）と `hRY : WfT2X.T2BelowRV2Y` に替えた形。
  T2BadRes の第 1 成分（偽の `SrcC3Res` を含む）はもう要らない。
- `T2BelowRV2Y` = `T2BelowRV2X` から `NotBumpKidX` を外した形。残る新しい欄は `AbsWNx` だけ（WfAbsW で全集合・接ぎ木で例外 0）。

## NotBumpKidX は構造で証明した（WfT2R9 `notBumpKidX_of`）
m = P₀ i が p = P₀ m の bump 子なら e₁ p = e₁ m < e₁ i（BadAbsShape の P₁ i = m）。
`BumpLeaf`（LocInv の欄、標準形で真）から e₂ i = 0。BdX の e₂ i ≠ 0 と矛盾。
測定（probe_nbk_struct.py）: graft36c・graftM36x・std_a で、構造の形をもつ列 25 万 8 千個のうち m が bump 子のものは 0。
bump 子の子はすべて e₂ = 0（std_a 先頭 2 万個で 20497 個）。

## hQlowV は全部 Lean で証明済み
使う Q は 5 つで、すべて引数 0 の最後の子は書き換えないので空虚に成り立つ:
QFO（qFO_lowV）、QFCo（qFCo_lowV）、QVRAt（qVRAt_lowV）、QT2F（qT2F_lowVXR）、QT2P（qT2P_lowVXR）。測定は不要。

## ファイル
- WfT2R1: VRA 系の写し（pathLvAll_pre_t2・t2VRAPre_of・t2VRASeed(G)_of・V3T2VRASV の種の補題・vsmallRAll_expand_t2・
  t2VRAV2_of）と `pathLv_of_shapeXR`。
- WfT2R2: clField_expand_t2（hQlowV を足した）・frameOT_expand_t2、FDCopy の source_v_base_*、FDCopyRoot の 3 本。
- WfT2R3: bumpFields・rootP・G.ph3c/fc3_expand_t2(S)・t2_val_expand・vsmallF_expand_t2(V)・clField_expand_t2SK
  （hQlowV を足した）・frameClosed_expand_t2K・t2VSFCV2_of(2)。
- WfT2R4: `t2_assembleRootX`（t2_assembleOTX の結論を根の下降に。PX.lt で悪い列でも σ < ρ、根は悪くない）と
  `t2_sv_rootX`・`t2_qr_rootX`・`t2_qn_rootX`（t2_*_belowX の結論を根の下降に）。
- WfT2R5: `t2_root_ofX`（t2BelowXS_ofX の証明で根のエンジンを使う）: n ≥ 2 の M[n] の根の値が下がる。
- WfT2R6: `hExp_t2_inv3V2XR`・`expT2V2_ofXR`（下降は t2_root_ofX から。t2_drops_ge2 と Res3T2 を使わない）。
- WfT2R7: `Res3T2X`（Res3T2 から偽の欄 absN を外した形）、`R2V2X`、`r2V2_ofXR`、`T2Drop2X`（t2Drop2X_of）、
  `t2_dropsCX`・`hT2_V2XR`・`desc3_V2OXR`・`badOutT2B_ofXR`。
- WfT2R8: `trio_terminates_main_V2_baseXR`・`trio_terminates_main_V2_curXR`（hRX : T2BelowRV2X）。
- WfT2R9: `notBumpKidX_of`、`T2BelowRV2Y`、`trio_terminates_main_V2_curYR`。
- 生成: gen.py・run_gen.py（写しは機械的、手の修正は PATCH と patch7/8.py）、gen4.py・gen5.py。

## 発見
- `Res3T2.absN`（V3T2Top）は AbsWN M M[n] そのもの。よって `R2V2` は `T2BelowXResV2` と同じ偽の欄を持ち、
  `r2V2_of`・`hR2_t2_ofW` を使う `hExp_t2_inv3V2`（t2_drops_ge2）と `hT2_V2`（t2_dropsC）もそこを読んでいた。
  X 版では absN を根の下降 `T2Drop2X` に替え、t2_root_ofX で証明した。

## 残り
1. `T2BelowRV2Y` の `AbsWNx` 欄（と `T2SeedRR`）。
2. `T2CBadOut`（トップの仮定のまま）は `Res3T2` を返すので、偽の欄 absN を含む。T2CBad の形の M では
   `t2_dropsC`（旧）と `t2_drops_ge2` を通る。X 版にするには T2CBadOut を Res3T2X ∧ 根の下降に替えた
   `T2CBadOutX` を作り、hT2_V2XR・badOutT2B_ofXR・hInvV2_all の T2CBad の枝を写す必要がある。
   absN が T2CBad の行列で偽かどうかは未測定。
