# 落とす補題と t0・t2 エンジンの作り直し（ブランチ drop-redesign、2026-10-24 開始）

接ぎ木の標準形（tmp/ytosk-handoff/sets/graftA.pkl・graftB.pkl）で、最上位の残り HDropV2W・HFrameV2 と不変条件 Inv3V2 の欄 TPLoW・AbsDW が偽（desc.md「接ぎ木の標準形で最上位の残りを測り直した」以降）。原因は「x − 1 が上がり先を失う」弱い変化が、今の設計が想定しない形（x − 1 の親が bump 子・弱い列が x − 1 でない・弱い元が数える子 x を持つ）で伝わること。

## 済んだ書き換え（このブランチ、ビルドは未完）
- `UpgAbsXW`・`UpgAbsXW0` と落とす補題の hX1 の弱い選択肢から `NBPar` を外した（V3MainT1D・V3DropMain・V3DropStrong・V3DropWeak0・V3DropR）。測定: UpgAbsXW0 の破れ 756 件はすべて NBPar だけ（tmp/claude/uaw0c.py）。
- `CntX` の第 2 の選言を「数える子は最後の列だけ ∧ `UpgBad M ρ (M.length - 2)`」にした（NBPar を外し、UpgBad を x − 1 で問う）。測定: PV がこの形で graftB 全数・ext2・std_b・ext1 で例外 0（tmp/claude/popvg2.py）。
- pv_of 系（4 ファイル）の x − 1 の弱い道を新しい CntX に合わせた。
- 偽になる補題を消した: `CntX.nocnt_of_bump`（V3DropMain）、`UpgAbsXW.toX_xm1`・`PO.zero_of_ne`・`CntX.nocnt_of_ne`・`PO.zero_t0`・`CntX.nocnt_t0`（V3MainT1D）。`PO.zero_of_strong`・`CntX.nocnt_of_strong` は新しい形に合わせた。

## 残りの手順
1. V3BumpDrop（いま build が止まる所）:
   - `BumpNewAt M x ρ ρ' i` = (x ∈ children M i ∧ children M i ≠ [x]) ∨ (bump 子 jl の子 kl < x が数える子 x を持ち v′(kl) ⋪ v(kl)) ∨ (V = v(P₁ i) の加数 r で ¬ r < W′、r < W、¬ r ◁ W)。
   - 新しい残り（BumpAbsC の置き換え）: BumpNewAt の列で bump_rel の結論（isOT v′(i) ∧ (v′ ⊴ v ∨ WkVA ∧ WCSP ∧ CntX)）。測定: PV は新しい CntX で例外 0 なので成り立つ。
   - bump_rel の冒頭で BumpNewAt を場合分け。g_level に「新しい弱い元がない」と「x は i の子でない」を渡し、`nocnt_of_bump` の 2 か所（kl の CntX が第 2 の選言なら x は kl の数える子で弱い → 新しい弱い元）を置き換える。
   - `BumpWeakShapeSrc` に前提「x ∉ children M i」を足す（測定: 広げた形も例外 0、tmp/claude/dropres2.py の BWS.jx・BWS.jxUB）。
   - BumpAbsC の中身を使う AbsWN の導出（V3T0AbW の absWN_take_t0、V3T2Top・V3T2AbW の absWN_of_absC、V3BumpExt）を、接ぎ木で測ってから直す。
2. t0 エンジン: `PO.zero_t0`・`CntX.nocnt_t0` の 9 ファイル（V3T0DepH・DepH0・DepR・TopR・DepT・DepU・VSR・OT、V3T0C）と V3T0Weak・V3T0UpgAbs（`strong_of_not_nb` は偽）。
   - ¬ UpgBad(x − 1) なら x − 1 で強い吸収が成り立ち（`UpgBad` の否定）、新しい CntX の第 2 の選言も起きない → 今までの議論が通る（置き換えの補題 `PO.zero_of_noBad`・`CntX.nocnt_of_noBad` を足す）。
   - UpgBad(x − 1) ∧ r = x − 1 ∧ NBPar は今までの弱い場合（V3T0Weak）。
   - それ以外（UpgBad(x − 1) ∧ (¬NBPar ∨ r ≠ x − 1)）が新しい形。t0 で o′(r) ◁ o(r) が偽になる 72 件（tmp/claude/t0or.py）はここ。エンジンの結論を新しい残りで受ける。V3T0C の弱い場合の枝は WkVA・WCSP しか使わないので、場合分けを ¬ LhdE だけにすれば通る見込み。
3. t2 エンジン（V3T2Top・V3T2UpgAbs・V3T2QUBad・V3MainV2・V3ResV2）: 「強い吸収の破れは NBPar を与える」を同じ場合分けに。
4. Inv3V2 から TPLoW・AbsDW を外す（または前提で制限）。t = 1・q = r のエンジン（V3QRKeep の lo_keep_Q など）が使う (L)(ii) が接ぎ木で破れる場合を調べる。
5. すべて済んだら、新しい残りを接ぎ木と 11 集合で測り直し、main にまとめる。

## 方針の変更（2026-10-24、ブランチ guard-redesign）
- graftB を Bad2(M) :=「x − 1 に上がり先がある ∧ x − 1 の親が bump 子」で分けた（tmp/claude/badsplit2.py）。Bad2 でない graftBn2（75698 個）では、HFrameV2（TPLoW・AbsDW）・落とす補題の欄（BumpWeakSrc・UpgAbsXW0・BumpAbsC）・PV（元の CntX）・qncl がすべて例外 0（使っていない AbsSR・BumpAbsS を除く）。Bad2 は graftB の約半分（接ぎ木の作り方による）、ext2 の 0.27%（4073 個）、std_a の 67 個。
  - 狭い Bad（UpgBad(x − 1) ∧ ¬NBPar(x − 1)、756 個）では足りない: BumpAbsC 9 件・TPLoW 10 件・AbsDW 5 件は Bad の外（x − 1 = 33 の V = 0 で吸収は自明だが、o(33) が変わり i = 31 で r ∈ [W′, W) が残る）。
- よって CntX などの定義は元のままでよい。drop-redesign の書き換えは使わない（ブランチは残す）。
- guard-redesign で済んだこと（ビルド未完）: `Bad2` を V3Inv2 に定義。Inv3V2・TakeFrameV2 の tplow・adw を「¬ Bad2 M → …」に（これで HFrameV2 は接ぎ木でも真）。qr_final_inv3V2・V3ExpInv2 の 2 定理に hNB : ¬ Bad2 M。土台 SRO[n] は fun _ => で包んだ。
- 止まった所: V3MainV2 の expT1Out_of_step（qr の枝で hNB が要る）。
- 残りの設計:
  1. ExpT0OutV2・ExpT1OutV2・ExpT2V2・R2V2 に前提 ¬ Bad2 M。Bad2 の M の段は新しい残り（T2CBadOut と同じ形: 展開の Inv3V2・根の下降・t = 2 の Res3T2）。
  2. HDropV2W（DropResH0）に前提 ¬ Bad2 M。StepCtxV2 の R を ¬ Bad2 M → Res3AW に、pre の Res3AW を ¬ Bad2 (M.take j) → に弱める。
  3. 接頭辞の Inv3V2 を作る pre_V2（1 列ずつ落とす）は、途中の接頭辞が Bad2 だと DropRes がない → Bad2 の行列の 1 列落としを新しい残り（TakeBad: Inv3V2 P → Inv3V2 (P.take) の形、HTake と同じ出力）にする。
  4. t = 2 の下降の Res3D（接頭辞を落とす鎖）も Bad2 の接頭辞で切れる → 鎖が使う関係（t2_dropsC）を調べ、Bad2 の段は新しい残りで受ける。
  5. 新しい残りは Bad2 の行列だけについての主張なので、接ぎ木の Bad2 側（graftBb2.pkl）と ext2 の Bad2 側で測る。
