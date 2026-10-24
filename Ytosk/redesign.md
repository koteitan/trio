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
