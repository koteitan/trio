# GraftAll campaign plan (v0.100.0 時点)

状態: `Wstar2_closed_of_graftAll` (Lcone.lean) により、trio 停止性の残核は

```
GraftAll := ∀ S, argOK S → S ≠ [] → ∀ u, ∀ y ∈ W u, based y → graft S y ∈ Wstar2
```

ただ一つ。本文書はその証明キャンペーンの設計地図（probe 済み事実・故障モード・
残る 3 装置）。probe スクリプトはセッション scratchpad、詳細ログは
セッション memory `trio-wset-redesign.md`。

## 1. アーキテクチャ: 𝒳-機械

`𝒳 := {y | based y → ∀ S ∈ CTX, graft S y ∈ Wstar2}` を `Aop`-閉に見せて
A2 で `W u ⊆ 𝒳` を得る。閉包ステップ（要素 Y, データは `Aop W u 𝒳 Y`）の
枝分けと現状:

| 枝 | 状態 |
|---|---|
| (a) 尾部が Y 内に親（B2a 型）| ✅ 一段: clause-2 データ + `liftInner_holds` |
| (b) succ / (c) 死孤児 | ✅ 一段: `graft Y [] = Y.dropLast`（(c) は clause-3 の w:=[]）|
| (d) 行2塔・clause-3 由来 | ✅ 一段: `towerGraft2_lift_mem` + graft-assoc（`graft (graft S Y) w = graft S (graft Y w)`, 段 m_Y < u ガード付き）|
| (e) 行1塔 × 外来リフト t>0 | ⛔ 装置 α |
| (f) 行2塔・clause-2 由来（死孤児が根に復活）| ⛔ 装置 β |
| (g) ブロッカー（尾部が S.dropLast に復活, 0.9%）| ⛔ 装置 γ |

## 1.5 Lean 済み部品（Xbar.lean, v0.101.0–v0.102.2, 全て sorry 0 / axioms clean）

- `oper_append_inner` / `oper_graft_inner`: 尾部親が引数内 → ミラー
- `oper_append_pred` / `oper_graft_pred`: 親なし → 剥離（前置素通し）
- `blocked_parent_lt`: 内部親なし ∧ graft 親あり → 親は文脈部（三分法完成）
- `oper_graft_blocked`: ブロック済み展開 = `graft (M.take (p+1)) (shiftl0 w' copies)`
  — **文脈が厳密に短くなる**（γ の降下ステップ）
- `based_blocked_element` / `argOK_take` / `take_ne_nil`（降下の整合部品）
- `parent_region_row0_ge` / `srow_graft_last` / `parent_append_right_of` / `nextR_nonzero`
- **γ のリフト互換ステップ合成は既証明補題のみで書ける**:
  `liftInner_holds`（ブロック済み = B2a なので適用可）∘ `oper_cons_nat` ∘
  `oper_graft_blocked`。残る γ の未設計部分 = 降下後の新要素
  `shiftl0 w' copies`（M-接尾辞コピー + y-片の混合）への**データ変換**
  （= セグメント化された要素データの合成規則）。

## 1.7 確定アーキテクチャ（2026-08-05 夜）

二層構造（Buchholz 2.7 + 2.5 の trio 対応）:

- **MASTER** = 長さ帰納（`mem_of_Aclosed_aux` 型）: 全ブロック ∈ Wstar2。
  主要ケース (0,v,z)::R は GX-機械への還元で処理。
- **GX-機械** = A2（要素 y の W-構造帰納）:
  `GX := {y | based y → ∀ M（argOK, ≠[], CTXcond M）, ∀ v z a t: Lift1 ((0,v,z)::graft M y) t ∈ W a}`
  - **CTXcond M := 全接頭辞パッケージ**
    `∀ k ≤ M.length, ∀ v z a t: Lift1 ((0,v,z)::M.take k) t ∈ W a`
    — 再帰なしの平 Prop。**MASTER の長さ IH がちょうど供給**
    （文脈 S = Rt は |R| = |M|−1 なので接頭辞は全て短い）。
    take で自明に保存 → blocked-降下と整合。
  - 枝: inner（lift_graft_inner_step + clause-2 データ）✓ /
    dead（lift_graft_dead_step + データ）✓ /
    tower2-clause3（graft_assoc + towerGraft2_lift_mem + データ; Wstar2 の
    パッケージ = CLM そのもの）✓ /
    **CoreBlocked**（降下後の Y'-義務）⛔ /
    **CoreT1L**（α）⛔ / **CoreT2E**（β; clause-2 由来塔）⛔

## 1.8 ✅ GX 機械 Lean 化完了（Gamma.lean, v0.104.0）

`CtxOK`（接頭辞パッケージ）/ `GX` / 三核 `CoreBlocked`・`CoreT1L`・`CoreT2E` /
**`GX_closed`**（(a)/(b)/(c)/(γ-還元)/(d) 全て一段で閉、sorry 0, axioms clean）/
`W_le_GX`（A2）/ `graftAll_of_GX`。残る作業:
1. 三核の証明（α: E-測度 / β: X̄+∀s-key / γ': 降下後 Y'-義務）
2. MASTER 長さ帰納（CtxOK の供給 + graftAll_of_GX を
   liftTower1_of_graftAll 型消費者へ配線; IH は「長さ < N の全ブロックの
   パッケージ」なのでリフト済み接頭辞も自動被覆）
3. 単集合文脈 |S| = 1（graft S y = shift y; W_shift で別処理）

## 1.9 CoreT2E 設計解析（2026-08-05 深夜）— 核心は CtxOK の合成供給

* CoreT2E の自然な放電 = 機械を複合文脈 S' := graft M Y で再起動
  （`graftAll_of_GX S'`）。必要装備は **CtxOK (graft M Y)**。
* **CtxOK は strict で十分**（k < |S|; k = |S| はどの消費者も使わない — 要確認済み）。
* **同値**: `CtxOK S ⟺ ∀ k < |S|, S.take k ∈ Wstar2`（パッケージ = Wstar2 の定義そのもの）。
* 複合文脈の接頭辞: k ≤ |M|-1 は CtxOK M ✓;
  k = |M|-1+j (j < |Y|) は `graft M (Y.take j)` のパッケージで、
  `Y.take j = Y.dropLast.take j`。塔枝の Y は dead-trailing なので
  `Y.dropLast ∈ GX` はデータ一段 ✓ — しかし**深い接頭辞は反復 dropLast で
  データが失われる**（GX 所属は集合所属でありデータを持たない）。
* 候補解:
  (a) GX の義務に要素接頭辞パッケージを内蔵。inner-Y では bad root p_Y 以浅の
      接頭辞が展開で保存される（Y⟦n⟧.take j = Y.take j for j ≤ p_Y — 要 probe）
      ので datum 一段; p_Y 超の接頭辞の供給が未解決。
  (b) **W の接頭辞閉性** M ∈ W u → M.take k ∈ W u?: 成立すれば
      W_le_GX 経由で全て解決。ただし interior 列の staging = 旧 tbAll の内容で
      おそらく非自明（一段では閉じない）。要 probe/検討。
      注: 旧 W* の tbAll 除去は「全段化」で消した — 同じ手（∀a 量化）が
      CtxOK 供給にも効く可能性。
  (c) 消費される k の有限性 → ✗（入れ子降下で全 k が要る）。
* β の段ジャンプ（stage m_G の fresh A2 の整礎化）は依然独立の問題
  （機械の自己適用は Lean 的に ill-founded; 測度が要る）。

## 1.9.5 ✅ β の族化（v0.105.0-1）

- `towerGraft2_lift_fam` / `towerGraft2_lift_mem_fam`（Wset）:
  行2塔は**自分の族要素の graft-義務だけ**を消費する（∀-W-m 界面は不要;
  key の帰納も消える — 所属構築は界面の供給側の仕事に移動）。
- `CoreT2EFam`（Gamma）+ `coreT2E_of_fam`: GX_closed の残核は
  **CoreBlocked + CoreT1L + CoreT2EFam** に更新。

## 1.9.6 ✅ β の単一ステップ核への還元（v0.106.0）+ 装備合成（v0.107.0）

- **`CoreT2EStep`** := β-サイトで `∀ e ∈ W (2*w1+z), based e → graft Y e ∈ GX`
  （w1 = 孤児の行1値; z < w2 なのでこの段は孤児レベル 2w1+w2 より真に下）。
- **`coreT2EFam_of_step`**: j-帰納は機械的 —
  j=0 は datum の peel（`Y.dropLast ∈ GX`）or 単集合なら CtxOK;
  j+1 は IH のパッケージを (v,z,a:=2(v+d1)+z,t:=d1) に適用して
  E_{j+1} ∈ W (2w1+z) を作り hs を適用、graft_assoc で M-graft へ。
  GX_closed の残核 = **CoreBlocked + CoreT1L + CoreT2EStep**。
- **GX'（v0.107.0）**: CtxOK を strict 化（k < |M|）し、GX に
  **要素接頭辞義務**（graft M (y.take i), i ≤ |y|）を内在化。
  閉包の接頭辞放電は全 datum-節で一段
  （clause-2: `oper_take_prefix`（コピー0非シフト）; clause-3:
  `dropLast_take`; 短要素: 文脈パッケージ）。
- **`ctxOK_graft`**: CtxOK M + `Y.dropLast ∈ GX` → CtxOK (graft M Y)。
  §1.9 の CtxOK-合成問題は**解決**。

## 1.9.7 ★ CoreT2EStep の完全形状還元（次の Lean 目標）+ 最終残核

**形状としては CoreT2EStep ⟸ `e ∈ GX` まで潰せる**（未 Lean 化、設計済み）:
`graft Y e ∈ GX` の義務は ∀M'（装備済み）: graft M' ((graft Y e).take i):
- i ≤ |Y|-1: = graft M' (Y.take i) — hYd（datum peel）の接頭辞義務 ✓
- i = |Y|-1+i': `take_graft_high` で = graft M' (graft Y (e.take i'))
  = (assoc) graft (graft M' Y) (e.take i') — **e ∈ GX の接頭辞義務を
  装備済み複合文脈 graft M' Y（`ctxOK_graft`）で呼ぶだけ** ✓
つまり **CoreT2EStep ⟸ W (2w1+z) ⊆ GX（= 機械自身の A2）**。
残るのは唯一、この自己参照の整礎化 = **層化測度**。
naive なレベル帰納の穴: A2 は W-導出木の全ノードを触り、Aset clause-3 の
∀z ∈ W m 量化が任意の W-要素（孤児レベル非有界、"W 0 に lev 201" 病理）を
持ち込む。→ 測度は W-クラス経由ではなく provenance 構造（§1.12）に載せる。

## 1.9.9 ★★★ スライス装備で α 残差消滅（v0.112-113）— 残差は3つ

**第7設計（義務量化子のスライス化）を実装、全ビルド緑**:
- v0.112: tower 界面（towerGraft2_lift/_fam/_mem/_mem_fam, tower1_mem2）の
  hgr/hgrF を ambient (v,z)-スライス + ∀(a,s) に in-place 縮小
  （証明はもともとそのスライスしか消費していなかった）。
- v0.113: `CtxOK M v z`（スライス装備）+ GX の義務を per-slice 装備と対に。
  **`ctxOK_ltail`**: リフト済み複合文脈の (v+t,z)-スライス装備は
  文脈の (v,z)-スライス + peel の接頭辞義務から合成（Lift1_Lift1 +
  ltail_take）→ **CtxLiftT1 は削除（α 残差消滅）**。
  `coreT1L_of_le : (∀σ W σ ⊆ GX) → CoreT1L`。
- **GX_loop (CoreBlockedElt) (CoreBlocked0) (W ⊆ GX)** — 残差3つ:
  γ' 要素合成（文脈長降下）、γ' 根スライス（shift 化; 文脈は argOK なので
  シフト量 = entry M 0 0 > 0）、β の自己参照整礎化（§1.12 の provenance）。

## 1.9.10 ★★★★ 接ぎ木閉包 `gx_graft` で自己参照が消滅（v0.114）— 新設計

**塔は「自分の主ブロックへの反復接ぎ木」である**（`graft_cons`）:
`tow v z R (k+1) = graft ((0,v,z)::R) (tow v z R k)`。したがって

- `gx_take`: GX は接頭辞閉（義務が ∀i を持つので自明）
- **`gx_graft`**: `E.dropLast ∈ GX → w ∈ GX → graft E w ∈ GX`
  （低位接頭辞 = E の真接頭辞義務、高位 = `take_graft_high`+`graft_assoc`
  で装備済み複合文脈 `graft M E` 上の w の義務; 文脈装備は `ctxOK_graft`）
- **`tow_mem_GX`**: `(0,v,z)::R.dropLast ∈ GX` だけで塔要素が全部 GX に入る

⟹ **α も β も「W σ ⊆ GX」を全く必要としない**。α は
`coreT1L_of_plant`（塔 = tow_mem_GX + GX_full）、β は
`coreT2EFam_of_plant`（族要素 `Lift1 (Nb⟦j⟧) d1` の j-帰納）。
`CoreT2EStep` とその W-還元は削除。**機械の自己参照（旧 §1.9.7 の
最終残核）は消滅した**。

新しい残差（v0.114, `GX_loop'`）:
- **`CoreLift`**: `y ∈ GX → Lift1 y t ∈ GX`（GX のリフト閉包）
- **`CorePlantCtx`**: `(0,v,z) :: M.dropLast ∈ GX`（文脈の植え付き peel）
- γ' の 2 核（CoreBlockedElt / CoreBlocked0）

### probe: 複合リフトは引数の Lift1 に落ちない（probe_liftplant.py）
`Lift1 ((0,v,z)::graft R y) t = (0,v+t,z) :: graft (ltail v z R t) y↑` の
y↑ は **coneV マスク**（y の全 le1-祖先が entry1 > v）であり、
- y の根 entry1 ≤ v なら y↑ = y（違反 0/369920 — 既知の (B)）
- y の根 entry1 > v でも y↑ ≠ Lift1 y t（**違反 100664/222 千**、
  最小反例 y=[(0,1,0),(1,1,0)], v=0: 第2列は y の錐外だが複合では錐内）
⟹ 「リフトを graft の中へ押し込む」経路は**閉じた**。CoreLift は
リフト言語の最小形として残る（(e)-壁の純粋形）。

### γ' も同じ形に落ちる（✅ v0.115 で Lean 化: srow ≤ 1）
`gcopies_succ_shift`（d1=0, Core.lean:3658）は
`gcopies (n+1) = gcopy 0 ++ shiftr01 d0 0 (gcopies n)` であり、
`graft E X = E.dropLast ++ shiftr01 (entry E 0 last) 0 X` と同型:
**E := 再基底化した窓（ブロック列を含む末尾つき）** を取れば
`gcopies (n+1) = graft E (gcopies n)` ⟹ `tow_mem_GX` と同じ帰納で
**CoreBlockedElt ⟸ `E.dropLast ∈ GX`**。さらに
`E.dropLast = graft Msuf (Y.dropLast)`（Msuf = M の p 以降の再基底化接尾辞）
なので `gx_graft` で **CoreBlockedElt ⟸ `Msuf.dropLast ∈ GX`**。
（srow=2 のガード付きコピーは d1>0 なので `CoreLift` を経由する。）

**v0.115 実装**: `shiftl0_gcopies_succ`（`gcopies_succ_shift` + shiftl0 の
可換化）で `copies (n+1) = graft (cwin) (copies n)`、`gcopies_mem_GX` で
窓の GX-所属から全コピー塊が GX に入る。核は `CoreWindow`
（再基底化した窓 ∈ GX）と `CoreBlockedEltHi`（srow=2 のガード付き、
リフト残差）に分割: `coreBlockedElt_of_window`, `GX_loop''`。

### ⟹ 残差の統一像
すべての核が「**文脈の断片が GX に入るか**」に収束する:
- 植え付き接頭辞 peel `(0,v,z)::M.dropLast`（α/β）
- 再基底化接尾辞 `Msuf.dropLast`（γ'）
+ リフト閉包 `CoreLift`。
これは「良い文脈クラス 𝒞（接頭辞・接尾辞・graft・断片 ∈ GX で閉じる）を
パラメータとして機械を回し、最後に 𝒞 を構成する」設計に一致する
（𝒞 をパラメータにすれば GX の定義に GX が負の位置で現れる問題は起きない）。
𝒞 の構成が MASTER 長さ帰納（`mem_of_Aclosed_aux`）の仕事。

## 1.9.11 ★★ リフト残差の精密解析（probe 4 本, 2026-08-05）

`CoreLiftPlant`（残る唯一の非-γ' 核）の中身を probe で確定した。

**複合リフトの真の形**（既知 §2 の一般化）:
`Lift1 ((0,v,z) :: graft M D) e = graft (Lift1 ((0,v,z)::M) e) (plift v e D)`,
`plift v e D := liftset D (coneV D v) e`,
`coneV D v = {j | j と j の全 le1-祖先の entry1 が > v}`。
⟹ `gx_graft` と合わせて
**CoreLiftPlant ⟸ (リフト済み植え文脈 peel ∈ GX) ∧ (GX の plift 閉包)**。

probe 結果:
- `probe_liftplant`: 引数の根 entry1 > v のとき `plift v e D ≠ Lift1 D e`
  （違反 100664 件）。根 entry1 ≤ v なら `plift = id`（違反 0）。
- `probe_lowroot`: **塔サイトでは常に「引数の根 entry1 > v」**
  （tower1 564864/564864, tower2 330192/330192, coneV も常に非空）。
  理由: 引数の根は死んだ末尾列の行0祖先なので、死性から
  entry1(根) ≥ w1 > v が強制される。⟹ **plift 部は決して自明化しない**。
- `probe_plift`: cone も coneV も**リフト安定**（0/2313）⟹ どちらの
  リフトも合成可能（`Lift1_Lift1` の coneV 版が成り立つ）。
- `probe_tower2lift` (T): **真の tower2 サイトでは**
  `Lift1 (Nb⟦j+1⟧) e = graft (Lift1 Nb e) (Lift1 (Nb⟦j⟧) (d1+e))`
  （違反 0/21408）⟹ β の族は「リフト済み植え peel ∈ GX」+ `gx_graft`
  だけで閉じる（α の要求と**同一の核**）。
  一方 (T1) 行1塔 `Lift1 (tow v z R k) s = tow (v+s) z (ltail v z R s) k`
  は**偽**（20608/41216; 内側の植えた根は錐外なので Lift1 が上げない）。
  ⟹ α は「リフト済み文脈 Rt 上の塔」として扱うのが正しい（現行どおり）。

**帰結**: α・β は同一の核 `CoreLiftPlant`（= リフト済み植えブロック ∈ GX）
に完全収束。(T) を Lean 化しても核の**型は変わらない**（D := Y.dropLast は
任意の GX 要素を走る）ので優先度は低い。攻めるべきは
`plift 閉包`（要素側）と `リフト済み植え文脈 peel`（文脈側）の 2 つ。

## 1.9.12 ★ plift 残差の分解案（次の攻め口）

`CoreLiftPlant ⟸ CorePlantCtxL ∧ CorePlift`:
- `CorePlantCtxL`: `Lift1 ((0,v,z) :: M.dropLast) t ∈ GX`（文脈側）
  — `ltail_dropLast` で `(0,v+t,z) :: (ltail v z M t).dropLast` に一致
- `CorePlift`: `D ∈ GX → plift v t D ∈ GX`（要素側）

`probe_allhigh`: 塔サイトのうち **68%（tower1 384000/564864,
tower2 228528/330192）は D の全列が entry1 > v**、その場合
`coneV D v = 全体` すなわち **plift = 一様な行1シフト `shiftr1 t`**
（trio には `oper_shiftr1`/`le1_shiftr1`/`lev_shiftr1` の同変性一式がある）。
残り 32% は「低い列（entry1 ≤ v）に高い部分木がぶら下がる」形。

⟹ **分解案**: D を「低い列 + 高い部分ブロック」に分け、plift は各高部分
ブロックへの**一様行1シフト**として作用する（マスクは部分木単位）。
`gx_graft` が既にあるので、D の分解が graft-合成で書ければ
`CorePlift ⟸ GX の一様行1シフト閉包` に落ちる。
一様シフト閉包は `oper_shiftr1` 同変性で機械の枝解析が通る可能性がある
（節3データの整合だけ要確認）。⚠ ただし値ベースのリフト言語は 6 回
反証されているので、**分解の probe を先に**（未実施）。

## 1.9.14 ✅ v0.116: γ' 窓核 → 文脈接尾辞核（残差の最終形）

`seg_graft_eq`（複合の窓 = 文脈の接尾辞 ++ シフトした datum の peel）と
`shiftl0_seg_graft`（再基底化すると窓 = `graft Msuf (Y.dropLast)`）で
`CoreWindow ⟸ CoreCtxSuffix`（`coreWindow_of_suffix`）。補助として
`entry0_shiftl0` / `entry0_seg` / `shiftl0_seg_dropLast` /
`shiftl0_shiftr01_sub` / `le0_of_le1` を追加。

**残差の最終形（`GX_loop_pieces`）**:
| 種別 | 核 | 内容 |
|---|---|---|
| 文脈断片 | `CorePlantCtx` | `(0,v,z) :: M.dropLast ∈ GX`（植え付き接頭辞 peel）|
| 文脈断片 | `CoreCtxSuffix` | `shiftl0 (entry M 0 p) (seg M p (|M|-1-p)) ∈ GX`（再基底化接尾辞）|
| 文脈断片 | `CoreBlocked0` | p=0 の根スライス（単列文脈 = shift 形）|
| リフト | `CoreLift` | `y ∈ GX → Lift1 y t ∈ GX` |
| リフト | `CoreBlockedEltHi` | srow=2 ブロッカーのガード付きコピー |

すなわち **「文脈の断片が GX に入る」+「GX がリフトで閉じる」** の 2 種類
だけ。前者は MASTER 長さ帰納（`mem_of_Aclosed_aux`）/ 文脈クラス 𝒞 の仕事、
後者が (e)-壁の最終形（§1.9.13）。

## 1.9.15 ★ plift の構造（probe_pliftseg, 2026-08-05）— 分解の底は「植えた根」

**却下**: 「plift = 部分木ごとの一様行1シフト」は**偽**
（`probe_pliftseg`: run が部分木にならない 38608/52428、
子孫閉性の違反 5824）。マスクは行1値で細かく交錯する
（例 `D=[(0,1,0),(1,0,0),(2,1,0)]`, v=0: 列2は entry1=1>0 だが
le1-親が列1（entry1=0）なので錐外）。⟹ 値ベースのマスク言語の 7 度目の反証。

**しかしマスクは graft 分解に沿って再帰的**: 低い列（entry1 ≤ v）にぶら下がる
部分木は丸ごとマスク外、高い列にぶら下がる部分木のマスクはその部分木自身の
coneV。したがって `gx_graft` + 部分木分解でブロックを削っていくと、
**底は単列ブロック `[(0,v,z)]`（植えた根）**になる。

`om_Aop`（v0.117, Lean 済み）: 植えた根の `Aop` は節3であり、そのデータ段は
`2v+z-1` — **根のレベルより厳密に低い**。したがって:

> すべての残差（文脈断片・plift・リフト）は最終的に
> **「一段下の `W σ` が `GX` に入る」** に集約される。

これは旧・自己参照（段 `m+2t` で**増加**）と違い**降下**している。残る問題は
「どの帰納パラメータでこの降下を回すか」: GX が ∀(v,z,t,a) を含むため、
段の降下と要素の生成降下が直積になっていない（∀根レベルが素朴な段帰納を
壊す）。次の設計課題はこの整礎化のパラメータ選び。

## 1.9.16 ★★ 2 つの決定的 probe（2026-08-05 深夜4）

**(A) TbOper は成立**（`probe_tboper`, 0/11304）: 主ブロック
`N = (0,v,z)::R` の最小 tbAll 境界 `u0(N)`（接頭辞の孤児レベルの上限）は
**展開で増えない**（n=1,2,3）。かつて tbAll を捨てた理由（TbOper が未証明）
は解消できる見込み。⟹ tbAll 簿記は「使える資産」。

**(B) しかし natDom 復活ルートは (c) 枝で反証**（`probe_deadgraft`）:
死んだサイトで clause 3 を使うには
`graft (Lift1 N t) w = Lift1 (graft N w) t`（**リフト後の graft**）が必要だが、
**違反 9377004/26740030**（レベル制限 `lev w ≤ m` に絞っても 247734/2083496）。
最小反例 `N=[(0,0,0),(1,0,1)]`, t=1, w=[(0,1,0)]:
接ぎ木した w の列が**リフト後は錐外・リフト前は錐内**になるため。
⟹ §1.9.13 の「natDom を戻しても壁が (c) に移るだけ」が**測定で確定**。

**帰結**: 残る道は
1. 新しい義務言語（既存の自然な候補はすべて反証: 値マスク／整列リフト／
   部分木一様シフト／リフト後 graft）
2. 文脈クラス 𝒞 パラメータ化（残差の再配置。壁自体は残る）
3. 段の funnel（§1.9.15）の整礎化 — `GX` の ∀(根レベル, 段) が
   素朴な帰納を壊すので、**根レベルと段を結びつける新しい指標**が要る。

## 1.9.17 ★★★ 整列リフト計算則（probe_alignedsite: 0/191880）— 次期設計の核

**塔サイト + 整列データ**でリフトは閉じた計算則をもつ:

```
  Lift1 (graft E (Lift1 X d0)) d = graft (Lift1 E d) (Lift1 X (d0 (+) d))
  d0 (+) d := if d0 = 0 then 0 else d0 + d
```
- `E = (0,v,z) :: R` が塔サイト（根が末尾孤児を復活させる）
- `X` は **整列した主ブロック**: X = [] または `X = (0,v,z) :: T` かつ
  **`argOK T`（T の全列が深さ ≥ 1、すなわち X は単一木）**

⚠ **自己監査による訂正（必読）**: 当初「整列」だけで成立と書いたが、
X が**森**（深さ0の列を2つ以上もつ）の場合は**破れる**
（`probe_alignedforest`: tower1/aligned/d0=0 で 30448/93024 違反。
最小反例 `X=[(0,0,0),(0,1,0)]`, v=0, R=[(1,1,0)]: 第2成分の根は
entry1=1>v なので ambient 根に復活させられ錐に入る）。
機械がリフトする対象（塔要素・植えた peel）は**すべて主ブロック**
（根の後ろは graft の像で深さ ≥ 1）なので、この条件は自動的に満たされる。

測定（`probe_alignedsite`）:

| クラス | 件数 | 違反 |
|---|---|---|
| tower1 / aligned / d0=0 | 42432 | **0** |
| tower1 / aligned / d0>0 | 84864 | **0** |
| tower2 / aligned / d0=0 | 21528 | **0** |
| tower2 / aligned / d0>0 | 43056 | **0** |
| tower1 / 非整列 | 128928 | 85792 |
| tower2 / 非整列 | 65412 | 43532 |

**整列がちょうど正しい条件**（非整列は d0=0 で 100% 違反）。塔サイト条件も
必須（サイトを外すと整列 d0>0 でも 15% 違反 — `probe_alignedcalc`）。
**単一木条件も必須**（森にすると 33% 違反 — `probe_alignedforest`）。

**意味**: 機械がリフトする対象は**すべて ambient 根に植えたブロック**
（塔要素・植えた peel）であり、それらは整列している。したがって
「要素リフトを内在化した整列言語」を作れば、複合リフトは
リフトパラメータの加算に吸収され、**リフト残差が言語内部で閉じる**。
Aop 由来の一般データ（非整列）は `GX_full` 経由でしか使われず、
要素リフトを要求しない ⟹ 2 つの述語（一般 GX と整列 GXt）の分業でよい。

**次期設計 (v0.118 目標)**:
`GXt := {y | based y, 根 = (0,v,z) → ∀ M 装備済み, ∀ d i a t,
  2(v+t)+z ≤ a → Lift1 ((0,v,z) :: graft M (Lift1 (y.take i) d)) t ∈ W a}`
- リフト閉包が定義から自明（`Lift1_Lift1` + 上の計算則）
- `tow_mem_GX` を GXt 版に（塔要素は整列 ✓）
- α/β の核が「整列植えブロック ∈ GXt」に統一され、リフト残差が消える見込み

## 1.9.18 ★★★★ 接ぎ木リフト計算則を Lean 化（v0.118, Cgraft.lean）— 一般形は**環境マスク**

§1.9.17 の「整列リフト計算則」を精密化して Lean 化した。自己監査で 2 度の
訂正が入った（どちらも probe で捕捉）:

1. **ガードは「引数の根が `v` より上」ではない**（probe_lowcalc: 7814/102572
   違反）。文脈 `R` の途中の低い列が行 1 の親を横取りするので、正しいガードは
   **接ぎ木点そのものの錐所属**。修正版は 0/241816（probe_calc2）。
2. **単一木の仮定は落とせる**。落とすと結論はリフトではなく**環境マスク
   リフト**になる（probe_maskcalc: 0/200000。マスクが引数自身の錐と食い違う例が
   131887/200000 ある = 真に一般な形）。

### Lean 資産（`Cgraft.lean`, sorry 0, build 緑 598 jobs）

```
coneV A v j   := j の行 0 祖先（自身含む）がすべて行 1 で v を超える
SiteHigh E    := 接ぎ木点の**手前の**行 0 祖先がすべて根より行 1 で高い
mlift A v d   := coneV A v の上だけ行 1 を d 持ち上げる
HighPar A v   := 根以外の行 1 孤児は行 1 で v 以下

cone_graft_mask : le1 (graft E A) 0 (|E|-1+j) ↔ SiteHigh E ∧ coneV A (entry E 1 0) j
lift_graft_mask : Lift1 (graft E A) d
                    = graft (Lift1 E d) (if SiteHigh E then mlift A (entry E 1 0) d else A)
cone_graft_high : （HighPar 版）le1 (graft E A) 0 (|E|-1+j)
                    ↔ le1 (graft E A) 0 (|E|-1) ∧ le1 A 0 j
lift_graft_cone : Lift1 (graft E A) d
                    = graft (Lift1 E d) (if 接ぎ木点が錐 then Lift1 A d else A)
```
補助: `highPar_of_shallow`（単一木は自動で HighPar）、`highPar_Lift1`、
`exists_root_anc`、`rtg0_graft_split` / `rtg0_graft_join`（行 0 祖先鎖の分解）、
`nextrel0_graft_site`（接ぎ木点への一歩 = 引数の任意の深さ 0 列への一歩）、
`lift_graft_of_entries`（組み立て）、成分補題一式。

### 帰結: α / β の残差がきれいに割れる

- **β**: 塔ステップは `Nb⟦i+1⟧ = graft Nb (Lift1 (Nb⟦i⟧) d1)` で、引数は
  植えたブロック（単一木 ⟹ `highPar_of_shallow` + `highPar_Lift1`）、接ぎ木点は
  `nextrel2 Nb 0 last` が含む `le1` で錐の中。⟹ `lift_graft_cone` がそのまま効き、
  塔要素は閉じた形をもつ（`d0 ⊕ d` 則）。**β のリフト残差は消える見込み**。
- **α**: 機械の義務そのものが `Lift1 ((0,v,z) :: graft M Y) t`。`lift_graft_mask` で
  ```
      Lift1 ((0,v,z) :: graft M Y) t
        = graft (Lift1 ((0,v,z) :: M) t) (mlift Y v t)      （SiteHigh のとき）
  ```
  すなわち **α の残差は 2 つに割れる**:
  - (α1) **リフトした植え文脈** `Lift1 ((0,v,z)::M) t ∈ GX` — データを含まない
    純粋な文脈側の言明（CorePlantCtx + リフト）。
  - (α2) **データのマスクリフト** `mlift Y v t ∈ GX`（`Y ∈ GX`）。
  これが (e)-壁の**最終形**であり、`CoreLift`（`Lift1 y t ∈ GX`）が偽/届かない
  理由も同時に説明する: 一般のデータでは複合の錐は `Y` 自身の錐ではなく
  `coneV Y v` だから（probe_liftplant の反証の正体）。

### なぜ mlift なら閉じ得るか（probe_mliftgraft: 0/200000）

`Lift1` はブロックごとに閾値を根の行 1 値へ**リセット**する。だから
「接ぎ木の内側でリフトする」が言語の外に出る（§1.9.13 の壁）。
`mlift` は閾値 `v` が**定数**で、接ぎ木に分配する:

```
  (D)  mlift (graft M y) v d = graft (mlift M v d) (if SiteV M v then mlift y v d else y)
       SiteV M v := M の末尾列の行 0 祖先（末尾自身を除く）がすべて行 1 で v より上
```

つまり機械の接ぎ木義務は**同じ `v`** のマスクリフトで安定。`Lift1` にできな
かったことがちょうどできる。⟹ **次期設計: 義務言語を `mlift` でパラメータ化**
（`Lift1` は「整列データに対する mlift の特殊形」ではないので、β 用の
`lift_graft_cone` と併用する 2 パラメータ設計になる）。

## 1.9.13 ★ 壁の同定: 「リフト後 graft」言語の非閉性（2026-08-05 深夜）

残る核（`CoreLift` / `CoreLiftPlant` / `CoreBlockedEltHi`）はすべて
**「リフトを graft の内側に持ち込む」**操作であり、機械の義務言語
`Lift1 ((0,v,z) :: graft M y) t`（= graft の**後**にリフト）は
この操作で閉じていない。probe（§1.9.11）が示すとおり複合リフトは
引数に coneV マスクで作用し、要素自身の `Lift1` とは一致しない。

**W 階層の再設計（節2に natDom を戻す）で α だけは解けるが割に合わない**:
- yapss（PSS）では clause 2 が `natDom M ∧ ∀n M⟦n⟧ ∈ X` なので、
  塔サイトのデータは必ず clause 3 になり `hgr`（graft 閉包）が付いてくる。
  trio が natDom を落としたのは「死んだ行2孤児はレベル無制限」だから。
- 旧設計（memory v0.85 系）の "clause 4"（`(∃m, domT M m) ∧ 節2`）は
  **srow=2 の孤児でしか発火しない**（srow≤1 の死 ⟹ w1 ≤ v ⟹ m < a）。
  したがって節2を `natDom ∨ srow=2` に絞れば **α のデータは必ず clause 3**
  になり CoreT1L は `hgr` で閉じる。
- ⚠ 代償: (c) 枝（死んだ srow≤1 孤児の peel）が clause 3 を使うことになり、
  そこで `graft (Lift1 X t) w`（= **リフト後に graft**）の義務が必要になる。
  これは同じ非閉性そのもの。⟹ **正味の利得なし**（α の壁が (c) に移るだけ）。

⟹ 突破口は「義務言語の拡張」しかない。候補:
1. 2 パラメータ言語 `Lift1 ((0,v,z) :: graft M (plift v s y)) t`
   （plift は ambient マスク; `plift v s ∘ plift v t = plift v (s+t)` は
   probe 済み 0/2313）。**閉包性は取れるが**、機械の β 族要素
   `Lift1 (Nb⟦j⟧) d1` は整列ブロック（根 entry1 = v）なので
   `coneV = ∅` すなわち plift では表せない（要素の錐リフトと ambient
   マスクリフトは別物）— 両方を持つ言語が要る。
2. 文脈クラス 𝒞 のパラメータ化 + 断片 ∈ GX𝒞（負の出現を回避）で
   文脈側だけ先に閉じ、リフト核を最小形に絞る。
3. MASTER 長さ帰納（`mem_of_Aclosed_aux`）を Wstar2/GX に配線して
   文脈断片を供給し、リフト核だけを残す。

## 1.9.8 ★ α の残差解析（v0.109-110）— 整列供給 ✓ / 非整列 = (e)-壁の最終形
（→ 1.9.9 で解決済み。以下は経緯の記録）

- `coreT1L_of_le`（v0.109）: **CoreT1L ⟸ (∀σ W σ ⊆ GX) + CtxLiftT1**
  （リフト済み複合文脈 Rt = ltail v z (graft M Y) t の装備だけが残る）。
  `GX_loop`: 機械の閉包全体が CoreBlocked + CtxLiftT1 + 自身の包含のみを
  消費する形で一本化。
- 資産（v0.110, probe 0 違反→Lean 化）: `Lift1_Lift1`（リフト合成、錐は
  リフト不変）、`ltail_take`（錐は接頭辞局所的）。
- **整列インスタンス**（v' = v+t, z' = z）の CtxOK Rt は完全供給できる:
  Rt.take k = ltail v z (R.take k) t（ltail_take）→ lift_cons⁻¹ +
  Lift1_Lift1 で Lift1 ((0,v,z)::R.take k) (t+t') に潰れ、
  k < |M| は CtxOK M、k ≥ |M| は datum の接頭辞義務（v0.107）で供給 ✓。
  制約 2(v+(t+t'))+z ≤ a' は要求とちょうど一致。
- **残差 = 非整列ルート (v',z') ≠ (v+t,z) × リフト済み本体**のパッケージ。
  ⚠ 却下済み 6 変種（§5, 値ベース/マスク言語）に隣接 — 再挑戦は形を変えて。
- **リード（第7の設計・未検証）: 義務量化子のスライス化**。実消費は常に
  「その機械インスタンスの ambient (v,z)」スライス + ∀(a,t) のみ:
  towerGraft2_lift_fam は hgrF を同一 (v,z) でしか呼ばない、hctx も
  ambient のみ、(v,z) の流れは α-サイトの v → v+t（単調増加）だけ。
  GX/Wstar2/CtxOK の ∀v'z' を「初期 (v0,z0) から到達可能なスライス」に
  狭めれば非整列要求は消える可能性。probe 済みの消費規律
  （t は常に d1-値、族は (v,z)-スライスのみ）が根拠。次の設計検討課題。

## 1.12 ★★ provenance probe（probe_strat.py, 2026-08-05）— β の測度の実体

タグ付き walk（初期列に位置タグ、タワー生成列に fresh タグ; expand は
S[:r] + 窓コピー×n で位置的に伝播）:
- **t2-サイトの孤児は 5235/5235 全て初期文脈列（のコピー）** —
  タワー生成列（族要素・塔本体・E-リフト）が β-孤児になることは**皆無**。
- **孤児の初期位置は t2-鎖に沿って非増加**（up 0 / eq 736 / dn 1499）。
- **m-eq 対は 414/414 同一初期列**（別列同レベル 0）— eq = 同じ列の
  コピーの再遭遇（∀M-内在化で吸収する型）。
- **t1-サイトの孤児は 3415/3415 全てタワー生成列**（文脈列 0）—
  α の孤児は常に機械が植えた根 (0,v°,z°)、レベル 2v°+z° は生成サイトの
  段で有界 → α 測度（v-ヘッドルーム）と直結。
- 帰結: β は「トップブロックの列材だけを上から順に消費する」大域構造
  （heartwood 型）。fresh 素材に降りないので、測度は文脈列の
  (位置, コピー多重度) 側に住む。同位置再燃（eq）の Lean 側吸収は
  ∀M-内在化（同一 A2 の別文脈インスタンス）が既に用意されている。

## 1.10 塔鎖の遷移行列（probe_walk8, 2514 鎖 / 5650 対）— β の測度データ

連続する塔サイト間の孤児レベル m の遷移:

| 遷移 | down | eq | up |
|---|---|---|---|
| t2 → t2（純 β 鎖）| 1499 | 287 | **0** |
| t2 → t1 | **2430** | 0 | 0 |
| t1 → t1 | 0 | 529 | 456 |
| t1 → t2 | 0 | 0 | 449 |

**m が増えるのは t1（E-リフト）経由のみ** — 増分は正確に α 機構
（m + 2t、E-測度 = v-ヘッドルーム厳密減少で有界）。純 β 鎖は m 非増加
（84% で厳密減少）。合成測度候補: lex (E-予算 [α 検証済], m [β], t2-eq の
タイブレーク [open — 候補: 文脈深さの層化 = Buchholz 2.4a→2.5 の層構造の
一般化、または外側 A2 の要素降下に入れ子 A2 を埋め込む])。
t2-eq 連は短い（長さ2: 259, 長さ3: 14）。タイブレーク候補「ブロック長」は
285/287 で降下するが**反例 2 件**（(m=2,len=11)→(m=2,len=17) と len=5→5、
B2a 展開の膨張による）— 生の長さは測度ではない。残る eq-t2 残差は、
スパウンの要素が外側 A2 の要素降下で被覆されるか構造検査が必要。

## 1.11 β の最終整理（2026-08-05 深夜2）

* **同段スパウン（eq-t2）は測度不要**: GX は ∀M（全装備文脈）を内在化して
  いるので、同段の「新しい塔閉包」は同じ A2 の別 M-インスタンス + `W_mono`。
  条件は CtxOK 合成（1.9）だけ。例外 2 件（長さ増加）もこの吸収で消える見込み
  （スパウンではなく同一 A2 内の文脈パラメータ替え）。
* **m-ジャンプ（m_G > u）は実測 0**（t2→t2 の up = 0/1786）。これは
  「W m の要素の孤児レベル ≤ m」という **tbAll 型不変量の実測**。
  この不変量が成れば CoreT2E の段ジャンプは空虚になり、残るのは
  境界ケース（孤児レベル = 段、clause-3 の m < u が破れる）のみ —
  それは同段吸収で処理。⟹ **β = tbAll-不変量 + CtxOK 合成に還元**。
* tbAll-不変量の形: 機械が実際に W σ に置く要素は全て構成的
  （塔要素・展開・graft）— 各構成が孤児レベル ≤ σ を保つことを検査
  （towerGraft2_lift の key は 2(v+s)+z ≤ m で構成 ✓; 検査対象は
  W-クラスの一般要素ではなく**機械が構成する要素**に限定できるか、
  つまり hgr-インターフェースを「∀ w ∈ W m」から
  「∀ w constructed-with-orphan-bound m」に狭められるかが焦点）。

## 2. probe 済み事実（違反 0 のもの）

- (e)-サイトで `ltail v z (graft S Y) t = graft S↑ (liftset Y (coneV Y v) t)`、
  `coneV Y v = {j | Y 内の全 le1 祖先 i が entry Y 1 i > v}`（0/42498）。
- 行1塔リフト族は `F(R,v,z,t,k) := tow (v+t) z (ltail v z R t) k` と既存関数で
  表現できる（位置データは k のみ）。値ベースのマスクは不可能
  （同一列値で異なる扱いの反例 = マスクは位置的）。
- E-スパウン鎖に沿って **v+t と孤児添字 w1 が厳密増加**（0 違反）。
  v はどの枝でも非減少。→ 装置 α の測度。
- 消費されるリフト t は常に包絡行2塔の d1（`towerGraft2_lift` の key は
  s ∈ {0, d1} しか消費しない）。
- fs はトップレベル和では分解する（UBI ブロッカーは部分木接ぎのみ）。

## 3. 残る 3 装置

### α (e)-枝: E-スパウンの整礎化
E-還元: 義務 `Lift1 ((0,v,z)::B) t`（t>0）は `(0,v+t,z)::ltail v z B t` の
t=0 義務に等しい（`lift_cons`）。残る消費は「リフト済み文脈の graft 閉包
@ 段 m_Y + 2t」= GA の新インスタンス。測度候補: **(A2 段 u, u − 2v)-lex**
— E は同段で v を +t (≥1)、clause-3 塔は段を m_Y < u に厳密降下。
リスク: E の段 m_Y + 2t が u を超える場合の第一成分の増加。
対策候補: 義務言語に根値キャップを入れ、v の予算で第二成分を先に整礎化。

### β (f)-枝: clause-2 死孤児復活塔
孤児レベル m' は u と無関係（W 0 に孤児レベル 201 の例あり）。
Buchholz 双対: dom(b) = {0} の後続塔 = X̄（連接閉包, 2.5 case 4）。
鍵観察: `graft Y w = Y.dropLast ++ shift w` で Y.dropLast は clause-2 データ
そのもの。srow≤1 なら X̄-型（連接 + 行0シフト）で、srow=2 は d1-リフト付き
（∀s-key 必要）。X̄-trio の閉包はブロッカー (γ) と連動。

### γ (g)-枝: UBI ブロッカー — **文脈長降下で処理**（2026-08-05 確定方針）
walk 計装の結果: 接ぎ木直後のブロックは 0/8650、遅延越境（y-領域が
部分的に剥がれた後）は 1235 件で全て B2a 型・srow ≤ 1（消費データ上
srow=2 は 0）。**鍵**: ブロック済み展開の bad root p は文脈接頭辞内
(p < 境界) にあり、展開後の新文脈 = take p は**厳密に短い** →
γ の再帰は (|文脈|, 要素構造)-lex で整礎。処理形: 展開 = take p ++
(文脈接尾辞 ++ shift(y-残基)) のコピー列 = X̄-連接形（β と共通装置）。
srow=2 の遅延越境も同じ降下で処理できる見込み（d1' > 0 なら glift/Gtrans
資産でコピーを扱う）→ その場合 δ は不要。
**簡約**: ブロック済みケースは外側ブロック (0,v,z)::graft S Y の B2a
そのものなので `liftInner_holds`（証明済み）が適用でき、義務は
∀n: (graft S Y)⟦n⟧ の (v,z,t)-義務に還元される。残る仕事 =
展開ブロック take p ++ copies の義務導出（文脈長降下 + 分解）。
注意: copies の graft-提示は一般に不可（p の列は lev 0 があり得るので
新文脈が domT を満たさない）— 提示は `mem_of_Aclosed_aux` 型の
split_lastMin（d0'=0 なら最終コピー根が last minimum になり P = 1 コピー分）
を検討。rsum は A-部で一般に破れるため XA_closed の直接適用は不可。

#### 旧 δ 案の測定結果（参考）
単純レベルキャップ `ytr ≤ m_ctx` は消費対で反証（超過最大 +10）。
成立していた関係: t2-プラグでは常に y_r1 ≥ ctx_r1（<は 0 件）。

#### （旧記述）
Y の尾部が S.dropLast の列に復活するケース。⚠ srow=2 の空性は
**`maxlev Y ≤ m` の下でのみ**成立（probe_ga3: 無制約では srow=2 blocker
10961 件）。同様に srow≤1 の場合の解析も尾部レベル制約に依存する見込み。
→ **装置 δ（キャップ簿記）が前提**: 機械の要素にレベル制約
（`lev(trailing) ≤ m` / tbAll 型）を復活させる。かつて `W*` から除去した
tbAll はここで必要だった可能性が高い。キャップが閉包で保存されるか
（clause-2 の ∀n コピーは行1を +k*d1 する — 尾部は上がるか？）を先に probe。
srow(S-orphan)=1 の場合の空性証明スケッチ（キャップ仮説付き）:
死性 → 孤児の row-0 祖先は r1 ≥ r1(orphan); 越境 le1-辺の親 p' は
その祖先集合内; 一方 c の le1-祖先は r1 < r1(c) ≤ (m-1)/2 < r1(orphan) — 矛盾。
⚠⚠ さらに: 機械が実際に消費する塔要素自体が大きな尾部レベルを持ち得る
（R = [(1,50,0),(2,1,1)] の tow 1 = (0,v,z)::R.dropLast は尾部 lev 100 > m=2）。
よって γ は「ブロッカー空性」では済まず**ブロック済み展開の処理**が必要:
(graft S Y)⟦n⟧ ≠ graft S (Y⟦n⟧)（ミラー破れ）のとき、展開は
S.dropLast の接尾辞 ++ shift Y にまたがるコピー。処理候補: 文脈 S に
自身の Aop データ/Wstar2-導出を持たせ（CTX を「装備付き文脈」にする）、
ブロック済み展開を S-側データと Y-側データの合成として導出する。

## 4. 実行順序（v0.114 改訂）

1. ✅ β 族化 → 単一ステップ核 → 装備合成（§1.9.5–1.9.6）
2. ✅ スライス装備で α 残差消滅（§1.9.9）
3. ✅ **接ぎ木閉包で自己参照消滅**（§1.9.10, v0.114）
4. γ' を新形に還元（`gcopies = graft E (gcopies n)` の Lean 化 →
   CoreBlockedElt ⟸ Msuf.dropLast ∈ GX、CoreBlocked0 は p=0 の shift 形）
5. **文脈クラス 𝒞 のパラメータ化**（GX を 𝒞 で添字づけ、核の仮定を
   「𝒞 の断片が GX𝒞 に入る」に統一）
6. `CoreLift`（GX のリフト閉包）: 唯一残るリフト言語。ここだけは
   probe 先行（既存 6 変種の反証を踏まえた形の探索）
7. 𝒞 の構成 = `mem_of_Aclosed_aux` の Wstar2/GX への再配線 + Final.lean 差し替え

## 5. 却下済み経路（再挑戦禁止; 詳細は memory）

- 弱錐 S2 / 閾値・混成マスク（S3-S6）: B2a か tower2 が壊れる
- 項側 Buchholz-W ピボット: W₀ はゲーム木 wf であり olt-wf でない;
  橋渡しの BM-fs シミュレーションはリフトと同内容
- `Aop` 節3の全段閉包化: 段再帰の整礎性が壊れる
- 値ベース要素リフト言語（LiftVc*/origin-mask/TLift 脊柱型): 位置性で全滅
- GA の素朴な A2（キャップなし）: 段 m_Y+2t の幾何的成長
