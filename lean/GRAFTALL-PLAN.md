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

## 1.9.19 ★★★★★ 階段リフト `glift` — (e)-壁を溶かす閉じた言語（2026-08-05 深夜5）

`mlift` の閾値族は入れ子で、しかも**一つの数値でパラメータ化される**:

```
  mu A j := j の行 0 祖先鎖（j 自身を含む）の行 1 値の最小値
  coneV A v = { j | mu A j > v }
```

したがって `mlift A v s` は「`mu > v` の列を `s` 上げる」であり、マスクリフトの
合成は**階段関数**になる:

```
  phi(m) = m + Σ_i s_i · [m > v_i]          （有限個の (v_i, s_i)）
  glift A phi := 各列 j を  phi(mu A j) - mu A j  だけ行 1 で上げる
```

`phi(m) - m` が単調非減少という条件で閉じており、`mlift A v s` は
`phi = (m ↦ m + s·[m > v])` の場合。**この階段クラスは合成で閉じる**。

### 測定（tools/probe_glift.py / probe_glift2.py, 計 100000 サンプル、いずれも違反 0）

| 法則 | 内容 | 違反 |
|---|---|---|
| (G6) | `mu (glift A phi) j = phi (mu A j)` | 0 |
| (G5) | `glift (glift A phi1) phi2 = glift A (phi2 ∘ phi1)` | 0 |
| (G2) | **`glift (A⟦n⟧) phi = (glift A phi)⟦n⟧`（展開と可換、無条件）** | 0 |
| (G3) | `glift (graft M y) phi = graft (glift M phi) (y を mu を文脈で cap して glift)` | 0 |

`Lift1` が条件付きでしか展開と可換でなかった理由も同時に説明される:
`Lift1 ((0,v,z)::R) t` は根（`mu = v`）まで上げるので `glift` ではない。
尾部だけ見れば `glift R (m ↦ m + t·[m > v])` に一致する
（`lift_cons_eq_mlift`, Lean 済み）。

### (G3) の cap は階段のまま

接ぎ木した引数の側では `mu_composite(j) = min (mu_y j) c`（`c` = 接ぎ木点の
文脈祖先の行 1 最小値）なので、引数に効くのは
`psi(m) := m + (phi(min(m,c)) - min(m,c))`。`phi(x)-x` が単調なら
`psi(m)-m` も単調 ⟹ **`psi` も階段**。したがって接ぎ木再帰の中で言語が閉じる。

### 帰結: 義務言語を `glift` でパラメータ化すれば (e)-壁は消える

機械の義務は `Lift1 ((0,v,z) :: graft M y) t ∈ W a`。マスク表示（Lean 済み
`lift_plant_graft`）で

```
   = (0, v+t, z) :: graft (mlift M v t) (mlift y v t)
```

なので、**要素側のパラメータを階段 `phi` として内在化した集合**

```
  GXg := { y | ∀ phi 階段, ∀ 装備文脈 M, ∀ (v,z), ∀ i, ∀ a,
             (0, phi v, z) :: graft (glift M phi) (glift (y.take i) phi) ∈ W a }
```

を取れば
- **リフト閉包は定義から自明**（`glift y phi ∈ GXg` は `phi' ∘ phi` を取るだけ; (G5)）
- **接ぎ木閉包は (G3)** で cap 付き階段に落ちる
- **Aop の輸送は (G2)**（展開と可換なので節2がそのまま移る）

⟹ `CoreLift` / `CoreMaskLift` / `CoreLiftPlant` が**すべて消える**見込み。
残るのは文脈側（`CorePlantCtxLift` / `CoreCtxSuffix` / `CoreBlocked0`）と
γ' の `CoreBlockedEltHi`。

**次期作業 (v0.119)**: `glift` の Lean 化（`mu`・階段の型・(G6)/(G5)/(G2)/(G3)）
→ `GXg` 定義 → `gxg_graft` / `gxg_glift` → α/β の再配線。

## 1.9.20 ✅ v0.118.5-7: 階段言語の Lean 化（残るは展開との可換性 (G2) だけ）

`Cgraft.lean`（1350 行, sorry 0, build 緑 780 jobs）に階段言語一式:

```
amin A j        行 0 祖先鎖（自身含む）の行 1 最小値   coneV_iff_amin: coneV A v j ↔ v < amin A j
Stair φ         φ m ≥ m ∧ (φ m - m 単調) ∧ φ 0 = 0     stair_step / stair_comp / stair_cap
slift A φ       列 j を φ (amin A j) - amin A j 上げる  mlift_eq_slift
amin_slift      (G6) amin (slift A φ) j = φ (amin A j)
slift_slift     (G5) 合成則
amin_graft_low / amin_graft_high_eq / capV / slift_graft   (G3) 接ぎ木分配（cap 付き）
```

**構造保存（(G2) の心臓部）も済み**:
```
amin_min_below_parent : 祖先鎖の最小値は行 1 の親 j0 の側で達成される
amin_parent / amin_between / amin_le1 : 親・間の祖先・行 1 祖先鎖は同じ amin
  ⟹ 行 1 の親子判定はすべて「同じ定数シフト」の下で行われる
nextrel1_slift / le1_slift / nextrel2_slift / nextR_slift
hasParent_slift / parent_slift / srow_slift / entry1_slift_pos
```
逆向きは `stair_strictMono`（階段は狭義単調）→ `stair_inj` で持ち上げ側の
`amin_parent` を降ろす。**`Stair` に `φ 0 = 0` が必要**（行 1 = 0 の列が動くと
`srow` が変わる）— マスク生成の階段は自動的に満たす。

### 残る一点: `amin` のコピー周期性

(G2) `slift (A⟦n⟧) φ = (slift A φ)⟦n⟧` は、分岐データ（`j1, i1, j0, d0, d1`）が
すべて保存される（`d1` は `amin_le1`）ので、次の一点に還元される:

```
   amin (A⟦n⟧) idx = amin A (idx のコピー元)     （接頭辞では idx 自身）
```

すなわち**展開のコピー列は元の列と同じ `amin` をもつ**。測定済み
（tools/probe_aminexp.py, 21693 展開）:

| | 内容 | 違反 |
|---|---|---|
| (A1) | `amin (S⟦n⟧) i = amin S i`（接頭辞 `i < r`） | 0 |
| (A2) | `amin (S⟦n⟧) (r + a*L + xx) = amin S (r + xx)`（コピー） | 0 |

`L = x - r`。(A1) は `(S⟦n⟧).take r = S.take r` と鎖の接頭辞局所性で軽い。
(A2) は行 0 の鎖の反転（`Lcone.gexp_flat_chain_inversion` / `Gtrans` の
`gexp_chain_inversion`）が道具 — コピー内の鏡像は行 0 で同型、コピーの根から
先は前のコピー→接頭辞へ降り、最小値は接頭辞側（`amin S r` 以下）で達成される
ので `k` に依存しない。これが済めば (G2) が出て `GXg`（§1.9.19）に進める。

Lean 側で `oper` は
```
  M.take j0 ++ (range n).flatMap fun k => (range' j0 (j1-j0)).map fun j =>
    (entry M 0 j + (if le0 M j0 j then k*d0 else 0),
     entry M 1 j + (if le1 M j0 j then k*d1 else 0), entry M 2 j)
```
なので、分岐データの保存（`srow_slift` / `hasParent_slift` / `parent_slift` /
`entry1_slift_pos` / `d1` は `amin_le1`）とガードの保存（`le0` は行 0 不変、
`le1` は `le1_slift`）はすでに Lean 済み。残るのは (A1)(A2) だけ。

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

## 1.9.21 ✅ v0.118.11-13: (A2)/(G2) 完成 → **β からマスク核が消えた**

### 済み

| | 内容 | 場所 |
|---|---|---|
| (A2) | `amin (M⟦n⟧) (j0+(k*Lb+q)) = amin M (j0+q)` | `Aexp.amin_oper_mir` |
| (G2) | `slift (A⟦n⟧) φ = (slift A φ)⟦n⟧`（**無条件**） | `Aexp.slift_oper` |
| (ML) | `mlift (Lift1 ((0,v,z)::R) d) v e = Lift1 ((0,v,z)::R) (d+e)`（`0<d`） | `Aexp.mlift_Lift1_cons` |

(A2) は `Lcone` の錐輸送 `gexp_cone_mir` / `gexp_cone_mir_flat` の**閾値版**
（根 `0` を経由しないので `hj0`・`hr0` が不要）。2 相の分岐は `srow`:
`i1 ≥ 1` は上昇コピー（`gexp_chain_inversion` + 側条件 `amin M j0 ≤ amin M j1`
= `le1 M j0 j1` から `amin_le1`）、`i1 = 0` は同一コピー（`gexp_flat_*`)。
side condition `hrow1` は `i1=0` では偽（probe 4387/5967）なので相分けが必須。

これで階段言語 (G2)(G3)(G5)(G6) が揃った。

### ★ (ML) が β のマスク核を消した

塔の帰納で使うデータは**任意の GX 元ではなく、前段の根リフト**
`Lift1 (Nb⟦i⟧) d1` である。`Lift1 X d` は根の錐をちょうど `d` 上げるので
`d>0` なら「`Lift1 X d` の閾値 `v` の環境マスク＝`X` の根の錐」
(`coneV_Lift1_cons`)、したがって

    mlift (Lift1 X d) v e = Lift1 X (d + e)

塔の帰納を `∀ j s, Lift1 (Nb⟦j⟧) (d1+s) ∈ GX` に強めれば、`s`-リフトの
マスクは `d1+s` の根リフトに吸収されて IH で閉じる。結果

    coreT2EFam_of_plantctx : CorePlantCtxLift → CoreT2EFam

**β は `CoreMaskLift` を一切使わない**。ついでに `CoreT2EFam` / `CoreT2E` の
仮定は `Y.dropLast ∈ GX` に弱めた（節 2 は他で使っていなかった）。

### α はまだマスク核（`GXg` は Aop 節3 で壁）

α (`CoreT1L`) が要るのは `Lift1 ((0,v,z) :: graft M Y↓) t ∈ GX`。データ
`Y↓ = Y.dropLast` は塔の元ではない**任意の GX 元**なので (ML) は効かない。

§1.9.19 の `GXg`（義務言語を階段でパラメータ化）で `CoreMaskLift` を定義から
自明にする案には**未検討の壁**がある: `Aop W u GXg Y → Y ∈ GXg` を示すには
`slift Y φ` の `Aop` が要るが、

- 節1（短い）: `lev` は保存 ✅
- 節2（展開）: (G2) でそのまま移る ✅
- 節3（塔データ）: `domT (slift Y φ) m'` の `m' = m + 2δ` は**元より高い段**。
  `W m` のデータからは `W m'` のデータが作れない ❌

ただし節3 の `Y` は `¬hasParent`（`domT` の第 2 成分）なので `|Y| ≥ 2` なら
`Y⟦n⟧ = Y.dropLast` となり**節2 に落ちる**。残る唯一の穴は
**`|Y| = 1`（植えた根 `[(0,b,c)]`、`om_Aop`）**: マスクリフトは根のレベルを
`2b+c → 2(b+t)+c` に上げるので、必要な段が上がる。
「α-orphans = planted roots, stage-bounded」（`GX_loop` の docstring）と同じ壁。

**次の一手（v0.119 候補）**:
1. `GXm := {y | y ∈ GX ∧ ∀ v t, mlift y v t ∈ GX}` を機械の集合にし、
   節3 を「`¬hasParent` ⟹ 節2」で潰す。残るのは植えた根の単元だけなので、
   マスタ帰納（段について）に `∀ w ∈ W m, based w → w ∈ GX` を**全段**で
   持たせられるかを検討する（`Wf` の段再帰との整合が要点）。
2. あるいは α を (ML) 型に組み替える: `Y↓` を塔の元に見せる分解を探す。

## 1.9.22 ★★★★★ v0.118.15-16: **リフト核が全滅**、残差は文脈 3 本 + γ' 1 本

```
GX_loop_pieces : CoreCtxSuffix → CoreBlockedEltHi → CoreBlocked0
               → CorePlantCtxLift
               → ∀ u Y, Aop W u GXs Y → Y ∈ GXs
```

### 機械の集合を階段閉包にした

```
GXs := { y | y ∈ GX ∧ ∀ φ 階段, slift y φ ∈ GX }
```

- `gxs_slift`（(G5)+`stair_comp`）・`gxs_take`（`slift_take`）で閉じる
- `gxs_mlift`: `GXs` の元の環境マスクリフトは `GX` に入る（`mlift_eq_slift`）
- したがって **α**（`CoreT1L`）は仮定を `Y.dropLast ∈ GXs` にするだけで
  `liftPlant_of_mask` に必要なマスクを読み出せる ⟹
  `coreT1L_of_plantctx : CorePlantCtxLift → CoreT1L`
- **β** は §1.9.21 の (ML) で既にマスク不要 ⟹ `coreT2E_of_plantctx`

⟹ `CoreLift` / `CoreLiftPlant` / `CoreMaskLift` は機械のループから消滅。

### `Aop` の階段輸送とその唯一の穴 → それも塞がった

`aop_slift`: `Aop W u GXs Y` → `Aop W u GXs (slift Y φ)`（`2 ≤ |Y|`）。
節1 は `Stair.zero`、節2 は (G2) `slift_oper`、節3 は `domT` の第 2 成分が
`¬hasParent` なので `Y⟦n⟧ = Y.dropLast` となり**節2 に落ちる**。

残った `|Y| = 1`（植えた根）は `CoreStairOm` として切り出したうえで
**証明済み**（`coreStairOm_holds`）: 長さ 1 の列の末列には親が存在しえない
（添字が負になる）ので、`gx_of_pieces` を「空の peel + 空虚な inner 節」で
走らせればよく、`Aop` すなわち段をまったく消費しない。

### `GX_closed` を部品化した（この整理が鍵）

```
gx_of_pieces (hb h1 h2) u Y
  (hYd : Y.dropLast ∈ GXs)
  (hin : hasParent Y … → ∀ n ≥ 1, Y⟦n⟧ ∈ GXs) : Y ∈ GX
```
`Aop` から `hYd` を取り出すのは節2 でも可能（`gxs_take` + `oper_take_prefix`
で `Y.dropLast = (Y⟦1⟧).take (|Y|-1)`）。

### ⚠ 引き換えに核を強めた（要監視）

`CoreBlocked` / `CoreBlockedElt` / `CoreWindow` / `CoreBlockedEltHi` /
`CoreBlocked0` の仮定を `Aop W u GX Y` から `Y.dropLast ∈ GXs` に置き換えた。
`hpY : ¬hasParent Y` が別途あるので節2 は `Y.dropLast` と同値、節1 は
`|Y| ≤ 1`、失うのは**節3 の `W m` データ**だけ（これらの核の結論に `w` は
現れない）。同じ理由で行 2 接ぎ木塔の枝 (d) を `CoreT2E` に畳んだ。
**もし今後これらの核が偽と分かったら、まずこの弱化を疑うこと。**

## 1.9.23 v0.118.18: 残る 4 核の地図（`CorePlantCtxLift` の設計メモ）

### 上界: 自己参照

`CtxOK M v z` を `k = |M|-1` で使うと `Lift1 ((0,v,z) :: M.dropLast) t ∈ W a`
がそのまま出る（`corePlantCtxLift_of_self`）。つまり

```
CorePlantCtxLift ≤ 「based な W の元は GX に入る」（= 自己参照）
```

自己参照は v0.114 で消したものなので**これは使えない**（`A2'` は最小不動点の
下界で、帰納法の IH をもたない）。よって核は**文脈の長さ帰納**で潰す必要がある。

### 長さ帰納の言語（v0.119 の設計）

`gx_of_pieces` に渡すのは (peel ∈ GXs) と (hin: 末列に親があるときの展開)。
植えブロック `P = Lift1 ((0,v,z) :: R) t = (0, v+t, z) :: mlift R v t` について

- **peel**: `P.dropLast = Lift1 ((0,v,z) :: R.dropLast) t`（`Lift1_dropLast`）
  ⟹ 長さ帰納の IH でよい。底は `singleton_mem_GXs`（v0.118.18 で証明済み）。
- **GXs 成分**: 植えブロックの族は階段リフトで閉じる（v0.118.18 で Lean 化）:
  ```
  slift ((0,B,z) :: S) φ = (0, φ B, z) :: slift S (m ↦ m + (φ (min B m) - min B m))
  ```
  （`slift_cons_plant`、キャップは `stair_cap`。補助に `amin_cons` /
  `coneV_cons_iff`）。したがって帰納の言語は `{(0,B,z) :: slift R ψ}`。
- **hin**: ここだけが残る。⚠ **長さ帰納では出ない**（展開は列を伸ばす）。
  装備 `CtxOK` から `P ∈ W a` は出るが、そこから `GXs` に行くのが自己参照。
  親が根 `0` のとき（塔）は `oper_cons_tower1/2` + `tow_mem_GX` + (ML) で
  IH に落ちる見込み。親が `≥ 1` のとき（ブロック）は `gcopies_mem_GX`
  （`srow ≤ 1`）と `CoreBlockedEltHi`（`srow = 2`）に落ちる見込み。
  ⟹ **v0.119 の主タスク: `hin` を塔／ブロックの 2 相に分けて IH に落とす**。

## 1.9.24 v0.118.21: 4 核の共通の底 — 「`∈ W a` を `∈ GX` に上げる」

### 装備を取り戻した

`coreBlockedElt_of_window` は `CtxOK M v z` をスコープに持ちながら `CoreWindow`
に渡していなかった。渡すようにした（`CoreWindow` / `CoreCtxSuffix` が装備つき
に）。装備なしの文脈核は事実上「定理そのもの」なので、この修正は必須だった。
また `CoreT1L` 以外はデータのマスクを使わないので、ブロック系 5 核の仮定は
`Y.dropLast ∈ GX` に戻した（核が弱くなる = 証明しやすくなる）。

### 4 核はすべて同じ底に落ちる

どの核も、装備 `CtxOK` からは目的の対象が `∈ W a` であることまでしか出ず、
そこから `∈ GX` に上げるところが残る。例:

- `CorePlantCtxLift`: `CtxOK M v z` を `k = |M|-1` で使えば
  `Lift1 ((0,v,z)::M.dropLast) t ∈ W a`（`corePlantCtxLift_of_self`）。
- `CoreCtxSuffix`: `graft (M.take (p+1)) S = M.dropLast` なので、装備は
  **その 1 つの文脈での** 義務を与える。`GX` は全文脈を要求する。
- `CoreT1L` の `hTplant` も `ctxOK_graft` から `∈ W a` までは出る。

`W a ⊆ GXs` は `A2'`（最小不動点の下界）で得るので IH をもたない ⟹ **この
持ち上げを機械の中で使うと循環**。機械の外（文脈の長さ帰納）で供給する必要が
あるが、そこで `gx_of_pieces` を回すと peel の **GXs 成分**（階段リフト）に
対応する装備がない — これが v0.119 の設計上の緊張。

### `CoreBlocked0` は `GX` の `2 ≤ M.length` の副産物

`coreBlocked_of_elt` が `p = 0` を別扱いするのは、降下した文脈 `M.take (p+1)`
の長さが 1 になり `GX_full`（`2 ≤ M.length` を要求）が使えないからだけ。
`(0,v,z) :: graft (M.take 1) C = graft ((0,v,z) :: M.take 1) C` と書けるので、
`GX` の文脈条件を `1 ≤ M.length` に緩められれば `CoreBlocked0` は消える見込み
（ただし `graft_length` 経由で `hGL` 等が壊れるので要検討）。

## 1.9.25 ★ 収束点: 残る仕事は**植えブロック族** `{(0,B,z) :: slift S φ}` ただ一つ

4 核をそれぞれ最後まで追うと、いずれも同じ対象に落ちる:

| 核 | 落ちる先 |
|---|---|
| `CorePlantCtxLift` | `Lift1 ((0,v,z) :: M.dropLast) t = (0,v+t,z) :: mlift M.dropLast v t` |
| `CoreT1L` の `hTplant` | 同上（複合文脈版） |
| `CoreBlockedEltHi` | 窓 `cwin` の**根リフト**全部（下記） |
| `CoreBlocked0` | `GX` の `2 ≤ M.length` の副産物（§1.9.24） |

`CoreBlockedEltHi`（`d1 > 0` の上昇コピー）は、`d1 = 0` の `gcopies_mem_GX`
と同じ「窓への反復接ぎ木」だが、各段が前段の**根リフト**になる
（`oper_root_tower` / `gcopy_succ_glift` / `glift_eq_Lift1`）。外側のリフトは
(ML) `mlift_Lift1_cons` でデータ側に吸収されるので、要るのは
**窓 `cwin` とその根リフト全部が `GX` に入ること**。

そして基づく列 `X`（根 `(0,B,C)`）の根リフトは
```
Lift1 X s = (0, B+s, C) :: mlift X.tail B s = (0, B+s, C) :: slift X.tail χ
```
であり、`slift_cons_plant` により**植えブロック族は階段リフトで閉じる**。
つまり campaign の残りは

> 「装備つきの文脈から作った植えブロック族 `{(0,B,z) :: slift S φ}` が `GX`
> （さらに `GXs`）に入る」

の一点に集約される。v0.119 はこの族の帰納法（長さ帰納 + 装備の設計）に集中
すればよい。⚠ 装備なしの版は定理そのものなので、**装備をどう族に沿って
伝播させるか**が唯一かつ本質的な設計問題（§1.9.24 の緊張）。

## 1.9.26 ★★ v0.119 の設計: 「基づく列はすべて `GX`」を長さ帰納で（強さは装備側）

### 気づき: `GX` の主張は**条件つき**なので、長さ帰納が通る可能性がある

`y ∈ GX` は「**装備つき**文脈に接ぎ木したら複合列が `W a` に入る」という条件つき
主張。停止性の強さは `CtxOK`（文脈の植えブロックが `W a` に入る）側にあり、
`CtxOK M v z` は実際に強い条件（行 1 レベルが `2(v+t)+z` を超える孤児を含む
文脈では偽）。したがって

```
   ∀ y, based y → argOK y.tail → y ∈ GX      （長さ帰納）
```

は「停止性を証明してしまう」わけではない。`gx_of_pieces` に渡す 2 つの部品は

- **peel**: `y.dropLast` は真に短い ⟹ IH（`slift` は長さを変えないので `GXs` も IH で出る）
- **hin**: `y⟦n⟧ ∈ GXs`（末列に親があるとき）。`y⟦n⟧` は**長い**が、
  短い部品から `gx_graft` で組める見込み:
  - バッドルート `j0 = 0`（塔）: `oper_cons_tower1/2` + `tow_mem_GX`（底は peel = IH）
    + 塔の段の帰納（データは前段の根リフト ⟹ (ML) で吸収）
  - バッドルート `j0 ≥ 1`（ブロック）: `y⟦n⟧ = graft (y.take (j0+1)) (shiftl0 c (copies))`。
    `y.take j0` は IH、コピー塊は `gcopies_mem_GX`（`d1 = 0`）またはその
    (ML) 拡張（`d1 > 0`）で、**窓は真に短い**（長さ `|y| - j0 - 1 ≤ |y| - 2`）⟹ IH
  - `lev = 0` / 親なし: `oper_cons_succ` / `oper_cons_nat`（peel のコピー）

### ⚠ 破らねばならない循環

`gx_of_pieces` は `CoreBlocked / CoreT1L / CoreT2E` を要求し、後 2 者は
`CorePlantCtxLift`（= 上の帰納の対象、ただし**文脈 `M` は長さ無制限**）から来る。
`GX` の定義が `M` を全称量化するので、素朴な「データの長さ」帰納では
文脈側の長さが抑えられない。⟹ **複合列の長さ `|M| - 1 + i` で帰納する**、
あるいは文脈長とデータ長の辞書式で回す設計が要る。ここが v0.119 の核心。

### 副産物: `CoreBlocked0` の消し方（実験済み）

`GX` の文脈条件を `2 ≤ M.length` → `1 ≤ M.length` に緩めると
`coreBlocked_of_elt` の `p = 0` 分岐が `GX_full` で処理でき `CoreBlocked0` は
消える。実験すると **12 エラー**、うち 11 は `2 ≤` を渡している箇所の機械的修正、
実質的なのは 1 箇所（`gx_of_pieces` の `hGL`）= **`|M| = 1` かつ `|Y| = 1` の
退化ケース**（複合列が 1 列）。そこは `hctx` の `k = 0`
（`Lift1 ((0,v,z) :: []) t = [(0,v+t,z)] ∈ W a`）から直接処理できる見込み。
ただし `GX` が強くなるので `CoreBlockedElt/Hi/Window/CtxSuffix` の結論も
単元文脈まで含むことになる（トレードオフ）。

## 1.9.27 ⛔ 「装備に `GX` 成分を焼き込む」は**定義の循環**で不可（実験済み）

§1.9.26 の設計を回すには、装備を

```
CtxOK M v z := (∀ k < |M|, ∀ a t, … → Lift1 ((0,v,z)::M.take k) t ∈ W a)
             ∧ (∀ k < |M|, ∀ t,        Lift1 ((0,v,z)::M.take k) t ∈ GX)
```

に強めればよい（そうすれば `CorePlantCtxLift` は核から消え、`CoreWindow` /
`CoreBlockedEltHi` は「窓は真に短い」ので長さ帰納で潰せる）。

**しかし `GX` は `CtxOK` を使って定義されているので、`CtxOK` が `GX` に言及
できない**（Lean で実際に試すと `Unknown identifier GX`）。展開しても
`CtxOK` の自己言及になり、well-founded でない。

### 逃げ道の候補

1. **文脈長で層化する**: `GX_n` は長さ `≤ n` の文脈に対する義務だけを課し、
   `CtxOK_n M v z` の `GX` 成分は `GX_{n-1}` を使う（`M.take k` は真に短い）。
   `GX := ⋂_n GX_n`。再帰は文脈長の上界に関して整礎。**最有力**。
2. 装備を `GX` のパラメータにする（`GX (E : TrioSeq → ℕ → ℕ → Prop)`）で、
   `E` を別途最小不動点として構成する。
3. 現状維持（`CorePlantCtxLift` を核のまま残す）。

### ⛔ 1（文脈長での層化）も接ぎ木で壊れる

`gx_graft` は `graft M'' (graft E w) = graft (graft M'' E) w`（`graft_assoc`）で
`w` の義務に落とすが、複合文脈 `graft M'' E` の長さは `|M''| - 1 + |E| > |M''|`。
つまり**接ぎ木は文脈長を増やす**ので、`GX_n`（長さ `≤ n` の文脈）では
`gx_graft` が同じ層に閉じない。層化パラメータには「接ぎ木で増えない量」が要る
が、根 `(v,z)` は接ぎ木で保たれるものの、植えブロックの根は `(v+t,z)` で
レベルが上がるため `2v+z` も使えない。

### ⚠ 訂正: 2（装備の不動点化）も**素朴には不可**

一度「`F` は単調」と書いたが**誤り**。正しくは:

- `GXe E := {y | … ∀ M, argOK M, E M v z → …}` は `E` に**反単調**
  （`E` が大きい = 課される文脈が増える ⟹ `GXe E` は小さい）。
- `EqStep E := (W 部分) ∧ (植えブロックが GXe E に入る)` は、`GXe E` が
  **正の位置**に現れるので `E` に**反単調**（単調ではない）。

したがって Knaster-Tarski は直接使えない（単調なのは `EqStep ∘ EqStep`）。
反復すると `E_0 = CtxW ⊇ E_2 ⊇ E_4 ⊇ … ⊇ … ⊇ E_3 ⊇ E_1` と偶数列が減少・
奇数列が増加して挟み込む形になる。

### ✅ 得られたもの: 核の正体は「装備クラスの自己支持性」

欲しい条件 `E ⊆ EqStep E`（= 装備つき文脈の植えブロックがまた `GX` に入る）は
**`CorePlantCtxLift` そのもの**であることを Lean で確認した:

```
EquipSelf ↔ CorePlantCtxLift        (corePlantCtxLift_of_equipSelf /
                                     equipSelf_of_corePlantCtxLift)
EquipSelf := ∀ M 装備つき, ∀ 0 < k < |M|, ∀ t,
               Lift1 ((0,v,z) :: M.take k) t ∈ GX
```
（`ctxOK_take` で `k` と `k = |M|-1` を往復するだけ。）

⟹ **パラメータ化しても核は消えない**。核は「装備クラスが自己支持的である」
という*クラスの性質*だと分かったのが収穫で、v0.119 は
「自己支持的かつ実際の文脈を含む装備クラスを構成する」問題に置き換わる。
3（現状維持）と実質同じだが、対象が単一の文脈から**クラス**に変わったので、
`ctxOK_graft` / `ctxOK_ltail` / `ctxOK_take` が自己支持性を保つかを個別に
検査する（＝クラスを閉包で構成する）道が開ける。

## 1.9.28 ✅ 自己支持性はクラスとして閉じる／⛔ 定義に取り込むのは変性で不可

### 得られた閉包則（Lean 済み, v0.118.29）

```
SelfSup M v z := ∀ 0 < k < |M|, ∀ t, Lift1 ((0,v,z) :: M.take k) t ∈ GX

selfSup_take  : SelfSup M v z → SelfSup (M.take j) v z
selfSup_graft : 装備 + SelfSup M + (Y.dropLast ∈ GXs) → SelfSup (graft M Y) v z
selfSup_ltail : SelfSup R v z → SelfSup (ltail v z R t) (v+t) z
```

`selfSup_graft` の中身: 接頭辞 `(graft M Y).take k` は
`k ≤ |M|-1` なら文脈側（`take_graft_low`）、そうでなければ
`graft M (Y.take j)` で、後者は `liftPtant_of_plant`（新設）により
「`M` の植え接頭辞（= `SelfSup M` の `k = |M|-1`）」＋「データのマスク
（`gxs_mlift`）」に分かれる。

⟹ **機械が作る文脈（`take` / `graft` / `ltail`）は自己支持性を保つ**。
したがって `CorePlantCtxLift` は「**最上位の文脈 `S` が自己支持的**」に還元
される（`graftAll_of_GX` の仮定を `CtxOK S v z ∧ SelfSup S v z` に強める形）。

### ⛔ しかし `GX` の定義に取り込むのは変性の問題で不可（3 通り試して全滅）

`gx_of_pieces` の内部で得られるのは `hctx : CtxOK M v z` だけで、`SelfSup M v z`
を得るには `GX` の定義側で文脈を絞る必要がある。ところが

- `GX` は装備クラス `E` に**反単調**、`SelfSup`（= 装備の `GX` 成分）は `GX` に
  **単調**なので、合成は反単調 ⟹ 最小/最大不動点が取れない（§1.9.27 訂正済み）。
- 深さで層化しても `GX_0 ⊆ GX_1 ⊇ GX_2 ⊆ …` と振動する。
- 文脈長で層化すると `gx_graft` が層をまたぐ（§1.9.27）。

### ⟹ v0.119 の選択肢（更新）

1. **最上位の装備を強める**: `graftAll_of_GX` / `Wstar2_closed_of_graftAll` /
   `GraftAll` の仮定に `SelfSup` を足し、機械の内部では `CorePlantCtxLift` を
   核のまま残す（＝現状の 4 核から実質 3 核 + 装備強化）。閉包則が揃ったので
   **これは今すぐ実装可能**。ただし `GX` 内部で `SelfSup` が使えない以上、
   `CorePlantCtxLift` 自体は消えない（核の供給元が変わるだけ）。
2. `GX` を「文脈を明示的に持ち歩く」形に書き換える（義務を集合ではなく
   文脈つきの関係として定義し、自己支持性を関係の側で帰納的に構成する）。
   変性の問題を回避できる可能性があるが大改造。
3. 現状維持で `CoreWindow` / `CoreBlockedEltHi` / `CoreBlocked0` を先に潰す。

## 1.9.29 ✅ v0.118.31: `GX` の文脈を**単元まで緩めて** `CoreBlocked0` を消した

### 何をしたか

`GX` の文脈条件 `2 ≤ M.length` を `1 ≤ M.length` に緩めた。連動して
`GX_full` / `ctxOK_graft` / `ctxOK_ltail` / `liftPlant_of_plant` /
`liftPlant_of_mask` / `selfSup_graft` / `graftAll_of_GX`、および
`CoreT1L` / `CoreT2E` / `CoreT2EFam` / `CorePlantCtxLift` / `CorePlantCtx` /
`CoreLiftPlant` / `EquipSelf` / `SelfSup` を `1 ≤` 版にした。

- `coreBlocked_of_elt` の `p = 0` 分岐（降下文脈 `M.take 1` の長さが 1）が
  `GX_full` で処理できるようになり、**`CoreBlocked0` は定義ごと削除**。
- ブロック系の核（`CoreBlocked` / `CoreBlockedElt` / `CoreWindow` /
  `CoreCtxSuffix` / `CoreBlockedEltHi`）は `2 ≤ M.length` のまま。
  `gx_of_pieces` の γ 枝では `hplt : p < |M| - 1` から `2 ≤ |M|` が復元でき、
  `hGL : |graft M Y| - 1 ≠ 0` も `hpG` から `nextR_index_lt` で出る
  （旧 `hGlen` は `1 ≤ |graft M Y|` に弱めた）。

### なぜ「核が強くなる」トレードオフではないのか

以前 §1.9.26 でこの緩和を「他の核の結論が強くなるので net progress ではない」
と評価したが、**それは誤り**だった。最終目標の

```
GraftAll : ∀ S, argOK S → S ≠ [] → ∀ u y, y ∈ W u → based y → graft S y ∈ Wstar2
```

は**もともと単元文脈 `S ≠ []` を要求している**。緩和前の `graftAll_of_GX` は
`2 ≤ S.length` しか出せず、単元文脈は既知のギャップだった。緩和後は

```
graftAll_of_GX : ∀ S, argOK S → 1 ≤ S.length → (∀ v z, z ≤ 1 → CtxOK S v z) → …
```

となり、**`GraftAll` との差は装備 `CtxOK S v z` の一点だけ**になった
（文脈長のギャップは消滅）。

### 残差（3 本）

| 核 | 内容 |
|---|---|
| `CorePlantCtxLift` | 装備つき文脈の植えた peel のリフトが `GX` |
| `CoreWindow`（⊂ `CoreCtxSuffix`） | 複合列の窓が `GX` |
| `CoreBlockedEltHi` | 行 2 ブロッカーの上昇コピー塊（`d1 > 0`）が `GX` |

`GX_loop (he : CoreBlockedElt) (hp : CorePlantCtxLift)` /
`GX_loop_window (hw) (hhi) (hp)` / `GX_loop_pieces (hsuf) (hhi) (hp)`。

## 1.9.30 ★★★ v0.118.32-33: 残差が**2 核**に — `CoreBlockedEltHi` が消えた

### 何が起きたか

`gcopies_mem_GX`（`d1 = 0`）は「コピー塊 = 窓への反復接ぎ木」だった。
行 2 ブロッカー（`d1 > 0`）でも同じ形になることを Lean で示した:

```
gcopies B 0 L d0 d1 (n+1) = graft B (Lift1 (gcopies B 0 L d0 d1 n) d1)
                                     ^^^^^ 前段の**根リフト**
```

（`Croot.gcopies_succ_graft_lift`）。これは列ごとの計算に落とすと

```
le1 (gcopies B 0 L d0 d1 n) 0 (k*L+q)  ↔  le1 B 0 q
```

すなわち**ブロック自身の根の錐輸送**と同値。`Lcone.gexp_cone_mir` は
宿主の根（`j0 > 0` の下）用なので、その `j0 = 0` 版
`Croot.gexp_cone_mir_root` を新設した。前置ブロックが無いぶん鎖分解は素直で、
代わりに 2 つの仮定が要る（tools/probe_coneroot.py で確定）:

* `0 < d1` — コピーの根 `k*L` が錐に入るのは行 1 が `k*d1` 上がるから
* `le1 B 0 L` — ブロックされた列が根の錐に入ること（行 2 ブロッカーでは
  `parent R 2 x` から自動: `nextrel2` は `le1` を含む）

宿主 `R` の窓を単独ブロック `B = shiftl0 c (seg R p (L+1))` に切り出す再基底化は
**無条件の既存補題だけ**で済んだ（`le1_take` + `le1_append_right`）。

### GX 側の帰納

外側のリフトは (ML) `mlift_Lift1_cons` でデータ側に吸収されるので、強めた帰納

```
∀ n s, Lift1 (gcopies B 0 L d0 d1 n) s ∈ GX
```

が `liftPlant_of_plant`（装備不要に整理: `hz1` / `hctx` は未使用だった）だけで
回る。底は `∀ s, Lift1 B.dropLast s ∈ GX` = **窓とその根リフト全部**。

### 残差（2 核）

| 核 | 内容 |
|---|---|
| `CorePlantCtxLift` | 装備つき文脈の植えた peel のリフトが `GX` |
| `CoreWindowLift` | 複合列の再基底化した窓**とその根リフト全部**が `GX` |

```
GX_loop_lift (hwl : CoreWindowLift) (hp : CorePlantCtxLift)
  : ∀ u Y, Aop W u GXs Y → Y ∈ GXs
```

`CoreWindowLift` の `s = 0` が旧 `CoreWindow`。両核とも
**「植えブロック族 `{(0,B,z) :: …}` とその根リフトが `GX`」**という
§1.9.25 の収束点そのままの形になった。

## 1.9.31 ★★★ v0.118.34: 残る 2 核が**どちらも純粋な文脈の言明**になった

```
GX_loop_ctx (hsl : CoreCtxSuffixLift) (hp : CorePlantCtxLift)
  : ∀ u Y, Aop W u GXs Y → Y ∈ GXs
```

`CoreWindowLift`（複合列の窓）は `shiftl0_seg_graft` で
「文脈の再基底化した接尾 `E` にデータの peel を接ぎ木したもの」に分解する。
`E` は根 `(0, entry M 1 p, entry M 2 p)` をもつ**植えブロック**なので、
`liftPlant_of_plant` がリフトを

* `E` 自身の根リフト = `CoreCtxSuffixLift`
* データの環境マスク = `gxs_mlift`（そのためブロック系の核の仮定を
  `Y.dropLast ∈ GX` から `Y.dropLast ∈ GXs` に戻した。`gx_of_pieces` は
  もともと `GXs` を持っている）

に割る。⟹ **`CoreWindowLift` は `CoreCtxSuffixLift` に落ちる**。

### 残差（2 核、どちらも文脈だけ）

| 核 | 対象 |
|---|---|
| `CorePlantCtxLift` | `Lift1 ((0,v,z) :: M.dropLast) t ∈ GX`（周囲の根で植えた peel） |
| `CoreCtxSuffixLift` | `Lift1 (shiftl0 (entry M 0 p) (seg M p (\|M\|-1-p))) s ∈ GX`（自身の根で再基底化した中間ブロック） |

どちらも「装備つき文脈から切り出した**植えブロック + その根リフト全部**が
`GX`」という同じ形。§1.9.25 の収束点が Lean の命題として実現された。

### 次の設計

`CoreCtxSuffixLift` を `CorePlantCtxLift` に落とすには、接尾を文脈と見た
`M' := shiftl0 c (seg M (p+1) (\|M\|-1-p))` に対する
`CtxOK M' (entry M 1 p) (entry M 2 p)`（**再基底化した中間ブロックの
package**）が要る。ambient の `CtxOK M v z` は `M.take k` の package しか
与えないので、これは新しい義務 — つまり「装備クラスを中間ブロックについても
閉じる」設計（§1.9.28 の選択肢 1 = 最上位の装備を強める）が次の一手。
`entry M 2 p ≤ 1` も要確認（z<2 断片の不変量）。

## 1.9.32 ★★★★ v0.118.35: **装備ギャップが閉じた** — `GraftAll` を核から直接出せる

### `Wstar2s`（接頭辞閉包）

装備 `CtxOK M v z` は「`M` の全接頭辞の植えブロックが `W a` に入る」であり、
`∀ k, M.take k ∈ Wstar2` と同じ。`Wstar2` は接頭辞で閉じていないが、A2' を回す
集合を接頭辞閉包 `Wstar2s := {R | ∀ k, R.take k ∈ Wstar2}` にすれば
**帰納法自身が装備を供給する**:

```
take_mem_Wstar2_of_Aop : Aop W u0 Wstar2s R → ∀ k < |R|, R.take k ∈ Wstar2
```

真の接頭辞は `Aop` のデータから読める — 節 2 なら `R⟦1⟧` の接頭辞
（`oper_take_prefix`）、節 3 なら `graft R [] = R.dropLast`（`W_nil`）。
（これは `GXs_closed` が peel を `Y⟦1⟧` から取るのと同じ手。）

### `GraftAll` の再定義

`GraftAll` に文脈の装備を持たせ、`graft S y ∈ Wstar2` を根ごとに展開した:

```
GraftAll : ∀ S, argOK S → S ≠ [] → ∀ v z, z ≤ 1 →
  CtxOK S v z → ∀ u y, y ∈ W u → based y → argOK (graft S y) →
  ∀ a t, 2(v+t)+z ≤ a → Lift1 ((0,v,z) :: graft S y) t ∈ W a
```

`LiftTower1` / `LiftTowerExp2` に接頭辞仮定を足し、`Wstar2_closed` の入力を
`Aop W u0 Wstar2s R` にすることで、消費側（`liftTower1_of_graftAll` は
`Rt = ltail v z R t` を、`liftTowerExp2_of_graftAll` は `R` を）で
`CtxOK` が作れる（`ltail_take` + `Lift1_Lift1`）。

⟹ **`graftAll_of_GX : CoreBlocked → CoreT1L → CoreT2E → Wset.GraftAll`**
（以前は「装備つき文脈だけ」で、単元文脈と装備が二重のギャップだった）。

### 到達点

```
W_le_Wstar2s_of_cores (hsl : CoreCtxSuffixLift) (hp : CorePlantCtxLift)
  : ∀ u, W u ⊆ Wstar2s
```
sorry 0、axioms = [propext, Classical.choice, Quot.sound]、build 782 jobs。

つまり **トリオ側の閉包はすべて 2 本の文脈核に還元された**。

## 1.9.33 ★★★★★ v0.118.36: **停止性が 2 本の文脈核だけに乗った**

```
TRIO_terminates_of_cores : CoreCtxSuffixLift → CorePlantCtxLift
                         → WellFounded stepRel
```
sorry 0、axioms = [propext, Classical.choice, Quot.sound]、build 782 jobs。

### 配線替え

`mem_of_Aclosed_aux` 以下（`mem_of_Aclosed` / `mem_Wstar` /
`mem_W_of_bound(_aux)` / `mem_W_maxlev` / `W_membership` /
`wf_olt_ST_TS_of_cofinality`）は `TowerOK` を `Wstar` の A-閉性にしか使って
いなかったので、**集合 `S` でパラメータ化**した:

```
{S : Set TrioSeq} (hSle : S ⊆ Wstar)
  (hScl : ∀ u0 R, Aop W u0 S R → R ∈ S)
```

* 旧トラック: `S := Wstar`, `Set.Subset.rfl`, `Wstar_closed (towerOK_of h2 he)`
* 新トラック: `S := Wstar2s`, `Wstar2s_le_Wstar`,
  `Wstar2s_closed_of_graftAll (graftAll_of_cores hsl hp)`

`Final.lean` に新トラックの `wf_olt_ST_TS_of_cores` /
`TRIO_terminates_of_cores` / `no_infinite_expansion_of_cores` を追加
（旧 `TRIO_terminates (h2 he)` はそのまま残してある）。

### いま残っているもの（これだけ）

```
CorePlantCtxLift  : 装備つき文脈 M について ∀ t, Lift1 ((0,v,z) :: M.dropLast) t ∈ GX
CoreCtxSuffixLift : 装備つき文脈 M, p < |M|-1 について
                    ∀ s, Lift1 (shiftl0 (entry M 0 p) (seg M p (|M|-1-p))) s ∈ GX
```

## 1.9.34 ★★★ v0.118.37: 残差が **`GX` 核 1 本 + `W` レベルの装備 1 本**に

```
TRIO_terminates_of_plant : InfEquip → CorePlantCtxLift → WellFounded stepRel
```

### ⚠ まず確認したこと: 還元は**同値変形**でしかない部分がある

```
corePlantCtxLift_of_graftAll : Wset.GraftAll → CorePlantCtxLift   （新規, Lean 済み）
graftAll_of_cores            : 2 核 → Wset.GraftAll
```
つまり `CorePlantCtxLift` は `GraftAll` から**出てしまう**（＝ `GraftAll` より
強くない）。したがって「さらに小さい核へ還元する」だけでは決して閉じない。
閉じるには**新しい帰納法**が要る。この事実は明示しておく必要がある
（還元を証明と取り違えない）。

### 接尾核は「中間ブロックの装備」だけで植え核に落ちる

`CoreCtxSuffixLift` の対象 `shiftl0 c (seg M p (|M|-1-p))` は、
中間ブロック `M' = shiftl0 c (seg M (p+1) (|M|-1-p))` を根
`(entry M 1 p, entry M 2 p)` で植えたブロックそのもの。よって

```
coreCtxSuffixLift_of_plantctx : CorePlantCtxLift → InfEquip → CoreCtxSuffixLift
```

`InfEquip`（新設）は**純粋に `W` レベル**の言明:

```
InfEquip : ∀ M p, argOK M → 2 ≤ |M| → p < |M|-1 → (窓条件) →
  ∀ v z, z ≤ 1 → CtxOK M v z →
    entry M 2 p ≤ 1 ∧ CtxOK (shiftl0 (entry M 0 p) (seg M (p+1) (|M|-1-p)))
                            (entry M 1 p) (entry M 2 p)
```

`GX` を一切含まない。`Wstar2s` が接頭辞の package を帰納法から供給したのと
同じ手が使える見込み（要る中間ブロックは**末尾列に触れない**ので `R⟦1⟧` から
継承できるはず）。`entry M 2 p ≤ 1` は z<2 断片の `zle1` 不変量で、いまは
文脈側に通っていないので `InfEquip` に同梱してある。

### 残差

| 残るもの | 種類 |
|---|---|
| `CorePlantCtxLift` | `GX` レベル（`GraftAll` より弱い） |
| `InfEquip` | `W` レベル（装備の強化で供給できる見込み） |

## 1.9.35 v0.118.38: `InfEquip` を装備から供給する道筋（計測で法則を確定）

`InfEquip` は `GX` を含まない `W` レベルの言明なので、`Wstar2s` が接頭辞の
package を供給したのと同じ手（`R⟦1⟧` からの継承）で供給できる見込みが立った。

### なぜ継承できるか（接頭辞と同じ理由）

`InfEquip` が要求する中間ブロックは `p + k < |M| - 1`、すなわち**末尾列に
触れない**。`oper_take_prefix` により `R⟦1⟧` の接頭辞は `R` の接頭辞なので、
そのような中間ブロックは `R⟦1⟧`（節 2）と `graft R [] = R.dropLast`（節 3）
の両方から継承できる。節 1（`|R| ≤ 1`）では条件が空。

### ★ ただしリフト文脈 `ltail` では法則が違う（計測: probe_infltail.py）

素朴な「中間ブロックの**根リフト**」は**偽**（窓条件つきでも 1911/35973）。
周囲の根の行 1 値が中間ブロックの根より小さいと、周囲の錐は中間ブロックの
自前の錐より真に大きくなる。正しい法則は**環境マスクリフト**:

```
shiftl0 c (seg (ltail v z R t) p (k+1))
  = mlift (shiftl0 c (seg R p (k+1))) v t      （p が周囲の錐に入るとき）
  = shiftl0 c (seg R p (k+1))                  （入らないとき・窓条件が要る）
```

計測（150000 サンプル）:

| 場合 | サンプル | 違反 |
|---|---|---|
| in（窓条件なし） | 12283 | 0 |
| in（窓条件あり） | 35973 | 0 |
| out（窓条件あり） | 75328 | 0 |
| out（窓条件なし） | 26416 | 4555 |

理由: 窓条件があると中間ブロックの列の行 0 祖先鎖は `p` を通ってから外へ出るので
`amin_N(q) = min (amin_infix q) (amin_N p)`。`p` が錐に入る（`amin_N p > v`）なら
これは `amin_infix q > v` と同値 = `mlift . v t` そのもの。

`mlift` は階段リフト（`Cgraft.mlift_eq_slift`）なので、**文脈成分 `CtxInf` は
`GXs` と同じく階段閉包にしておく必要がある**。これが v0.119 の設計。

## 1.9.36 ★★ v0.118.39: (IL) 計算則が Lean で揃った — v0.119 の設計確定

### 証明済み（Croot.lean, sorry 0）

```
amin_seg   : amin R (p+q) = min (amin (seg R p (k+1)) q) (amin R p)
             （窓の鎖 rtg0 R p (p+q) のもとで）
coneV_seg  : coneV R v (p+q) ↔ coneV (seg R p (k+1)) v q ∧ coneV R v p
seg_mlift  : seg (mlift R v t) p (k+1)
               = if coneV R v p then mlift (seg R p (k+1)) v t
                 else seg R p (k+1)
seg_slift  : seg (slift R φ) p (k+1)
               = slift (seg R p (k+1)) (φ を amin R p でキャップした階段)
             （`stair_cap` の階段）
ltail_eq_mlift, shiftl0_slift, shiftl0_seg_slift, shiftl0_seg_ltail,
nextrel0_shiftl0 / rtg0_shiftl0 / coneV_shiftl0 / amin_shiftl0 / shiftl0_mlift
```

### v0.119 のレシピ（これで設計は確定）

**文脈成分**（階段閉包にするのが必須。素朴な根リフト版は偽）:

```
CtxInf M : ∀ p k, p + k < |M| - 1 →
  entry M 2 p ≤ 1 ∧
  ∀ φ Stair, ∀ a t, 2 * (φ (entry M 1 p) + t) + entry M 2 p ≤ a →
    Lift1 (slift (shiftl0 (entry M 0 p) (seg M p (k+1))) φ) t ∈ W a
```

* `take` 伝播: 自明（entry と seg が一致）。
* `ltail` 伝播: `ltail_eq_mlift` + `seg_mlift` + `slift_slift` + `stair_comp`。
  錐に入る場合は根の行 1 が `+t` されるので `ψ ∘ φ_{v,t}` を渡す。入らない場合は
  そのまま。**両分岐とも計測で違反 0**。
* `graft` 伝播: (i) `M` 内部 → そのまま、(ii) 接ぎ木点をまたぐ →
  `shiftl0_seg_graft` で `graft (M の再基底化接尾) (E.take j)` になり、
  `slift_graft` (G3) で階段が両側に分かれるので、`E.dropLast ∈ GXs`（＝
  `gx_graft` の仮定を `GX` から `GXs` に強める）と `CtxInf M` から出る、
  (iii) `E` の内部 → `CtxInf E`（各呼び出し点で `E` は具体的なので導ける）。
* 供給元: A2' の集合を `Wstar2s` からさらに強めた `Wstar2i` にする。要る中間
  ブロックは `p+k < |R|-1` で**末尾列に触れない**ので、接頭辞と同じく
  `R⟦1⟧`（節 2）・`R.dropLast`（節 3）から継承できる。階段リフト成分も
  同じ中間ブロックなのでそのまま継承。
* 結果: `InfEquip` が装備から出て、残差は `CorePlantCtxLift` ただ 1 本。

⚠ ただし §1.9.34 のとおり `CorePlantCtxLift` は `GraftAll` から出るので、
これでも**閉じない**。閉じるには新しい帰納法が要る。

## 1.9.37 v0.118.41: `CtxInf` の take / ltail は済み、残るは graft（設計上の帰結）

### 済み（Gamma.lean, sorry 0）

```
CtxInf M : ∀ p k, p + k < |M| - 1 → (窓の鎖) →
  entry M 2 p ≤ 1 ∧
  ∀ φ Stair, ∀ a t, 2 * (φ (entry M 1 p) + t) + entry M 2 p ≤ a →
    Lift1 (slift (shiftl0 (entry M 0 p) (seg M p (k+1))) φ) t ∈ W a

ctxInf_take          : CtxInf M → CtxInf (M.take j)
ctxInf_ltail         : argOK M → CtxInf M → CtxInf (ltail v z M t)
infEquip_at_of_ctxInf: CtxInf M → （InfEquip の中身、φ = id の切片）
```
`ctxInf_ltail` が (IL) の山場。錐に入る枝は `seg_mlift` + `mlift_eq_slift` +
`slift_slift` + `stair_comp` で `ψ_{v,t}` を合成して落ちる。

### ★ 残る `ctxInf_graft` の設計上の帰結（重要）

複合文脈 `graft M E` の中間ブロックは 3 通り:

1. `M` 内部 — そのまま（`take_graft_low`）
2. `E` 内部 — `CtxInf E`（各 `gx_graft` 呼び出し点で `E` は具体的なので導ける）
3. **接ぎ木点をまたぐ** — `shiftl0_seg_graft` で
   `graft (M の再基底化接尾 A) (E.take j)` になり、`slift_graft` (G3) で
   `graft (slift A φ) (slift (E.take j) ψ)` に分かれる。これは
   `slift (E.take j) ψ` の **`GX` 義務**（文脈 `(slift A φ).tail`、根
   `(φ r1, r2)`）そのもの。文脈の装備は `CtxInf M` から出る。

⟹ 3 のために **`gx_graft` の仮定を `E.dropLast ∈ GX` から `∈ GXs` に強める**
必要がある。するとその呼び出し点（`plantCtx_graft` / `tow_mem_GX` /
`gcopies_mem_GX` / 窓）で `E` の peel の**階段閉包**が要るので、残る核も
`CorePlantCtxLift` の階段閉包版に強まる。ここが v0.119 の実装コスト。

## 1.9.38 v0.118.43-44: `ctxInf_graft` は「またぎ」1 ケースだけ残り（手順確定）

### 済み

```
seg_graft_low            : p+k < |M|-1 → seg (graft M E) p (k+1) = seg M p (k+1)
shiftl0_seg_graft_high   : |M|-1 ≤ p のとき再基底化した中間ブロックは E のもの
seg_graft_cross          : またぎの中間ブロック（一般長）の分解
shiftl0_seg_graft_cross  : = graft (M の再基底化接尾 A) (E.take j)
ctxInf_graft_of_cross    : CtxInf M → CtxInf E → (またぎ) → CtxInf (graft M E)
```

### 残り `ctxInf_cross` の手順（この形で書けば通るはず）

仮定: `argOK M`, `2 ≤ |M|`, `based E`, `E ≠ []`, `CtxInf M`,
**`E.dropLast ∈ GXs`**（← `gx_graft` の仮定強化が要る理由）。

1. `p < |M|-1` なので `entry (graft M E) i p = entry M i p`（`entry_graft_low`）。
2. `M` 内の行 0 鎖: `hwin` を `le0_take` + `take_graft_low` で `M` に移す。
   これで `entry M 2 p ≤ 1` は `CtxInf M` の `k = 0` から出る。
3. `j := k+1 - (|M|-1-p)`（`1 ≤ j ≤ |E|-1`）。`hle : entry M 0 p ≤ entry M 0 (|M|-1)`
   は `hwin (|M|-1-p)` + `rtg0_entry0_lt` + `hgp`（`based E` で接ぎ木点の深さが
   `entry M 0 (|M|-1)`）から。
4. `shiftl0_seg_graft_cross` で対象 = `graft A (E.take j)`,
   `A := shiftl0 (entry M 0 p) (seg M p (|M|-p))`, `|A| = |M|-p ≥ 2`。
5. `slift_graft` (G3) で `slift (graft A B) φ = graft (slift A φ) (slift B ψ)`,
   `ψ = stair_cap φ (capV A)`。`hne` は `y = 0`（窓で `A` の根が最浅）。
6. `A` の頭は `(0, r1, r2)`（`entry0_shiftl0` + `entry_seg`）、`amin A 0 = r1`
   （`amin_zero`）なので `slift A φ` の頭は `(0, φ r1, r2)`。`graft_cons` で
   `graft (slift A φ) B' = (0, φ r1, r2) :: graft ((slift A φ).tail) B'`。
7. `GX_full` を適用。必要な部品:
   * `slift (E.take j) ψ ∈ GX` ← `gxs_take hEd j` + `dropLast_take` + `.2 ψ`
   * `based`（`entry0_slift`）、`argOK ((slift A φ).tail)`（窓、`entry0_slift`）
   * `CtxOK ((slift A φ).tail) (φ r1) r2` ← **`CtxInf M` を φ で使う**。
     `(slift A φ).take (k'+1) = slift (A.take (k'+1)) φ`（`slift_take`）、
     `A.take (k'+1) = shiftl0 c (seg M p (k'+1))`（`seg_take`）で一致。
   * `r2 ≤ 1`、レベル条件はそのまま。

⚠ 実装時の注意: `entry A i q` の一般補題を作ろうとすると行 2 の添字合わせで
ハマる。必要なのは `q = 0` の 3 つと `A.take` の形だけなので個別に出すこと。

## 1.9.39 ★★★ 新しい帰納法の検討: 本質的困難は「リフトによる段の押し上げ」

### 1. いまの循環の正体（Buchholz との対応）

Buchholz 1987 では `W_u ⊆ X^(a)` を (A2)（最小不動点の下界）で得る。
`X^(a) = {y | ∀ M, graft M y ∈ W a}` は我々の `GX` そのもので、
A-閉性 `Aop W u X^(a) y → y ∈ X^(a)` が「一段ミラー 2.4(a)」で示される。
我々の `GXs_closed` がまさにそれで、**核が出るのはミラーが破れる枝だけ**:

* γ（ブロック）: 複合列の悪根が**文脈側**に落ちる
* α/β（塔）: 末尾列が文脈（または植えた根）に**再接続**される

### 2. 帰納法の向きは 2 つとも試されている

| 向き | 集合 | 開いた核 |
|---|---|---|
| データ側 | `GX` / `X^(a)` | `CorePlantCtxLift`（文脈の植えブロックが `GX`） |
| 文脈側 | `Wstar` / `Wstar2s` | `TowerOK` / 塔枝 |

どちらも**塔枝**で止まる。

### 3. ★ 塔枝の本質: `t = 0` では自由、`t > 0` で段が上がる

`liftTower1_of_graftAll` が要求するのは

```
∀ y ∈ W (m + 2t), … Lift1 ((0,v+t,z) :: graft Rt y) 0 ∈ W a'
```

すなわち **段 `m + 2t`** の接ぎ木閉包。一方 `Aop` の節 3 が与えるのは
**段 `m`** の閉包（`∀ z ∈ W m, graft R z ∈ X`）。`t = 0` なら
`graft ((0,v,z)::R) w = (0,v,z) :: graft R w`（`graft_cons`）で節 3 に直接落ち、
塔は `tow k ∈ W m` の `k` 帰納で閉じる（`tower1_le` が `2v+z ≤ m` を与える）。

⟹ **核の内容はすべて `t > 0`（周囲の行 1 リフト）に由来する**。リフトは
コピーの根を全部持ち上げるので、必要な段が `m` から `m + 2t` に上がり、
`Aop` のデータが届かなくなる。

### 4. 段は帰納法の測度になれない（要注意）

`2v + z ≤ m`（`tower1_le`）より `2(v+t)+z = 2v+z+2t ≤ m+2t`。目標段 `a` は
`2(v+t)+z ≤ a` しか満たさないので、必要データ段 `m+2t` と `a` の間に
**厳密な降下がない**（等号が起こりうる）。⟹ 段による強帰納法は不可。

### 5. 却下済みの測度（再挑戦禁止）

* データの長さ: 文脈の植えブロックは**データより長い**（`|M|+|Y|-1`）
* 複合列の長さ: `gx_graft` は複合長を保つが、`GX` の「∀ 文脈」で非有界
* 文脈長: `graft` が文脈を伸ばす（§1.9.27）
* 装備の不動点: 反単調（§1.9.27 訂正）
* 段: 上記 4

### 6. ★ 有望な方向: 文脈の全称量化は**過剰**

実際の使用箇所では文脈は任意ではない:

* α: 塔の反復で現れる文脈は `{graft^n Rt P}`（`P = (0,v+t,z) :: Rt`）だけで、
  データは塔添字 `k` で**降下**する（`tow (k+1) = graft P (tow k)`）。
* γ: 文脈は `graft (M.take (p+1)) (部分コピー塊)` だけで、データはコピー数 `n`
  で降下する。しかも複合列の展開は `graft (M.take (p+1)) …` なので
  **文脈長が真に縮む**（`p+1 ≤ |M|-1`）。

`GX` が「∀ 装備つき文脈」なのは `gx_graft` を回すための過剰近似。
⟹ **次の設計候補**: `GX` を「文脈を持ち歩く関係 `GXrel N y`」にし、
`tow_mem` / `gcopies_mem` を塔添字・コピー数の帰納で、文脈は上の
**明示的に生成される族**に限って回す。そうすると核は
「生成族の植えブロックが `W` の package」になり、生成族の植えブロックは
**より短いデータの複合列**なので（データ長, 添字）の辞書式で降下する見込み。

### 7. まず確かめるべき最小の問い

> `t > 0` の塔で、段 `m + 2t` の接ぎ木閉包を、段 `m` のデータと
> **塔自身の元だけ**から作れるか（行 2 では `towerGraft2_lift_fam` が
> 「塔自身の元だけ」の形を実現している。行 1 に同じ族形式があるか）。

`tower1_mem2` の `hgr` は実際には `tow v z R k` にしか適用されていないので、
`LiftTower1` の族形式（`∀ y ∈ W m` を捨てる）は書けるはず。これが書ければ
α 枝は `GraftAll` を経由せずに閉じ、残るのは γ 枝だけになる。

## 1.9.40 ★★★★ 新しい帰納法の**具体案**: 生成族の上で複合列長の帰納

### 出発点: 行 1 の族形式は書ける（`tower1_mem2` の中身を読んで確認）

`tower1_mem2` の `hgr` は実際には `tow v z R k` にしか適用されていない。
したがって族形式

```
tower1_mem2_fam :
  (∀ k a', 2v+z ≤ a' → Lift1 ((0,v,z) :: graft R (tow v z R k)) 0 ∈ W a')
  → ∀ k, tow v z R k ∈ W a
```
は自明に書ける（`tow (k+1) = (0,v,z) :: graft R (tow k)`、`graft_cons`）。
⟹ **`∀ y ∈ W (m+2t)` の界面が消え、§1.9.39 の「段の押し上げ」が статement
から消える**。内容は「塔自身の元を `R` に接ぎ木したもの」に移る。

### 生成族と測度

`P := (0,v+t,z) :: Rt`、`N_0 := Rt`、`N_{n+1} := graft N_n P` と置くと

```
graft Rt (tow (v+t) z Rt (k+1)) = graft (graft Rt P) (tow k) = graft N_1 (tow k)
… ⟹ 塔全体は「N_k.dropLast が W package」に還元
N_k.dropLast = graft N_{k-1} (P.dropLast)
```

つまり必要なのは **`Rt` の植えブロックが族 `{N_n}` に接ぎ木できること**だけで、
`GX` の「∀ 装備つき文脈」は要らない。

⚠ **訂正**: 塔の再結合そのものは複合列長を**保つ**（Lean で確認:
`graft_tow_succ : graft N (tow v z R (k+1)) = graft (graft N ((0,v,z)::R)) (tow v z R k)`、
両辺は同じリスト）。よって複合列長だけでは塔は回らず、**塔は添字 `k` の
帰納で駆動する**必要がある。複合列長が効くのは残りの義務のほう:

```
N_n の接頭辞 = N_{n-1} の接頭辞 or graft N_{n-1} (P.take i)
|graft N_{n-1} (P.take i)| = |N_{n-1}| - 1 + i  <  |N_n| = |N_{n-1}| - 1 + |P|
```

すなわち**植えブロック／窓の義務では複合列長が真に降下する**。γ 枝でも複合列の
展開は `graft (M.take (p+1)) (コピー塊)` で文脈が真に縮む。

⟹ **測度 = （複合列長, 塔／コピー添字）の辞書式**。複合列長は `gx_graft` の
再結合（`graft_assoc`）で不変なので整合する。§1.9.39 で複合列長が却下された
理由は「`GX` の ∀ 文脈で非有界」だったので、**文脈を生成族に限れば復活する**。

### v0.120 の設計案

1. `GX` を文脈つきの関係 `GXrel N y`（= 「`y` は `N` に接ぎ木できる」）にする。
2. 文脈は帰納的述語 `Ctx`（`Rt` / `graft N P` / `take` / `ltail` で生成）で限定。
3. `tow_mem` / `gcopies_mem` を塔添字・コピー数の帰納で回す（文脈は生成族）。
4. 全体を**複合列長**の強帰納法で回す。`gx_graft` は複合列長を保つので、
   再帰は `graft_assoc` で平坦化して長さで測れる。
5. 核だったものは「生成族の植えブロックが `W` package」になり、これは
   `N_n.dropLast` の形で**より短い複合列**なので帰納法の内側に入る。

⚠ 未検証のリスク: (a) `ltail` が族に入ると長さは保つが根が変わる、
(b) γ 枝の窓が族に属することの確認、(c) `Aop` の節 3 データ（段 `m`）の
取り込み口。まずは 1.-3. を行 1 塔だけで試作するのが安全。

## 1.9.41 ★★★★ v0.118.50: 還元を Lean で確定 — 塔もコピー塊も「生成族の peel」

### 証明済み（Gamma.lean / Wset.lean, sorry 0）

```
gpow N E 0 = N,  gpow N E (n+1) = graft (gpow N E n) E     -- 生成族

graft_iter_gpow : f 0 = [] → (∀ n, f (n+1) = graft E (f n)) →
  ∀ n k, graft (gpow N E k) (f n) = (gpow N E (k+n)).dropLast

tower1_mem2_fam  : 塔は「塔自身の元を R に接ぎ木」だけで閉じる（∀ y ∈ W m 不要）
graft_tow_gpow   : 塔の instance（E = (0,v,z)::R）
graft_gcopies_gpow : ブロック済みコピー塊の instance（E = cwin, d1 = 0）
tower1_mem2_gpow : ∀ k a', 2v+z ≤ a' →
    Lift1 ((0,v,z) :: (gpow R ((0,v,z)::R) k).dropLast) 0 ∈ W a'
  → ∀ k, tow v z R k ∈ W a
```

### 意味

塔とコピー塊はどちらも「`f 0 = []`, `f (n+1) = graft E (f n)`」という
**同一の反復接ぎ木**で、`graft_assoc` で文脈側に畳むと

> 義務 = **生成族 `gpow N E k` の peel が `W` package**

に化ける。したがって

* `∀ y ∈ W m` の界面が消える ⟹ **段の押し上げ `m → m+2t` が消える**（§1.9.39）
* `GX`（∀ 装備つき文脈）が要らない — 文脈は `gpow N E k` だけ

⟹ **v0.120 の残りは「生成族の peel が `W` package」を示すこと**だけ。
`(gpow N E (k+1)).dropLast = graft (gpow N E k) E.dropLast` なので、これは
「`E` の peel を生成族に接ぎ木する」義務であり、`E.dropLast` は `E` より短い。
生成族の接頭辞は `graft (gpow N E (k-1)) (E.take i)` で複合列長が真に降下する
（§1.9.40 の訂正版）。⟹ （複合列長, 添字）の辞書式で回る見込み。

### ★ 生成族の peel には `k` の降下がある（これが「新しい帰納法」の芯）

```
(gpow N E (k+1)).dropLast = graft (gpow N E k) E.dropLast        （graft_dropLast）
```

つまり `Φ(k) := 「(gpow N E k).dropLast が W package」` と置くと

* `Φ(0)` = `N.dropLast` … **装備 `CtxOK N` からそのまま出る**
* `Φ(k+1)` = 文脈 `gpow N E k` にデータ `E.dropLast` を接ぎ木したもの。
  機械を回すと必要になるのは
  - データ側: `E.dropLast` の peel / 展開（`E.dropLast` は `E` より短い）
  - **文脈側の植えブロック** = `(gpow N E k).dropLast` = **`Φ(k)`** ⟸ 降下！

⟹ いままで「文脈が任意なので降下しない」と言っていた核が、生成族に限ると
**`k` について厳密に降下する**。これが `GX` の ∀ 文脈を捨てる最大の理由。

外側はデータ長（`E`, `E.dropLast`, … と 1 ずつ短くなる）、内側は `k`。
⟹ **測度 = (データ長, k) の辞書式**。§1.9.40 の「(複合列長, 添字)」を
生成族の言葉で言い直したもの。

### 次の一手

`CoreT1L` を `tower1_mem2_gpow` 経由で書き直し、`tow_mem_GX` / `GX_full` /
`CorePlantCtxLift` を通さない版を作る。そこで要るのは
「生成族 `gpow Rt ((0,v+t,z)::Rt) k` の peel が `W` package」だけ。

## 1.9.42 ⛔ v0.118.52: 生成族還元は**トートロジー**だった（§1.9.40–41 の訂正）

### 実装して分かったこと

`coreT1L_of_gpow : CoreGpowPeel → CoreT1L` は Lean で通った（sorry 0）が、
その `CoreGpowPeel` は**還元先ではなく言い換え**である。機械検査済みの同一視:

```
gpow_dropLast_eq_tow :
  (0,v,z) :: (gpow R ((0,v,z)::R) k).dropLast = tow v z R (k+1)
```

したがって

```
CoreGpowPeel  ≡  ∀ k a, 2(v+t)+z ≤ a → tow (v+t) z Rt (k+1) ∈ W a
```

であり、`CoreT1L` の結論（`A1_intro` 節 2 + `oper_cons_tower1`）は
`∀ n ≥ 1, tow (v+t) z Rt n ∈ W a`。**両者は添字のずらしだけで同値**。
`tower1_mem2_fam` / `tower1_mem2_gpow` の証明も実際 `cases k` の再添字づけ
だけで、内容を一切消費していない。

### なぜ「段の押し上げが消えた」ように見えたか

`tower1_mem2`（本物）は

* `hgr : ∀ y ∈ W m, based y → … graft R y の package`
* 内部で `ih m hvm : tow k ∈ W m` を作って `hgr` に食わせる

という構造で、`∀ y ∈ W m` の界面は**内部で自分で潰している**。
族形式はその潰した後の残差を書いただけなので、界面が「消えた」のではなく
**結論と同じものに化けた**。§1.9.39 の「リフトによる段の押し上げ」は
一切解消していない。

### 残るもの（正味の収穫）

1. `CoreGpowPeel` は α の義務の **`GX`-free・段 free な素の形**。
   「装備 `CtxOK Rt (v+t) z` のもとで塔の全段が `W` package」。
   今後の新帰納法はこの形を直接攻めればよい（`GX` の ∀ 文脈は不要）。
2. `coreGpowPeel_of_plantctx` に旧 `coreT1L_of_plantctx` の中身
   （`tow_mem_GX` + `GX_full` + `liftPlant_of_mask`）がそのまま残っており、
   **無回帰**（新形 ≤ 旧核）は機械検査済み。
3. `gpow` / `graft_iter_gpow` / `graft_tow_gpow` / `graft_gcopies_gpow` は
   「塔もコピー塊も同一の反復接ぎ木」を与える正しい補題群で、これ自体は有効。

### 教訓（メモリ soundness-discipline に追記済み）

**「界面を族形式に絞る」書き換えは、絞った先が結論と一致していないか
必ず確認する。** 一致していれば還元ではない。確認方法は今回のように
「族の subject を元の再帰の言葉に戻す等式」を Lean で書くこと。

### 次の一手（差し替え）

塔の段 `k` に関する真の帰納は、`hgr` の `∀ y ∈ W m` 界面を**保ったまま**
段 `m` を下げるか、あるいは装備 `CtxOK` から `tow k ∈ W m` を直接作るしかない。
⟹ 次は **`tow v z R k ∈ W m`（段 `m` = 末端孤児の段）を装備だけから作れるか**
を測定する。ここが取れれば `tower1_mem2` がそのまま回り、`GX` も要らない。

## 1.9.43 ★★★ v0.118.53: 核から**リフト量詞が落ちた** — 残核は `t = 0` の一本

### 証明済み（Gamma.lean / Final.lean, sorry 0, build green 782）

```
ctxOK_ltail_self : CtxOK M v z → CtxOK (ltail v z M t) (v+t) z

CorePlantCtx0 : ∀ M, argOK M → 1 ≤ |M| → ∀ v z, z ≤ 1 → CtxOK M v z →
                  (0,v,z) :: M.dropLast ∈ GX                     -- ★ リフトなし

corePlantCtxLift_of_plant0 : CorePlantCtx0 → CorePlantCtxLift
plant0_of_corePlantCtxLift : CorePlantCtxLift → CorePlantCtx0    -- 同値

TRIO_terminates_of_plant0 : InfEquip → CorePlantCtx0 → WellFounded stepRel
  #print axioms = [propext, Classical.choice, Quot.sound]
```

### 仕組み

根リフトは `ltail` で**文脈側に吸収**できる:

```
Lift1 ((0,v,z) :: M.dropLast) t = (0,v+t,z) :: (ltail v z M t).dropLast
                                                       （ltail_dropLast）
CtxOK M v z ⟹ CtxOK (ltail v z M t) (v+t) z            （ltail_take + Lift1_Lift1）
```

したがって「リフトした植え peel」は「リフトした文脈の植え peel（リフトなし）」
であり、装備クラスが `ltail` で閉じている以上 `∀ t` は**冗長**。
`selfSup_ltail` が `SelfSup` で示していたことを、核そのものに適用した形。

### 現在の残核（2 本、いずれもリフト量詞なし）

1. `CorePlantCtx0`（`GX` レベル）:
   装備つき文脈の植えた peel `(0,v,z) :: M.dropLast` が `GX` に入る。
2. `InfEquip`（`W` レベル）: 文脈の窓の再基底化中置が再び装備になる。

`CorePlantCtx0` を `GX` の定義に展開し、外側のリフトも同じ手で落とすと

```
Core0 : M, N ともに装備つき（M は根 (v,z)、N は根 (v',z')）のとき
        (0,v',z') :: graft N ((0,v,z) :: M.take i) ∈ W a'   (a' ≥ 2v'+z')
```

= **「装備つき文脈に装備つき植えブロックを植えたものが package」**。
量詞は文脈 2 本と接頭辞 `i` だけになった。

### 次の一手

`Core0` を `i` または `|N|` の帰納で回せるかを Lean で試す（外側リフトの
消去 `GX` 版を先に作る）。§1.9.42 の教訓により、還元先が結論と一致していない
ことを毎回確認する。

## 1.9.44 ★★★★★ v0.118.54: `GX` 側の核が**一列族** `[(0,b,c)] ∈ GX` に潰れた

### 発見

`gx_graft` は**無条件の合成則**である:

```
gx_graft : E ≠ [] → based E → E.dropLast ∈ GX → w ∈ GX → based w → graft E w ∈ GX
```

（文脈側の装備は `ctxOK_graft` が内部で作る。）基づく列 `y`（長さ ≥ 2）を、
末尾側 `[1,|y|)` で行 0 の深さが最小になる位置 `p` で切ると

```
y = graft (y.take (p+1)) (shiftl0 (entry y 0 p) (y.drop p))        （graft_take_drop）
```

で、文脈側の peel は `y.take p`（長さ `p < |y|`）、データ側は長さ
`|y| - p < |y|`（`p ≥ 1`）。**両方とも真に短い**ので長さの強帰納法が回り、
基底は基づく単元だけになる。

### 証明済み（Lind.lean, sorry 0, build green 783）

```
entry_drop / le_of_mem_drop / dropLast_take_succ / graft_take_drop
mem_GX_of_singletons : (∀ b c, [(0,b,c)] ∈ GX) → ∀ n y, |y| < n → based y → y ∈ GX
CoreSingleton := ∀ b c, [(0,b,c)] ∈ GX
mem_GX_of_core / corePlantCtx0_of_singleton : CoreSingleton → CorePlantCtx0
coreSingleton_of_plant0 : InfEquip → CorePlantCtx0 → CoreSingleton   （無回帰＝同値）

TRIO_terminates_of_singleton : InfEquip → CoreSingleton → WellFounded stepRel
  #print axioms = [propext, Classical.choice, Quot.sound]
```

### `CoreSingleton` の中身（`GX` を展開した素の形）

`[(0,b,c)].take i` は `i = 0` なら `[]`（= 文脈の装備そのもの、自明）、
`i = 1` なら `[(0,b,c)]`。よって

```
CoreSingleton ⟺ 装備つき文脈 M（根 (v,z), z ≤ 1）に対し
   Lift1 ((0,v,z) :: (M.dropLast ++ [(entry M 0 (|M|-1), b, c)])) t ∈ W a
                                              (a ≥ 2(v+t)+z, ∀ b c)
```

= **「装備つき文脈の末尾列の添字を任意の (b,c) に差し替えても package」**
（キャップ補題）。さらに §1.9.43 の吸収でリフト `t` も落ちる。

⟹ 残核は 2 本、どちらも量詞が最小化された:
1. `CoreSingleton`（一列キャップ, `GX` レベル）
2. `InfEquip`（窓の再基底化中置が装備, `W` レベル）

### 注意（§1.9.42 の教訓の適用）

`CoreSingleton` は `CorePlantCtx0` と（`InfEquip` を法として）**同値**であって
真の弱化ではない。しかし量詞は「∀ 装備つき文脈 + ∀ 接頭辞」から
「∀ 添字対 (b,c)」に落ちており、`2b+c` の帰納法という新しい攻め口が立つ。

### 次の一手

`CoreSingleton` を `2b+c` の帰納で攻める。`mem_GX_of_singletons` は
**y の列の添字レベルだけ**を使うので、レベル制限版
「レベル < L の列だけからなる基づく列は `GX`」が同じ証明で出る。
問題は核の証明で必要になる文脈 `M` の植え peel（`M` は任意レベル）。
ここを回避できるかが次の判定点。

## 1.9.45 ★★★★★ v0.118.55: 残核から `GX` が消えた — **キャップ補題 + InfEquip**

### 頂点（Final.lean, sorry 0, build green 783）

```
TRIO_terminates_of_cap : InfEquip → CoreCap → WellFounded stepRel
  #print axioms = [propext, Classical.choice, Quot.sound]

CoreCap : ∀ M, argOK M → 1 ≤ |M| → ∀ v z, z ≤ 1 → CtxOK M v z →
  ∀ b c a t, 2(v+t)+z ≤ a → Lift1 ((0,v,z) :: cap M b c) t ∈ W a
    where cap M b c = M.dropLast ++ [(entry M 0 (|M|-1), b, c)]
```

`graft_singleton_eq_cap : graft M [(0,b,c)] = cap M b c` と、`GX` の接頭辞義務
`i = 0` が装備そのものであることから `CoreSingleton ⟺ CoreCap`
（`coreSingleton_of_cap` / `cap_of_coreSingleton`）。

⟹ **残核 2 本はどちらも純 `W` レベル**（`GX` を含まない）:
1. `CoreCap`: 装備つき文脈の末尾添字を任意に差し替えても package
2. `InfEquip`: 文脈の窓の再基底化中置が再び装備

### 現在地の正直な評価（重要）

このセッションの 3 手（生成族、リフト量詞、長さ帰納）はいずれも**同値変形**で
あって真の弱化ではない。`CoreCap → 機械 → CoreCap` の閉路は次の通り:

* `CoreCap` ⟹（`Lind.mem_GX_of_singletons`）⟹ 任意の基づく列が `GX`
* ⟹ `CorePlantCtx0` ⟹ 三核 ⟹ `GX_closed` ⟹ `singleton_mem_GXs` ⟹ `CoreCap`

閉路が切れないのは、`GX`（および `ctxOK_graft`）が**任意の装備つき文脈**を
量化するため、どの分岐でも「文脈の植え peel が `GX`」が再生産されるから。
`Aop` の節 3 データ（段 `m`）を使うと α は閉じる（`tower1_mem2`）が、
節 2 で正当化された末端孤児つき元には節 3 データが無く、そこでは
「`W m ⊆ GX`（`m` は非有界）」＝定理自身が要る。

⟹ **量詞整理はここで打ち止め**。次に要るのは BM4 展開そのものに対する
新しい数学的入力（測度・多重集合順序・段の再設計のいずれか）。

### 記録しておく計算則（今後の入力）

* `graft N y` は `N.dropLast` と `entry N 0 (|N|-1)` にしか依らない
  ⟹ `graft (cap M b c) y = graft M y`（キャップは接ぎ木に影響しない）
* よって α 分岐の義務は `(b,c)` に依存せず「装備つき文脈 `M` 上の塔
  `tow v z M k` が `W` package」だけ
* γ' 分岐は文脈が `M.take (p+1)` に**真に短くなる**（唯一の長さ降下）

## 1.9.46 ⛔★★★★★ v0.118.56: `InfEquip` は**偽**だった／残核は 1 本になった

### 反例（Lean で機械検査済み: `Infcex.not_infEquip`, sorry 0）

`InfEquip` の結論には `entry M 2 p ≤ 1` が含まれるが、これは
`argOK M`（行 0 が正、という条件）からも装備 `CtxOK M v z` からも**出ない**。

```
M = [(1,0,2),(2,0,0)],  p = 0,  根 (v,z) = (0,0)
  argOK M ✓（深さ 1, 2 > 0）    窓条件 entry M 0 0 = 1 < 2 = entry M 0 1 ✓
  CtxOK M 0 0 ✓ — 接頭辞は [] と [(1,0,2)] だけで、リフト像は
      [(0,t,0)]（Om_mem_W）と [(0,t,0),(1,0,2)]
    後者の末尾列 (1,0,2) は行 1 が増えないため行 1 の祖先を持たず、
    UBI により行 2 の親も持たない ⟹ oper = Pred ⟹ 節 2 で W a に入る
  しかし entry M 2 0 = 2 > 1
```

⟹ `InfEquip` を仮定していた頂点定理（`TRIO_terminates_of_plant` /
`_of_plant0` / `_of_singleton` / 旧 `_of_cap`）は**すべて空虚**だった。
`coreCtxSuffixLift_of_plantctx` / `graftAll_of_plant` / `GX_loop_plant` /
`W_le_Wstar2s_of_plant` も同様。Final.lean から撤去済み、Gamma.lean の
`InfEquip` に ⛔ 注記を付けた。

### 正しい置き換え（Lind.lean, これで残核は 1 本）

`CoreCtxSuffixLift` の結論も `CorePlantCtxLift` の結論も
「**基づく列が `GX` に入る**」だけなので、長さ帰納 `mem_GX_of_core` が直撃する:

```
corePlantCtxLift_of_core   : CoreSingleton → CorePlantCtxLift
coreCtxSuffixLift_of_core  : CoreSingleton → CoreCtxSuffixLift
coreSingleton_of_cores     : CoreCtxSuffixLift → CorePlantCtxLift → CoreSingleton （無回帰）

wf_olt_ST_TS_of_core / TRIO_terminates_of_core : CoreSingleton → WellFounded stepRel
TRIO_terminates_of_cap                          : CoreCap → WellFounded stepRel
  #print axioms = [propext, Classical.choice, Quot.sound]、sorry 0、build 784
```

⟹ **トリオ停止性の残核は `CoreCap` ただ 1 本**（純 `W` レベル、`GX` 無し、
リフト量詞は §1.9.43 の吸収で落ちる）:

```
CoreCap : 装備つき文脈 M（根 (v,z), z ≤ 1）の末尾列の添字を任意の (b,c) に
          差し替えても Lift1 ((0,v,z) :: cap M b c) t は W a に入る
```

### 教訓（memory soundness-discipline に追記）

**核を新設したら、その核が真であることを（小さな具体例で）必ず検査する。**
`InfEquip` は「装備クラスの性質」に見えたが、`z<2` 断片の条件を装備から
導けると暗黙に仮定していた。`argOK` は**行 0 の条件だけ**である。

## 1.9.47 v0.118.57: 残核 `CoreCap` の健全性チェック（catch #8 の適用）

`InfEquip` の一件を受けて、**新設した核は必ず具体例で検査する**。
`W 0` は `Aop` の節 2（`∀ n, M⟦n⟧ ∈ X`）の最小不動点なので
**`W 0` = 遺伝的停止列**であり、`W` は単調。したがって `CoreCap` の
**必要条件**は「キャップした複合列が BM4 展開で停止すること」。

`tools/probe_cap.py`（縮小版, STEPS=200）:

```
case                     samples     viol
cap/z=0/c=0..2              2592×3        0
cap/z=1/c=0..2              2592×3        0
ctx/equipped                   432        0
```

⟹ 15552 インスタンス（`c = 2`、すなわち z<2 断片の外側も含む）で違反 0。
`InfEquip` のような構造的な偽は見つからなかった。

⚠ スコープの限界（catch #7）: (a) 装備 `CtxOK` は「植えた接頭辞が停止する」で
近似しており、この列サイズでは全 432 文脈が通ってしまい**フィルタが効いて
いない**。(b) 停止性は特定の `n` スケジュール（(1,1) と (1,2,3)）でのみ検査
しており、遺伝的（∀n）ではない。(c) 段（`W a` の `a`）は検査していない。
より深い検査は列長 3 以上 + `n` の全探索が要る。

## 1.9.48 ★★★ v0.118.58: 段の階層は**単元だけ**が担っている（構造的事実）

### Lean 済み: `Lind.aop_clause3_to_clause2`

`|M| ≥ 2` かつ `domT M m` なら、末尾列は親を持たないので

```
M⟦n⟧ = Pred M = M.dropLast = graft M []
```

であり、`Aop` の節 3 の `z = []` の場合がそのまま節 2 を与える。
⟹ **長さ 2 以上では節 3 は節 2 に吸収される**。

節 3 が本質的に効くのは `|M| = 1` のときだけ: `oper` は `|M| - 1 = 0` で
**恒等**（`oper M n = M`）なので単元は節 2 では絶対に `W` に入れず、
`Om_mem_W : [(0,v,z)] ∈ W (2v+z)` は節 3 経由でしか得られない。

⟹ **段 `u` の階層は根の単元 `[(0,v,z)]` が生成している。**
残核が単元核 `CoreSingleton` に落ちたことはこの構造と整合的で、
「段の押し上げ」（§1.9.39）が単元のところに集約されるのも同じ理由。

### 併せて確定した否定的知見

1. `W u` は**高レベルの死んだ孤児**を含みうる: 例 `[(0,0,0),(1,0,5)]` は
   末尾列が行 1 の祖先を持たない（⟹ UBI で行 2 の親も無い）ので
   `oper = Pred`、よって `W 0` に入る。末尾孤児の段は 4 で `u = 0` を超える。
   ⟹ `tbAll`（接頭辞の末尾孤児 < u）は `W` の性質としては**成り立たない**。
   `InfEquip` を壊したのもこの形の列である。
2. したがって「データの段 < 文脈の段」を仮定する帰納法は組めない。
3. **レベル上限つきのクラスは展開で保たれない**（コピーは行 1 に `k*d1` を
   加えるのでレベルは無制限に増える）⟹ `2b+c` による帰納法も単純には不可。

## 1.9.49 v0.118.59: 段まで見た `CoreCap` の健全性チェック（probe_cap2）

### probe_cap.py は**モデルが違っていた**（catch #7 の再発）

`tools/trio.py` の `expand` は長さ 1 の列を `[]` に落とす（`r is None` 枝）が、
Lean の `oper` は長さ 1 で**恒等**（`if j1 = 0 then M`）。したがって
正レベルの根 `[(0,v,z)]` は Lean モデルでは決して停止せず、節 3 経由で
`2v+z <= a` のときだけ `W a` に入る（`Om_mem_W`、逆も成立）。
⟹ probe_cap.py の「[] に到達するか」という判定は**別の（弱い）命題**を
測っており、段をまったく見ていなかった。

### 正しい判定（probe_cap2.py）

`aop_clause3_to_clause2`（§1.9.48）と `A1` から、長さ 2 以上では

```
S in W a  <->  forall n >= 1, S[n] in W a
```

が**厳密に**成り立ち、葉は長さ <= 1 の列だけ。よって

```
[(d,v,z)] in W a  <->  2v+z <= a
```

を葉の判定にすれば `W a` 所属の再帰的特徴づけになる。**反証条件**は
「展開木がレベル > a の単元に到達する」こと。

```
case                       count
cap/ok                      5048
cap/unknown                  136     （深さ/長さ予算切れ）
ctx/equipped                 432
VIOL                           0
```

⟹ 段を含めた形でも `CoreCap` の反例は出なかった（`InfEquip` は最小サイズで
即座に壊れたのと対照的）。unknown は ω^ω 相当の深い枝（例
`[(0,0,0),(1,0,0),(1,1,1)]`, a=0）で、深さ 8 では閉じないもの。

## 1.9.50 ★★★★★ v0.118.61: **`(WL)` 根リフトは段をちょうど `2d` 上げる**（計測）
### ＋ 階段リフト版は Lean で証明済み（核なし）

### yapss（ペア数列）との比較でわかったこと

yapss の `Wstar_closed` は**文脈なし・リフトなし・核なし**で通っている:

```
Wstar := {R | argOK R → ∀ v, (0,v) :: R ∈ W v}
```

分岐は (1) 短い (2) `natDom R`（`oper` が根の前置と可換）(3) `domT R m`:
`v ≤ m` なら塔（節 3 データ + `W_mono`）、`m < v` なら節 3 の転送。
trio が文脈・リフト・GX を必要としたのは**行 2 崩壊**（コピーが行 1 で上昇＝
データが根リフトされる）だけ。

### 計測（`tools/probe_lift.py`, `W a` の厳密特徴づけ §1.9.48 を使用）

```
minstage (Lift1 X d) = minstage X + 2*d      -- 18300 例すべてで**等号**
（違反 0、slack 0。L ≤ 3、depth ≤ 8、n ∈ {1,2}）
```

⟹ 予想 **(WL)**: `X ∈ W m → Lift1 X d ∈ W (m + 2d)`。

### ★ (WL) は行 2 塔の分岐に**ぴったり合う**

行 2 塔: 合成列 `(0,v,z) :: R` の末尾列が行 2 で根を親に持つ場合、
`w := 行1(末尾)`, `d1 = w - v`, 孤児の段 `m + 1 = 2w + 行2(末尾)`。
塔の要素は前段を `Lift1 · d1` したもの。(WL) より

```
prev ∈ W (2v+z)  ⟹  Lift1 prev d1 ∈ W (2v+z+2d1) = W (2w+z)
2w + z ≤ 2w + 行2(末尾) - 1 = m     ⟺  z < 行2(末尾)   ← 根が行 2 の親である条件そのもの
```

⟹ **段がちょうど合う**。つまり (WL) さえあれば行 2 塔は yapss の行 1 塔と同じ
形（節 3 データ + 段の単調性）で閉じ、`Wstar` にリフト量詞を入れる必要が無くなる
＝ `GraftAll` / `GX` / `CoreCap` の全体が不要になる見込み。

### 証明済み（`lean/Wslift.lean`, sorry 0）: 階段リフト版

```
slift_mem_W : Stair φ → ∀ X ∈ W m, slift X φ ∈ W (2 * φ m + m)
```

`slift_oper` (G2) で節 2 は可換に移り、節 3 は長さ 2 以上で節 2 に吸収され
（§1.9.48）、**段を上げてよい**ので長さ 1 の根も `singleton_mem_W` で通る。
⟹ `CoreStairOm`（段固定では通らない唯一の箇所）は、段を緩めれば**核ではない**。

### (WL) の証明の勘所（未着手）

`Lift1` は `oper` と**可換ではない**（計測: 1360/36936 で不一致）。不一致は
**バッドルートの親が `j0 = 0`（＝窓が根を含む）**の場合だけで、そこでは
`(Lift1 X d)⟦n⟧` は「各コピーの錐列を `d` 持ち上げたもの」になり、
`Lift1 (X⟦n⟧) d`（`X⟦n⟧` の内在錐だけ持ち上げ）より**多く**持ち上がる。
`j0 ≥ 1` と「親なし／全零」の場合は可換なので帰納で流れる。
⟹ 残るのは `j0 = 0` の場合の議論。周期マスクは階段リフトではない
（行 1 = 0 の列が持ち上がって `srow` が変わりうる）ので `slift_mem_W` では
届かない。

## 1.9.51 ★★★★ v0.118.62: マスクリフトの**厳密な段法則**を証明（核なし）

### 証明済み（`lean/Wslift.lean`, sorry 0, build 786）

```
slift_mem_W_tight : Stair φ → (∀ k, φ k ≤ k + d) → X ∈ W m → slift X φ ∈ W (m + 2d)
mlift_mem_W       : X ∈ W m → mlift X v d ∈ W (m + 2d)          -- 環境マスクリフト
```

段の上げ幅は**ちょうど `2d`**で、`(WL)`（根リフト）の計測値と同じ。長さ 1 の
根で `2 φ b + c ≤ (2b+c) + 2d ≤ m + 2d` となるのが効いている。
⟹ **データ側のリフト閉包は `W` レベルで核なしに得られる**（`GXs` の階段閉包が
段を固定していたために核に見えていただけ）。

### (WL) 残りの隙間の所在（計測で確定）

`Lift1` と `oper` の非可換は**バッドルートの親が `j0 = 0` かつ `i1 ≤ 1`**の
場合だけ:

```
i1=2/j0=0     540 例  違反 0      ← 行 2 塔（本命）は可換！
i1=2/j0>=1    972 例  違反 0
i1=1/j0>=1 / i1=0/j0>=1 / 親なし / 全零   すべて違反 0
i1=1/j0=0    1068 例  違反 712
i1=0/j0=0     972 例  違反 648
```

`j0 = 0` は「窓が根そのものを含む」場合で、`(Lift1 X d)⟦n⟧` は**各コピー**の
錐列を持ち上げるのに対し `Lift1 (X⟦n⟧) d` は `X⟦n⟧` の内在錐しか持ち上げない。

⛔ 失敗した修復案（記録）: `(Lift1 X d)⟦n⟧ = slift (X⟦n⟧) φ_v`
（`φ_v k = k + (if v ≤ k then d else 0)`, `v = entry X 1 0`）は**偽**
（v=0 で 9072/12312、v≥1 でも 10368/24624 の違反）。周期マスクは `slift` では
書けない。

### 次の一手

`i1 = 2` では可換なので、**行 2 塔の分岐だけなら (WL) は不要かもしれない**:
`(Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d` が使えるので、`Wstar3`（リフト無し）の
行 2 塔分岐を直接組む方が近道の可能性がある。まず `i1 = 2 ∨ j0 ≥ 1 ∨ 親なし`
での可換性を Lean 補題にし、(WL) をその 3 ケース＋`j0 = 0, i1 ≤ 1` に分ける。

## 1.9.52 ★★★★★ v0.118.63: **2 トラック体制の整理**と (WL) ルートの位置づけ

### trio には既に「リフト無しトラック」がある（見落としていた）

```
Wset.lean:2333  Wstar := {R | argOK R → ∀ v z a, z≤1 → 2v+z ≤ a → (0,v,z)::R ∈ W a}
Wset.lean:3877  Wstar_closed (htow : TowerOK)         -- リフト無しで閉包が通る
Wset.lean:4018  towerOK_of (h2 : TowerGraft2) (he : TowerExp) : TowerOK
Final.lean:60   no_infinite_expansion_holds (h2 : TowerGraft2) (he : TowerExp)
```

* `TowerGraft2` = 行 2 塔（節 3 データあり）
* `TowerExp`  = 塔だがデータが節 2 経由（graft closure が無い）

**現在の 2 トラック**

| | 残核 | 備考 |
|---|---|---|
| 旧: リフト無し `Wstar` | `TowerGraft2` + `TowerExp` | `Lift1` が statement に出ない |
| 新: `Wstar2s` + `GX` | `CoreCap` 1 本 | リフト閉包のために GX を建てた |

`Wstar2`（リフト閉）は `TowerGraft2` を解くために導入されたもので、そこから
`GraftAll` → `GX` → `CoreCap` の全体が生えた。**(WL) があれば `TowerGraft2` を
リフト無し `Wstar` のまま解ける見込み**なので、旧トラックに戻れる。

### `Aop` 節 2 に `natDom` ガードが無い件（設計履歴、再提案禁止）

yapss の節 2 は `natDom M ∧ ∀ n, M⟦n⟧ ∈ X` だが trio は無ガード。履歴:

* v0.79.0 ガードを外す → v0.80.0 **差し戻し**（「無ガードだと消費側に
  `M.dropLast` しか残らず塔分岐が壊れる」）＋ `tbAll` で principal block を添字づけ
* v0.86.0 再び無ガード化し `tbAll` も削除。`Wstar` を「根レベル以上の**全段**で」
  にすることで「同じ列を別の段で別の節から証明できる」ようにし、`TbOper` を削除

⟹ **無ガードは意図的な設計**。その代償が「`W u` はレベル > u の死んだ孤児を
含む」ことで、`InfEquip` を偽にしたのもこれ（§1.9.46）。設計を戻す提案は
2 回却下済みなので**再提案しないこと**。

### 推奨する次の一手（優先順）

1. `i1 = 2 ∨ j0 ≥ 1 ∨ 親なし` での `Lift1`-`oper` 可換性を Lean 補題化
   （計測では違反 0）。
2. それで `TowerGraft2` をリフト無し `Wstar` に対して証明できるか試す
   （段勘定は §1.9.50 の通り合っている。`mlift_mem_W` が使える）。
3. 通れば残核は `TowerExp` 1 本。通らなければ (WL) を `j0 = 0, i1 ≤ 1` の
   場合込みで証明する。

## 1.9.53 ★★★★★ v0.118.64: **(WL) から行 2 塔核が落ちた** — GX を通さない第 3 トラック

### 証明済み（`lean/Wtower2.lean`, sorry 0, build 787）

```
LiftStage : ∀ m d X, X ∈ W m → Lift1 X d ∈ W (m + 2*d)        -- (WL)

towerGraft2_of_liftStage : LiftStage → Wset.TowerGraft2        -- ★ リフト無し Wstar に対して
TRIO_terminates_of_liftStage        : LiftStage → TowerExp → WellFounded stepRel
no_infinite_expansion_of_liftStage  : 同上
  #print axioms = [propext, Classical.choice, Quot.sound]
```

### 何が起きたか

`towerGraft2_holds`（Wset.lean）は塔の帰納を「**すべての**リフト量 `s`」で
強めて回していた。そのために `Wstar2`（リフト閉）が必要になり、そこから
`GraftAll` → `GX` → `CoreCap` の全体が生えていた。

しかし塔が実際に消費するのは**ただ 1 つのリフト `d1 = 行1(末尾) - v`** だけで、
段の勘定は

```
prev ∈ W (2v+z) --(WL)--> Lift1 prev d1 ∈ W (2v+z+2d1) = W (2w+z) ⊆ W m
  （w = 行1(末尾)、根が行 2 の親 ⟹ z < 行2(末尾) ⟹ 2w+z ≤ m）
```

でちょうど閉じる。⟹ **`∀ s` の強化は不要**で、`Wstar`（リフト無し）のままで
`TowerGraft2` が出る。⟹ `Wstar2` / `Wstar2s` / `GraftAll` / `GX` / `CoreCap` は
**全部迂回できる**。

### 3 トラック体制（現状）

| トラック | 残核 | 状態 |
|---|---|---|
| 旧 | `TowerGraft2` + `TowerExp` | `TowerGraft2` は (WL) から出るので実質下と同じ |
| GX | `CoreCap` 1 本 | 60 版かけた機構。閉路が確定していて動かない |
| **新 (WL)** | **`LiftStage` + `TowerExp`** | (WL) は計測で**等号**、階段版は証明済み |

### 残る 2 本の性格

* `LiftStage` (WL): `W` だけの命題。階段リフト版 `slift_mem_W_tight` /
  `mlift_mem_W` は**核なしで証明済み**。残る隙間は `Lift1` が `oper` と
  非可換になる `j0 = 0 ∧ i1 ≤ 1` の場合だけ（§1.9.51）。
* `TowerExp`: 節 2 経由（graft closure なし）で来た死んだ孤児が根で復活する場合。
  無ガード節 2 の代償（§1.9.52）。`R.dropLast ∈ Wstar` しか無いので
  `W_add` の `rsum` 条件（追加ブロックが最浅）も満たせない。

### 次の一手

1. (WL) を `j0 ≥ 1 ∨ i1 = 2 ∨ 親なし` の可換性 + `j0 = 0 ∧ i1 ≤ 1` の
   個別議論に分けて証明する。`i1 = 0, j0 = 0` はコピーが同一なので
   `W_flatMap_copies` で閉じる見込み（rsum 条件は `j0 = 0` が行 0 の親である
   ことから出る）。`i1 = 1, j0 = 0` が唯一の難所。
2. `TowerExp` は別途。`R.dropLast` しか無い状況で塔を回す方法を探す。

## 1.9.54 v0.118.65: (WL) を `slift` に帰着する試みは**境界 `amin = v` で失敗**

### 何を試したか

`slift_mem_W_tight`（証明済み）で (WL) を出したい。`Lift1` を `slift` で
書ければ終わる。計算すると、基づく合成列 `X = (0,v,z) :: R` に対し

```
slift X φ = (0, φ v, z) :: 「amin R ≥ v の列を φ(v)-v だけ、
                             amin R < v の列を φ(amin R)-amin R だけ持ち上げ」
```

（頭が深さ 0 なので全列の `amin X` が `v` で頭打ちになる）。一方 `Lift1`:

```
Lift1 X d = (0, v+d, z) :: mlift R v d    （ltail_eq_mlift）
          = 「amin R > v の列だけ d 持ち上げ」   ← **strict**
```

⟹ **`amin R = v` の列で必ず食い違う**。`slift` は `amin X` しか見られないので
この境界を区別できない。⛔ 具体的な反証:

* `Lift1 X d = mlift X (v-1) d` は**偽**（argOK 尾部で 1344/2744、
  反例 `X = [(0,1,0),(1,1,0)]`, d=1: 列 1 は `amin = 1 = v` で
  `Lift1` は持ち上げないが `mlift X 0` は持ち上げる）
* `(Lift1 X d)⟦n⟧ = slift (X⟦n⟧) φ_v` も**偽**（§1.9.51）

### 副産物（証明可能な形）

`v ≥ 1` なら `φ = step (v-1) d` は `Stair` で `φ k ≤ k + d` なので

```
slift ((0,v,z) :: R) (step (v-1) d) = (0, v+d, z) :: 「amin R ≥ v を d 持ち上げ」
  ∈ W (m + 2d)          （slift_mem_W_tight）
```

が**証明できる**。`Lift1` との差は `amin R = v` の列だけ。`oper` のコピーマスクは
`le1`（＝ `amin R > v`, `ltail_eq_mlift` で確定）なので、この ≥ 版をそのまま
塔に使うことはできない。

### 現状の (WL) 攻略ルート（優先順）

1. `j0 ≥ 1 ∨ i1 = 2 ∨ 親なし ∨ 全零` での `Lift1`-`oper` 可換性を Lean 化
   （計測では違反 0）。これで (WL) は `j0 = 0 ∧ i1 ≤ 1` に限定される。
2. `i1 = 0, j0 = 0`: コピーが同一なので `W_flatMap_copies` で閉じる見込み
   （`rsum` 条件は「`j0 = 0` が行 0 の親 ⟹ 以降の列はすべて深い」から出る）。
3. `i1 = 1, j0 = 0`（行 1 塔）が唯一の難所。ここは `amin R = v` 境界の問題と
   同じ根を持つ可能性が高い。

## 1.9.55 ★★★★ v0.118.67: (WL) は「**親のある場合**」だけに縮んだ

### 証明済み（`lean/Wtower2.lean`, sorry 0, build 787）

```
Lift1_of_length_one     : |X| = 1 → Lift1 X d = [(entry X 0 0, entry X 1 0 + d, entry X 2 0)]
lift_oper_of_noParent   : 2 ≤ |X| → ¬hasParent X (srow X last) last →
                            (Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d          -- Pred 分岐は可換
LiftStageParented       : 親のある場合の (WL) 残差
liftStage_of_parented   : LiftStageParented → LiftStage
TRIO_terminates_of_parented : LiftStageParented → TowerExp → WellFounded stepRel
  #print axioms = [propext, Classical.choice, Quot.sound]
```

### なぜ縮むか

`Lift1` は行 2 を動かさず、行 1 も錐の列しか動かさない。錐の列は
`le1_entry1_lt` より行 1 が根より真に大きいので、`srow` は保たれる
（`srow_Lift1`）。`hasParent` も保たれる（`hasParent_Lift1`）。よって
`oper` の `Pred` 分岐（全零 or 親なし）はリフトと**可換**。

`Aop` の各節での使われ方:

* 節 1: 長さ ≤ 1。`Lift1` は単元をレベル `+2d` にするだけ ⟹ `singleton_mem_W`
* 節 2: 長さ ≤ 1 なら `oper` は恒等で仮定＝結論。長さ ≥ 2 は
  親なし ⟹ 可換 ✓ / **親あり ⟹ 残差**
* 節 3: `domT` ⟹ 親なし ⟹ 可換 ✓（長さ 1 は段の計算）

⟹ **残るのは節 2 の「長さ ≥ 2・末尾列に親あり」だけ**。さらに計測（§1.9.51）
より、その中でも `j0 ≥ 1` と `i1 = 2` は可換なので、真の残差は
**`j0 = 0 ∧ i1 ≤ 1`**（＝窓が根を含む行 0/行 1 の崩壊）。

### 現在の頂点定理（3 本）

```
TRIO_terminates             : TowerGraft2 → TowerExp → WellFounded stepRel   （旧）
TRIO_terminates_of_cap      : CoreCap → WellFounded stepRel                  （GX）
TRIO_terminates_of_parented : LiftStageParented → TowerExp → WellFounded stepRel （新・本命）
```

## 1.9.56 ★★★★ v0.118.68: `LiftStageParented` を 4 枝に分割（各枝の道具を確定）

### Lean（`lean/Wtower2.lean`, sorry 0, build 787）

```
LSPOn C : 親ありの残差を「末尾列のクラス C」に制限したもの
badPar X := parent X (srow X (|X|-1)) (|X|-1)
srow_cases : srow X j = 0 ∨ 1 ∨ 2

liftStageParented_of_cases :
  LSPOn (1 ≤ badPar ·) → LSPOn (badPar = 0 ∧ srow = 2)
  → LSPOn (badPar = 0 ∧ srow = 0) → LSPOn (badPar = 0 ∧ srow = 1)
  → LiftStageParented
```

### 各枝の状況（計測 §1.9.51 と既存補題の対応）

| 枝 | 計測 | 使える道具 | 状態 |
|---|---|---|---|
| `1 ≤ badPar`（`i1` 任意） | 違反 0 | `i1 = 2` は `gexp_guard_transport`（`j0` 一般）。`i1 ≤ 1` は既製補題なし | 要作業 |
| `badPar = 0, i1 = 2` | 違反 0 | `glift_eq_Lift1`（周期マスク＝内在錐）。仮定 `hup`/`hd0pos`/`hd1pos`/`hle1lp` の導出は `Wset.lean:2790-2850` が雛形 | 見通し良 |
| `badPar = 0, i1 = 0` | 違反あり（可換でない） | `d0 = d1 = 0` なのでコピーは同一。`X⟦n⟧` は `X.dropLast` の `n` 個並び、`(Lift1 X d)⟦n⟧` は `Lift1 (X⟦1⟧) d` の `n` 個並び ⟹ `W_flatMap_copies`。`rsum` 条件は `nextrel0` の no-dip 節から | 見通し良 |
| `badPar = 0, i1 = 1` | 違反あり | 行 1 塔。`graft` 閉包が無いので既製の道具なし | **難所** |

`i1 ≤ 1` では `d1 = 0` なので `Lift1 (X⟦n⟧) d` はコピー 0 の錐しか持ち上げず、
`(Lift1 X d)⟦n⟧` は各コピーの錐を持ち上げる。ここが非可換の実体である。
`i1 = 0` はコピーが完全に同一なので、可換性を経由せずに直接 `W` 所属を作れる。

### 次の一手

1. `badPar = 0, i1 = 0` を `W_flatMap_copies` で埋める（可換性は不要）。
2. `badPar = 0, i1 = 2` を `glift_eq_Lift1` の雛形で埋める。
3. `1 ≤ badPar` を `i1 = 2` と `i1 ≤ 1` に再分割し、前者を
   `gexp_guard_transport` で埋める。
4. 残る `badPar = 0, i1 = 1`（＋ `1 ≤ badPar, i1 ≤ 1`）が (WL) の真の核。

## 1.9.57 ★★★ v0.118.69: 枝 `badPar = 0, i1 = 0` を証明（4 枝のうち 1 本）

### Lean（`lean/Wtower2.lean`, sorry 0, build 787）

```
gcopy_flat / gcopies_flat : d0 = d1 = 0 のコピーは seg そのもの
oper_of_srow0_par0 : 2 ≤ |X| → hasParent … → badPar X = 0 → srow X (last) = 0 →
    X⟦n⟧ = (List.range n).flatMap (fun _ => X.dropLast)
lspOn_srow0 : LSPOn (badPar = 0 ∧ srow = 0)          ★ 証明済み
```

`i1 = 0` では `srow` の `if` が両方偽なので `d0 = d1 = 0`、つまりコピーは
**完全に同一**。したがって

```
X⟦n⟧          = X.dropLast の n 個並び        （特に X⟦1⟧ = X.dropLast）
(Lift1 X d)⟦n⟧ = Lift1 (X.dropLast) d の n 個並び   （Lift1_dropLast）
```

で、`Lift1 (X.dropLast) d = Lift1 (X⟦1⟧) d ∈ W (m+2d)` は仮定そのもの。あとは
`W_flatMap_copies` を使うだけで、**可換性を経由しない**。その `rsum` 条件
「先頭列が最浅」は `nextrel0 X 0 (|X|-1)` の no-dip 節
（`∀ j, 0 < j < |X|-1 → entry X 0 (|X|-1) ≤ entry X 0 j`）と
`entry X 0 0 < entry X 0 (|X|-1)` から出る。

### 4 枝の現状

| 枝 | 状態 |
|---|---|
| `badPar = 0, i1 = 0` | ✅ `lspOn_srow0` |
| `badPar = 0, i1 = 2` | 未（手順は下記。道具は全部そろっている） |
| `1 ≤ badPar` | 未（`i1 = 2` は `gexp_guard_transport` が `j0` 一般なので同手順、`i1 ≤ 1` は道具なし） |
| `badPar = 0, i1 = 1` | **難所**（行 1 塔） |

### 枝 `badPar = 0, i1 = 2` の手順（道具は確定済み）

示すべきは可換性 `(Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d`。`L := |X| - 1` として

1. `parent_nextR hp` を `hbp`/`hsr` で書き換えて `nextrel2 X 0 L` を得る
   （`nextR` の `if` を 2 回 `if_neg`）。
2. `hle1lp : le1 X 0 L` は `nextrel2` の第 5 連言子。
   `hd1pos : 0 < D1` は `le1_entry1_lt hle1lp`。
3. `rtg0_of_rtg1`（Aexp.lean:215）で行 1 鎖を行 0 鎖に落とし、
   `window_of_rtg0`（Lcone.lean:456）で
   `hup : ∀ l, 0 < l → l ≤ L → entry X 0 0 < entry X 0 l` を得る。
   `hd0pos`/`hd0e` は `hup L` から。
4. `oper_eq_gexp n hL hz hp hbp` ＋ `hsr` の `if_pos` 2 回で
   `hgexp : X⟦n⟧ = gexp X 0 L D0 D1 n`。同じものを `Lift1 X d` にも適用する
   （`srow_Lift1` / `parent_Lift1` / `hasParent_Lift1` で仮定を移送、
   `D0` は行 0 不変、`D1` は `0` と `L` がともに錐にいるので不変）。
5. 残るのは `gexp (Lift1 X d) 0 L D0 D1 n = Lift1 (gexp X 0 L D0 D1 n) d` の
   成分計算。行 0・行 2 は不変、行 1 は
   `entry1_Lift1` ＋ `le1_Lift1` ＋ **`gexp_guard_transport`**
   （コピー位置 `k*L+q` の錐 ⟺ 窓位置 `q` の錐）で一致する。
   `glift_eq_Lift1`（Wset.lean:2716）の証明がこの成分計算の雛形。

## 1.9.58 ★★★★ v0.118.71: 枝 `badPar = 0, i1 = 2` も証明（4 枝のうち 2 本）

### Lean（`lean/Wtower2.lean`, sorry 0, build 787）

```
getElem_eq_getD'      : 補助
gexp_lift_eq_glift    : gexp (Lift1 X d) 0 L D0 D1 n = glift X L 0 d (gexp X 0 L D0 D1 n)
                        ← D0, D1 を固定した**純粋な成分計算**（gexp_getD_mir + le1_Lift1）
lspOn_srow2 : LSPOn (badPar = 0 ∧ srow = 2)     ★ 証明済み
```

### 筋

1. `nextrel2 X 0 L` から `hcone : le1 X 0 L`、`hd1pos`（`le1_entry1_lt`）。
2. `rtg0_of_rtg1` ＋ `window_of_rtg0` で `hup`、そこから `hd0pos` / `hd0e`。
3. `oper_eq_gexp` を `X` と `Lift1 X d` の両方に適用（`srow_Lift1` /
   `parent_Lift1` / `hasParent_Lift1` で仮定を移送。`D0` は行 0 不変、
   `D1` は `0` と `L` がともに錐にいるので不変）。
4. `gexp_lift_eq_glift` で「リフトしてから展開」＝「展開してから周期マスク」。
5. `glift_eq_Lift1` で周期マスク＝内在錐（ここで `0 < d0` と `0 < d1`、
   すなわち**行 2 崩壊**が効く）。⟹ 可換性 `(Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d`。

### 4 枝の現状

| 枝 | 状態 |
|---|---|
| `badPar = 0, i1 = 0` | ✅ `lspOn_srow0`（`W_flatMap_copies`、可換性不要） |
| `badPar = 0, i1 = 2` | ✅ `lspOn_srow2`（可換性） |
| `1 ≤ badPar` | 未。`i1 = 2` は `gexp_guard_transport` が `j0` 一般なので同じ筋。`i1 ≤ 1` は道具なし |
| `badPar = 0, i1 = 1` | **難所**（行 1 塔） |

⟹ 次は `1 ≤ badPar` を `i1 = 2` と `i1 ≤ 1` に割り、前者を `lspOn_srow2` と
同じ手順（ただし `j0` 一般の `gexp_getD_mir` / `gexp_guard_transport`）で埋める。
`glift` は `j0 = 0` 専用（`idx % L` が窓位置）なので、一般 `j0` 版の周期マスクを
定義するか、`gexp_guard_transport` から直接組む必要がある。

## 1.9.59 ★★★ v0.118.72: 枝 `badPar = 0, i1 = 1` の正体は**塔の接ぎ木漸化式**

### 計算

`i1 = 1` では `d1 = 0`、`d0 = entry X 0 L - entry X 0 0 > 0` なので

```
gcopy X 0 L d0 0 k = shiftr01 (k*d0) 0 (seg X 0 L)      （行 1 は動かない）
X⟦n⟧ = flatMap_{k<n} shiftr01 (k*d0) 0 X.dropLast        （深さ増加のコピー並び）
```

`X` が based（`entry X 0 0 = 0`）なら `d0 = entry X 0 L` なので

```
graft X z = X.dropLast ++ shiftr01 (entry X 0 L) 0 z = X.dropLast ++ shiftr01 d0 0 z
⟹ X⟦n+1⟧ = X.dropLast ++ shiftr01 d0 0 (X⟦n⟧) = graft X (X⟦n⟧)
```

すなわち **`badPar = 0, i1 = 1` の展開は塔の接ぎ木漸化式そのもの**
（`oper_cons_tower1` / `tow` と同じ形）。`Lift1 X d` も based なので同様に
`(Lift1 X d)⟦n+1⟧ = graft (Lift1 X d) ((Lift1 X d)⟦n⟧)`。

⟹ この枝を `n` の帰納で回すには **`graft (Lift1 X d) Y ∈ W (m+2d)`**（Y は
前段）が要る。これは接ぎ木閉包そのもので、仮定
「`Lift1 (X⟦n⟧) d ∈ W (m+2d)`」からは出ない。

### 帰結: 2 本の残核は**同じ現象**

* (WL) の残り枝 `badPar = 0, i1 = 1` … 行 1 塔の接ぎ木閉包
* `TowerExp` … 節 2 経由で来た死んだ孤児が根で復活する行 1/行 2 塔

どちらも「`R.dropLast` しか手元に無い状態で塔を回す」形であり、
`Wstar` の graft 閉包（＝ 旧 `GraftAll`）の核と同一の現象と見てよい。
⟹ **新トラックの真の残核は 1 つ**（行 1 塔の接ぎ木閉包）に集約される見込み。

## 1.9.60 ⚠ v0.118.73: 訂正 — `1 ≤ badPar` は「同じ筋」では通らない

§1.9.57/1.9.58 で「`1 ≤ badPar` の `i1 = 2` は `gexp_guard_transport` が `j0`
一般なので同じ筋」と書いたが、**これは誤り**。可換性に要るのは
`Lift1 (X⟦n⟧) d` の側、すなわち **`X⟦n⟧` の添字 0 からの錐**である。ところが

```
gexp_guard_transport : le1 (gexp M j0 Lb d0 d1 n) j0 (j0 + (k*Lb+q)) ↔ le1 M j0 (j0+q)
```

が与えるのは **`j0` からの錐**であって、`0` からの錐ではない。`j0 ≥ 1` では
両者は一致しない（`0` の錐に入るが `j0` を経由しない列がありうる）。
`glift`／`glift_eq_Lift1` が `j0 = 0` 専用なのも同じ理由。

⟹ `1 ≤ badPar` には**新しい輸送補題**（コピー塊での「添字 0 からの錐」の
特徴づけ）が要る。計測では違反 0 なので命題自体は正しい見込み。

### 残作業（新トラック）— v0.118.77 で 1 枝に

1. ✅ `1 ≤ badPar`（全 `i1`）: **落ちた**（v0.118.75-77, `lspOn_pos`）。
   鍵は「窓の行 0 値は根より真に大きい（`hup`）ので、行 0 の鎖は窓に入る前に
   必ずバッドルートを通る」という切断補題 `rtg0_split_at`。これで
   `le1_iff_chain_window` の前提（`rtg0` の存在）が両側で対応づき、
   `Lcone.gexp_cone_mir` / `gexp_cone_mir_flat` が要求していた
   「根が厳密に最浅」`hr0` を落とせる（`LSPOn` は `W` の任意の元に対する
   主張なので `hr0` は使えない）。
   - 上昇枝（`i1 ≥ 1`, `d0 > 0`）: `gexp_cone0_transport`。ガードが立った
     位置は `le1 M j0 ·` から行 1 値が既に `entry M 1 j0` を超えるので、
     乗るリフト `k*d1` は不等式を壊さない。
   - 平坦枝（`i1 = 0`, `d0 = d1 = 0`）: `gexp_cone0_flat`。切断点は `j0` では
     なく**コピー `k` の根**。`Lcone` の平坦補題（`nextrel0_flat_root` /
     `gexp_flat_chain_inversion` / `gexp_flat_rtg0_low`）をそのまま使う。
   - 可換性は `gexp_Lift1_comm_of_transport` に一本化（錐輸送を仮定として
     受け取り、上昇版・平坦版の 2 系にする）。
2. `badPar = 0, i1 = 1`: 塔の接ぎ木漸化式（§1.9.59）。**真の核、唯一の残り**。
3. `TowerExp`: 2 と同じ現象（§1.9.59）。

`Final.lean` の到達点: `TRIO_terminates_of_srow1 (hs1 : LSPOn (badPar = 0 ∧
srow = 1)) (he : TowerExp) : WellFounded stepRel`（公理は
`[propext, Classical.choice, Quot.sound]` のみ）。

## 1.9.61 ★★★ v0.118.75-79: 残差が **(TOW)/(CAT) + TowerExp2** の 2 本になった

### 済んだこと

1. **`1 ≤ badPar` の枝が完全に落ちた**（v0.118.75-77）。
   鍵は切断補題 `rtg0_split_at`:「窓 `(j0, j0+Lb]` の行 0 値は根より真に大きい
   （`hup`）ので、行 0 の鎖は窓に入る前に必ず `j0`（平坦枝ではコピー `k` の根）を
   通る」。これで `le1_iff_chain_window` の前提が両側で対応づき、
   `Lcone.gexp_cone_mir` / `gexp_cone_mir_flat` が要求していた「根が厳密に最浅」
   `hr0` を外せる（`LSPOn` は `W` の任意の元についての主張なので `hr0` は無い）。
   - 上昇枝 `gexp_cone0_transport`（`d0 > 0`）／平坦枝 `gexp_cone0_flat`（`i1=0`）
   - 可換性は `gexp_Lift1_comm_of_transport` に一本化
2. **最後の枝 `badPar=0, i1=1` と `TowerExp` の行 1 部分が同じ形に落ちた**
   （v0.118.78）。`i1 = 1` では `d1 = 0` なので展開は行 0 ずらしコピー塔:

   ```
   oper_of_srow1_par0 :  X⟦n⟧ = shTower X.dropLast (entry X 0 j1 - entry X 0 0) n
   shTower Q e n      = ⧺_{k<n} shiftr01 (k*e) 0 Q
   ```

   `Lift1` は行 0 を動かさないので `(Lift1 X d)⟦n⟧ = shTower (Lift1 X.dropLast d) d0 n`。
   **仮定 `hop` は `n = 1` でしか使わない**（`X⟦1⟧ = X.dropLast`）。よって

   ```
   (TOW)  Q ∈ W u → （根が最浅）→ shTower Q e n ∈ W u        [ShiftTowerClosed]
   ```

   に還元。`TowerExp` も `domT R m` から `R⟦n⟧ = Pred R = R.dropLast` なので
   同じく `n = 1` だけで足り、行 1 部分は `(TOW)` に落ちる（`towerExp1_of_tower`）。
3. **`(TOW)` の候補上位 `(CAT)`**（v0.118.79）。`W_add` の `rsum`
   （`B` の根が最浅）は `XA_closed` の**証明**の都合であって、塔ではちょうど逆
   （後半が最深）。仮定なしの

   ```
   (CAT)  A ∈ W u → B ∈ W u → A ++ B ∈ W u                    [WCat]
   ```

   は `tools/probe_cat.py` で 372290 例（短列全数 + 長列ランダム + ST_TS 由来）
   違反 0、判定を `n ∈ {1,2,3}` に上げた再計測でも 28065 例違反 0。
   `W_shift` と合わせて `(TOW)` は 2 行（`shiftTowerClosed_of_cat`）。

### 到達点（`Final.lean`、公理は `[propext, Classical.choice, Quot.sound]`）

```
TRIO_terminates_of_srow1 (hs1 : LSPOn (badPar=0 ∧ srow=1)) (he : TowerExp)
TRIO_terminates_of_tow   (htow : ShiftTowerClosed) (h2 : TowerExp2)
TRIO_terminates_of_cat   (hcat : WCat)             (h2 : TowerExp2)
```

### `(CAT)` の証明がどこで詰まるか（次に攻める場所）

`A ++ B` のバッドルートが `B` の中にある場合は易しい:
`hasParent B (srow B (|B|-1)) (|B|-1)` なら `hasParent_append_right_of` と
`le0/le1_append_right` から `(A++B)⟦n⟧ = A ++ B⟦n⟧` が出るはず（`rsum` 不要の
`oper_append_gen`。未実装、機械的で ~80 行）。

**詰まるのは `B` の末尾が `B` の中では孤児なのに `A` から親を貰う場合**で、
このとき `(A++B)⟦n⟧ = A.take j0 ++ （`A.drop j0 ++ B.dropLast` のコピー塔）`
となり、`A` は短くなるがコピーは伸びる。これは `TowerExp` と同じ「文脈が死んだ
孤児を復活させる」現象であり、`(CAT)` は少なくとも `TowerExp` と同程度に難しい。

### v0.118.81: `(CAT)` は **1 列の追加 `(SNOC)`** に落ちる

`Xbar.oper_append_inner`（`rsum` も根条件も無い既存補題）

```
(AP)  T ≠ [] → |T|-1 ≠ 0 → hasParent T (srow T (|T|-1)) (|T|-1)
      → (A ++ T)⟦n⟧ = A ++ T⟦n⟧
```

を使って `{B | A ++ B ∈ W u}` の上で A2' を回すと、`Aop` の全節が 1 列追加に落ちる:

| 節 | 処理 |
|---|---|
| 節 2・`B` に親あり | (AP) + `mem_of_oper_mem` |
| 節 2・`B` 末尾が孤児 | `B⟦n⟧ = Pred B = B.dropLast`、`A ++ B = (A ++ B.dropLast) ++ [末尾]` |
| 節 3 | `graft B [] = B.dropLast` で同上 |
| 節 1 | `B = []` 自明 / `B = [p]` は 1 列追加 |

追加列が `C ++ [p]` でも孤児なら展開は `Pred` なので**ただ**（`snoc_step` で処理済み）。
残るのは

```
(SNOC)  C ∈ W u → C ≠ [] → hasParent (C ++ [p]) (srow (C++[p]) |C|) |C|
        → C ++ [p] ∈ W u          [WSnoc, wcat_of_snoc : WSnoc → WCat]
```

＝「**親を見つける 1 列を足しても段は上がらない**」。計測 `tools/probe_snoc.py`:
14455 例違反 0（孤児側の対照 34507 例違反 0）。`p` のレベル上限では言い換え
られない: `C = [(0,0,0)]`, `p = (1,5,0)` は `lev p = 10` だが `C ++ [p] ∈ W 0`
（親が付くと `C` の窓の塔になる）。

到達点: `TRIO_terminates_of_snoc (hsn : WSnoc) (h2 : TowerExp2) : WellFounded stepRel`

### v0.118.83: `(SNOC)` の自由な断片と、`TowerExp2` についての firm な否定

**自由な断片（証明済み `snoc_flat_root`）**: `i1 = 0` かつ `j0 = 0` なら
コピーは `C` そのものなので `W_flatMap_copies` で無条件に閉じる
（`C` の根が最浅なのは `C` の根が `p` の行 0 の親だから＝ no-dip 節）。
残るのは `j0 ≥ 1`（接頭辞が残る）と `i1 ≥ 1`（コピーが持ち上がる）。

**`(SNOC)` は簿記ではなく本物の停止性を含む**: 節 1 の基底
（`C = [q]`, `lev q = 0`）ですら `M⟦n⟧ = [(a+k*d0, k*d1, 0)]_{k<n}` という
**対角列**であり、これが `W u` に入ることは 1 行／2 行（原始・ペア）数列の
停止性そのものである。したがって `(SNOC)` に「量詞整理」で到達することは
できず、yapss 型の議論の移植か新しい数学が要る。

### ⛔ `TowerExp2` は `(CAT)` からは**原理的に**出ない（v0.118.83 確認）

`TowerExp2` の消費点は `hgr : ∀ y ∈ W m, based y → graft R y ∈ Wstar` で、
`Wstar` は「**任意に小さい根** `(0,v',z')`（`2v'+z' ≤ a'`）の下に植えられる」
ことを要求する。`graft R y = R.dropLast ++ shiftr01 c 0 y` なので `(CAT)` で
繋ぐには `y ∈ W a'` が要るが、実際には `y ∈ W m` で `2v+z ≤ m`、つまり
**データの段のほうが結果の段より高い**。`(CAT)` は段を保つだけなので、この
崩壊（高い段のデータを低い根の下で捕まえる）は `Aop` 節 3 でしか起きない。

⟹ `TowerExp2` を消すには **`Aop` 節 2 に `natDom` ガードを戻す**（孤児は節 3
経由しか許さない）か、GX トラックの機構が要る。ガードを戻したときに壊れる
3 箇所（`Wslift:88/138`, `Wtower2:129`）は **`(CAT)` があれば修復できる**:

```
目標 Lift1 X d ∈ W (m+2d) を節 3 で:
  domT (Lift1 X d) m''、m'' ≤ m' + 2d、節 3 より m' < m ⟹ m'' < m+2d
  graft (Lift1 X d) z = Lift1 (X.dropLast) d ++ shiftr01 c 0 z
    前半: 節 3 のデータを z = [] で（graft X [] = X.dropLast）
    後半: z ∈ W m'' ⊆ W (m+2d)（W_mono）→ W_shift
    (CAT) で連結
```

⚠ ただしガード付き `W` は今の probe 道具では**決定できない**（節 3 が
`∀ z ∈ W m` を含む）ので、`(SNOC)`/`(CAT)` の測定証拠が使えなくなる。
⟹ **順序は `(SNOC)` を証明 → `(CAT)` が定理 → その後でガード復活**が安全。

### v0.118.84: 還元は打ち止め — なぜ `(SNOC)` に強度が全部集まったか

**(a) すべての枝が `(SNOC)` に合流することを確認した。**
`(TOW)` を `Q` への A2' で回すとキャップ版 `(TOW')`
（`∀ Y ∈ W u, shTower Q e n ++ shiftr01 (n*e) 0 Y ∈ W u`）が要り、
その内側 A2'（`Y` について）は

```
Y に親あり  : oper_append_inner で (T_n ++ shift Y)⟦j⟧ = T_n ++ shift (Y⟦j⟧)  → IH
Y が孤児     : Y⟦j⟧ = Y.dropLast、T_n ++ shift Y = (T_n ++ shift Y.dropLast) ++ [末尾] → snoc
Y = []       : T_n ∈ W u   ← n の外側帰納法で供給できる
```

となり、**孤児枝と節 1 がちょうど `(SNOC)` になる**。`wcat_of_snoc` はこれの
一般形なので、新しい還元は出てこない。

**(b) `(SNOC)` は簿記ではない。** 節 1 の基底（`C = [q]`, `lev q = 0`）ですら
`M⟦n⟧ = [(a + k*d0, k*d1, 0)]_{k<n}` という対角塔で、これが `W u`（`u` は小さい）
に入ることは 1 行／2 行数列の停止性そのもの（`d1 = 0` なら原始数列 = ε_0 強度）。
`W u` は最小不動点なので、そのような元は超限的な導出をもつ。
⟹ 「量詞整理」で `(SNOC)` に到達することはできない。**新しい数学が要る**。

**(b2) ★ `(SNOC)` は yapss の定理を含む。** 節 1 の基底で `i1 = 2` を取ると
`M = [(a,0,0), (b,w,1)]`（`nextrel2 M 0 1` は `0 < w` と `0 < z` を要求する）で

```
M⟦n⟧ = [(a + k*d0, k*w, 0)]_{k<n}      -- 行 2 が 0 の 2 行対角列
```

これが小さい段の `W u` に入ることは**ペア数列の停止性そのもの**、すなわち
lean-yapss の定理全体である。⟹ `(SNOC)` を直接証明する道は「yapss を trio の
中でやり直す」ことに等しく、trio の証明が yapss より短くなることはない。
これは想定どおりで矛盾ではないが、**`(SNOC)` を核として直接攻めるのは筋が悪い**
ことを意味する。

**(c) yapss が核なしで通る理由（設計上の差）。** yapss の `Wstar` の界面は
**前置**（`(0,v) :: R`）であり、前置は `oper_append_inner` が素通しする。
trio が `(SNOC)`（**後置**＝列の追加）に到達したのは、行 2 崩壊のために周囲リフト
`Lift1` を導入し、(WL) の残差が塔になったからである。

⟹ 次の研究上の問い: **trio の行 2 の扱いを「前置だけの界面」に書き直せるか**
（`Lift1` を根の前置で置き換えられるか）。これができれば (WL) も `(SNOC)` も
要らなくなる可能性がある。できないなら、`(SNOC)` を対角塔の停止性から直接
組み上げるしかない。

**(d) 捨てた仮定の記録**: `lspOn_srow1_of_tower` は `hop` を `n = 1` でしか
使っていない。`hop n`（全 `n`）は `Lift1 (shTower Q0 d0 n) d ∈ W (m+2d)` を
与えるので、真の隙間は「塔の**内在錐**リフトから**周期マスク**リフトへ」である
（`i1 = 2` では `glift_eq_Lift1` で両者が一致する。`i1 = 1` は `d1 = 0` ゆえ
コピーの根が錐に入らず一致しない）。より弱い核を立てるならこの形。

### v0.118.87: 「前置だけの界面」は⛔、だがガード復活が (CAT) 抜きで**ほぼ**通る

**(A) ⛔ 前置だけの界面は不可能（計測 `tools/probe_prepend.py`）。**
行 2 塔ホスト 2352 本・9408 インスタンスで

```
0 錐が根だけ {0}          507 / 9408
0 錐が前置切片            5032 / 9408（うち全体 4128）
0 錐が非前置             4376 / 9408   例: [0,2,4,6]（コピー根の周期）
平均錐サイズ / 平均長      5.44 / 7.30
```

⟹ `Lift1` は根だけを動かすわけでも前置を動かすわけでもなく、**行 1 の祖先鎖**
（塔では周期的）を動かす。`Lift1 (based Y) d = (0, v+d, z) :: mlift (tail) v d`
なので尾部に環境マスク `mlift` が残り、yapss 型の前置界面では表せない。
⟹ (WL) は trio に本質的。この選択肢は閉じた。

**(B) ★ ガード復活の 3 箇所は `Cgraft.lift_graft_cone` で (CAT) 抜きに通る（1 例外）。**

```
lift_graft_cone : 2 ≤ |E| → based A → (A の非根が深い) → HighPar A (entry E 1 0) →
  Lift1 (graft E A) d
    = graft (Lift1 E d) (if le1 (graft E A) 0 (|E|-1) then Lift1 A d else A)
```

ガード下で `Lift1 X d ∈ W (m+2d)` を節 3 で通すには
`∀ z ∈ W m'' based, graft (Lift1 X d) z ∈ W (m+2d)` が要る。ここで `m''` は
`domT (Lift1 X d) m''` から**末尾列の `lev` で決まる**:

* 末尾列が 0 錐に**入らない**なら `m'' = m'`。このとき `lift_graft_cone` の
  `if` は偽側なので `graft (Lift1 X d) z = Lift1 (graft X z) d` となり、
  節 3 のデータ `hgr z`（`z ∈ W m'`）がそのまま効く。**(CAT) 不要**。
* 末尾列が 0 錐に**入る**なら `m'' = m' + 2d` で、要求されるデータ類が
  `W (m'+2d)` に膨らむ。`lift_graft_cone` が作れるのは `Lift1 A d`（`A ∈ W m'`）
  の形だけなので届かない。⛔

**例外ケースの正体**: `domT X m'` かつ末尾列が 0 錐に入る、は
`srow X last = 1` では**起きない**（行 1 の鎖が末尾に届けば `hasParent X 1 last`
になり `domT` と矛盾）。起きるのは `srow X last = 2` かつ `le1 X 0 last` の場合で、
これは `entry X 2 0 ≥ entry X 2 last ≥ 1`、すなわち **`X` の根の行 2 が 1** を要する。
塔の段 `M⟦j⟧ = (0,v,z) :: …` では `z = 1` のときだけ。

⟹ 次の一手: **`z = 0` に制限した (WL) でガード復活が閉じるか**、あるいは
`z = 1` の例外を別扱いできるかを調べる。ここが通れば `TowerExp` が丸ごと消え、
残差は `(SNOC)` 1 本になる。

### v0.118.88: ★ 最終設計 — ガード復活で残差は `(SNOC)` **1 本**になる

**確実な事実**: `natDom R := ∀ m, ¬ domT R m` なので `domT R m0` は
`¬ natDom R` を**定義から**与える。したがってガードを戻すと
`towerOK_of` の節 2 分岐（`hop`）は `hdR : ∃ m0, domT R m0` と両立せず
**空虚**になる ⟹ **`TowerExp` / `TowerExp1` / `TowerExp2` は丸ごと消える**。

ガード後の trio の残差構造（yapss と同型）:

```
TowerOK の分岐   節1        : W_flatMap_copies                      ✅ free
                 節2        : ガードで空虚                          ✅ 消滅
                 節3 srow=1 : tower1_mem（hgr を使う）              ✅ 証明済み
                 節3 srow=2 : TowerGraft2 ⟸ (WL)                    ← 行 2 固有
(WL) の 4 枝     1<=badPar / badPar=0,i1∈{0,2}                      ✅ 証明済み
                 badPar=0,i1=1                                      ⟸ (SNOC)
ガードの修復     末尾列が 0 錐の外（srow=1 は自動）: lift_graft_cone ✅ (CAT) 不要
                 例外（srow=2 かつ根の行2=1）                        ⟸ (CAT) ⟸ (SNOC)
```

⟹ **すべてが `(SNOC)` 1 本に集まる**。yapss に `(SNOC)` が現れないのは行 2 が
無いからで、`(SNOC)` は **trio の行 2 固有の内容**である（ただしその節 1 基底は
行 2 が 0 の対角塔なので、ペア数列の事実を含む — それは trio 側の行 1 塔
`tower1_mem` が既に担っている部分と重なる）。

**実測したリファクタ規模（v0.118.88、その場で適用して計測・revert 済み）**:
`Aop` 節 2 に `natDom M ∧` を足しただけで **`Wset.lean` 単独で 41 エラー**。
下流（`Wchar` / `Wslift` / `Wtower2` / `Gamma` / `Core` / `Infcex` / `Lind`）は
Lean がそこで止まるので未到達。エラーは規則的なペアで機械的:

```
"Application type mismatch" + "No goals to be solved"  … 節 2 の導入
    （Or.inr (Or.inl (fun n hn => …)) → ⟨natDom 証明, fun n hn => …⟩）  約 20 組
"Function expected at"                                  … 節 2 の分解
    （rcases … | hop | … の hop が対になる）                約 6 箇所
Wset.lean:4038 は towerOK_of の節 2 分岐 = **空虚化して消える箇所**（狙いどおり）
```

⟹ 全体で 150〜300 箇所の修正が見込まれる。1 セッション分の作業。

**次セッションの主タスク（設計は確定、作業は機械的）**:
1. `Aop` 節 2 に `natDom M ∧` を戻す（`Wset.lean`）。
2. 節 2 導入 23 箇所 + `mem_of_oper_mem` 7 箇所に `natDom` を供給する。
   `Wchar.mem_iff_oper_mem` は `natDom` 付きの条件付き版になる。
3. 壊れる 3 箇所（`Wslift:88/138`, `Wtower2:129`）を `lift_graft_cone` で修復
   （末尾列が 0 錐の外の場合）。例外ケースは `(CAT)` を仮定として残す。
4. `TowerExp*` と `towerExp_of_rows` 系を撤去、`Final.lean` を配線替え。
⚠ ガード付き `W` は probe で決定できないので、(SNOC) の測定証拠は
**ガード前の `W`** についてのものであることを明記して持ち越すこと。

### ⚠ 健全性の注意: `(CAT)` / `(TOW)` は定理の**下流**でもある

`mem_W_maxlev`（A 閉集合 `S` を法として）は `zle1 M → M ∈ W (maxlev M)` を与え、
`maxlev (A ++ B) = max (maxlev A) (maxlev B)` なので、**完成した定理から
`zle1` 列についての `(CAT)` は出る**。したがって `(CAT)`/`(TOW)` は
「定理より小さい命題」ではなく、`corePlantCtxLift_of_self` と同じ
「還元だけでは閉じない」型である。今回の前進は**閉包ではなく形の単純化**
（4 枝 + `TowerExp` ⟹ 2 本の素朴な命題）であって、証明そのものではない。

### `TowerExp2` は `(CAT)` からは出ない（確認済み）

行 2 崩壊のコピー `k` は行 1 が `k*d1` 上がるので、単体では段
`2(v + k*d1) + z` を要求し `W a` に入らない。したがって「`W a` の元の連結」の
形にならない。`TowerExp2` は `Aop` 節 3 が担う本来の崩壊であり、別核として残る。

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

## 4.4 ★★ 残差は `(SNOC)` 1 本になった（v0.118.94）

```
TRIO_terminates_of_snoc : WSnoc → WellFounded stepRel
  axioms = [propext, Classical.choice, Quot.sound],  sorry 0,  build 787
```

### 見落としていたこと: `TowerExp` は**そのまま snoc**

`TowerExp2` が `(CAT)` から出ないのは正しいが、**`(SNOC)` からは直接出る**。
`(SNOC)` は「文脈から親を貰う 1 列の追加」なので、まさに `TowerExp` の状況
（死んだ孤児が根で復活する）そのものだった。

```
Wtower2.towerExp_of_snoc (hsn : WSnoc) : Wset.TowerExp
```

証明（`Wtower2.lean` 末尾、~20 行）:

* `domT R m` ⟹ `R⟦1⟧ = graft R [] = R.dropLast`
  （`oper_eq_graft_nil_of_domT` + `graft_nil`）
* 節 2 のデータ `hop 1` は `R.dropLast ∈ Wstar`、これを `(v,z,a)` に当てて
  `C := (0,v,z) :: R.dropLast ∈ W a`
* `C ++ [R.getLast] = (0,v,z) :: R = M`（`List.dropLast_append_getLast`）
* `snoc_step hsn` で `M ∈ W a`、`oper_closed` で `M⟦n⟧ ∈ W a`
* `|R| = 1` の場合は `R.dropLast = []` で `C = [(0,v,z)]`、`Om_mem_W` + `W_mono`
* **`hpM` は不要**（`snoc_step` が孤児側も処理済み）

### なぜ `(CAT)` では届かなかったか

`(CAT)` は両辺が `W a` に居ることを要求する。`TowerExp` で追加される列は
レベルが幾らでも高く（`m+1 = 2w+z'`）、**文脈から親を貰うことではじめて無害になる**。
`(SNOC)` はその「親を貰う」を条件に持つので一段強い。

### 統一核の計測（`tools/probe_ltow.py`）

両残差が生む対象は同じ「リフト付きコピー塔」:

```
(LTOW)  X ∈ W u → concat_{k<n} shiftr01 (k*d0) 0 (Lift1 X (k*d1)) ∈ W u
        側条件: X は based、非根列の深さ ≥ d0（no-dip）
```

計測 12920 例 0 違反（うち `d1 > 0` が 7806）。`d1 = 0` が `(TOW)`、
`j0 = 0` の文脈付き版が `TowerExp2`、一般の `j0` が `(SNOC)`。
`TowerExp2` 自体も 1330 例 0 違反（`tools/probe_towerexp2.py`、未判定 2336）。

### ⚠⚠ 但し書き: `(SNOC)` は**強すぎる**（強さのトレードオフ）

1 本化は**表示の統合**であって強さの削減ではない。`(SNOC)` は
**ペア数列の停止性を含む**:

```
節 1 の基底: C = [(d,0,0)] ∈ W 0,  p = (d', w, 1)（根が行 2 で親になる）
  ⟹ (C ++ [p])⟦n⟧ = [(d + k*(d'-d), k*w, 0)]_{k<n}   -- 行 2 が 0 の対角列
  ⟹ これが W 0 に入る ⟺ ペア数列の停止性（lean-yapss の定理全体）
```

一方 **`(CAT)` はペア定理を含まない**: `(CAT)` は**両辺が `W u` に居る**ことを
要求するので、レベルを上げる列を新たに作れない。実際
`[(0,0,0),(1,1,0),(2,2,0)]` を `W 0` の 2 つの連結として書こうとすると
`[(2,2,0)] ∈ W 4` が要り、`u = 0` では不可能。
`(SNOC)` が**任意のレベルの列を 1 本追加できる**のが強さの差。

⟹ **2 つの提示を両方残す**（`Final.lean` に両方ある）:

| 定理 | 核 | 性質 |
|---|---|---|
| `TRIO_terminates_of_cat (hcat : WCat) (h2 : TowerExp2)` | 2 本 | `(CAT)` は**ペア定理を含まない**（狭い） |
| `TRIO_terminates_of_snoc (hsn : WSnoc)` | 1 本 | `(SNOC)` は**ペア定理を含む**（広い） |

**ペア定理の содержание は `TowerExp2` に集中している**:
`TowerExp2` の `|R| = 1` 基底は `M = [(0,v,z), q]`（`srow q = 2`）で
`M⟦n⟧ = [(k*d0, v + k*d1, z)]_{k<n}`、`z = 0` ならこれがペア対角列。
`TowerGraft2` は接ぎ木データがあるので `hgr` が吸収する（ペア定理を含まない）。

### ⟹ 次の具体的タスク

```
(PAIR)  zle0 S → entry S 0 0 = 0 → lev S 0 = 0 → S ∈ trio.W 0
        「根の添字が 0 の、行 2 が 0 の based ブロックはすべて W 0」
```

これは trio 内では循環するが、**lean-yapss の
`PSS_terminates_unconditional` からは出る**（整礎帰納法 + 「based ブロックの
展開の終端は根」）。行 2 が 0 のブロックでは trio の `oper` は
yapss の `oper` と一致する（`t = max{y | S_(X-1)y > 0} ≤ 1`）。

* 移植の要点: `PairSeq → TrioSeq` の埋め込みが `oper` と可換、
  `yapss.W v ⊆ trio.W (2v)`、そして `yapss` 側で `W 0` 版を作る
* ⚠ 注意: 行 2 が 0 のブロックに限れば **`natDom` ガードは健全**
  （反例 `(x,0,1)` は行 2 を使う）。yapss の証明が核なしで通るのはこのため。

### 残差の性質

`W 0` は「遺伝的に停止する列」そのもの（`[(d,v,z)] ∈ W a ⟺ 2v+z ≤ a`、
`|S|≥2` では `S ∈ W a ⟺ ∀n, S⟦n⟧ ∈ W a`）。よって **`(SNOC)` の `u = 0` 事例は
停止性定理そのもの**で、さらに小さい命題への還元では閉じない。
`(SNOC)` の節 1・`i1=2` の基底は `[(a,0,0),(b,w,1)]` で、その展開
`[(a+k d0, k w, 0)]_{k<n}` は行 2 が 0 の 2 行対角列 ＝ ペア数列の停止性。
⟹ **新しい帰納法**が要る。

## 4.15 `TowerExp2Root` の `|R| ≥ 2` の構造（次セッション用の解析）

`|R| = 1` は片付いた（`z=0` は `diag_mem_W` ✅、`z=1` は `oper = Pred` で自明）。
`|R| ≥ 2` は次の形になる。

```
M = (0,v,z) :: R,  domT R m,  根が行 2 で復活,  d0 = entry R 0 (|R|-1),  d1 = w - v
hop ⟹ R.dropLast ∈ Wstar            （domT なので R⟦n⟧ = Pred R = R.dropLast）

M⟦n⟧ = ⧺_{k<n} shiftr01 (k*d0) 0 (Lift1 ((0,v,z) :: R.dropLast) (k*d1))
```

### `|R| = 1` との関係（有望な見方）

`|R| = 1` 版 `M₀ = [(0,v,z), q]` の展開は
`M₀⟦n⟧ = ⧺_k shiftr01 (k*d0) 0 (Lift1 [(0,v,z)] (k*d1)) = [(k*d0, v + k*d1, z)]_{k<n}`
＝ **`diag_mem_W` で証明済みの対角列**。

一般の `M⟦n⟧` は、この対角列の**各列 `c_k = (k*d0, v + k*d1, z)` の下に
「リフトされた `R.dropLast`」を挿し込んだもの**である。

各ブロックの段は合っている:

* `(0,v,z) :: R.dropLast ∈ W (2v+z)`（`hop` ＋ `Wstar`）
* `(WL) LiftStage` より
  `Lift1 ((0,v,z) :: R.dropLast) (k*d1) ∈ W (2v+z+2k*d1) = W (2(v+k*d1)+z)`
  ＝ **`c_k` 自身のレベルちょうど**

⟹ 残るのは

```
(SUBST)  Q ∈ W u、各列 j について B_j（頭が Q[j]、他の列は Q[j] より真に深い、
         B_j ∈ W (lev Q[j])）⟹ ⧺_j B_j ∈ W u
```

という**代入閉包**。`W_add` は `rsum`（後半の根が最浅）を要求するので直接は使えない
（後のコピーほど深い）。`(CAT)` も両辺が同じ段を要求するので届かない。

**計測 `tools/probe_subst.py`: 判定 38403 例 0 違反**（未判定 2014、ホスト 2010）。

### なぜ `(SUBST)` を選ぶか（`(GC)` は強すぎる）

もう一つの分解は `Wset.oper_cons_tower2`（**既存**）

```
((0,v,z) :: R)⟦n+1⟧ = (0,v,z) :: graft R (Lift1 (((0,v,z) :: R)⟦n⟧) (w - v))
```

を使った塔の帰納で、必要になるのは

```
(GC)  domT R m → (∀n≥1, R⟦n⟧ ∈ Wstar) → ∀ Y ∈ W m, based Y → graft R Y ∈ Wstar
```

＝「後者節のデータが接ぎ木閉包に格上げされる」。だが `|R| = 1` では
`graft R Y = Y'` なので `(GC)` は「任意の `Y ∈ W m` を根の下に植えると
`W a'`（`a'` は 0 まで小さい）に入る」を要求し、これは `mem_Wstar`
（＝目標そのもの）に近い。⟹ **`(GC)` は強すぎる**。

`(SUBST)` は各ブロックの段が `lev Q[j]` に**ぴったり合っている**閉包なので、
`(CAT)` と同じ「純粋な `W` の閉包」型であり、ペア定理も含まない見込み
（各 `B_j` が既に `W (lev)` に居ることを要求するので、対角列を無から作れない）。

### ⟹ 予想される最終形

```
TRIO_terminates : WCat → SubstClosed → WellFounded stepRel
```

必要な配線: `TowerExp2Root ⟸ (SUBST) + (WL) + diag_mem_W`。
Lean 側の部品は揃っている（`oper_eq_gexp` / `gexp` = `gcopies` /
`glift_eq_Lift1` / `Croot.gcopies_succ_graft_lift` / `diag_mem_W`）。
残る作業は `gcopy M 0 L d0 d1 k = shiftr01 (k*d0) 0 (Lift1 (seg M 0 L) (k*d1))`
の形を出すこと。

### 段の帳尻（確認済み）

`m + 1 = 2w + y`、`z < y` より `2w + z ≤ m`。したがって塔の漸化式
`M⟦n+1⟧ = graft M (Lift1 (M⟦n⟧) d1)` では
`Lift1 (M⟦n⟧) d1 ∈ W (2v+z+2d1) = W (2w+z) ⊆ W m` とぴったり収まる。
不足しているのは `graft R Y ∈ Wstar`（接ぎ木閉包）だけで、後者節は
`R.dropLast ∈ Wstar`（＝ `graft R []`）しか与えない。

## 4.2 ★★ ペア数列の停止性は**臨界経路上にある**（v0.118.103）

`TowerExp2Root` の `|R| = 1` の場合を計算すると、ペア定理が**どこに居るか**が
完全に特定できる。`M = [(0,v,z), (e,w,y)]` の展開は（`tools/probe_diag.py` で
形を全数照合、不一致 0）

```
M⟦n⟧ = [(k*e, v + k*(w-v), z)]_{k<n}        -- 行 2 は「根の z」であって孤児の y ではない
```

よって残差の基底は

```
(DIAG)  0 < e → 0 < f → z ≤ 1 → [(k*e, v + k*f, z)]_{k<n} ∈ W (2v+z)
```

これは `z` で綺麗に割れる:

* **`z = 1` は自明**: 全列の行 2 が 1 なので、行 2 の親（＝行 2 がより小さい
  行 1 祖先）を持つ列が 1 つも無い。⟹ どの列も孤児 ⟹ `oper = Pred` で
  1 列ずつ縮み `[(0,v,1)]` に至る。そのレベル `2v+1` は目標段そのもの。
  計測 108/108 ✓、`expand(D,2) = D.dropLast` も確認。
* **`z = 0` は正真正銘のペア数列**: `v = 0` を取ると
  `[(k*e, k*f, 0)]_{k<n} ∈ W 0` ＝ **ペア数列の停止性そのもの**
  （lean-yapss の `PSS_terminates_unconditional`）。計測 60 判定 0 違反
  （48 は探索打ち切りで未判定）。

⟹ **trio の証明は、必ずペア数列の停止性の証明を含む。**
これは当然（trio ⊋ ペア）だが、`(CAT)` はそれを含まない（両辺が `W u` なので
レベルを上げる列を作れない）ので、**ペア定理は `TowerExp2Root` の
`|R| = 1, z = 0` 基底からのみ入る**。

### ⟹ 具体的な次の一手

```
(PAIR)  zle0 S → entry S 0 0 = 0 → lev S 0 = 0 → S ∈ trio.W 0
```

行 2 が 0 のブロックでは `t = max{y | S_(X-1)y > 0} ≤ 1` なので trio の `oper`
は yapss の `oper` と一致する。lean-yapss の
`PSS_terminates_unconditional` から整礎帰納法で `W 0` 版を作り、
埋め込み `PairSeq → TrioSeq` で移す。
⚠ 行 2 が 0 のブロックに限れば `natDom` ガードは健全（反例 `(x,0,1)` は行 2 を
使う）。yapss が核なしで通るのはこれが理由。
⚠ (PAIR) は `TowerExp2Root` の**基底だけ**を与える。必要条件であって
十分条件ではない。

## 4.0 ★★★ 残差 = `(CAT)` + `(SUBST)`（v0.118.113、現在の頂点）

```
Final.TRIO_terminates_of_cat_subst : WCat → SubstClosed → WellFounded stepRel
  axioms = [propext, Classical.choice, Quot.sound],  sorry 0,  build 800
```

**両方とも「純粋な `W` の閉包」命題**であり、**ペア数列の停止性は証明の内部で
完全に解消済み**（`Pair/` に取り込んだ lean-yapss ＋ `PairBridge.diag_mem_W`）。

| 核 | 内容 | 計測 |
|---|---|---|
| `(CAT) WCat` | `A, B ∈ W u → A ++ B ∈ W u` | 372290 対 0 違反 |
| `(SUBST) SubstClosed` | `W u` の各列（**行 0 で狭義増加＝鎖でよい**）の下に「その列のレベルの `W` ブロック」を挿しても `W u` | 判定 38403 例 0 違反 |

### 配線（すべて Lean 済み）

```
(CAT) ─→ (TOW) shiftTowerClosed_of_cat
      ─→ (WL) liftStageParented_of_tower → liftStage_of_parented
      ─→ TowerExp の m < a 側        towerExp_of_cat
(SUBST) + (WL) ─→ TowerExp2Root      towerExp2Root_of_subst      ← ★ v0.118.113
                  基底 |R| = 1: diag_mem_W (z=0, ペア定理) / diag1_mem_W (z=1)
⟹ TRIO_terminates_of_cat_subst
```

### `towerExp2Root_of_subst` の骨子

```
M⟦n⟧ = gexp M 0 L D0 D1 n                       oper_eq_gexp（j0 = 0 は parent_cons_eq_zero）
     = ⧺_{k<n} shiftr01 (k*D0) 0 (Lift1 M.dropLast (k*D1))     gcopies_eq_tower
ホスト Q = [(k*D0, v + k*D1, z)]_{k<n} ∈ W (2v+z)              diagz_mem_W
copy k ∈ W (2*(v + k*D1) + z) = W (lev Q k)                     (WL) + W_shift
  ← M.dropLast = p_{v,z}(R.dropLast) ∈ W (2v+z)                 後者節 hop
⟹ (SUBST) が閉じる
```

## 4.01 ★★★★★ 残差は `(SUBST1g)` **1 本**になった（v0.118.122、現在の頂点）

```
Final.TRIO_terminates_of_subst1g : Subst1g -> WellFounded stepRel
  axioms = [propext, Classical.choice, Quot.sound],  sorry 0,  build 800

Subst1g : S in W u -> p < |S| -> C /= [] -> C in W (lev S p) ->
          entry C 0 0 = entry S 0 p ->
          (forall j, 1 <= j < |C|, entry S 0 p < entry C 0 j) ->
          S.take p ++ C ++ S.drop (p+1) in W u
```

**`(SUBST1g)` は `Aop` 節 3 の 2 点緩和そのもの**:
節 3 は「**末尾**列に `W m` ブロック（`m = lev - 1`）を graft してよい」。
`(SUBST1g)` は (a) 位置を任意にし、(b) ブロックの段を `lev - 1` から `lev` に
1 つ上げただけ。だから「新しい公理」ではなく既存公理の最小の強化である。

### `(CAT)` が消えた — 消費者 2 本とも `(SUBST)` だった

| 旧消費者 | 置換 | 鍵 |
|---|---|---|
| `(TOW)` シフトコピー塔 → `(WL)` | `shiftTowerClosedS_of_substG` | ホスト = **定数対角** `[(x0+k*e, b, c)]_{k<n}`（レベルはどの列も `2b+c = u`）。`diagz_mem_W` を `f = 0` で使う（`e = 0` は `constcol_mem_W`）。コピー `k` = `shiftr01 (k*e) 0 Q ∈ W u = W (lev ホスト k)` |
| `TowerExp` の `m < a` 枝 | `cons_mem_W_of_substG` | ホスト = **二列** `[(0,v,z), t] ∈ W a`（`two_col_mem_W`）。その 2 つのレベルが皮 `p_{v,z}(R.dropLast) ∈ W (2v+z)` と末尾単元 `[t] ∈ W (m+1)` にちょうど一致 |

### `two_col_mem_W`（新規・単独で強い）

```
two_col_mem_W : z <= 1 -> 2v+z <= a -> forall t, [(0,v,z), t] in W a
```
第 2 列は**深さもレベルも任意**。孤児なら `oper = Pred`、親があれば根が親で
展開はちょうど対角 `[(k*D0, v+k*D1, z)]_{k<n}`（`gcopies_eq_tower` を
`M.take 1 = [(0,v,z)]` で）。だから `[(0,0,0), (1,100,1)] ∈ W 0` — レベル 201 の
列がレベル 0 の根の下で無害になる。**ペア定理がここで効いている。**

### `(TOW)` の仮説を厳格化した

`ShiftTowerClosedS`（根が**厳密に**最浅）。`(SUBST)` はブロックをホスト列より
厳密に深く置く必要があるため。消費者は 2 本ともこれを供給できる
（`lspOn_srow1_of_tower` は `window_of_rtg0`、`towerExp1_of_tower` は `argOK`）。
`shiftTowerClosedS_of_closed : ShiftTowerClosed -> ShiftTowerClosedS` で
旧 `(CAT)` 経路も生きたまま。

## 4.02 ★★ `(SUBST)` は**単一ブロック** `(SUBST1)` に割れた（v0.118.120）

```
Subst1 : S ∈ W u → p < |S| → C ≠ [] → C ∈ W (lev S p) →
         (∀ i, entry C i 0 = entry S i p) →
         (∀ j, 1 ≤ j < |C|, entry S 0 p < entry C 0 j) →
         S.take p ++ C ++ S.drop (p+1) ∈ W u
substClosed_of_subst1 : Subst1 → SubstClosed          -- Lean 済み
Final.TRIO_terminates_of_cat_subst1 : WCat → Subst1 → WellFounded stepRel
```

* 各列の置換は**独立**で、左から順に行える（位置 `p` の置換は `p` より左を乱さない）。
  段 `k` の対象は `⧺_{j<k} B j ++ Q.drop k` で、ブロック境界の列はまだ `Q k`
  （entry も lev も同一）。`(SUBST1)` 一発で段 `k+1`、`k = |Q|` が目標。
* `(SUBST)` の**鎖条件は使わない**（計測でも不要）。
* 計測: `tools/probe_subst1.py` 62151 例 0 違反（判定 58799 / 未判定 3352）。
* さらに強い**位置つき graft 形** `(SUBST1g)`（頭の一致を捨て `entry C 0 0 = entry S 0 p`
  だけ課す。`C ∈ W (lev S p)` が `lev (C 0) ≤ lev S p` を自動で与える）も
  0 違反: `tools/probe_subst1g.py` 210201 例（うち頭が異なる 148050）。
  `(TOW)` は `(SUBST1g)` を定数対角 `[(k*e, b, c)]_{k<n}`（全列が永久孤児なので
  `W (2b+c)`）の上で反復した形なので、`(CAT)` の消費者 1 本は吸収できる見込み。
  ⚠ ただし `towerExp_of_cat` の `m < a` 枝（`C ++ [t]`, `lev t = m+1 ≤ a`）は
  `(SUBST1g)` では届かない（末尾に**挿入**する形が要る）。`(CAT)` は依然独立。

## 4.05 `W` の構造的補題（v0.118.117-118、残差攻略の道具）

```
W_take                : M ∈ W u → M.take k ∈ W u          -- 接頭辞閉包
W_dropLast            : M ∈ W u → M.dropLast ∈ W u
lev_root_le_of_mem_W  : M ∈ W u → M ≠ [] → lev M 0 ≤ u    -- singleton_mem_W の逆
```

* **接頭辞閉包**は計測が先（317824 例 0 違反・未判定 0）。証明は `A2'` で、
  真の接頭辞は各節のデータから（節 2 は `oper_take_prefix`＝コピー 0 が非シフト、
  節 3 は `graft M [] = M.dropLast`）、ブロック全体はデータを自分の長さで取る。
* ⚠ **接尾辞閉包は偽**: `[(0,0,0),(1,1,0)] ∈ W 0` だが `[(1,1,0)]` は `W 2` が要る。
  根を落とすとレベルが露出する。`Wstar`（根を植え直す界面）が必要な理由そのもの。
* **根のレベルは段を下から抑える**: 展開は先頭列を決して落とさない
  （コピー 0 は非シフト、`Pred` は末尾だけ）ので、終端の単元は根であり
  そのレベルが `u` に収まる必要がある。`|M| = 1` の節 3 は `domT M m` と `m < u` から即。

**使いどころ**: `(SUBST)` を `|Q|` について帰納するとき、
`Q.take n ∈ W u`（接頭辞閉包）で帰納法の仮定が回る。
`lev Q 0 ≤ u` より**最初のブロック `B 0 ∈ W (lev Q 0) ⊆ W u` は無料**。
残るのは「`W u` の塊に `W (lev Q k)` の塊を継ぐ」一歩で、`rsum` が立たないため
`W_add` は使えない（後のブロックほど深い）。

## 4.1 ★★★ ペア定理を trio に取り込んだ（v0.118.104-106）

lean-yapss の 11 モジュールを `lean/Pair/` として取り込み（名前空間は `YAPSS`
なので `TRIO` と衝突しない。モジュール名だけ `Pair.*` にリネーム）、
**橋渡しを完成させた**（`lean/Pair/Bridge.lean`、sorry 0、
axioms = [propext, Classical.choice, Quot.sound]、build 800）。

```
emb S := S.map (fun p => (p.1, p.2, 0))

oper_emb          : (emb S)⟦n⟧ = emb (S⟦n⟧)
emb_mem_W         : S ∈ YAPSS.W v → emb S ∈ TRIO.W (2v)
pair_plant_mem_W  : argOK R → emb ((0,v) :: R) ∈ TRIO.W (2v)          -- (PAIR)
diag_mem_W        : 0 < e → [(k*e, v + k*f, 0)]_{k<n} ∈ TRIO.W (2v)   -- ★ 基底
```

### `oper_emb` の要点

trio の `oper` は BM4 の上昇行列 `A_xy` のガード付き
（`if le0 M j0 j then k*d0 else 0`）だが、yapss の `oper` にはガードが無い。
ペアではこれが一致する:

* `d1 = 0`（両側とも `if 1 < i1 then … else 0` で `i1 ≤ 1`）⟹ 行 1 のガードは無害
* 行 0 のガードは**窓の中では常に真**（`le0_window`）:
  `window_of_rtg0`（窓の列は根より真に深い）と `rtg0_of_window`（深ければ行 0 の
  子孫）の合成。両方とも既存補題。

### `emb_mem_W` の要点

転送では **trio 側の `Aop` 節 3 を一切使わない**。
yapss 側の節 3 は `domT S m` を持つので `S⟦n⟧ = graft S []`、つまり `z = []` の
データだけで trio 側の節 2 が立つ。これで「trio の `W m'` は埋め込み像より真に
大きい」という量詞のずれを回避できる。`|S| = 1` の場合だけ
`singleton_mem_W`（`m+1 ≤ v` は `m < v` から）。

### ⟹ 残差 `TowerExp2Root` の基底は**証明済み**になった

`|R| = 1` かつ `z = 0` の場合、`M⟦n⟧ = [(k*e, v + k*(w-v), 0)]_{k<n}` は
`diag_mem_W` そのもの。残るのは `|R| ≥ 2`（と `z = 1` だが、こちらは
全列の行 2 が 1 で `oper = Pred` なので自明、§4.2）。

## 4.3 ★★ 残差の最終形（v0.118.99-101）

```
TRIO_terminates_of_cat_root : WCat → TowerExp2Root → WellFounded stepRel
  axioms = [propext, Classical.choice, Quot.sound],  sorry 0,  build 787
```

### 何を削ったか

1. **`TowerExp` を `m < a` で分割**（`towerExp_of_cat`）:
   `m < a` なら追加される列は**単体で** `W a` の元（`lev = m+1 ≤ a`）なので
   `(CAT)` で `p_{v,z}(R.dropLast)` に貼るだけ。⟹ 残るのは `a ≤ m`。
2. **`a` の量詞は余計**（`towerExp2_of_root`）: `W_mono` が `W (2v+z)` を
   すべての `a ≥ 2v+z` に持ち上げ、`tower1_le` が `2v+z ≤ m` を与えるので、
   行 2 の残差は**段 `2v+z` 一点**に縮む。
3. **行 2 復活のギャップを核に焼き込んだ**（`row2_revival_gap`）:
   根が行 2 の親 ⟹ `nextrel2` の `le1` 成分から `v < w`、行 2 の狭義上昇から
   `z < y`。⟹ `2v+z < m+1`。核の仮定に加えたので核は**形式的に弱く**なった。

### 残差の内容（これだけ）

```
TowerExp2Root :
  argOK R → R ≠ [] → z ≤ 1 → domT R m →
  (∀ n ≥ 1, R⟦n⟧ ∈ Wstar) →            -- 後者節のデータ（接ぎ木閉包は無い）
  srow R (|R|-1) = 2 →                  -- 行 2 崩壊
  hasParent ((0,v,z) :: R) 2 |R| →      -- 根が孤児を復活させる
  v < entry R 1 (|R|-1) → z < entry R 2 (|R|-1) →
  ∀ n ≥ 1, ((0,v,z) :: R)⟦n⟧ ∈ W (2v+z)
```

日本語で言うと **「引数が後者節で来た行 2 崩壊 `p_{v,z}(R)` が、根自身の段
`W (2v+z)` に入る」**。`(CAT)`（`W u` は連結で閉じる）が残り全部を運ぶ。

### なぜここで止まるか

塔の漸化式は `M⟦n+1⟧ = (0,v,z) :: graft R (Lift1 (M⟦n⟧) d1)` で、
`(WL)` があれば段は `2v+z+2d1 = 2w+z ≤ m` にぴったり収まる。だが
`graft R y ∈ Wstar`（接ぎ木閉包）が要り、**後者節は `R.dropLast ∈ Wstar` しか
与えない**。これを `R.dropLast ∈ Wstar` から出そうとすると
「`W m` のブロックを `W a'`（`a'` は幾らでも小さい）のブロックに連結する」
＝ 崩壊そのものになり循環する。

## 4.5 `natDom` ガードは⛔反証（v0.118.90）

**結論: `Aop` 節 2 に `natDom M` を戻す設計は、`Wstar_closed` を偽にする。**
実装を最後まで走らせて `Wset.lean` の 41 → 16 エラーまで削った時点で
counterexample が出た。以下は反例そのもの（`tools/trio.py` で数値確認済み）。

### 反例（決定的・単純）

```
R = [(1,0,1)]                 -- 行2=1, 行1=0 の孤児（lev = 1）
M = (0,0,0) :: R = [(0,0,0),(1,0,1)]
```

* `srow R 0 = 2`、`parent R 2 0 = None` ⟹ `domT R 0`
* `M` でも `parent M 2 1 = None`。理由は構造的:
  `nextrel2` は `le1 M j0 j1` を要求し、`le1` は行 1 の**真の増加**を要求する。
  葉の行 1 は 0 なので行 1 祖先は存在し得ない。
  ⟹ **`(x,0,1)` 型の列は常に死んだ孤児（lev 1）**
* `M⟦n⟧ = Pred M = [(0,0,0)]`（`trio.expand` で確認）

したがって

| | 無ガード `W 0` | `natDom` ガード付き `W 0` |
|---|---|---|
| 節 1 | ✗ (len 2) | ✗ |
| 節 2 | ✅ `M⟦n⟧ = [(0,0,0)] ∈ W 0` | ✗ (`domT M 0` で `natDom` 不成立) |
| 節 3 | — | ✗ (`m = 0 < u = 0` が偽) |

⟹ ガード付きでは `M ∉ W 0`。

一方 `R = [(1,0,1)] ∈ Wstar` は `Aop` 節 3 で導出可能
（`domT R 0`、`0 < u0`、`graft R y = shiftr01 1 0 y` は `y ∈ W 0` = ゴミ無し
に対して `Wstar` に入る）。よって `Wstar_closed` は
`(0,0,0) :: R = M ∈ W 0` を要求し、**偽**。

### 何が起きているか（設計上の教訓）

`Wstar` の doc comment が既に書いていた「junk below `m`」がまさにこれ。
**無ガード節 2 の役割は「段より下のゴミ（死んだ孤児）を Pred で吸収すること」**
であり、これは飾りではなく本質。ガードはこの吸収路を塞ぐので、`W u` が
「lev < u の死んだ孤児を含むブロック」を失う。

### 弱いガード `domLow` も⛔

`domLow u M := ∀ m, domT M m → u ≤ m`（節 2 を `domLow u M ∧ …` に）なら
上の反例は通る（`0 ≤ 0`）。しかし本来の目的 = `towerOK_of` の節 2 分岐
（`Wset.lean:4050`, `TowerExp` の呼び出し）を空虚化する力が無い:

```
R = [(1,1,0)], v = z = 0, a = 0   -- 根が行1で孤児を復活させる
domT R 1,  m0 = 1,  domLow a R ⟺ a ≤ m0 ⟺ 0 ≤ 1  … 成立してしまう
```

`hpM`（根が復活させる）からは `m0 < a` は出ない（`m0 = 2w-1` は幾らでも
大きくできる）。よって `TowerExp` は残る。

### ★ `tbAll` を戻せば救済できる（v0.118.91 で訂正）

ガード + `Wstar` に `tbAll R a` を足せば反例は排除できる: 反例は
`tbAll R 0` ⟺ `domT R 0 → 0 < 0` が偽なので仮定が立たない。

**この訂正の要は `TbOper` が真だったこと**（当初「コピーが行 1 を `k*d1` 上げる
から偽」と書いたが誤り）。

```
(TB) TbOper : tbAll X u → tbAll (X⟦n⟧) u
```

`tbAll X u` は「`X` の親を持たない列はすべて lev < u」と同値なので
(TB) ⟺ `u0 (X⟦n⟧) ≤ u0 X`（`u0` = 親無し列の lev の最大）。

* 計測 `tools/probe_tboper2.py`: **185138 例 0 違反**
  （短列全数 24624 / ランダム長列 160000 / 反復降下）。
  うち **3305 ホストが危険ケース（`i1 = 2` かつ `d1 > 0`＝コピーが行 1 リフト）**。
* **構造的理由**: `d1 > 0` は `i1 = srow X (|X|-1) = 2` のときだけ。そのとき
  コピー根 `j0` は末尾列の**行 2 の親**なので `entry X 2 j0 = 0`。
  よって `j0` の行 1 錐に入る行 2 の列は必ず行 2 の親（`j0` 以近）を持つ
  ⟹ **親無しの行 2 列は決してリフトされる錐に入らない**。
  親無しの行 1 列はそもそも誰の行 1 錐にも入らない（`le1` の最後の一歩が
  その列の行 1 の親だから）。⟹ 親無し列の lev は展開で上がらない。

### ⟹ 改訂設計（v0.118.91、実装対象）

```
Aop 節 2   : natDom M ∧ ∀ n ≥ 1, M⟦n⟧ ∈ X
Wstar      : argOK R → ∀ v z a, z ≤ 1 → 2v+z ≤ a → tbAll R a → (0,v,z) :: R ∈ W a
新補題     : TbOper      : tbAll X u → tbAll (X⟦n⟧) u          （probe 185138/0）
             mem_W_tbAll : M ∈ W u → tbAll M u                  （A2' 帰納、易しい）
既存で足りる: tbAll_take / tbAll_graft / tbAll_of_lev_bound（すべて証明済み）
供給点      : Wset.lean:4113 に `htb : tbAll Q (maxlev Q)` が**すでに計算されている**
             （旧 tbAll 設計の遺物。そのまま使える）
```

`Wstar_closed` の枝ごとの帰結（yapss の `Wstar_closed` と同型になる）:

| 枝 | 扱い |
|---|---|
| 節 1 | 後者手（現行のまま） |
| 節 2・親あり | `oper_cons_nat` で可換。`tbAll (R⟦n⟧) a` に **(TB)** が要る |
| 節 2・親なし | `natDom R` が `lev R last = 0` を強制 ⟹ 後者手。`tbAll_take` |
| 節 3・根が復活 | 塔（`tower1_mem` / `TowerGraft2`）。接ぎ木データあり |
| 節 3・死んだ孤児 | `tbAll R a` から `m < a` ⟹ **節 3 が使える**。`tbAll_graft` |

⟹ **`TowerExp` / `TowerExp2` が枝ごと消える**。`TowerGraft2` は
`towerGraft2_of_liftStage` で `(WL)` に、`(WL)` は `(TOW)`→`(CAT)`→`(SNOC)` に
落ちるので、目標は

```
TRIO_terminates_of_snoc : WSnoc → WellFounded stepRel      -- 残差 1 本
```

### ⛔ 改訂設計も閉じない（v0.118.92、実装を走らせて確定）

改訂設計を Wset.lean に実装し（ブランチ `guard-tbAll-wip`, HEAD eddcd9c）、
機械的 9 箇所を修理して `mem_W_tbAll` まで **GREEN** にしたところで
側条件の閉性が破れることが確定した。

**側条件は 2 本要る**（どちらか一方では足りない）:

```
(C1) tbAll M a                  -- 節 3・死んだ孤児の枝が要求（m < a）
(C2) tbAll M (max (2v+z) 1)     -- 塔の枝が要求（tower1_mem が段 m で回るので tbAll M m）
```

* (C1) 単独では不足: 塔の再帰は段 `m` で回るが `m` と `a` は無関係。
  計測: 塔ホスト 135680 例のうち **18760 例で `u0(M) > m`**
  （`tower1_le : 2v+z ≤ m` は 135680/135680 で成立）。
  反例型 `M = [(0,0,0),(1,0,1),(2,1,1),(1,1,0)]`（`m = 1`, `u0 = 3`）:
  `(1,0,1)` が行 1 の鎖を塞ぐので `(2,1,1)` が永久孤児になる。
* (C2) 単独でも不足: `a = 0` で死んだ孤児（lev 1）を排除できない。
* ✅ **(C2) は `oper` で保たれる**（`probe`: 164232 例 0 違反）。
  `TbOper` と同じ構造的理由。
* ⛔ **(C2) は `graft` で保たれない**: `Aop` 節 3 の界面は `∀ y ∈ W m` なので
  `u0(y)` が `m` まで大きい `y` が渡ってくる。
  計測: 595809 例中 **87015 例で違反**。最小反例

  ```
  M = [(0,0,0),(1,2,0)]   m = 3   B = max(2v+z,1) = 1
  y = [(0,0,1),(1,1,1)]   u0(y) = 3 ≤ m,  ガード付きでも y ∈ W 3 は可能
  graft M y = [(0,0,0),(1,0,1),(2,1,1)]   u0 = 3 > 1
  ```

⟹ **構造的障害**（補題の欠落ではない）: 側条件は「段 `a` で抑える」と
「段 `m` で抑える」を同時に満たさねばならないが、後者は `Aop` 節 3 の
`∀ y ∈ W m` 界面を通れない。ガード路はここで閉じる。

### ⛔ 「標準断片に制限する」逃げ道も無い（決定的）

「ガードが壊れるのは非標準ブロックだからでは？」を潰した。
**真の `ST_TS` 種（`diagSeqT` のみ）から生成した 109 行列**で測ると:

* 行列全体では `u0 M = 0`（親無しの正レベル列は無い）109/109 ✓
* `(x,0,1)` 型の列は **1 つも現れない**（`z1pos`: `0 < row2 → 0 < row1`）4205/4205 ✓
* しかし **`mem_of_Aclosed_aux` が `Wstar` に渡す「再基底化した部分木」では
  (S1) が 22533/34050 で破れる**:

  ```
  T = [(0,1,1),(1,2,1),(2,3,1)]     -- 根 lev 3
      (1,2,1) は T の中では行 2 の親を持たない（親は木の外）→ 親無し lev 5 > 3
  ```

  木の内部の列の行 2 の親は木の外（根より浅いところ）にあり得るので、
  木を切り出して再基底化すると**根より高いレベルの死んだ孤児が必ず生じる**。

⟹ `Wstar` の「任意に小さい `a`（`2v+z ≤ a`）で主張する」設計は、この
「根より高い死んだ孤児」を無ガード節 2（`Pred` 吸収）で飲み込むためのもの。
標準性をどれだけ足してもこの現象は消えない。**ガード路は完全に閉じた。**

### この探索で得た再利用可能な事実

1. **(TB) `tbAll X u → tbAll (X⟦n⟧) u`**: `tools/probe_tboper2.py` 185138 例 0 違反。
   根拠: `d1 > 0` ⟹ `i1 = 2` ⟹ コピー根 `j0` は末尾列の行 2 の親 ⟹
   `entry X 2 j0 = 0` ⟹ `j0` の行 1 錐の行 2 列は必ず行 2 の親を持つ
   ⟹ **親無し列はリフトされる錐に入らない**。
2. **(S1'') `u0 M ≤ max(2v+z,1)` も `oper` で保たれる**（164232 例 0 違反）。
3. ★ **標準行列には正レベルの親無し列が無い**（`u0 M = 0`）:
   162 行列 / 3822 接頭辞すべて。BM の「標準形では親無しは起きない」
   （`trio.py` の `expand` のコメント、`oper_eq_pred_of_noParent` の保険分岐）を
   数値で確認したもの。`ST_TS M → tbAll M 0` として Lean 化する価値がある。
4. **`mem_W_tbAll : M ∈ W u → tbAll M u`**（ガード下で成立、Lean 証明済み・
   ブランチ `guard-tbAll-wip` にある）。`tbAll_graft'`（`m < u` 不要版）も同上。

### なぜ yapss には要らないのか（設計の core）

yapss の `Wstar_closed` は `v ≤ m ⟺ 根が孤児を復活させる`という**厳密な二分法**で
通っている（`nextrel1 M 0 last` ⟺ `v < entry R 1 last = m+1`）。trio でこれが
破れるのは行 2 だけ:

* `srow = 1`: 復活しない ⟹ `w ≤ v` ⟹ `m+1 = 2w ≤ 2v ≤ a` ⟹ `m < a` **自動**
* `srow = 2`: `nextrel2` は `le1` を要求するので、`(x,0,1)` 型は**永久に**親無し。
  `m` と `2v+z` の間に関係が無い ⟹ 側条件 `tbAll R a` が要る

⟹ `tbAll` は「行 2 の永久孤児のレベルを段が上回る」という trio 固有の簿記。

## 5. 却下済み経路（再挑戦禁止; 詳細は memory）

- 弱錐 S2 / 閾値・混成マスク（S3-S6）: B2a か tower2 が壊れる
- 項側 Buchholz-W ピボット: W₀ はゲーム木 wf であり olt-wf でない;
  橋渡しの BM-fs シミュレーションはリフトと同内容
- `Aop` 節3の全段閉包化: 段再帰の整礎性が壊れる
- 値ベース要素リフト言語（LiftVc*/origin-mask/TLift 脊柱型): 位置性で全滅
- GA の素朴な A2（キャップなし）: 段 m_Y+2t の幾何的成長
- **`Aop` 節 2 の `natDom` ガード（側条件なし）／`domLow` 弱化**: §4.5 の反例で決着。
  **ガード + `Wstar` の `tbAll` 側条件**も閉じない（§4.5 改訂設計、計測で確定）。
  ガード路全体が閉じた
