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

## 4. 実行順序（推奨・2026-08-05 深夜3 改訂）

1. ✅ β 族化 → 単一ステップ核 → 装備合成（§1.9.5–1.9.6）
2. **CoreT2EStep ⟸ e ∈ GX の形状還元を Lean 化**（§1.9.7 の
   plumbing: take_graft_high + graft_assoc + ctxOK_graft。
   `coreT2EStep_of_WleGX : (W (…) ⊆ GX) → CoreT2EStep` の形で
   sorry なしに書ける — 自己参照はまだ解かない）
3. γ' (CoreBlocked): 降下後 Y'-義務のデータ変換（文脈長降下は確保済み）
4. α (CoreT1L): E-測度（v-ヘッドルーム; §1.12 で孤児 = 植えた根と確定）
5. **層化測度の設計**（§1.12 の provenance 構造を Lean の測度に翻訳 —
   相互参照 {cores ↔ W_le_GX} の joint wf）
6. `mem_of_Aclosed_aux` の Wstar2 への再配線 + Final.lean 差し替え

（δ = レベルキャップ簿記は γ の「空性→処理」転換により不要見込み。）

## 5. 却下済み経路（再挑戦禁止; 詳細は memory）

- 弱錐 S2 / 閾値・混成マスク（S3-S6）: B2a か tower2 が壊れる
- 項側 Buchholz-W ピボット: W₀ はゲーム木 wf であり olt-wf でない;
  橋渡しの BM-fs シミュレーションはリフトと同内容
- `Aop` 節3の全段閉包化: 段再帰の整礎性が壊れる
- 値ベース要素リフト言語（LiftVc*/origin-mask/TLift 脊柱型): 位置性で全滅
- GA の素朴な A2（キャップなし）: 段 m_Y+2t の幾何的成長
