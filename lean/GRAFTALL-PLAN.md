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

### γ (g)-枝: UBI ブロッカー
Y の尾部が S.dropLast の列に復活する 0.9%（srow ≤ 1 のみ、srow=2 は 0）。
d1' = 0 なのでコピーは行0シフトのみ。`oper_shiftr01` 系の資産で
「S 側にまたがる展開」を直接処理する見込み。まず srow=2 が空であることを
Lean 化（`nextrel2` の le1-制約から）。

## 4. 実行順序（推奨）

1. γ の srow=2 空性（軽い; (d) の場合分けを完全にする）
2. β の srow≤1 版（X̄-trio = 連接閉包; `XA_closed` の姉妹補題）
3. α の測度の paper-sketch → キャップ付き GA の文 → Lean
4. β の srow=2 版（∀s-key と X̄ の合成）
5. `mem_of_Aclosed_aux` の Wstar2 への再配線 + Final.lean 差し替え

## 5. 却下済み経路（再挑戦禁止; 詳細は memory）

- 弱錐 S2 / 閾値・混成マスク（S3-S6）: B2a か tower2 が壊れる
- 項側 Buchholz-W ピボット: W₀ はゲーム木 wf であり olt-wf でない;
  橋渡しの BM-fs シミュレーションはリフトと同内容
- `Aop` 節3の全段閉包化: 段再帰の整礎性が壊れる
- 値ベース要素リフト言語（LiftVc*/origin-mask/TLift 脊柱型): 位置性で全滅
- GA の素朴な A2（キャップなし）: 段 m_Y+2t の幾何的成長
