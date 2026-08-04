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

### γ (g)-枝: UBI ブロッカー — **文脈長降下で処理**（2026-08-05 確定方針）
walk 計装の結果: 接ぎ木直後のブロックは 0/8650、遅延越境（y-領域が
部分的に剥がれた後）は 1235 件で全て B2a 型・srow ≤ 1（消費データ上
srow=2 は 0）。**鍵**: ブロック済み展開の bad root p は文脈接頭辞内
(p < 境界) にあり、展開後の新文脈 = take p は**厳密に短い** →
γ の再帰は (|文脈|, 要素構造)-lex で整礎。処理形: 展開 = take p ++
(文脈接尾辞 ++ shift(y-残基)) のコピー列 = X̄-連接形（β と共通装置）。
srow=2 の遅延越境も同じ降下で処理できる見込み（d1' > 0 なら glift/Gtrans
資産でコピーを扱う）→ その場合 δ は不要。

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

## 4. 実行順序（推奨・2026-08-05 改訂）

1. γ/β 共通の X̄-連接装置の paper-sketch:
   ブロック済み展開の分解補題（oper = take p ++ copies(suffix ++ shift y)）
   と文脈長降下の帰納の骨格。srow≤1（d1'=0, shiftr01 資産）から。
2. γ の Lean 化（文脈長降下; srow≤1 → srow=2 の順）
3. β（clause-2 復活塔; X̄ + ∀s-key）
4. α の測度の paper-sketch → キャップ付き GA の文 → Lean
5. `mem_of_Aclosed_aux` の Wstar2 への再配線 + Final.lean 差し替え

（δ = レベルキャップ簿記は γ の「空性→処理」転換により不要見込み。）

## 5. 却下済み経路（再挑戦禁止; 詳細は memory）

- 弱錐 S2 / 閾値・混成マスク（S3-S6）: B2a か tower2 が壊れる
- 項側 Buchholz-W ピボット: W₀ はゲーム木 wf であり olt-wf でない;
  橋渡しの BM-fs シミュレーションはリフトと同内容
- `Aop` 節3の全段閉包化: 段再帰の整礎性が壊れる
- 値ベース要素リフト言語（LiftVc*/origin-mask/TLift 脊柱型): 位置性で全滅
- GA の素朴な A2（キャップなし）: 段 m_Y+2t の幾何的成長
