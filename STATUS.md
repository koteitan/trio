# 現在地（2026-08-31 未明 3）

## ★★★★★★ **核は 2 本**（`TowerExpBig` の完全な分解、§206）

    **(1) `LiftTieCore`**（§29、3 量化 / 4 前提）
        … ブロック 1 個を持ち上げる（**経路 C と D で同じ命題**、`block_mem_of_liftTieCore`）
    **(2) `LiftTowerSelf`**（§55、4 量化 / 3 前提、**段が現れない**）
        … **マスクつき**塔が `Wself` に閉じる。**ブロッカーの有無に依らず `srow=2` の枝を覆う**
        （`towerExp2_of_liftTowerSelf`、緑。ブロッカー無しなら `ShTower2Self` に落ちる ＝ 16.8%）
        ⚠ **改名予定 `operTower` / `OperTowerSelf`**（`L51Lift.liftTower`（**一様版**）と衝突）

## ⚠⚠ **マスクがブロック局所かは未証明**（(2) の証明の分かれ目、測定中）

    `mTower`（H12 / R2 の実測の形）… マスクを**ブロックごとに `Q` の中で**計算
    `liftTower`（L3、Lean で出る形）… マスクを**塔全体の上で**計算
                                    ＝ **`oper_cons_tower2` が実際に作る形**
    **`Wset.le1_take`（`:908`、緑）は接頭辞局所性しか与えない**
      ⟹ **第 `k` ブロック（`k>=1`）のマスクが `Q` だけで決まることは Lean では出ない**

H12 の §211「マスクは全ブロックで同一」（80137 件・例外 0）は**その主張の実測**。
**L3 は「実測を Lean の仮定に紛れ込ませるのは教訓 14」として `liftTower` で核を立てた（正しい）。**
⟹ **`mTower = liftTower` を陽性・陰性対照つきで測定中**（H73 / R113）。
**真なら `mTower` の形で立て直せてブロックごとの議論が使える。偽なら塔全体で見続けるしかない。**

`CoreCap`（⟺ `Wset.GraftAll`）は **(1)(2) の両方を内側に畳んだ形**。

### `TowerExpBig` の分解（全部緑）

    `|R| = 1`                  `towerExp_singleton`（**仮定ゼロ**、§39）
    `R.dropLast` の行 2 ≡ `z`  `tower_of_row2const`（**仮定ゼロ**、§40。`= z` なので `z=1` でも効く）
    `srow = 1`                 `shTower` ⟹ `ShiftTowerClosedS` ⟸ `L47W.shiftTowerClosed_iff_wself`
    `srow = 2` ブロッカー無     `shTower2` ⟹ **`ShTower2Self`**（`towerExp2_of_shTower2Self`、§54）
    `srow = 2` ブロッカー有     ブロック所属 ＝ **`LiftTieCore`**（§52）＋ 繋ぎ ＝ `ShTower2Self` のリフト版

⟹ **(2) の側は `srow` によらず「同じ 1 単位を等差にずらして並べた塔が `Wself` に閉じる」1 文。**

## ★ 残核の大きさ（(δ) ＝ (1) の大きさ。箱を固定して `|R|` だけ動かした）

| | `|R|`=2 | 3 | 4 | **5** |
|---|--:|--:|--:|--:|
| ブロッカー無し（一様に潰れる） | 62.5% | 39.5% | 25.6% | **16.8%** |
| ⛔ **(γ) 行 2 ≡ 0** | **0%** | **0%** | **0%** | **0%** |
| (α) タイ無し | 9.4% | 10.2% | 8.3% | 6.0% |
| (β) `TieFree`（⚠ **`v >= 1` 限定**） | 0% | 0.6% | 1.2% | 1.6% |
| **(δ) ＝ 残核 ＝ `LiftTieCore`** | 28.1% | 49.7% | 65.0% | **75.6%** |

**単調増加で頭打ちなし。`|R|=6` で 83.22%**（R2 が H12 の箱で完全再現。ずれは箱の違いだけだった）。
**無料の枝 3 本を全部足しても `|R|=6` で 6% 弱**（(α) 9.38% → 4.17%、(β) 0% → 1.68%、**(γ) は 0 件**）。

> **⟹ 「小さい隅を潰す」戦略では終わらない。`LiftTieCore` を正面から証明する必要がある。**

⚠⚠ **但し書き（教訓 41、R2）**: これは **`R.dropLast ∈ Wstar` を落とした上位集合**での割合。
**「(δ) が大きい」は「構文の前提を満たすものの中で大きい」という意味**であって、
**「実際に `Wstar` に入る `R` の中で大きい」ではない。そこは有限では測れない**（R94）。

## ⛔ 死んだ道（全部確認ずみ）

    連結（`W_add` / `rsum`）… 塔は**深いほうを足す**ので構造的に不可
    **`WCat`**             … ブロックの段が `k` とともに上がり `W_mono` は上げる向きだけ
    `|R|` の帰納           … 節 3 の `domT` と仮定の `hasParent` が排他
    導出の帰納             … `Wstar` は Π 命題で導出木が無い ⟹ `Wstar_closed` と循環
    分解して組み直す        … 接頭辞でも行 0 でも `WCat` に落ちる
    **`zle1` を足す**       … **`Aop` の節 3 で壊れる**（`W m` に制限が無い）。
                            通すには `W` の定義から作り直し（§202。**team-lead の承認が誤りだった**）
    ⛔ **(γ) 行 2 ≡ 0**     … **構造的に空虚**（前提 `∃ p ∈ R.dropLast, p.2.2 ≠ z` と矛盾。§206）
    `LiftTowerClosed`（一様） … 証明しても `|R|=5` で **16.8% しか覆わない**（§203）

## ★ (2) に要る命題は Lean に**形すら存在しない**（§203）

> **`Q ∈ W u` →（根が最浅）→
> `(range n).flatMap (fun k => Lift1 (shiftr01 (d0·k) 0 Q) (d1·k)) ∈ W u`**
>
> マスクは `le1 Q 0 ·` で `Q` に内在（`Wset.le1_take`、緑）。
> **`d1 >= 1` は `L53.tower2_vw` が強制**するので `d1 = 0` に逃げられない。

`L51Lift.LiftTowerClosed`（`:63`、未証明）は**行 1 が一様版**で足りない。
L3 が `ShTower2Self` として `L105Cap.lean` に定式化ずみ（§54）。

## ★★★ 残核の中心は **「`v = 0`・`z = 0`・段 0・タイあり」**（§207、H12 の最終結果）

    (δ) の **7 割が `v = 0`**（66.7% → 69.3% → 70.7% → **71.3%**、`|R|`=2..5）

⛔⛔ **「`v = 0` は `z = 0` を強制する」は誤り（§211 で撤回）。箱の産物だった。**

    機構は `v` ではなく**行 2 の上界**:
    `L53.tower2_zr`（`:2380`）… `domT` ＋ `srow=2` ＋ `hasParent` ⟹ **`z < entry R 2 (|R|-1) = c`**
    ⟹ `z <= 1` のもとで **`z = 1 ⟺ c >= 2`**
    ⟹ **箱の行 2 が `<= 1` なら `z = 0`。`v` には依らない。**
    ⚠ **`c >= 2` を許せば `v = 0, z = 1` は起きる。** R2 自身の最小例:
       **`R = [(1,0,0), (1,1,2)]`, `v = 0`, `z = 1`, `c = 2`**（L3 が前提 4 つを手で確認）

**⟹ H12 の「94334 件で例外 0」は箱の行 2 が `<= 1` だったことの帰結。**
H12 は「機構は導いていない」と但し書きしていたので、**それを引用して課題にした team-lead の落ち度。**
⟹ 段が `a = 0` になるのは **`zle1` の箱に限った話**（＝ 我々の断片。`tower2_z_zero_of_zle1`、緑）。

### 既存の道具が段 0 では 3 本とも使えない

    `liftTie_case_tieFree`（`L53Subst:2615`） ⛔ **`1 <= v` が要る**。7 割の `v=0` に使えない
    `liftStage_of_noTie_zero`（`:1618`）      ⛔ `v=0` 用はあるが**タイ無し**が要る。(δ) はタイあり
    `liftStage_of_zeroRow2`（`:2036`）        ⛔ **構造的に空虚**（§206）

## ★★★ team-lead の発見: **段 0 では `Aop` の節 3 が使えない**

`Wset.lean:174` の `Aop` の節 3 は **`∃ m : ℕ, m < u`** を要求する。
**`u = 0` では `m < 0` を満たす自然数が存在しない。**

> **⟹ `W 0` は節 1（`|M| <= 1 ∧ lev M 0 = 0`）と節 2（`∀ n >= 1, M⟦n⟧ ∈ W 0`）だけで決まる。**
> **⟹ `graft` の機械が丸ごと消える。**

⟹ **「節 3（graft）が唯一の道」という (2) の議論は段 0 では成り立たない。**
段 0 では節 2 だけで降りるしかなく、それは
**「展開を繰り返して節 1（1 列以下・`lev = 0`）に着く」**ということ。
⟹ **`M ∈ W 0` のきわめて具体的な特徴づけになるはず。**
`v=0, z=0` の塔の根は `(0,0,0)` で `lev = 0` なので**節 1 の形にちょうど合う**。

**⟹ H12 が「道具が 3 本とも無い」と特定した領域は、
実は `W` の定義がいちばん単純になる領域だった。** L3 に `mem_W_zero_iff` 的な特徴づけを
書かせている（`A1`（`Wset:243`）で 1 段開いて節 3 を `Nat.not_lt_zero` で潰すだけのはず）。

## ★ (2) は `srow` に依らず 1 つの問題になった（§208、L3 の L134）

    `srow = 1` `oper_shTower`（§48）  `shTower Q e n ++ shiftr01 (n*e) 0 (Q⟦m⟧)`
    `srow = 2` **`oper_shTower2`（§56）** `shTower2 Q d e n ++ shiftr01 (n*d) (n*e) (Q⟦m⟧)`

どちらも節 2 で降りると**両端が揃い**（`Q⟦m⟧ ∈ W (lev Q 0)` は `oper_mem_of_mem`、
前半は帰納法の仮定）、**繋ぐのは連結で `rsum` が破れる** ⟹ **同じ形**。
⚠ 行 1 のシフトの可換には **`lev Q (|Q|-1) ≠ 0`** が要る（`Wset.oper_shiftr1`（`:730`）。
`srow=1` 側には不要だった条件）。

## ★ 次の一手（課題 L135）

    **1（最優先）** `v = 0` ⟹ `z = 0` を**定義から**確かめる
    **2** **段 0 で節 3 が使えないことを Lean で明示**し、**`W 0` の特徴づけ**を書く
    **3** その特徴づけで `v=0, z=0` の塔（＝ (δ) の 7 割）が扱えるか
    4 `v >= 1` の 3 割は `TieFree` の道具が残っているので後回し
## ★★★ (2) は **補題 1 本**に絞れた（H73 完了、§212）

H12 の測定（commit `961f955`。定義は `L105Cap.lean:4159`/`:3407` から写した）:

    **塔単位**（2 箱 × `|R|`=2〜5 × `n`=2〜6）… **165576 塔で食い違い 0**
    **ブロック単位**（錐がブロック局所か）    … **34326 ブロックで食い違い 0**
    **陽性対照**（マスクを 1 列ずらした版）    … 31128 で **100% 鳴る**
    (q2) 第 2 ブロックのマスクが第 1 と違う例 … **見つからず**

> **⟹ L3 が証明すべき補題は 1 本:
> 「`operTower` の第 `k` ブロックの `le1` 錐は、そのブロック単体の錐と一致する」（`k >= 1`）**
> **`k = 0` は `Wset.le1_take`（`:908`、緑）で既に出ている。**

**⟹ 出れば `mTower = operTower` ⟹ `mTower` の形で立て直せる ⟹ succ 形が書ける
⟹ (2) の帰納が `srow = 1` 側とまったく同じ形になる。**

★ **R2 の 2 本が直接効くはず**（H12 の見立て。ブロックは `Lift1` と `shiftr01` でできている）:

    **`Wset.le1_Lift1`（`Wset.lean:1213`、緑・無条件）** 錐は **`Lift1` で動かない**
    **`Core.le1_shiftr01`（`Core.lean:3470`、緑・無条件）** 錐は **行 0 の一様シフトでも動かない**

⚠ H12 の但し書き:「**これは実測であって証明ではない。`operTower` で核を立てたままにしているのは
正しい判断（教訓 14）。私が出せるのは的だけ。**」

## ⚠⚠ (1) の本線は **計器が 0% だった領域**（H12 §168）

    **`v = 0`** … 決定率 **0%**（432 件すべて未判定）。**予算を 27 倍にしても動かない**
    `v = 1` / `v = 2` / `v = 3` … 33% / 50% / 50%

> **⟹ 残核の中心（`v=0`・タイあり）は反証器が 1 件も判定できなかった領域。
> 測定側から援護は期待できない。証明でしか埋まらない。**
> ⟹ **「段 0 で `Aop` が 2 節に縮む」という構造の単純さが唯一の足がかり。**

## 計器の教訓（`CORES.md` 冒頭）

    21 「100% の不変量」は報告前に必ず 1 段長い母集団で壊す
    22 陰性対照は壊し方を 2 種類以上、「どの葉で鳴ったか」を記録する
    23 「反例ゼロ」の前に前提の充足率（分母）を数える
       **—— 「無料で落ちる枝」を数え上げるときも分母が要る**（(γ) はこれで空虚と判明）
    24 候補補題は測る前に `grep` する
    25 「この補題で無料」と書く前に、**結論の段と向き**を紙に書き下す
    （R2）緑の補題を実測で検証するときは、**前提を `file:line` から写してから**測る
    （team-lead 43）「消費側が仮定を持っているか」は**帰納の内側に入る引数まで**追う
    26 **割合を報告するときは「単位」（列単位か事例単位か）を必ず書く。
       場合分けが効くのは事例単位だけ**（`|R|=2` では両者が一致して違いが見えない）

## 検算（team-lead 自身）

    `lean/` に **`sorry` は 1 つも無い** ／ `leanman build` **809 jobs / exit 0**
    `Final.lean:353` `TRIO_terminates_of_towerExpBigRow2`（**仮定 1 本**）
    `SESSION-2026-08-28.md` は 2 ファイルに分裂していたので統合ずみ（`95a625a`）

## ⚠⚠⚠ 実測はもう誰も守らない —— 反証器は**全核に盲目**（§147）

R2 の定理（定義からの算術、`R2-NOTES.md` §R94）:

    `oper`（`Trio.lean:98`）は**第 1 列を絶対に落とさない**
      （`j0=0` でも flatMap の `k=0, j=0` の項が `M[0]` そのもの）
    ⟹ 木のどのノードも先頭列は `S[0]` ⟹ **到達する単元は `[S[0]]` だけ**
    ⟹ **反証器が False を返す ⟺ `lev S 0 > a`**

結論の根の `lev` が前提から自動で上界に収まる核は**絶対に鳴らない**:

    `WCat` `WSnoc` `CoreCap` `TowerOK*` `LiftTieSelf` `LiftTieCore` … **全部該当**
    （`LiftTieCore` の根は `(0,v+1,z)`、`lev = 2v+z+2` ＝ 上界とちょうど等しい）

⟹ **H12 の「全核で確定した反例ゼロ」は空虚だった。**
⚠ **陰性対照も空虚**（「段を 1 下げると鳴る」は計器が唯一見られる種類の偽を作っているだけ。
**対照の設計は team-lead の指定。H12 の規律の問題ではない**）。
⚠ `inW` のメモのバグ（`None` を深さ抜きで恒久保存、修正版 `tools/dbms/winw.py` の `inW2`）。
`False` の健全性には影響しないが `ok`/`unknown` の内訳には影響する。

**⟹ `LiftTieCore` が真である外的証拠は、いま存在しない。残るのは Lean の証明だけ。**

## 教訓 13（3 度目の書き直し）

    1 度目 「健全な反証器は原理的に存在しない」 → 誤り（`Wchar.lean` にあった）
    2 度目 「健全な反証器は存在する」           → 正しいが不十分
    3 度目 **「存在するが射程は `lev S 0 > a` だけ。我々の核はどれも段を保つ形に
            設計されているので、設計上どれ 1 つそこに入らない。反証器は全核に盲目。」**

## ⛔ `split_lastTie` 路線は繋がらない（L3 の判定）

> **タイの分解は接頭辞を短くするが、`Lift1` は列ごとではなく「根の錐」という大域的な
> 条件で決まるので、接頭辞の結果を全体に戻せない。戻す操作が `WCat` になる。**

（`Lcone.le1_zero_iff` `:36`: `le1 X 0 i` ⟺ `i` の根以外の行 0 祖先が全部 `row1 > v`。）

## ★ 次の一手（課題 L116 / H60）

**窓分解（`Lind.graft_take_drop`、`Lind.lean:63`）で切る** —— 行 0 の祖先鎖に沿って。
`Lind` の長さ帰納がその切り方なのは偶然ではない（§143 の (B)）。

    L116 … 窓の**外**が一様シフトに潰れるなら `ulift_mem_W` で無料。
           窓の**内**だけが残るならそこが真の核。繋がらないなら**どこで止まるか 1 行**
    H60  … `LiftTieCore` の実例で **`Lift1` と一様シフト `shiftr01 0 1` の差分**を出す。
           食い違う列の性質（行 0 祖先鎖のどこか、行 1 の値）を L116 と突き合わせる

## 核の同値（今日判明。すべて緑）

    **`CoreSingleton` ＝ `CoreCap` ＝ `GraftAll`** … 同じ命題の 3 つの名前
      `Lind.lean:181`/`:195` ／ `L105Cap.lean` §25 `coreCap_iff_graftAll`
      `graft M [(0,b,c)] = cap M b c`（`Lind.lean:169`）で `y` が 1 列に見えていた

⚠ **核の大小は仮定の本数でも量化子数でも測れない**（教訓 33）。今日 2 通りとも壊れた。
正しい比べ方は**鎖を `file:line` で開いて何が肩代わりされているかを見る**こと。

## ★ どこで止まっていたか（§143。構文レベルで特定ずみ）

> `j0 >= 1` の枝は `oper_cons_nat` で「尾が展開された同じ目標」に落ちるだけで、
> `CoreCap` は尾の `W` 導出（`Aop W u0 Wstar R`）を仮定していないので、そこで測度が無くなる。

降下の測度は **2 つあって別物**:

    (A) `Wstar` … `W` の最小不動点の**導出木**（`A2'`）＝ `TowerOK` の `Aop W u0 Wstar R`
    (B) `GX`    … `Lind.mem_GX_of_singletons` は **`y` の長さの強帰納**。展開 `⟦n⟧` は現れない

⚠ 長さでは回らない（`oper` の長さは `j0 + n*(j1-j0)`。`n=1` で減り `n>=2` で増える）。

## 反証器スイープ（H12、§144）: **全核で確定した反例ゼロ**

⛔ 欄は 6 件 → **5 件**（`Row0Free` は偽ではなく強すぎるだけ）。
⚠ 弱点 2 つ: **`TowerOK2` の決定率は 14%**（24 件で違反 0 は薄い）、
**`Aop` の節 3 側は握れていない**（250 標本すべて未判定）——
それは §143 で特定された「失われた測度」そのもの。

---

## ★★★ 残核は **`LiftTieSelf`** 1 本（§141）

    def LiftTieSelf …（`lean/L105Cap.lean` §21、L3）4 量化 / 3 前提、段は **`2v+z` に固定**
      ∀ d v z R, argOK R → (∃ p ∈ R, p.2.1 = v) → ((0,v,z) :: R) ∈ W (2v+z) →
        Lift1 ((0,v,z) :: R) d ∈ W (2v+z + 2d)

    `towerOK2_of_liftTieSelf`   ★ **`TowerOK2` ⟸ `LiftTieSelf`**（緑）
    `towerOK_of_liftTieSelf`    ★ `TowerOK` ⟸ `LiftTieSelf` ＋ `TowerExp`（緑）

`X ∈ W m` から `X ∈ W (lev X 0)` は出ないので **`LiftTie` の真の弱化**。
そして `Wstar` の元はすべて `Wself`（`L53.Wstar_iff_Wself`）⟹ **狙う場所とちょうど一致**。

## ★ `CoreCap` の債務表（R2、|M|<=4 の全数 2400 万件、破れ 0）

| 分岐 | 割合 | Lean | 状態 |
|---|---|---|---|
| `noparent` | 44.0% | `oper_eq_pred_of_noParent` | **無条件で閉** |
| `j0>=1` | 28.3% | `oper_cons_nat`（`Wset:2041`） | **無条件で閉** |
| `j0=0, srow=0` | — | `W_flatMap_copies`（`:2551`）＋ `rsum_self_cons`（`:2539`） | **無条件で閉** |
| `j0=0, srow=1` | — | `oper_cons_tower1`（`:2789`） | `TowerOK1`（節 3 の与件がある場面で既済） |
| **`j0=0, srow=2`** | — | `oper_cons_tower2`（`:3231`） | **`TowerOK2` ＝ 唯一の残核** |

`j0=0` の割合は |M| を伸ばしても **44% 前後に漸近して消えない**（|M|<=3 56.4% → <=4 49.5% → L=6 44.0%）。

## ★★ 今日の勝負どころ（課題 L113）: **`CoreCap ⟸ LiftTieSelf`**

    `CoreCap` の残債務 = `j0=0, srow=2` = `TowerOK2`、そして `TowerOK2 ⟸ LiftTieSelf`
    さらに `CoreCap` の経路（`coreSingleton_of_cap` `Lind:181` → `Final:559` → `:552`）は
    **`Wstar` / `TowerOK` / `TowerExp` を通らない**（`GX` の経路。`CORES.md` の「経路」列 C）

⟹ **通れば `LiftTieSelf` 単独で停止性が出る。文が最小で仮定 1 本という初めての形。**
怪しいのは `TowerOK2` の前提 `hgr : ∀ y ∈ W m, based y → graft R y ∈ Wstar`
（`CoreCap` の設定では `CtxOK` しか無い）。

## 核の地図（仮定の本数。`Final.lean` より）

    `TRIO_terminates_of_cap (hc : CoreCap)`                            … **1 本**
    `TRIO_terminates_of_liftTie (hlt) (he : TowerExp)`                 … 2 本
    `TRIO_terminates_of_row1down (h1) (h0) (he : TowerExp)`            … 3 本

実測: シート 4482 行のうち `TowerOK2` のタイは **24 節点（0.5%）**（H11）。

## ⛔ 撤回された「穴」3 つ（全部 team-lead の誤り。§139-140）

    「`c >= 2` が未処理」        ⛔ 生きている鎖は最初から `c` 一般。
                                 `tower2_root_z_zero`（`c=1` 限定）は**死んだコード**
    「`argOK` が木の下で破れる」  ⛔ 破れる起点は `srow=0` の塔だけ。しかもそこは
                                 `rsum_iff_based_of_root_mem` により**無料側**
    「親が根でない枝がある」      ⛔ `domT` があれば `parent_cons_eq_zero` が
                                 親 = 根を無条件に与える。**その枝は存在しない**
                                 （`TowerOK` の設定と `CoreCap` の snoc 残核の混同）

## `CoreCap` 側の現在地（`TowerOK` 側とは設定が違う）

`CoreCap` の snoc 残核では `domT` が**成り立たない**ので `j0 >= 1` が起きる（R2 実測 24.0%）。
そこは `oper_cons_nat`（`Wset.lean:2041`）の枝。**`TowerOK2` の枝とは別**。

    `rsum_iff_based_of_root_mem`  ★ **`rsum A Q` ⟺ `entry Q 0 0 = 0`**（接頭辞が根を含むとき）
    `prefixCopies_of_based`       ★ **`PrefixCopies` は写す塊が基づくなら仮定ゼロの定理**
    ⟹ 「`W_add` が死ぬ」と「`rsum` は成り立つ」は**同じ二分法の裏表**:
       `argOK` 生存 ⟹ 塊の根が深い ⟹ `rsum` 破れ
       `argOK` 破れ ⟹ 塊が基づく   ⟹ `rsum` 通る

## ⚠ `WSnoc` 路線は循環している（§131、ただし §133 で条件付きに訂正）

    塔の 1 段追加 shTower Q e n ++ shiftr01 (n*e) 0 Q の rsum は **n*e <= 0** を要求
    ⟹ **`d0 >= 1` のときだけ**破れる（`d0 = 0` なら塔が無いので無関係）
    ⟹ rsum なしの連結 = `WCat` が要る ⟹ `WCat` は残核より広い ⟹ `WSnoc` は循環

**⟹ `coreCap_of_wsnoc`（`L105Cap.lean`, 緑）は正しい含意だが前進ではない。**
L3 の副産物「**`CoreCap` の段リフト `t` は自由変数**。`t=0`/`t>=1` の場合分け不要」は残る。

## ⛔ 死んだ逃げ道: 「`CtxOK` の `∀ k`（接頭辞の鎖）」（§133）

`Wset.W_take`（`Wset.lean:2120`）は **無条件**で `M ∈ W u → M.take k ∈ W u`。
⟹ 接頭辞の鎖は `C ∈ W u` からタダ。`SnocPrefixOpen ⟺ WSnoc`（緑）。**接頭辞版の核は無意味。**

生きている差は 2 つだけ:

    (a) `CtxOK` の **`∀ t`**（リフト族）… 無料ではない。唯一の未使用資源
    (b) **主語の形** `Lift1 ((0,v,z) :: R) t`（`argOK R`, `z <= 1`）

このどちらでも `wcat_of_snoc` の適用が構文的に止まる。その形の核が緑になった:
**`CapSnocOpenExact ⟺ CoreCap`**（`lean/L105Cap.lean:§13`）。

## いま走っているエージェント（2026-08-30）

    L3  … 課題 L106（`WSnocCtx` を定義し `CoreCap ⟸ WSnocCtx`、`WCat` 非含意を確認）
    H12 … 健全な反証器を全 28 核に。**`WCat` → `WSnoc` を先頭に**（7 行がぶら下がっている）
    R2  … 課題 R89（上の分岐測定）＋ `lean/CORES.md` の状態列の同期

---

## 0-0. ⚠ **最良の到達点は今日の作業の外にある**（§126）

    `lean/Lind.lean:132`   **`CoreSingleton := ∀ b c, [(0,b,c)] ∈ GX`** —— **1 列についての 1 文**
    `lean/Final.lean:559`  **`TRIO_terminates_of_core (hs : CoreSingleton) : WellFounded stepRel`**

**これが今日より前からの到達点。今日 `Wstar` 路線で削った核（`TowerOK2` ほか）は
これより弱くない。** 両路線は比較不能だが、**狙うなら `CoreSingleton` のほうが小さい。**

⟹ **明日の最初の一手は「路線の選択」**。**まず `lean/CORES.md` を見ること。**

    **`lean/CORES.md`** … `TRIO_terminates_of_*` の仮定 **28 本**の一覧
      量化子数 / 前提数 / `GX` 込みの実効値 / 主語の大きさ / 経路 / より強いもの / 状態
      **⛔ 偽・空虚 6 件**（`InfEquip` 偽 / `TieFree` / `AminROper` 偽 / `WConvex1` /
        `Row0Free` 強すぎ / 族形 3 本は同語反復）
      **極小元 3 つ**: `CoreCap`（7 量化 / 5 前提、`GX` 無し）/
        `CoreSingleton`（`GX` 込みで実効 9 / 5）/ `TowerOK`（3 / 7）
      ⚠ 冒頭に「**代理指標にすぎない。順位表ではない**」の警告あり
        （`WCat` は文が最小（3/2）なのに残核より広い —— 表でいちばん危ない罠）

⟹ **`CoreCap` が第一候補**（§128: 前提が 4 本少なく、`t=0` の場合は今日の `WSnoc` そのもの）。

以下は今日の `Wstar` 路線の記録。

## 0. 検算（team-lead が自分で回した、2026-08-30 夜に更新）

    leanman check -C /home/koteitan/proofs/dbms/lean lean/Final.lean  ⟹ **exit 0（緑）**
    `trio_cofinality`（`Core.lean:4602`）は仮定が `ST_TS M` / `ST_TS N` だけ ＝ **無条件**
    ⚠ 訂正（2026-08-30 夜、team-lead 自身が検算）: **`lean/` に `sorry` は 1 つも無い。**
    以前ここに「`Dbms.lean` 1 本だけ」と書いてあったが、`Dbms.lean` の 2 件は
    **コメント内の言及**（`:67` `:74`）で、`sorry` 項ではない。
    `leanman build` 809 jobs / exit 0 ＋ `sorry` トークンゼロ ⟹ **`sorryAx` 依存もゼロ。**

    連鎖: `TowerOK` → `Wstar_closed` → `wf_olt_ST_TS_of_cofinality`（＋無条件の共終性）
          → `wf_Rnf_of_wf_TS` → `step_terminates` → **`WellFounded stepRel`**
    併せて `no_infinite_expansion_of_towerOK`:
      **¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i+1))**
      ＝ 「z<2 の標準形に無限展開列は無い」そのもの

## 1. 到達点

    lean/Final.lean
      **TRIO_terminates_of_towerOK (htow : Wset.TowerOK) : WellFounded stepRel**
      （`leanman check` exit 0 / sorry 0、commit `ff2bdff`）

`Wstar` 路線（2 行の完成証明 `lean/Pair/Wset.lean` と同じ道筋）では
**共終性 `trio_cofinality` は無条件**、`Wstar` の閉性が `TowerOK` だけを要求する。

## 2. `TowerOK`（`lean/Wset.lean:4365`）の場合分けと状態

| 枝 | 状態 | 根拠 |
|---|---|---|
| `srow = 1` | **証明ずみ** | `towerOK1_of_clause3` |
| `srow = 2`, `z = 1` | **起きない** | `tower2_root_z_zero` |
| `srow = 2`, `z = 0`, 無タイ | 根リフトは全 `v` で通る | `liftStage_of_noTie` |
| ↑ の `n` の帰納 | 債務 1・2 は済み、**債務 3 が残り** | `L53Subst.lean` |
| `srow = 2`, `z = 0`, タイ有り | 分解で割れる（実測 2474/2474）| `split_lastTie` |

### 残る核（§120 で §116・§117 を訂正）

⚠ **`TowerOK2` 単独では足りない。** `towerOK1_of_clause3` は**節 3 の与件**を要求するので、
**節 2 から来る `:4447` の枝では `TowerOK1` が落ちない**（R1 の R83）。

    `Wset.lean:4461`（節 3 / `srow=2`）… `TowerOK1` は落ちる。**`TowerOK2` が残る**
    **`Wset.lean:4447`（節 2）… `TowerOK1` も `TowerOK2` も残る**

`natDom` のガードで `:4447` を消す道は **`:4470`（dead root の逃げ道）を塞ぐので不可**（§119・§120）。
**理由は行 2 に段の上界が無いこと** —— 行 1 の孤児は自動的に根の段より下だが、行 2 は違う。
**これが 2 行 / 3 行の非対称性の正体。**

### （旧）残る核は `TowerOK2` 1 本 —— §120 で訂正

    `srow = 1`         **証明ずみ**（`towerOK1_of_clause3`）
    `srow = 2`, `z=1`  **起きない**（`tower2_root_z_zero`）
    `srow = 2`, 狭義   **証明ずみ・仮定ゼロ**（`towerOK2_of_strict'`）
    `srow = 2`, 無タイ **証明ずみ・仮定ゼロ**（`towerOK2_of_noTie'`）
    **`srow = 2`, タイ  残り**

⚠ **§107 の「`Subst1gRevive` ＋ `WSnoc` の 2 本」は過剰還元だった**（§116）。
2 行の `Wstar_closed` は**仮定ゼロ**で、鍵は `rsum_self_cons`（根の深さ 0 で自明）と
`oper_cons_nat`（末尾が `R` 内で親を持てば cons が保たれコピーが出ない）。
⟹ **「接頭辞つきコピー」は `Wstar` の道筋に原理的に現れない。**
3 行にも道具は全部あるので、**2 行の分岐を逐語で移せば `TowerOK2` だけが残るはず**。

今日作った `PrefixCopies` / `WSnocOpen1` / `WstarSnoc` / `MliftR` / `WConvex1` は
**道筋に現れない経路のもの**。道具として残すだけでよい。

### 実測はすべて通った

    伝播（`graft R (Lift1 (X⟦n⟧) t)` が `argOK` かつ無タイ）
      … **20000 件・n=1..12 で破れ 0**（対照つき、§78）。`argOK_Lift1` は緑
    タイ側の帰納 … 分解 100% 通る ＋ **最大 3 段**で無タイに帰着。`split_lastTie_len` で長さの帰納

**独立な裏づけ（§117、確定形）**:

> **`TowerOK2`（`srow = 2` の枝、しかもタイの場合だけ）を証明すれば、
> BM4-Analysis ブック全 7 シート 20415 行（`ψ(Ω_ω)` から `ψ(K·ω)` まで）と
> 対角生成元 `D_1..D_12` が、Lean で証明ずみの規則だけで `Wself` に入る。**

    `TowerOK2` だけ … **20415 / 20415**（予算 20000 でも 200000 でも同じ）
    対照 strict     … **9**
    `Subst1gRevive` ＋ `WSnoc` を足しても**変わらない**（§107 の 2 本は不要だった）

⚠ 門は含意地図を符号化したものなので、これは**地図が正しいことの帰結**であって
地図の独立検証ではない（R1 の但し書き、§117.1）。

## 3. 主要な補題（全部証明ずみ）

    lean/Wset.lean
      Wstar :2684 / **Wstar_closed (htow : TowerOK) :4372** / mem_Wstar :4646
      mem_W_of_bound :4732 / W_membership :4749 / wf_olt_ST_TS_of_cofinality :4757
      oper_cons_nat :2041 / oper_cons_succ :2392
      oper_cons_tower1 :2789 / **oper_cons_tower2 :3231**
      W_shift :1320 / W_shiftl0 :2246 / W_add :1682 / W_flatMap_copies :2552
      argOK :1314 / graft_cons :2545 / rsum_self_cons :2539
    lean/Wtower2.lean
      Le1 :333 / **liftStage_of_window :128** / Lift1_eq_mlift_of_tieFree :76
      snoc_zeroRow2 :3127 / snoc_orphan :3053 / snoc_flat_root :2208
      W_drop :2870 / W_segment :2981 / mem_Wself_iff :2991
    lean/Wslift.lean
      **ulift_mem_W :461**（`shiftr01 0 d X ∈ W (m+2d)`）
    lean/Lcone.lean
      **le1_zero_iff :36**
    lean/Pair/Wset.lean（2 行の完成証明）
      **split_lastMin :512** / Wstar :840 / Wstar_closed :1310 / mem_W_of_bound :1537
    lean/L53Subst.lean（今日書いたもの）
      comm_of_noRevive / split_lastMin（3 行版）/ tree_shift3 / argOK_normalize / Wstar3
      towerOK1_of_clause3 / tower2_root_z_zero / tower2_stage_fits / tieSyn_holds
      liftStage_of_window 系 / liftStage_of_noTie / **split_lastTie**

## 4. 順序数の地図（`bms -c` と BM4-Analysis ブックで確定）

    `(0,0,0)(1,1,1)` = **ψ(Ω_ω)** ＝ 2 行 BMS の極限（`psiI.json` 行 267）
    ── ブック全 7 シート（`ψ(I)` … `ψ(K)` … `ψ(K·ω)`）が**まるごとこの間に入る** ──
    **`(0,0,0)(1,1,1)(2,2,1)` = `D_2`** ＝ ブックのどの行列よりも大きい
    `(0,0,0)(1,1,1)(2,2,2)[v]` を展開すると `D_{v+1}`（yaBMS で確認）

## 5. 計器（進捗指標）

    `tools/dbms/ladder.py` … シートを先頭から連続で何行覆えたか（**`JUNCTION_RSUM=True` が健全**）
    `tools/dbms/wcert2.py` / `r66.py` / `r68.py` … R1 の証明書エンジン
    `tools/dbms/h1/h4*.py` … H11 の構造測定

**公式スコア（証明書エンジン路線）**: Lean 換算 **9 行**、C13 込み 10 行。
⚠ この指標は `W_add` で組み上げる路線のもの。**`Wstar` 路線の進捗指標ではない**（§69.1）。

## 6. 今日の教訓（11-16）

    11 母集団の定義が結論を決める（ランダム小行列の 71% はシートで 0.2%）
    12 計器が命題より強いことがある
    13 ⚠ **訂正（§130）**: 旧「反証器は原理的に鳴らない」は**誤り**。
       `Wchar.lean` に `⟺` の特徴づけが 2 本ある（`mem_iff_oper_mem` `:75` /
       `mem_iff_lev_le` `:106`、`aop_clause3_to_clause2` `:39` で節 3 が吸収される）
       ⟹ **健全な反証器は存在する。**
       新: **「原理的に不可能」と言う前に、厳密な特徴づけが既にないか確かめる。**
       「出せない」と「探したが出ない」は別の主張で、後者のほうが強い証拠。
    **14 神託は「証明したい定理の文」と 1 対 1 に対応させる**
       （`A ++ X ∈ W` を仮定すると連結が黙って入る。覆い 100% → 0.2%）
    **15 兄弟プロジェクトの越え方は、壁を特定した直後に見に行く**
       （CLAUDE.md に「lean-yapss に倣う」と書いてあるのに 1 日追ってから見た）
    **16 母集団を広げるときは、広げ方が仮定の量詞と合っているかを先に確かめる**
       （`Wstar_closed` の `v` は `R` と独立の全称なのに、シートの行から作ると `v=0` 固定）

## 7. 明日の最初の一手

    1. **無タイ条件の伝播**を測る（H11 の H50）。保たれるなら `towerOK2_of_noTie` が閉じる
    2. 閉じたら **タイ側**（`split_lastTie` の帰納、実測 2474/2474）
    3. `Final.lean` の 20 本の含意地図（R1 の R71）で `TowerOK` の位置を確認
