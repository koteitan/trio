# 現在地（2026-09-01 未明）

## ★★★★★★ 残るは **2 点だけ**。しかも `z` について**相補的**

`Final.lean:875`（team-lead が `leanman build` **809 jobs / exit 0** で検算、`sorry` 0）:

    **`TRIO_terminates_of_mTowerClosedRow2 (h : L105.MTowerClosedRow2) : WellFounded stepRel`**

    **A 側 `TowerSnocRoot`**（`L105Cap:7806`、§105）… **`z = 0` 側が重い**
      ⚠ **§110 で `MTowerClosedS` と同じ文だと判明**（`oper_snocRoot`、緑:
        `(Q ++ [r])⟦m⟧ = mTower Q d e m` ＋ `Wchar.mem_iff_oper_mem`）
      ⟹ **「塔が消えた」のは別問題にしたのではなく、同じ問題の最小形に書き直したもの**
      **`Q ∈ W u` ＋ `2 <= |Q|` ＋ 根が狭義最浅**
      **⟹ `Q ++ [(entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0)] ∈ W u`**
    **B 側 F2b（`z = 1`）**（§93）… **「命題が偽」＝ 復活を認めた上で示すしかない**
      （`mTower` は行 2 を動かさないので `+k*d2` が無い ⟹ 行 2 の壁は `¬F2b` でしか作れない。
       R2 の**実反例 1,812 件**）

> **⟹ どちらか一方だけでは `z<2` 断片は閉じない。両方要る。**

## ★★★ 今日 (D) から始まった連鎖（全部緑。R2 の実測 130 万件が定理に）

    §84 **(D)/(E)** `gexp_cone_mir_zero` … **`hj0` の使い所を「数えた」**（3 か所）
    §86 **行 0 の壁** ／ §98 **ブロックの根は塔の錐に入る** ／ §99 **鎖の反復**
    §87 **行 1 の壁（錐の中）** ／ **§107 行 1 の壁（錐の外）**
    §100・§102 **F1 `gexp_orphan_row1`**（任意の `(k,q)`）… R2 の **376,164 件**
    §106 `nextrel2` は同ブロックで `Q` と一致（**索引で `le1` を通らずに済んだ**）
    §108・§109 **F2a `mTower_orphan_row2`** … R2 の **933,768 件**

**L3:「(D) が落ちていなければ、どれも書けませんでした。」**
**そして (D) は R2（24,510 件）と H12（152,208 件）が「必要十分」と測った文。**

### ★ §107 の機構（今日いちばん短く言える形）

> **錐の外にする張本人が、同じブロックの中の行 0 祖先。それはリフトされないので、
> `nextrel1` の極小性が越境を殺す。G1/G2 の場合分けは要らない。**

**⟹ そしてそれは R2 の (a2)（「錐の外 ⟺ 行 1 の親鎖上にブロッカーがある」）が
言っていたこと。**

## ★★ 道具: **`lean/LEMMA-INDEX.tsv`**（2,946 件、`python3 tools/dbms/mkindex.py`）

**L3 が 9 回、既存の補題を書き直したので team-lead が作った。4 回効いた:**

    §98  「足りない 1 文」が `le1_zero_iff` として既にあった
    §106 **設計を 3 段から 1 段に**（`nextrel2_append_right` が全部運ぶ）
    `Gamma.le0_of_le1` が 1 回の grep で出た（10 回目の再発明が起きなかった）

    grep -i "nextR_src\|src_ge" LEMMA-INDEX.tsv     # **概念語**
    grep "theorem snoc_" LEMMA-INDEX.tsv            # **接頭辞**
    grep "le1 (Lift1" LEMMA-INDEX.tsv               # **型の断片** ← いちばん効く

⚠ **索引は型しか持たない。docstring は入っていない**（`nextR_src_ge` は docstring が本質を語る）。

## ⚠ 測定と証明の関係（今日 5 回起きた形）

> **測定が「証明すべき文」を特定し、証明がその測定を不要にする。**

| 枝 | R2 の実測 | いま |
|---|---|---|
| (D) | 24,510 ＋ 152,208（H12） | **定理**（§84） |
| **F1** | **376,164** | **定理**（§102） |
| **F2a** | **933,768** | **定理**（§109） |
| **F2b** | **1,812（0.50%）** | **残る 1 点。命題が偽** |

## ⚠⚠ 今日の教訓（`CORES.md` 21-29 に加えて）

    **教訓 45（L3 の改め）** 反例の形を書くのは**半分**。**充足率を自分で見積もる**まで 1 セット
    **教訓 51** 「壊しにいけ」の前に **結論の形**（等式 / `W` 所属）と **根の `lev`** を見る
    **教訓 52** 実測を中継するときは、元の報告の ⚠ 行を**そのまま貼る**。要約しない
    **教訓 54** 同じ誤りが 9 回出たら、**規律ではなく道具**を作る
    **教訓 55** 軸を指定する前に「**測る量が何を引数に取るか**」を定義で見る
    **教訓 56** 他人の結論を使うときは **`>=` か `=` か**を引用符ごと確かめる
    **教訓 57** 見立てには必ず「**これは見立て**」を付ける（8 回外れても安く訂正された）
    **教訓 58** 相手の測定を疑うときは、結論（「箱の産物だ」）ではなく
              **自分の状態**（「機構が見えない」）を書く

## ⚠ team-lead の今日の外し（8 件。全部エージェントが捕まえた）

    1 「`srow=2, z=1` は起きない」／2 「塔を 1 段進めれば `v` が変わる」
    **3** 「`srow=0` は `snoc_flat_root` で無料」… **主語違い**
    4 「`Aop` があるほうが強い前提」／**5** 「`hblk` 破れ ⟹ `lift_oper_of_noParent`」… **主語違い**
    **6** 「行 2 の上限を 3 段振れ」（`le1` は行 0/1 しか見ない）… **課題設計の誤り**
    **7** 「`j0 = (n-1)|Q|`」… L3 の `>=` を等号として使った
    **8** 「`j = 0` は特別ではない」… **1 列は自分の中に親を持てない**

**当たったもの: `srow=1` で `e=0` ⟹ 段が動かない／`j` で帰納する案（§94 になった）。**

> **⟹ 定義を開いたものは当たり、開かずに構造から推測したものは 8 件とも外れた。**
> **そして `snoc_flat_root` では 3 回、同じ補題で同じ穴に落ちた**
> （主語 → 転記 → 前提の読み落とし。**索引で型を見れば全部見えた**）。

**中継で但し書きを落としたのが 4 回**（`LiftFlatMapLocal` の箱／`snoc_flat_root` の主語／
R2 の教訓 14／§79 の 3 形のうち F2b）。

## ⚠⚠ 次に計器担当を置くときの申し送り（H12 の最後の助言）

> **本線（`v=0` 側）は反証器の決定率が 0% だった領域**（432 件すべて未判定、
> **予算 27 倍でも動かない**）。**測定側からの援護は期待できない。
> そこを測らせないほうがよい（時間を溶かす）。**
> **足がかりは「段 0 で `Aop` が 2 節に縮む」という構造の単純さだけ。**

## 計器の教訓（`CORES.md` 冒頭 21-27 ＋ R2 と team-lead の分）

    21 「100% の不変量」は報告前に必ず 1 段長い母集団で壊す
    22 陰性対照は壊し方を 2 種類以上、「どの葉で鳴ったか」を記録する
    23 「反例ゼロ」の前に前提の充足率（分母）を数える
       —— **「無料で落ちる枝」を数え上げるときも分母が要る**
    24 候補補題は測る前に `grep` する
    25 「この補題で無料」の前に結論の**段と向き**を書き下す
    26 割合には**単位**（列単位 / 事例単位）を書く
    **27 「0 件」も「100%」と同じ危険度で扱う。
       そして「機構は導いていない」という但し書きは免罪符にならない**
    （R2）緑の補題を実測で検証するときは、**前提を `file:line` から写してから**測る
    （R2）数字を共有するときは最初から**「箱」「単位」「分母」「サンプリングの有無」**を添える
    （team-lead 43）「消費側が仮定を持っているか」は**帰納の内側に入る引数まで**追う
    **（team-lead 45）「反例が起きるとしたらどういう形か」を先に書き、
       その形が母集団に入っているかを数える**（陽性対照は前提の非空虚性しか示さない）

**21-26 が「測る前に、測れているかを測れ」なら、27 は「測ったあとで、箱を疑え」。**

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
