# 現在地（2026-08-30 深夜）

## ★★★★★★ **3 行 z<2 の停止性は `TowerExp` 1 本に落ちた**

    `Final.lean:318`  **`TRIO_terminates_of_towerExp (he : Wset.TowerExp) : WellFounded stepRel`**
    `L105Cap.lean:2705` `towerOK_of_towerExp := towerOK_of_exp he towerGraft2Single_holds`
    （team-lead 検算: `leanman build` **809 jobs / exit 0**、`leanman check Final.lean` **exit 0**）

    def TowerExp（`Wset.lean:4506`）—— **開核 B**
      ∀ v z m a R, argOK R → R ≠ [] → z <= 1 → 2v+z <= a → domT R m →
        **(∀ n >= 1, R⟦n⟧ ∈ Wstar)** →
        hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R| →
        ∀ n >= 1, ((0,v,z) :: R)⟦n⟧ ∈ W a

### どうやって落ちたか（§163）

    1. R2 の §R98 … `domT R m` ⟹ 末尾は孤児 ⟹ `|R| >= 2` なら `R⟦n⟧ = R.dropLast`
                     ⟹ **節 3 に `y := []` を入れると節 2 そのもの**（仮定ゼロ）
                     ⟹ `TowerGraft2` が要るのは **`|R| = 1`** だけ
    2. `Wchar.aop_clause3_to_clause2`（`Wchar.lean:39`）… **既に存在していた**
    3. **`L105.towerGraft2Single_holds`**（仮定ゼロ、緑）… `|R| = 1` の `TowerGraft2` は**定理**
         `|R|=1` ⟹ `R.dropLast = []` ⟹ `graft R y` は `y` の行 0 をずらすだけ
         `Lift1` も `graft` も**行 2 を動かさない** ⟹ **塔の全列の行 2 が根の `z` に等しい**
         行 2 が定数 ⟹ 末尾列は**必ず孤児** ⟹ `oper` は `Pred` ⟹ 根の単元まで剥ける
    4. ⟹ **`towerOK_of_towerExp`**

⟹ **`TowerGraft2` / `LiftTie` / `LiftTieSelf` / `LiftTieCore` / `WConvex` 系は
核としては消えた。** 今日の午後ずっとそこを削っていたが**本線ではなかった**。
**道具は残る**（`srow_Lift1` / `liftStage_of_zeroRow2` / `le1_root_of_rtg0` / `srow_lowerAt` /
`constRow2_mem_W` は `TowerExp` でも使える可能性が高い）。

## ★★ さらに `TowerExpBig` まで絞れた（`L105Cap.lean:2752`、緑）

    `towerExp_singleton`       ★ **`|R| = 1` の `TowerExp` は定理**（仮定ゼロ）
    `oper_eq_dropLast_of_domT` `|R| >= 2` なら `domT` から `R⟦n⟧ = R.dropLast`
    **`towerOK_of_towerExpBig (h : TowerExpBig) : TowerOK`**（`:2770`、緑）

    def TowerExpBig
      ∀ v z m a R, argOK R → **2 <= |R|** → z <= 1 → 2v+z <= a →
        domT R m → **`R.dropLast ∈ Wstar`** →        ← **`∀ n` が消えた。仮定 1 本**
        hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R| →
        ∀ n >= 1, ((0,v,z) :: R)⟦n⟧ ∈ W a

## ★ 次の一手（課題 L121 / R102 / H64）

**`|R| = 1` の証明の骨がどこで効かなくなるかを特定する:**

    `|R| = 1`  … `R.dropLast = []` ⟹ `graft R y` は `y` の行 0 をずらすだけ
                 ⟹ **塔の全列の行 2 が `z`** ⟹ 末尾は必ず孤児 ⟹ `oper` は `Pred`
    `|R| >= 2` … `graft R y` の胴体に **`R.dropLast` が入る**
                 ⟹ その行 2 は `z` とは限らない ⟹ **行 2 は定数でなくなる**

⟹ **`|R| = 2` で `R.dropLast = [(d,b,c)]` の行 2 `c` が `z` と違うとき、
何が末尾列の孤児性を保証するのか。そこが `TowerExpBig` の本体。**


    `domT R m` ⟹ `|R| >= 2` なら `R⟦n⟧ = R.dropLast`（全 `n`）
    ⟹ **仮定 `∀ n >= 1, R⟦n⟧ ∈ Wstar` は `R.dropLast ∈ Wstar` と同値**のはず
    ⟹ `TowerExp` は実質 **「`R.dropLast ∈ Wstar` ⟹ `((0,v,z) :: R)⟦n⟧ ∈ W a`」**

    L121 … 上の同値を緑に（`∀ n` が消えて量化子が 1 本減る）。
           ⚠ **行 2 の定数性は `|R| >= 2` では効かないはず**（`graft R y` の胴体に
           `R.dropLast` が入り、その行 2 は `z` とは限らない）。効かない場所の特定が本題
    R102 … (m1) `((0,v,z)::R)⟦n⟧` の閉じた形を `|R|=2,3` で書き下す
           **(m2) 塔の各列の行 2 —— `|R|=1` では定数 `z` だった。
           `|R|>=2` で定数でなくなる場所の特定が本題**
           (m3) それでも末尾列は孤児か (m4) `(0,0,0)(1,1,1)(2,2,1)` ＝ `D_1` を完全に

## 残核の塔の閉じた形（R100、`|R| = 1` の場合）

    **((0,v,z) :: [(d,b,c)])⟦n⟧ = [ (k*d, v + k*(b-v), z) | k = 0..n-1 ]**   900/900

**`c` は塔に現れない**（1 段で行 2 が `z` に潰れる）。行 0 は公差 `d`、行 1 は公差 `b-v`。
⟹ L3 の `towerGraft2Single_holds` の設計図になった。

## 検算（team-lead 自身、2026-08-30 深夜）

    `lean/` に **`sorry` は 1 つも無い**（`Dbms.lean` の 2 件はコメント内の言及）
    `leanman build` **809 jobs / exit 0** ⟹ **`sorryAx` 依存もゼロ**

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
