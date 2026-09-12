# 壁

## いまの状況（先にここを読む）

- 壁は 1 本。**走りを 1 本伸ばす**こと。行列で言うと
      R375m ++ [(6,1,0)]   いま開いている最小の行列
      R375m ++ [(6,2,0)]   走り 3 連（`R375m_62_of_bdA2`、条件つき）
  `R375m = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)` は緑（`R375m_mem`）。
- 準位の鎖: `R338` →(単位 `(1,1,0)(2,2,1)`, `hangU11`)→ 準位 3 →`(3,1,0)`→ `R344`
  →`(4,2,0)`→ `R373` 準位 4 →`(5,2,0)`→ `R375m` 準位 5 →**吊るし 6 が壁**。
  2 の記録 1 本ごとに準位は上がる（`Stk`）。上がらないのではなく、上げる
  **一様条件**が「2 の記録が k 本乗った族の元にもう 1 本足す」＝走りになる。
- いちばん弱い仮定は `FoneB`（`R376_of_FoneB`、緑）。還元は 30 本以上ある（下の表）。
- `TwoOk` 版（`TwoOk Z` = 「`Z` を 2 の記録の直上に置ける」）で言うと**`two nil` 1 枚**:

      TwoOk nil / TwoOk (pay nil B) / TwoOk (two nil nil)   ★全部緑
      TwoStepP : Bok B → TwoOk (two nil (pay nil B))        ★壁

  `TwoOk_pay`（荷の W 帰納）が回るのは鎖が最上段のときだけ。1 段上げると
  鎖 `twoIt nil (pay nil Y) n` も 1 段上がって `TwoStep` に化ける（追記344）。
- **★ 荷を外した形**（追記347、2026-09-13 に緑）:

      ChBase : ∀ X, JkA X → TwoOk X → TwoOk (two X nil)
      TwoStepP_of_ChBase : ChBase → TwoStepP                  ★緑
      R375m61_of_ChBase  : ChBase → R375m ++ [(6,1,0)] ∈ W 0  ★緑

  `TwoOk_pay`（荷の W 帰納）を 1 段上げたもの。鍵は
  `plug (ctx ++ [ftwo N]) T = plug ctx (two N T)` で**文脈を 1 段伸ばして**
  `GoodFb_snoc_dupJt0` / `GoodFb_snoc_innerJt0` をそのまま使うこと。
  `TwoOk_twoWlNil`（緑）は兄弟に `Rq ks Wl`（＝`TopOk Wl`）を課すので
  2 頭の兄弟（鎖）に使えない。`ChBase` はそれを外しただけで、古い状態メモの
  **(c)「`Rq (false::ks) U = TopOk U` を 2 の枠の直下の 1 の枠から外す」** そのもの。
  （`ChBase` から出るのは `R375m (6,1,0)` まで。行376 には `PayB` / `FoneB` が要る。）
- **深さで見る**（追記348）: `LOk k X` = `X` を 2 の記録の `k` 段上に置く。`LOk 0 ↔ TwoOk`。

      深さ ≥ 1 : LOk_twoN（兄弟一般の `two N nil`）/ LOk_WWX（水平鎖）  ★緑
      深さ 0   : one V Z は緑（`TwoOk_one`、`V` が 2 頭＝走りでも通る）
                 two X nil が壁（`ChBase`、`X` が 2 頭のとき）

  **「走りが壁」ではない。**`TwoOk (one (two nil nil) nil)` は走りを含むのに緑。
  違いは先端の記録が `(h+1,1,0)` か `(h+1,2,0)` か。
- **量化子ゼロの壁**（いちばん具体的な形、2026-09-13 に緑）:

      Bd20 = bdA [2,0] = one nil (two nil (two nil (one nil nil)))
      jk1 l Bd20 = (l+1,1,0)(l+2,2,0)(l+3,2,0)(l+4,1,0)
      R375m61_of_Bd20 : GOK Bd20 → R375m ++ [(6,1,0)] ∈ W 0      ★緑

  `T6` は末尾の記録を `(l+4,0,0)` に替えただけで、`GOK_T6`（緑）から
  `R600_eq_R375m60 : R375m ++ [(6,0,0)] ∈ W 0`（緑）が同じ手順で出る。
  **壁は「字の末尾の記録の行 1 を 0 から 1 にする」1 点。**
- **いちばん短い言い方（2026-09-13）: 荷を頂上の「1 つ上」に吊るすこと。**
  `pay X B` の荷の高さは `X` の直上。だから

      pay X B の X ≠ nil → 荷は X の頂上と同じ高さ          緑
      pay nil B         → 荷は囲んでいる記録の 1 つ上       壁

  | 字 | 語 | 荷の高さ | |
  |---|---|---|---|
  | `payL4 B = one nil (pay (stk 2) B)` | `(l+1,1,0)(l+2,2,0)(l+3,2,0)` ++ `B↑(l+2)` | 頂上より下 | 緑 |
  | `NQB B = one nil (two nil (pay (two nil nil) B))` | 同上 ++ `B↑(l+3)` | 頂上と同じ | 緑 |
  | `Wall2 B = one nil (two nil (two nil (pay nil B)))` | 同上 ++ `B↑(l+4)` | **1 つ上** | 壁 |

  `B = [(0,0,0)]` の 1 個だけは 1 つ上でも緑（`GOK_T6`、`flat_mem''` が出す）。
  `snocd_mem` が `(d,1,0)` を出すのに要る塔 `TwD d Y n` は「`Y` を自分の上に積む」で、
  その 1 段が「1 つ上の吊るし」そのもの。`R375f13`（`(5,1,0)`、緑）は `d = 5` が
  `R375m` の頂上と同じ高さなので `NQB` で足りた。`(6,1,0)` は `d = 6` で 1 つ上。

## ★ 再導出しないこと（過去に何度も作り直した）

| 思いつき | 実際 |
|---|---|
| 幅の多重集合の DM 帰納で `bdA` が出る | `GOK_BCtx_nil` に既にある（追記335） |
| 予算の 1 ずれを外す族を作る | `QDP` で実測。外した分が「兄弟をいくらでも深く」で戻る（追記332） |
| 梯子の準位を上げる族を作る | `Stk` が既にやっている。壁は一様条件（追記339） |
| 荷を大きくして字を強くする | 実測で損。`[(0,0,0)]` が最適（追記340） |
| 兄弟を足して字を強くする | 非標準になる（追記337） |
| `bms` の上限を超える行列をシートに書く | 検証できないので書けない。上限は約 5100 文字 |


## 目標（シート行376）

    (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)   psi(W_w*psi_1(W_3))

行374（`R374_mem`）・行375（`R375m`）は緑。376 が次の行で正しい（`psiI.json` で照合済み）。

## 目標までの緑の還元（いちばん短い道）

    R376_of_TwoBud : TwoBud → 行376        ★2026-09-12 に緑
      PA M   := ∀ ks, FrmN ks M → WPd ks M
      TwoBud := ∀ V W, JkA V → JkA W → PA V → PA W → ∀ k ks, WPd ((k+1)::ks) (two V W)

`PA` の木の構造帰納は `nil` / `pay` / `one` と、`two` の `0 ::` 形が**全部無条件**。
`two` の `0 ::` 形が閉じるのは `WPd_twoOf` の予算を `0` に取れるからで、兄弟条件も
上の木の条件も帰納の仮定そのままで足りる（`PA_twoC0`）。だから残るのは
`TwoBud` 1 文だけで、そこから `∀ T, JkT T → GOK T`（z < 2 の停止性そのもの）が出る。

さらに `TwoBud` は**予算 1 の 1 文**に落ちる（`TwoBud_of_TwoBud1`、緑）。
`WPd_ck` を開いたあと `WPd_twoOf` の予算を `0` に取れば、上の木に要るのは
`WPd (1 :: …) (two V W)` だけで、兄弟条件は `x ≤ 0 → x ≤ k` で足りる。

    TwoBud1 := ∀ V W, JkA V → JkA W → PA V → PA W → ∀ ks, WPd (1 :: ks) (two V W)
    R376_of_TwoBud1 : TwoBud1 → 行376        ★これが最短

`TwoBud1` が硬い理由（追記331）: `WPd_ck 0 ks` を開くと、兄弟 `N` について
貰えるのは `∀ q(全部 0), WPd ((0::q)++B) N` だけ。これは

    **`N` は「1 の枠だけを積んだ文脈」でしか良さが保証されない**

という意味。`two N nil` の階段は 1 の枠の塔なので予算 1 でも通る（`WPd_nilF`）。
`two N (two V nil)` の階段 `nstN2` は各段が `[fone V, ftwo N]` で 2 の枠を積むので、
予算リストに 1 以上が 1 個ずつ増える。`WPd_nstN_run` はそれを
`hsib (q ++ replicate (t+1) 1)` で吸収するが `1 ≤ k` が要る。予算 1 では出ない。

DM 順序では直せない: `(k+1)::ks` から降りられるのは「`k+1` を除いて `k` 以下の元を
足した」多重集合だけ。`k = 0` なら 0 しか足せない。**測度を変えないと 1 ずれは消えない。**

上の木が空・予算 2 以上（`two V nil`）は `TwoBud_nilW` で緑。

古い還元（`StkL` / `BdAll` 経由）も残っている:

    R376_of_StkG  : StkG → 行376                  ★語の全称が要らない版
      StkG  := ∀ n, GoodFb (fun a b => wordJ a b [one nil (stk n)])
    R376_of_StkL  : StkL → 行376
      StkL  := ∀ n, GOK (one nil (stk n))
    R376_of_BdAll : BdAll → 行376
      BdAll := ∀ j m, GOK (bdA (replicate m j))    ← j = 0,1 は緑、j ≥ 2 が壁

    StkG は StkL の ws = [] の場合だけ（`StkG_of_StkL`、緑）。行376 に要るのは
    こちらだけなので、**どの良い語に継いでもよい**という全称は落とせる。

## ★ 走りの長さの帰納は閉じている。穴は荷だけ（追記338）

    one U (stk (n+1)) [k] = bdA (replicate (k+1) n)
    bdA (js ++ [j+1]) [k] = bdA (js ++ replicate (k+1) j)
    bdA (js ++ [0])   [k] = bdA js ++ 荷 (h,0,0) ++ 複製

    走り ≤ n+1 ⟸ 幅 n のブロックの塔 ⟸（幅の DM 帰納 `GOK_BCtx_nil`）⟸ 走り ≤ n
             …⟸ 走り ≤ 1（`WPd_bdA_le1`、緑）

**幅 0 のブロックだけ荷が出る。**だから全部 `PayB` に落ちる（`R376_of_PayB`、緑）。
`PayB` の最小の場合 `GOK (bdAC B [2]) = Wall2 B = Pay2` は `B = [(0,0,0)]` なら
`GOK_T6` で緑。次に攻めるのは「一般の `Bok C` を `[(0,0,0)]` に還元する」ところ。

`JkJ` が走りを禁じているのも同じ理由。`APd_all`（緑）の `JkJ (two N M)` は
`TopOk M` を要求する＝走り禁止。`GOK_oneU_twotwo`（走り 2 連、緑）が通るのは
階段 `two nil (otwJ m)` が走りを含まないから。走り 3 連の階段 `bdA (replicate k 2)`
は走り 2 連を含むので出ない。`WPd` の予算は「階段の走りの長さ」を数えているだけ。

## 族の梯子の地図（追記349）。段 = 入れ子になった 2 の記録の本数

    StkOk k D  = (GCtx 文脈) ++ [ftwo N] ++ (fone U)^k     2 の記録 1 本の k 段上
                 N の条件: APd で良い（＝走り無し）
    LOk k X    = ∀D, StkOk k D → GOK (plug D X)            LOk 0 ↔ TwoOk
    TwStk m D  = (StkOk (k+1) 文脈) ++ [ftwo N] ++ (fone U)^m   2 の記録 2 本
                 N の条件: ∀j, LOk (j+1) N
    TwM m X    = ∀D, TwStk m D → GOK (plug D X)
    LTwo Z     = ∀N(…), ∀k, LOk (k+1) (two N Z)     LTwo_of_TwM0 : TwM 0 X → LTwo X
    TwSt r m / TwOk r m / NTw r / TTwA              2 の記録 r+1 本

各段の `_nil` / `_pay` / `_one` / `_oneNil` / `_itJ` / `_chn` は**全部緑**。
**2 の記録を 1 本置くと段が 1 上がる。上には無限に伸びるが、下は `APd`
（走り無し）で止まる。** `StkOk 0` の兄弟の条件がそれで、`Rq (false::ks) U = TopOk U`
と同じもの。予算・準位・荷の高さ・鎖の位置は全部この「段の本数」の言い換え。

行376 には段が無制限に要る（`bdA (replicate m 2)` は 2 の記録 `m` 本）ので、
**底を 1 段緩めない限り届かない。**

## 行376 への還元の一覧（`R376_of_*`、全部緑。新しく作る前にここを見る）

`Small.lean` には行376 への還元が **30 本以上**ある。同じ壁の言い換えなので、
新しい還元を作る前に必ずここを見ること。よく使うもの:

| 定理 | 仮定 | 形 |
|---|---|---|
| `R376_of_FoneB` | `∀ws, GOK (plug (BCtx ws) (one nil nil))` | **裸の 1 の記録を 1 個足す（荷すら要らない、最弱）** |
| `R376_of_StkG` | `∀n, GoodFb (wordJ · · [one nil (stk n)])` | 単字の語 1 本 |
| `R376_of_StkL` | `∀n, GOK (one nil (stk n))` | 字 |
| `R376_of_BdAll` | `∀j m, GOK (bdA (replicate m j))` | ブロック列の字 |
| `R376_of_PayB` | `∀ws C, Bok C → GOK (plug (BCtx ws) (pay nil C))` | **荷 1 個**（`GOK_BCtx_nil` の幅の DM 帰納で `bdA` が全部出る） |
| `R376_of_TwoBud1` | `∀V W, PA V → PA W → ∀ks, WPd (1::ks) (two V W)` | `WPd` 1 文 |
| `R376_of_OneNil` / `R376_of_RPay` / `R376_of_WPay` / `R376_of_FoneB` / … | 文脈の族 | 追記315 の表 |

`PayB` は `Pay2`（= `GOK (bdAC B [2])`）の全文脈・全荷版。**`Pay2` だけでは行376 は
出ない**（`R375m (6,1,0)` までしか出ない）。`PayB` が要る。

## 壁の言い方（全部同値、どれも 1 手）

    (1) ChainStep : WPd_twoA_runB（緑）の結論 two A nil を two A (pay nil Y) に
    (2) ZApp2c    : ∀ N ∈ VCh nil, GOK (one nil (two nil (two N nil)))
    (3) TwoStepP  : ∀ B Bok B → TwoOk (two nil (pay nil B))   （TwoStep の荷への制限）
    (4) ChainW    : ∀ N ∈ VCh nil, ∃ b, ∀ k ≥ b, ∀ ks, WPd ((k+1)::ks) N
    (5) StkBlk2   : 2 ≤ k → WPd ((k+1)::ks) (stk 2)
    (6) BdAll の j ≥ 2 / Pay2 : ∀ B Bok B → GOK (Wall2 B)
        Wall2 B = one nil (two nil (two nil (pay nil B)))

    ChainStep → ChainW → ZApp2c → Pay2 → R375m (6,1,0) ∈ W 0   全部緑
    TwoStepP → Pay2                                             緑
    Pay2 → BdAll の一部（GOK_bdA20_of_Pay2）                     緑

## ★ 壁の正体：走りではなく「鎖の位置」

`WPd_ck` の**枠木（2 の記録の兄弟）**の条件は `∀ q(≤k), WPd ((0::q)++ks) N` で
`0 ::` 形。荷つきの水平鎖 `VCh nil` はこれを満たす（`WPd_VCh`、緑）。

    緑 : one nil (two N (two A nil))     N は水平鎖（兄弟）、A は予算つき ← 走りを含む
    壁 : one nil (two nil (two N nil))   N が走りの**上**（(k+1):: 形＝予算の位置）

**走り自体は壁ではない。** 荷つきの鎖を予算の位置に置けないことだけが壁。

予算の出どころは `WPd_stairB`: 階段が兄弟の形に `b+1`（`A` の予算）を押し込むので
`hsib` の上限 `k` が `b+1 ≤ k` を要求する。鎖は予算を持たないのでここで止まる。

## 塔が 2 種類あってどちらも塞がる

- `flat_mem''` の塔 = **平らな鎖** `twoIt A nil n`。`WPd_twoA_runB` を n 回使うので
  **予算を n 消費**。結論が `GOK`（予算なし）なら n ごとに予算を変えられる
  （`GOK_T6` はこれで通った）が、`WPd ((k+1)::ks)` だと `n ≤ k-b` で止まる。
- `GOK_oneUV_RunSB` の塔 = `UtwP Bs B`。`Bs = []` なら `one` しか増えないので
  予算を使わない（`GOK_oneTwoVChNil` はこれで通った）。`Bs = [N]` 以上だと
  `two N` が入って上の木に予算が要る。さらに `GOK_oneUV_genM` の `hVs`
  （語が裸の 2 の記録で終わる）が末尾の荷を許さない。

## 荷の高さ 4 / 5 / 6 の境目（語の 2 の記録の並びは同じ）

    payL4 B = one nil (pay (two nil (two nil nil)) B)  … ++ B↑(l+2)   ★緑
    NQB B   = one nil (two nil (pay (two nil nil) B))  … ++ B↑(l+3)   ★緑
    Wall2 B = one nil (two nil (two nil (pay nil B)))  … ++ B↑(l+4)   ★壁

`T6 = Wall2 [(0,0,0)]` だけは `flat_mem''` で緑（結論が `GOK` なので予算が要らない）。

## 緑になっている関連（2026-09-12 にまとめて取った）

    GOK_T6            : 走り 2 連の直上に荷 [(0,0,0)]（字として）
    TowOk_green       : #14 の壁（TWm 1 n = TW n で既に緑だった）
    R14_mem_green     : R375m (5,2,0) ∈ W 0 が無条件
    R600_221_mem      : P(6,0,0)(2,2,1) ∈ W 0、R6221_RunA0 で新しい台座
    Rz1 ws / T6w k    : どの良い語でも RunA 0 1。T6 を k 個で証明済みが伸びる
    WPd_VCh           : 水平鎖は 0:: 形で良い
    GOK_oneTwoVChNil  : ∀ N ∈ VCh nil, GOK (one nil (two N nil))
    GOK_oneTwoVChPay  : その上に任意の Bok 荷
    GOK_oneTwoVChRun  : GOK (one nil (two N (two A nil)))（走りを含む）
    TWB / WPd_TWB / TowOkB : TWm / WPd_TWm / TowOkM の単位を任意の木に
    WPd_chainP / GOK_oneChainP : 荷つき鎖は 0:: 形で良い

## ★ 壁の本当の正体（追記332、2026-09-12）

**予算（1 ずれ）は本当の障害ではない。** 兄弟の条件を予算つきのリストでなく
「どの `ks'` でも良い」にした族 `QDP P S`（緑）を作ると `QDP_twoOf` の予算は
自由になる。ところがその分がそのまま

    兄弟 `N` がいくらでも深い文脈で良いこと（＝ `PA N`、定理そのもの）

という要求になって戻る。走りの階段 `nstN2 N V i` が `N` を `i` 段深く使うからで、
どう定式化してもこれは消えない。

    壁 = 走りの階段が兄弟をいくらでも深く使う
       = 「兄弟が小さい」ことの整礎な理由が要る

`P := QD (s-1)`（高さで刻む）→ `QDP_nilF` の 1 の枠の塔が現在の層を要求し、
層の単調性が成り立たない。`P := WPd` → `QDP_step` が左の部分木に `WPd` を要求し
`PA` に戻る。

## 試して駄目だった道（再挑戦しない）

- `flat_mem''` で `ChainStep` → 平らな鎖の塔が予算を食う。
- `GOK_oneUV_genM` を末尾の荷つきに → `hVs` が壊れる。`snocYd_hang` を作ろうとすると
  また平らな鎖の塔に戻る。
- `BaseOk.hang` / `BaseOk.close` / `Lv_hang` → `LvB` の準位は**セグメントの頭**の高さで
  決まるので、末尾の記録の 1 つ上には届かない。
  （追記339 の補足: `Stk B 1` は 2 の記録 1 本ごとに準位を上げるので「上がらない」
  わけではない。`StkF B 1 (k+1)` の一様条件が「2 の記録が k 本乗った族の元にもう 1 本
  足す」＝走りになるのが壁。`k = 1` は `R14_mem_green` で緑、`k = 2` が壁。）
- `GOK_twoPay_of` の `ctx` を `[fone nil]` / `[fone nil, ftwo nil]` /
  `ctx0 ++ [fone U', ftwo N]` と変える → `htow` が `RunS` の**先端**に鎖を要求し、
  先端は予算の位置なので戻る。
- `WPd_chainT` / `WPd_two_of_ctx` / `WPd_ck` の組み合わせ → 同上。
- 字の在庫の総当たり（`TWL n` / `NQB B` / `copiesI` / `nil` 混ぜ / 荷の再帰）→
  どれも `T6` 1 個に負ける。

## 証明済みを伸ばす道（壁に触らずに効く）

    GOK_oneU_twotwo (U) (JkT U) (GOK U) : GOK (one U (stk 2))    ★既に緑
      → ItS U n（`stk 2` を n 回積む）。`JkT` も保たれる。
      jk1 l (ItS T6 n) = jk1 l T6 ++ ((l+1,1,0)(l+2,2,0)(l+3,2,0))^n
      Rz1 [ItS T6 n]   = R600 ++ copies [(3,1,0),(4,2,0),(5,2,0)] n ++ [(2,2,1)]

実測: `Rz1 (T6w 10) < Rz1 [ItS T6 10] < Rz1 [ItS T6 10]^3 < Rz1 [ItS T6 30]`。
**語に字を並べるより、1 つの字に `stk 2` を積む方が強い。**

### さらに強い：予算は `two nil X` で作り直せる（追記328）

`WPd_twoOf (k := b)` の `b` は結論に出てこない。`N := nil` なら前提は
`WPd ((b+1)::ks) V` だけなので、**`b` は好きに取れる**。だから

    Vlet X       = two nil (pay X [(0,0,0)])            `WPd_Vlet`（緑）
    NstT m 0     = twoIt nil nil m
    NstT m (r+1) = ItV (Vlet (NstT m r)) (twoIt nil nil m) m
    WPd_NstT     : m ≤ k → WPd ((k+1)::ks) (NstT m r)   ★緑

字は `NLet m r = Vlet (NstT m r)`、台座に積むのが `ItN m r j = ItV (NLet m r) T6 j`。
`Rz1 [ItS T6 29] < Rz1 [ItN 2 1 1]` なので、`r` を 1 上げるだけで前の 10 個を抜く。
強さは `m` > `r` > `j`。幅を上向きに増やす塔は非標準になる。
シートの証明済みは `Rz1 [ItN m r j]`（(2,3,2) から (3,3,1) まで 10 個）。

## 既存の族の一覧（新しい族を作る前に必ずここを見る）

| 族 | 2 の枠 | 荷 | 空木 | 走り |
|---|---|---|---|---|
| `APd`/`GCtx` | `[fone U, ftwo N]` 対で 1 枚 | 緑 | 緑 | 表現できない |
| `SCtx`/`SG` | `ftwo nil` 何枚でも | `SPayF` | `SNilT` | `SG_stkS`（長さ帰納、緑） |
| `RCtx`/`RG` | `ftwo N`（∀j 条件） | 緑 | 緑 | `RSp (false::ks)` が偽 |
| `WPd`/`WFd` | 予算 `k` | 緑（`WPd_payA`） | 緑 | `StkBlk2` |
| `ZT`/`ZG`、`ECtx`、`FCtx`、`GCx`、`HGx`、`RCx` | — | — | — | 追記315 の表 |

## 走りの道具（`GOK` 側、全部緑）

    GOK_twoNilW_gen    : two N nil                    ← 塔 (fone N)^m N
    GOK_twoTwoNilW_gen : two N (two Wl nil)           ← 階段 nstN2
    GOK_stkW_gen       : two N (stkP p (two nil nil)) ← 階段 nstQ
    GOK_runNil_gen     : one V (stkP j (two A nil))   ← 階段 Trm（= bdA）
    GOK_runGNil_gen    : 一般兄弟の走り（runJ / unR / nstR）
    GOK_oneUV_RunSB    : one U (RunS (Bs ++ [B]))     ← 階段 UtwP Bs B
    WPd_twoTwoGen_run  : WPd (0::B) (two N (stk 1))   ← 兄弟は 0:: 形でよい
