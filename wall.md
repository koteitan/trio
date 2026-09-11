# 壁

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
- `BaseOk.hang` / `BaseOk.close` / `Lv_hang` → 梯子の準位は**セグメントの頭**の高さで
  決まるので、末尾の記録の 1 つ上には届かない。
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
