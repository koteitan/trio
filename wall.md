# 残っている壁（1 文）

トリオ数列（3 行バシク行列, BM4, z < 2 の断片）の停止性証明。

2026-09-11 更新。**前の壁（`NRunNil` = 走り）は破れた。**シートの #14
`(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(5,2,0)` は
`R14_of_WPd` として無条件で緑。

いまの壁は次の行（行376）の 1 文。

## ★★★★★★ いまの最小形（族の外、2026-09-11 更新）

    PayB : ∀ ws (C : TrioSeq), Bok C → GOK (plug (BCtx ws) (pay nil C))

「**兄弟が全部 `nil` のブロック文脈の上に、荷を 1 個吊るせる**」。これだけ。

    R376_of_PayB : PayB → 目標の行376 …(4,2,0)(5,3,0)
    GOK_oneStk_ofPayB : PayB → ∀ q, GOK (one nil (stk q))

**走りの壁（`RunNilB` / `RunNil2` / `ZeroStep` / `MixTow`）は消えた。**

### 消えた理由: 族をやめて、文脈を `nil` のブロックだけに限った

    Bblk w   = PBlk (replicate w nil) nil     幅 w のブロック（1 の枠の木も兄弟も nil）
    BCtx []  = []
    BCtx (w :: ws) = BCtx ws ++ Bblk w        w が最上段

`bdA js` の文脈はこの形しか出てこない。この文脈だけに限ると
`GOK_oneUV_RunSB` の階段が作るのは

    幅 j+1 のブロック 1 枚 ⟹ 幅 j のブロック t+2 枚

だけなので、**ブロック幅の多重集合の DM** で帰納が閉じる（`GOK_BCtx_nil`、緑）。

    GOK (plug (BCtx ((j+1) :: ws)) nil)
      ← GOK (plug (BCtx ws) nil)                          幅 {j+1} → {}
      ← GOK (plug (BCtx (j :: ws)) nil)                   幅 {j+1} → {j}
      ← ∀t, GOK (plug (BCtx (j :: (replicate t j ++ (j :: ws)))) nil)
                                                          幅 {j+1} → {j}^(t+2)

追記261–267 の A/B の綱引き（荷は容量固定、階段は容量可変）は
**族の入り目の帳簿があるから起きていた**。兄弟が `nil` なら兄弟の条件が要らず、
帳簿ごと消える。

### 残る 1 文が要る場所

`j = 0` の底（`bdA [0] = one nil nil`）で `APnil_gen0` を使うところ。

    APnil_gen0 ctx V : JkT … → GOK (plug ctx V) → (∀C, Bok C → GOK (plug ctx (pay V C)))
                      → GOK (plug ctx (one V nil))

の第 3 引数が `PayB`。

### `PayB` の次の一手（追記270）

`AYs`（文脈一般の荷、緑）が使えるが、その `hAP` と、走りの位置の横鎖
`twoIt N T n` / `itJ T n X` が文脈を 1 枠ぶん広げる（2 の枠・1 の枠の木が
`nil` でなくなる）ので、**荷だけのための文脈族**

    PlB [] V        = GOK V
    PlB (0 :: ws) V = ∀ U, JkA U → PlB ws U → PlB ws (one U V)
    …

が要る。走りの階段はもう `GOK_BCtx_nil` が持っているので、この族は
`AYdR` / `AYdTR` / `WRd_payA` を写すだけでよいはず。

## 旧: 族 `WBd` の最小形（2026-09-11、いまは不要）

## ★★★★★★ いまの最小形（族 `WBd`、2026-09-11）

    RunNilB : ∀ m i ks, WBd ((m, i + 1) :: ks) nil

`i = 0`（走りの長さ 1）は `WBd_nilF1` で緑。**`i ≥ 1` が残り。**

    R375m_62_of_RunNilB : RunNilB → 証明中の行列 …(5,2,0)(6,2,0)
    R376_of_RunNilB     : RunNilB → 目標の行376 …(4,2,0)(5,3,0)
    GOK_bdA_ofB         : RunNilB → 幅に上限のないブロック列 bdA js が全部

`WBd` は入り目を **(ブロックの容量 m, ブロックの何枚目 i)** の対にして、
部分ブロックを形に書けるようにした族。`encE (m,i) = m*m+i` で ℕ に埋めて
多重集合 DM を測度にする。

    WBd []             V = GOK V
    WBd ((m,0) :: ks)  V = ∀ U, FrmB ks U → WBd ks U → WBd ks (one U V)
    WBd ((m,i+1)::ks)  V = ∀ q (入り目 < (m,i+1)), ∀ N, JkA N →
        (∀ q' (入り目 < (m,i+1)), WBd ((m,i) :: (q' ++ (q ++ ks))) N) →
        WBd ((m,i) :: (q ++ ks)) (two N V)

- **兄弟の形の頭を `(m,i)` に固定**したので、荷の横鎖は「同じブロックの
  `i+1` 枚目」になり走りが伸びない → `WBd_payA` が無条件。
- 走りの長さは位置 `i` に現れるだけなので**上限が無い**
  （`WQd` の `|Ns| ≤ k+1` が要らない）。

`i ≥ 1` に足りないのは、階段が作り直すブロックの枠の頭が `(m'', j-1)` なのに
兄弟の条件が頭 `(m, j-1)` しか与えないこと。**兄弟の条件の頭の容量を可変に**
すればよいが、そうすると横鎖が荷を「全ての容量で」要求する。次はそこ。

## ★★★ 最小形（2026-09-11 更新。族 `WRd` で書き直した）

    RunNil2 : ∀ k k' (B : List ℕ) (N : Jk1), JkA N →
        (∀ q (入り目 ≤ k), WRd (q ++ ((k'+1) :: B)) N) →
        WRd ((k'+1) :: B) (two N nil)

**「2 の記録の直上に 2 の記録を置く（底は空木）」— これだけ。**

    R375m_62_of_RunNil2 : RunNil2 → 証明中の行列 …(5,2,0)(6,2,0)
    R376_of_RunNil2     : RunNil2 → 目標の行376 …(4,2,0)(5,3,0)
    GOK_bdA_of          : RunNil2 → 幅に上限のないブロック列 bdA js が全部

もう壁に入っていないもの（全部無条件で緑）:

    WRd_payA      荷。走りの形でも。（前は QRunPay / RPayN0 / BLoad / hrun が壁）
    WRd_oneNil    1 の枠。（前は ZeroStep / OneNil が壁）
    WRd_nilT      1 の枠の形での空木
    WRd_twoNilGen 走りの長さ 1（外の形の頭が 1 の枠）
    WRd_stkP_of / WRd_bdA_of  幅の上限が無い（前は GOK_BTall の幅の帰納が要った）

## ★★★ 荷と走りは要求が逆（追記264、2026-09-11）

    A（階段・走り）  ∀e, ∃ e' < e, g(e') ≥ g(e) - 1
    B（荷・横鎖）    ∀e（g(e) ≥ 2）, ∃ e'' ≤ e, g(e'') ≥ g(e) + 1

`g(e)` = 入り目 `e` のブロックが持てる走りの長さの上限。
B は `e'' < e` を強いるので、「`g ≥ 2` の最小の入り目」で矛盾する。
**整礎な添字を持つ族では走りの長さ 2 以上は扱えない**（ℕ・対・多重集合、どれでも）。

`g(e) = 1` のときだけ B が要らない（鎖が 1 の枠の直上＝頭 0 に座るので
走りが伸びない）。これが `WPd`（融合 + `|Ns| = 1`）が全部緑な理由で、
壁はちょうど `|Ns| ≥ 2` から始まる。

    ほどいた族 WRd  鎖は節点自身の形に座る → 荷 ✓、階段 ✗（兄弟が自分の枠を越えられない）
    融合した族 WQd  兄弟の底がブロックの下 → 階段 ✓、荷 ✗（鎖が走りを 1 本伸ばす）

**補正**: B は「鎖が走りを伸ばす」ではなく「**兄弟を差す形の頭が 2 の枠だと
そこで走りが 1 本伸びる**」。だから兄弟の形の頭を 0（1 の枠）に固定すれば消える。
`WPd` の節はまさにそれ（`WPd ((0::q) ++ ks) N`）。
`WQd` が固定できないのは、ブロックの `i ≥ 2` 番目の兄弟が 2 の枠の直上に座り、
**融合した族では部分ブロック（ブロックの途中）が形に書けない**から。

    |Ns| = 1（= WPd）  兄弟の形の頭を 0 に固定できる → 荷も走りも緑
    |Ns| ≥ 2           部分ブロックの形が要る

次の一手は「**部分ブロックを形に書ける融合した族**」
（入り目を（長さの上限, いま何枚目か）の対にする）。

## 族 `WRd`（走りをほどいた族）

    WRd []            V = GOK V
    WRd (0 :: ks)     V = ∀ U, FrmN ks U → WRd ks U → WRd ks (one U V)
    WRd ((k+1) :: ks) V = ∀ r (入り目 ≤ k), r ++ ks ≠ [] → ∀ N, JkA N →
        (∀ q (入り目 ≤ k), WRd (q ++ (r ++ ks)) N) → WRd (r ++ ks) (two N V)

枠 1 枚 = 入り目 1 個。長さ `m` の走りは形 `(k_m+1) :: … :: (k_1+1) :: 0 :: ks`。
走りの長さが入り目に縛られない。停止性は多重集合 DM。
`r ++ ks ≠ []` は `TopOk (two _ _) = False` から。

**荷が通る理由**: `A2'` の横鎖 `twoIt N T n = two (twoIt N T (n-1)) T` は
`WRd` では**兄弟を伸ばすだけ**で、走りの長さも予算も増えない
（`AYdTR_hstep` が `WRd_ck_shift` で形をずらすだけ）。
`WQd`（融合した族）では同じ鎖が走りを 1 本伸ばすので `f(k)+1 ≤ f(k)` になっていた。

**`RunNil2` が残る理由**: 走りの階段（`GOK_oneUV_RunSB` の `UtwP`）の
1 ブロックは走りの枠を作り直すので、形が `[e2, 0]` 伸びる。
外の兄弟の条件は `e2 < e'`、内の兄弟の条件は `e2 = e'` を要求して両立しない。

## いまの証明中の行列（シート）

    (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,2,0)

帰着の鎖（全部緑）:

    R375m_62_of_bdA2   : (∀ n, GOK (bdA (replicate n 2))) → この行列
    bdA_rep2_of_mixed  : MixTow → ∀ n, GOK (bdA (replicate n 2))
    R375m_62_of_MixTow : MixTow → この行列

    def MixTow : ∀ n i, GOK (bdA (replicate n 2 ++ replicate i 1))
    MixTow_zero : n = 0 は緑（WPd_bdA_le1）

残りは `n ≥ 1`、木で書くと

    bdA (replicate (n+1) 2 ++ …) = one nil (two nil (two nil (bdA (replicate n 2 ++ …))))

＝ **幅 2 のブロックを木の上に足す**。`GOK_BTstep`（緑）は下にしか足せない。
これは下の `ZeroStep` と同じ 1 点。

## 最小形

    ZeroStep : ∀ U, JkT U → GOK U → ∀ pre, GOK (BT U pre) →
               ∀ i, GOK (BT U (pre ++ List.replicate i 0))

**「走りを含む文脈の先端で、裸の 1 の記録を積む」— これだけ。**

    R376_of_ZeroStep : ZeroStep → (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)

`bdA (js ++ [0]) = bdX (one nil nil) js` なので、これは `SelfW D nil`
（`D` の先端で `one nil` を `k` 個積む）と同じ。
ブロックの幅についての帰納 `GOK_BTall` は**既に緑**なので、幅 0 だけでよい。

## 同値な形（全部緑の含意、Lean 名つき）

    ZeroStep    R376_of_ZeroStep     走りを含む文脈の先端で 1 の枠を積む
    PayStep     R376_of_PayStep      BT の先端に荷を吊るす
    QTSibF      R376_of_QTSibF       走り（荷なし、兄弟は連鎖の木）
    QRunPay     R376_of_QRunPay      走りの直下の荷（WQd 層）
    RPayN0      R376_of_RPayN0       nil に荷を 1 個（文脈は任意）
    RStepN0     R376_of_RStepN0      裸の 1 の記録を 1 個積む
    RPay/RStep0 R376_of_RPay         枠木つきの版
    VPay/VStep1 R376_of_VPay         全部 nil の文脈で
    VOkk        R376_of_VOkk         全部 nil の文脈で nil
    UtwAll      R376_of_UtwAll       塔 Utw p n が全部良い
    RunAll      R376_of_RunAll       APd (true::ks) (stk q)
    TwoStep     R376_of_TwoStep      TwoOk Z → TwoOk (two nil Z)
    BLoad       R376_of_BLoad        走りの塔の文脈で nil に荷
    OneNil      R376_of_OneNil       one V nil をどの文脈でも
    hrun        Bk_pay_of の仮定      Bk (j+1) 0 での荷

## 済んでいる部分

    SelfW_of_WPd     : WPd の 1 の枠の文脈なら SelfW D V（V は頭 0 の形で良い木）
    TSibF_of_WPd     : 同じ文脈で TSibF ctx W W N
    WQd_nilF/nilAll  : ブロックの節でも nil はどこでも差せる
    WPd_bdA_le1      : 幅 ≤ 1 のブロック列はどの形にも差せる（GOK_bdA1 の一般化）
    WPd_stk1/stk2    : stk q は q ≤ 2 まで
    WPd_twoA_runB    : 走り（左の兄弟は任意、底は nil）。予算を上げられる
    WPd_twoIt_nil    : 平らな走り twoIt nil nil m（Δ=0）は全部差せる
    TowOkM / R373_copies52_mem : (…)(4,2,0)(5,2,0)^(m+1) ∈ W 0 が全ての m で

**足りないのは、走りの底が `nil` でない場合だけ**（＝ 文脈が
幅 ≥ 2 のブロックを含む場合）。

    平らな走り  twoIt A T m = two (two (… ) T) T    一般部分が左   ✓ 出る
    登る走り    stkP j X    = two nil (two nil (… X))  一般部分が右（底） ✗

`WPd_twoA_runB` で一般化できるのは**左の兄弟**だけ。底は `RunS` の `nil` に
固定されていて、`GOK_oneUV_genM` 系の塔補題がどれも
「`one U ·` にぶら下がる木の語が 2 の記録で終わる」ことを要求するのが理由。

## なぜ閉じないか（循環）

    one nil nil を D に置く   →  APnil_gen0 が ∀C, pay nil C を D に要求
    pay nil C を D に置く     →  A2' の連鎖が「走りを D に置く」に落ちる
    走りを D に置く           →  塔補題の階段が要る
    階段                      →  one nil … を D ++ ブロック に置く
                              →  最初に戻る（D が 1 段深い）

深くなるので整礎でない。

## 族の添字の付け替えでは消えない（4 通りすべて潰した。追記261）

入り目 `k` のブロックが持てる走りの長さを `f(k)` と置く。

- **階段から** `f(k) ≤ f(k-1) + 1`
  塔の単位はブロック丸ごとなので、階段は走りを入り目 `j` で作り直す。
  `j` は兄弟の条件の `q` に入るので DM から `j < k`。作り直す走りの長さは
  `L-1` なので `L-1 ≤ f(j) ≤ f(k-1)`。これが全ての `L ≤ f(k)` について要る。
- **荷の連鎖から** `f(k) + 1 ≤ f(k)`
  `A2'` の dup の横鎖は `twoIt N T n` で
  `RunP Ns (twoIt N T n) = RunP (Ns ++ [X]) T`（`X = twoIt N T (n-1)`）。
  走りが 1 本伸びるが、入り目は同じ `k` のままでないといけない。

矛盾。対 `(予算, 長さ)` に分けても、階段が長さと予算を同時に 1 ずつ落とすので
同じ不等式が出る。

**ほどく方（枠 1 枚 = 入り目 1 個、`WRd`、土台は緑）も駄目**:
階段の 1 ブロックは走りの枠を作り直すので形が `[e2, 0]` 伸びる。
外の兄弟の条件は `e2 < e'` を、内の兄弟の条件は `e2 = e'` を要求して両立しない。

    融合 + ℕ    = WQd    f の不等式で矛盾
    融合 + 対   = —      同じ不等式
    ほどく + ℕ  = WRd    e2 < e' と e2 = e' で矛盾
    ほどく + 対 = —      同じ

必要なのは次のどちらか。

1. 塔の単位が走りを作り直さない、別の塔補題。
2. 荷の連鎖が走りを伸ばさない議論（`twoIt` の平らさ Δ=0 を使う）。

**1 は無い（bms で実測）。**壁のいちばん小さい実例

    (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(6,1,0)

の展開は

    R375m ++ R375m↑6 ++ R375m↑12 ++ …     （R375m 丸ごとの複写）

で、単位が `R375m` 自身＝走り `(4,2,0)(5,2,0)` を含む。展開規則が決めるので
単位は選べない。だから残るのは 2 だけ。

## 2 の中身（いま向かうべき所）

必要な 1 文は

    WPd ((k+1) :: ks) (twoIt Wb T m)      T = pay X Y、連鎖の木は平ら（Δ=0）

「平らな連鎖の木を、走りの枠の下に、入り目を増やさずに差す」。
`WPd_twoIt_nil`（緑）は `twoIt nil nil m` を入り目 `m+1` で差すが、
`m` が非有界なので入り目を固定できないと駄目。

語で見ると `two N (twoIt Wb T m)` は

    N の語 (d+2,2,0) Wb の語 [(d+3,2,0) T の語]^m

で、m 本は**同じ高さ** `d+3`。高さが上がるのは 1 回だけ。
いまの塔補題（`snocY_mem` / `snocYd_mem`）は歩幅 `dl ≥ 1` しか無い。
**歩幅 0（同じ高さの繰り返し）の補題**が要る。

## 前の壁がどう破れたか（記録）

停止性の測度を「入り目の総和」から**多重集合の Dershowitz–Manna 順序**に変えた。

    {1}*i < {2}     全ての i について成立

走りの階段 `nstN N i` を差すには兄弟が「2 の枠 `i` 本ぶん深い形」に要り、
`i` は非有界。総和では `i` 対 `2` で負けるが、多重集合では勝つ。
順序数も ZFC も使わない（`Multiset.IsDershowitzMannaLT`）。

族 `WPd`（1 本の 2 の枠）:

    WPd []            V = GOK V
    WPd (0 :: ks)     V = ∀ U, FrmN ks U → WPd ks U → WPd ks (one U V)
    WPd ((k+1) :: ks) V = ∀ r (入り目 ≤ k), ∀ U N, … →
        (∀ q (入り目 ≤ k), WPd ((0::q) ++ (r++ks)) N) →
        WPd (r ++ ks) (one U (two N V))

無条件で緑: `WPd_run`（走り）/ `WPd_twoA_run`（左の兄弟が任意）/
`WPd_payA` / `WPd_nilAll` / `WPd_TW` / `TowOk_of_WPd` / `R14_of_WPd`。

要点は 2 つ。
- 節が張る形を `0^m ++ ks` でなく **`r ++ ks`（入り目 ≤ k の任意の `r`）** にする。
  荷の連鎖が `WPd_ck_shift` で閉じる。
- 兄弟の形の**頭を 0 に固定**する。頭が自由だと荷の連鎖の 1 歩が
  走りそのものになって循環する。

## いまの壁の舞台: `WQd` 層

`WQd` = 2 の枠の節が**走りのブロック `RunP Ns V` を一度に張る**族。
枠木・兄弟の条件に**荷閉包**（`∀ C, Bok C → WQd · (pay · C)`）を入れてある。

    WQd []            V = GOK V
    WQd (0 :: ks)     V = ∀ U, FrmN ks U → WQd ks U →
                          (∀ C, Bok C → WQd ks (pay U C)) → WQd ks (one U V)
    WQd ((k+1) :: ks) V = ∀ r (入り目 ≤ k), ∀ U Ns, Ns ≠ [] → Ns.length ≤ k+1 →
        （枠木 U: FrmN / WQd / 荷閉包）
        （兄弟 N ∈ Ns: JkA / ∀ q ≠ [] (入り目 ≤ k), WQd (q ++ (r++ks)) N / その荷閉包）→
        WQd (r ++ ks) (one U (RunP Ns V))

無条件で緑:

    WQd_nilF   : WQd ((k+1)::ks) nil        深さ「予算+1」までの走りの上
    WQd_oneNil / WQd_nilT / WQd_nilAll      走りの下でも nil が差せる
    WQd_Utw    : 行376 の塔 Utw p i がどの形でも差せる（QRunPay 仮定）
    AYdQ0      : 形 0::ks の荷（連鎖の木の荷閉包も運ぶ）
    WQd_payA   : QRunPay → どの形でも荷

`oneNil` が無条件で出るのは、枠木の条件に荷閉包が入っているから
（`APnil_gen0` がそれをそのまま要求する）。連鎖の木 `itJ T n X` の荷閉包は
**1 段浅い形 `ks` の荷の補題**から出る（`0::ks → ks` は DM で減る）。

## なぜ `QRunPay` だけ残るのか（測った）

走りの直下の荷の連鎖は `GoodFb_snoc_dupJt0` の `twoIt N T n`。

    RunP Bs (twoIt N T n) = RunP (Bs ++ [X]) T     X = twoIt N T (n-1)

ブロックの長さは増えない（`|Bs|+1 = |Ns|`）。詰まるのは**兄弟 `X` の条件**で、
`X` を入り目 `a = k'+1 ≥ 1` の形に差すと

    WQd ((k'+1)::rest) (two X T)  →  RunP (Ns'' ++ [X]) T     長さ |Ns''|+1

となり `|Ns''| ≤ k'+1` だから `k'' ≥ k'+1` が要る。一方 `Ns''` の兄弟条件は
予算 `k'` のものしか無いので `k'' ≤ k'` も要る。**矛盾**。

深さ `d` と予算 `s` を対 `(d,s)` に分けると `(d₂+1, s₂)` が取れて矛盾は消えるが、
そのとき `Z` が形 `(d₂+1,s₂)::rest` に要る。`Z` が全形で良い木（`nil` など）なら
問題ないが、連鎖の木は全形で良くない。ここが最後の 1 点。

一般に、族の節でこの 1 点を消すことはできない:

    nilF は  f(k) ≤ f(k-1) + 1   を要求（長さの上限 f）
    荷は     f(k) ≥ f(k) + 1     を要求

## 以下は前の壁（`NRunNil`）の記録

## 舞台: `NPd` 層

`NPd` = `APd` から `Rq` だけを外した族。`Rq (false::ks) U = TopOk U` は
「2 の枠の直下の 1 の枠の木が 2 の記録で始まってはいけない」＝走り禁止で、
`JkA` には要らない条件だった（`JkJ` 時代の名残）。

    NPd []           V = GOK V
    NPd (true :: ks) V = ∀ U, FrmJ ks U → NPd ks U → NPd ks (one U V)
    NPd (false::ks)  V = ∀ m U N, FrmJ (rep m true ++ ks) U → NPd (rep m true ++ ks) U →
        JkA N → (∀ j, NPd (rep j true ++ (true :: (rep m true ++ ks))) N) →
        NPd (rep m true ++ ks) (one U (two N V))

`NPd` 層では **`NRunNil` 以外は全部無条件で緑**:

    NPd_nilAll : ∀ ks, NPd ks nil                     （空木）
    NPd_payA   : FrmJ ks V → NPd ks V → Bok C → NPd ks (pay V C)   （荷）
    NPd_step   : 1 の記録
    NPd_twoOf  : 1 の枠の直上の 2 の記録
    NPd_nilF / NPd_twoNilGen / NPd_oneNil / NPd_nilT
    NPd_all_of_NRun : NRun → ∀ N ks, FrmJ ks N → NPd ks N

木の構造で回すと、閉じないのは `two A B` を形 `false::ks` に差す 1 ケースだけ
（`NRun`）。その中で `B = nil` の場合は `NLift` で閉じる
（`NPd_twoAnil_of_NLift`）。

## 安全な兄弟の族 `SbT` / `SbF`（壁が 1 つの節に一致する）

    mutual
    inductive SbT : nil | pay(SbT) | one(SbT,SbT) | two(SbT,SbF)
                 | ttwo(SbT) | ttwoB(SbT,SbF)
    inductive SbF : nil | pay(SbF) | one(SbF,SbT)
    end

    ttwoB : SbT A → SbF B → SbT (two A (two B nil))     ← 長さ 2 の走り

    NPd_true_of_SbT  : SbT N → ∀ kk, NPd (true :: kk) N     無条件・緑
    NPd_false_of_SbF : SbF N → ∀ kk, NPd (false :: kk) N    無条件・緑

`SbT` は `two A B` を `SbF B` の範囲で許すので、荷を乗せた 2 の記録
`two A (pay Z Y)` も入る。`SbF` にだけ `two` の節が無い。

**壁 = `SbF` に `two` の節を足すこと** ＝ `NPd (false::ks) (two A nil)`。

`TW n`（#14 の塔の木）は n ≥ 1 で `SbT` にも `SbF` にも入らない。
`TW (n+1) = one (two nil nil) (two nil (TW n))` を分解すると
`SbF (two nil nil)` が要るから。

木の側の兄弟 `A` は `SbF A`（形に依らない）で足りる。
**持ち上げが要るのは周囲の兄弟 `N`（`NPd_cf` の全称）だけ。**
枠の木 `U` は塔のコピーに巻き込まれないので持ち上げ不要（実測で確認）。

## 同じ壁の別の書き方（どれも緑で #14 を出す）

    NRunNil : ∀ ks, NPd (false::ks) (two nil nil)          ← 最弱
    NLift   : 兄弟条件を 2 の枠 1 本ぶん上げる（層 NPd）
    NRun    : two A B を形 false::ks に差す（走り 1 ケース）
    NTwStep : NTw r N → NTw (r+1) N（梯子 TwOk）
    WallT   : ∀ r, TwOk (r+1) 0 (two nil nil)（梯子 TwOk）
    MRun / MNil （層 MPd）
    OneNil / RPay / OneTwo / TWStep（文脈 plug）

## なぜ族を作り直しても動かないのか（最終形）

    定義の節が参照できる形    cntF が**厳密に小さい**もの（停止性から）
    走りの階段が要求する形    cntF + i（i は階段の段数、**非有界**）

これが埋まらない。障害は**測度でも節の数でもなく、階段の深さが非有界**という 1 点。

試して塞がった道:

    枠アルファベットを増やす（`List Bool` → `List ℕ`、枠の数字 = 2 の枠の本数）
      測度 `cntF = ks.sum` はそのまま通る。しかし節は cntF が小さい形しか
      参照できないので届かない。しかも `1^i`（1 の記録を挟んだ 2 の枠 i 本）は
      数字 i の枠 1 本とは**別の形**なので、広い枠で置き換えることもできない
    兄弟条件を形に依らない述語（`FrQ` / `SbT` / `NoRun`）にする
      走りの階段は通るが、`twoNilGen` の階段が兄弟の可差し性（意味定理）を要求し、
      その相互帰納が「部分導出でない周囲の兄弟」に依存して循環
    rank による階層化
      向きが合わない（rank が下がるほど族は強くなる）
    文脈の族を #14 の枠だけに制限
      荷の鎖 `itJ (pay V C) n V` が任意の枠木を要求する

### `SbT` と `SbF` の非対称の正体

    SbT に節を足すのは通る    節の証明が使うのは階段の**底**（部分導出）と
                              兄弟の意味定理（部分導出）だけ
    SbF に節を足すと通らない  節の証明が**周囲の兄弟**（全称、部分導出でない）の
                              意味定理を、非有界に深い形で要求する

`ttwoB`（長さ 2 の走り）が `SbT` に入ったのはこの理由。長さ 3 以上は
階段の段 `one nil (two nil (two nil ·))` が `NPd` の枠として書けない。

### 6 つの見方が同じ 1 点を指す

    語        1 段につき 2 の記録が 1 本増える
    木        経路は false^k、最内は常に false 文脈
    形        要る条件は true^(j+1) ++ false^b、b だけ動く
    切り方    #14 の切れ目 8 通り全部が SbF (two A nil) で止まる
    展開      A が two 頭なら最内は A そのもので停留
    枠        走りの長さ k の段は one + two^(k-1)。k ≥ 3 は枠アルファベットに無い

**要るのは別の整礎順序**（木を文脈ごと順序数で測るような）であって、
形の再帰ではない。

## 同じ壁の別表記（`OneNil`）

    OneNil : ∀ (D : List Frm) (W : Jk1), JkA W →
        (∀ X, JkA X → JkT (plug D (one W X))) →
        GOK (plug D W) → GOK (plug D (one W nil))

**「置ける `W` の上に裸の 1 の記録を 1 個積める」— これだけ。**

**シートの 2 行が両方これ 1 本から出る**（Lean で緑）:

    R14_of_OneNil  : OneNil → (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(5,2,0)
    R376_of_OneNil : OneNil → (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)
    OneNil_of_RPay : RPay   → OneNil

## #14 の道

    OneNil
      ↓ OneTwo_of_OneNil
    OneTwo : GOK (plug D W) → GOK (plug D (one W (two nil nil)))
      ↓ TWStep_of_OneTwo
    TWStep : GOK (plug D (two nil nil)) → GOK (plug D (TW 1))
      ↓ TowOk_of_TWStep
    TowOk → R14_mem

各段は `GOK_oneUV_RunSB`（走り、兄弟任意）＋ `GOK_appJ_UtwP`（塔を 1 ブロックに割る）。
基底 `plug TWD0 (two nil nil) = one nil (stk 2)` は `GOK_oneStk2`（既存、無条件）。

    TW 0 = two nil nil,  TW (n+1) = one (two nil nil) (two nil (TW n))
    TWBlk = [fone (two nil nil), ftwo nil],  TWD0 = [fone nil, ftwo nil]
    plug (D ++ TWBlk) X = plug D (one (two nil nil) (two nil X))
    plug D (TW (n+1))   = plug (D ++ TWBlk) (TW n)

## 行376 の道

    OneNil → RStepN0 → RStepN_rep → GOK_Utw_of_RStepN0 → UtwAll → R376_of_UtwAll

    Utw p n = UtwR (replicate p nil) n
    RBlk As = fone nil :: As.map ftwo
    plug (D ++ RBlk As) X = plug D (one nil (RunP As X))

## `OneNil` の中身

`APnil_gen0`（緑、文脈一般）で

    OneNil ⟸ ∀ C, Bok C → GOK (plug D (pay W C))     ＝ RPay（荷 1 個）

文脈の末尾で場合分けすると

    D = []      : AY0（緑、無条件）
    末尾 fone U : AYs / AYsF（緑）
    末尾 ftwo N : TSib_pay / TSibF_pay（緑、梯子なし）

兄弟の族に制限した版も両側とも緑（`OChain` / `TChain`）。
残るのは測度（下記）。

## `OneNil` は `GCtx` 文脈では緑

    OneNil_GCtx : GCtx ks ctx → FrmJ ks V → Rq ks V → APd ks V →
        GOK (plug ctx (one V nil))
    OneNil_GCtx_nil : GCtx ks ctx → GOK (plug ctx (one nil nil))

`APd_oneNil` と `APd_payA` はどちらも一般の `ks`（`false` を含む）で緑。
`APd_iff` で文脈に移すだけ。

**つまり `OneNil` の穴は「`GCtx` でない文脈」だけ。** `GCtx` からはみ出すのは

    (1) 1 の枠の木が `Rq (false::ks) U = TopOk U` を満たさない
        ＝ 2 の枠の直上に `two nil nil` を置く（`TW` の塔）
    (2) 2 の枠が連続する（走り）

の 2 つ。どちらも既知の壁。`OneNil` は新しい難しさではなく、
既知の壁ちょうどぶんだけ足りない。

## `Rq`（2 の記録の直上は `TopOk`）は主要補題から全部外れた

    AYdT'       : TopOk Z を外した（素通しで一度も使われていなかった）
    APd_payA'   : Rq なし
    AYs2        : CtxX なし（＝ Rq なし）
    APd_oneNil' : Rq なし
    MPd_oneNil  : MPd 層の one V nil

鍵は `CtxX ctx X` が `JkT_plug` のためだけに使われていたこと。

    JkA_plug' : CtxJ ctx → JkA T → JkA (plug ctx T)
    JkT_plug' : CtxOk ctx → JkA T → (ctx = [] → TopOk T) → JkT (plug ctx T)

`CtxOk ctx` があれば `ctx ≠ []` のとき先頭が 1 の枠なので `TopOk` は文脈が持つ。
`ctx = []` のときだけ `TopOk T` が要るが、`GCtx ks []` なら `ks = []` で
`FrmJ [] V = JkT V` が `TopOk` を持っている（`GCtx_cons_ne`）。

**残る `Rq` は `APd` / `GCtx` の定義に入っている分だけ。** 定義から外すと
`APd_all`（任意の `JkJ` 木を任意の形に差す）が壊れる。`MPd` はそこを
`FrQ` 枠で回避しているが、`MCtx` は 1 の枠の木に `MPd ks U` も課すので
`U = two nil nil` を `false` 頭に置くのは結局 `MNil`（`MPd` の壁）と同じ。

## 別ライン `MPd` の現状

    R14_mem_M  (MNil)   / R14_mem_A (∀ N, FrQ N → MBplus N)
    R14_mem_L  (LStep)  / R14_mem_L1 (LStep1) / R14_mem_L2 (LStep2)

    LStep2 : JkA N → AllA N → LAll N → JkA Z → LAll1 Z → LAll1 (two N Z)
      Z = nil     : LOk_twoNilA（緑）
      Z = pay A Y : LAll1_twoPay（緑、TSibF が仮定）
      Z = one/two : 走り

## 残っている測度の問題

    木の構造で降りる: 木が縮む、文脈が 1 伸びる
    荷（APnil_gen0）: 文脈が 1 縮む、木は任意（兄弟 `W`）

再帰は `(k, V) → (k + jsz V, nil) → (k + jsz V - 1, 任意の W)` となり、
レベルが `jsz V` 上がってから 1 だけ下がる。`W` が無制限なので止まらない。
梯子 `TwSt` は「その形の**全文脈**で良い」を持つので木を積み上げるだけで済み、
この再帰が起きない。**明示文脈の道は梯子を再現する。**

梯子の唯一の穴は `Fter`（2 の枠の直上に 2 の枠を積めない）＝ `WallT`。
ただし荷の障害は消えた（`TSib_pay` は `Fter` を要求しない）。残るのは
`GOK_twoNil_gen` / `GOK_twoTwoNil_gen` が「1 の枠止まりの文脈」を要求すること。

## 壁の正体は「レベル ⇄ 走りの長さ」の交換

    plug (D ++ [ftwo N]) (RunS Bs) = plug D (RunS (N :: Bs))

レベルが 1 下がるかわりに走りが 1 本伸びる。追記171 の「非可述性の正体は
2 の枠の本数」と、走りの長さの帰納（`WRunB`）は同じものの 2 つの見方だった。

## 部品（緑）

    AY0 / AYs / AYsF / OChain / GOK_chainJF / APnil_gen0
    TSib_pay / TSibF_pay / TChain / GOK_twoIt_chainF / GOK_twoIt_chain
    OSib / TSib / TSibF / SelfW / TSib_nil_of_SelfW / TSibF_nil_of_SelfW
    OneNil / OneTwo / TWStep / TWBlk / TWD0 / TowOk_of_TWstep / GOK_oneStk2
    RStepN / RStepN_rep / RStep / RStep_of_RPay / RStep_snoc / RStep_rep
    RunP / RunS / UtwP / UtwR / PBlk / RBlk / ABt / RFam / RFam_GOK
    GOK_appJ_UtwP / GOK_two_UtwP / GOK_ABt_of_step / NFam / NFam_GOK
    JkT_RFam_PBlk / JkT_RFam_RBlk / JkT_RFam_TWBlk
    My_RunP / hMy_RunP / jk1_RunS_snocB / jsz / jsz_RunP
    GOK_oneNN_genM / GOK_blkNN_genM / GOK_oneUV_genM / GOK_oneUV_RunSB
    TwSt_split3 / GOK_oneN_split / GOK_blkN_split / plug_blk2
    WRep / GOK_twoTwoNil_rep / NoRun / NTw_of_NoRun / STw_TTw / WallT_of_TSib

## 木の帰納の表（レベル添字版、参考）

    STw X = ∀ q, NTw q X          TTw X = ∀ q, TwOk (q+1) 0 X

    X          STw                        TTw
    -------------------------------------------------------------
    nil        NTw_nil                    TwOk_twoNilE
    one A B    STw A, STw B → 緑          TTw A, STw B → 緑
    pay A Y    STw A → 緑                 TTw A → 緑
    two A B    STw A, TTw B → 緑          ★ 壁 = TTwo
    -------------------------------------------------------------

`TTwo := ∀ A B, JkA A → JkA B → STw A → TTw B → TTw (two A B)`。
最小の場合 `A = B = nil` が `WallT`。`NTwUp` は `TTwo` から出る。
これまで出てきた壁

    WallT / WallP / Wall / OneGap / TwoStep / BStairAll / QPayPair
    WStep0 / WPay / LTwo (two nil nil) / NTwUp / TTwo / WRep

は全部 `NStep` に合流する。

## なぜレベル添字が邪魔だったか

`TwSt (r+1) 0` の文脈は `D' ++ [ftwo N]` の形で、持っている条件は

    NTw r N        ← レベル r で打ち止め

一方 `TwOk_twoTwoNil` は `∀ q, NTw q N`（全レベル）を要求する。
`NStep` は文脈を**具体的に**取るので、この差が消える。

## レベル 0 では壁は無い

    AUni N  = ∀ j kk, APd (rep j true ++ (true::kk)) N     （全 shape で良い）
    TwoOk Z = ∀ N, JkA N → AUni N → AUni (two N Z)

- `TwoOk_twoNil : TwoOk (two nil nil)` は緑。
- `LOk_twoNilAll : ∀ k, LOk k (two nil nil)` は緑（`LOk 0 ⟺ TwoOk`）。

つまり `StkOk`（梯子のレベル 0）では「2 の記録の直上の 2 の記録」は解けている。
理由は `StkOk 0` の 2 の枠の木 `N` が `AUni N`（全 shape 一様）を持っているから。
`APd_chainT'` の通り `AUni` は `twoIt N T n` で閉じている。

一方 `TwSt (r+1) 0` の 2 の枠の木 `N` は `NTw r N`（レベル r で打ち止め）しか持たない。

**壁 = 梯子の 2 の枠の木が一様でないこと。** 差はそこだけ。

## 梯子を作り直す道が塞がっている理由

2 の枠の欄を強めた梯子 `TwSt'` を作ると、必ず次のどちらかで詰まる。

1. 1 の枠の欄を **素の `TwSt` 相対**にすると `TwSt' ⊆ TwSt` が出るので
   `TwOk_twoTwoNil` がそのまま使えて `WallT'` は緑。しかし `TwOk_TWt`
   （`TW (n+1) = one (two nil nil) (two nil (TW n))`）が 1 の枠に
   `two nil nil` を積むので、素の `TwOk (r+1) 0 (two nil nil)` = `WallT` が要る。
2. 1 の枠の欄を **`TwSt'` 相対**にすると `TwOk_TWt` は `WallT'` から回る。
   しかし `TwSt' ⊆ TwSt` が消えるので `TwOk_twoTwoNil` を移植する必要があり、
   その連鎖が `TwOk'_nil → TwOk'_pay → TwOk'_pay_e → TwOk'_twoIt` まで届く。
   `TwOk'_twoIt` は `ftwo (twoIt N T n)` を積むので、2 の枠の欄の条件が
   `twoIt N T n` で閉じていなければならない。`NoRun` は閉じていない。
   全レベル一様 `∀ q, NTw' q N` にすると定義が循環する。

`AUni N` を欄に入れる案も、`r = 0` で `AUni X → LOk (j+1) X` が必要になって止まる。
`LOk` の 1 の枠は意味的（弱い）ので `APd` からは出ない。

## 壁が無い木の族（緑）

    NoRun nil
    NoRun A → NoRun B → NoRun (one A B)
    NoRun A → NoRun B → TopOk B → NoRun (two A B)
    NoRun A → Bok Y → NoRun (pay A Y)
    NoRun A → NoRun (two A (two nil nil))

    NTw_of_NoRun : NoRun X → ∀ q, NTw q X      -- 緑

上の表の緑のマスだけで閉じる族。壁は「走りを含む兄弟」だけに残っている。

## 記法

木 `Jk1`:

    nil | one N M | two N M | pay N Y

木から行列（語）への写像 `jk1 l : Jk1 -> TrioSeq`（`l` は高さ）:

    jk1 l nil       = []
    jk1 l (one N M) = jk1 l N ++ ((l+1,1,0) :: jk1 (l+1) M)
    jk1 l (two N M) = jk1 l N ++ ((l+1,2,0) :: jk1 (l+1) M)
    jk1 l (pay N Y) = jk1 l N ++ shiftr01 (l+1) 0 Y

`one N M` / `two N M` は「左兄弟 N、直上の子 M を持つ 1 / 2 の記録」。
`pay N Y` は N の上に荷 Y（`Bok Y`、それ自体が良い行列）を吊るす。

文脈は枠のリスト `List Frm`、`Frm = fone Jk1 | ftwo Jk1`。

    plug [] T                 = T
    plug (fone N :: rest) T   = one N (plug rest T)
    plug (ftwo N :: rest) T   = two N (plug rest T)

`GOK X` = 「どの良い語の右にも X の語を継いでよい」（`GoodFb` を保つ）。

## 層を通らない言い換え `WStep0`（参考）

    WCtxT ctx V := ∀ X : Jk1, JkA X → JkT (plug ctx (one V X))     -- 字レベルの妥当性だけ
    WV V        := V = nil ∨ V = two nil nil
    Wblk V p    := fone V :: (ftwo nil)^p
    WFam        := [] から Wblk V p（WV V）を積んで作る文脈の族

    WStep0 := ∀ ctx, WFam ctx → ∀ V, WV V → WCtxT ctx V → GOK (plug ctx V)
                → GOK (plug ctx (one V nil))

**「裸の 1 の記録をどの文脈でも置ける」— これだけ。**

これが出れば

    R14_of_WStep0  : WStep0 → (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,2,0)(5,2,0)
    R376_of_WStep0 : WStep0 → (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)

がどちらも出る（Lean で緑）。**層（`APd` / `Cok` / `Pok` / `TwSt`）を一切通らない。**

## どうやってここまで落ちたか

要は「主張を文脈について全称にすると、階段が文脈を伸ばしても帰納が回る」。

    plug ctx (one V (stk (p+1)))          stk q = 走り q（(l+1,2,0)…(l+q,2,0)）
      の階段は appJ V (Utw p k) で、これは plug (ctx ++ Wblk V p) (Utw p k) に等しい

    Utw p k = ブロック「(1,0) + 走り p」を k 個積んだ木

`k` について内側の帰納（文脈が伸びても主張は全称なので当たる）、
`p` について外側の帰納（走りが 1 段短くなる）。これで走りが層なしで通る（`WRun`）。

塔（証明中の行の展開列）も同じ形になる。

    TW 0 = two nil nil,  TW (n+1) = one (two nil nil) (two nil (TW n))
    plug ctx (one V (two nil (TW (n+1)))) = plug (ctx ++ Wblk V 1) (one (two nil nil) (two nil (TW n)))

底は `two nil (TW 0) = stk 2` なので `WRun` の走り 2。

## `WStep0` の中身

`APnil_gen0`（緑、文脈一般）が

    APnil_gen0 ctx V (JkT (plug ctx (one V nil))) (GOK (plug ctx V))
      (hang : ∀ C, Bok C → GOK (plug ctx (pay V C)))
      : GOK (plug ctx (one V nil))

なので、残るのは **`hang`（荷 1 個）**だけ。

    ctx = []  → AY0（緑、無条件）。荷の複製が「項ごとの繰り返し」で済む
    ctx ≠ []  → 下記の 2 つの形が残る

## 残っている 2 つの形

    (a) 兄弟が無制限の裸の 1 の記録
          ∀ W, CtxX ctx W → GOK (plug ctx W) → GOK (plug ctx (one W nil))

    (b) 走りの上の荷
          GOK (plug ctx (pay (two nil nil) C))      ctx の末尾が ftwo nil

(a) は `AYs`（緑、文脈一般の荷の補題）の仮定 `hAP` がそのまま要求するもの。

    AYs Y (Bok Y) ctx (CtxOk ctx) X Z (CtxX ctx X) (CtxT ctx Z)
        (hAP : ∀ V, CtxX ctx V → GOK (plug ctx V) → GOK (plug ctx (one V Z)))
        (GOK (plug ctx X))
      : GOK (plug ctx (one X (pay Z Y)))

`AYs` の証明を読むと `hAP` が当たるのは `X` と鎖 `itJ (pay Z Y') k X` だけなので、
`hAP` を族に制限した版は原理的に作れる。ただしその鎖が `{nil, two nil nil}` から出る。

(b) は既存の機械が**全部弾く**形。`AYs` は `CtxX`、`APd` は `Rq` で

    CtxXJ [ftwo _] X = JkA X ∧ TopOk X
    Rq (false :: ks) U = TopOk U

を要求し、`TopOk (two nil nil) = False` だから。行列で見ると

    …(d,2,0)(d+1,2,0)     ← 走り

になるので、走りを表現できない記法では書けない。

実測（`bms`）では (b) の展開は

    …(3,1,0)(4,2,0)(5,2,0)(6,0,0)  →  …(3,1,0)(4,2,0)(5,2,0)(5,2,0)

で、**証明中の行の行列そのもの**。横鎖 `twoIt nil (pay X C') k`（同じ高さに 2 の記録が
横に並ぶ、delta = 0）が出る。

## 欲しいもの

次のどれか。

1. `GOK_oneNN_gen` / `GOK_blkNN_gen` の `hNs`（N が走り）を外した一般版。
   一般の N では `one N N` の語の最後の記録が N の形で変わるので、
   バッドルートの場合分けが増える。そこを `GoodFb` の 3 フィールド
   （`pu` / `pk` / `seg`）だけで書けるか。

2. `NStep` の階段を実測して、一般の N でも `Utw p n` 型の塔になるか確かめる。
   なるなら `GOK_oneNN_gen` の証明がほぼそのまま通る。

3. `NStep` の第 2 文だけを先に落とす。第 1 文（`one N N`）は
   `NTw r N` の文脈では `TwOk_itJ` で無料なので、
   `[ftwo N, fone nil]` を足す第 2 文が本体。

## 木の側の走りは解けている（参考）

走り（`stk q` = `(l+1,2,0)…(l+q,2,0)`）を**木の先端**に置く問題は、
主張を文脈について全称にすると解ける。

    WRun : ∀ p ctx V, … → GOK (plug ctx V) → GOK (plug ctx (one V (stk p)))

`GOK_oneUV_gen` の階段 `appJ V (Utw p k)` が `plug (ctx ++ Wblk V p) (Utw p k)` と
等しいので、`k` について内側の帰納（文脈が伸びても主張は全称なので当たる）と
`p` について外側の帰納（走りが 1 段短くなる）で回る。

    Wblk V p = fone V :: (ftwo nil)^p
    Utw p k  = ブロック「(1,0) + 走り p」を k 個積んだ木

**文脈**の側の走り（＝左兄弟のレベル一様性）はこれでは解けない。それが `TTwo`。

## 参考

Lean のファイルは `lean/Small.lean`（約 61000 行、緑、`sorryAx` なし）。
経緯は `notes.md` の追記175〜206。
