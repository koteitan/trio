# 壁

## ★★★★★★★★★★★★★★ 壁の正体が確定した（2026-09-13）: 「幅の 1 ずれ」

### 今日緑にしたもの

    WQt / WQxt … `WQd`（ブロック族）を一般の予算型へ。幅は `Scale`（`S.nb w < b`）
      WQt_iff / WQt_step / WQt_congr / WQt_runStair / WQt_nilF / WQt_oneNil /
      WQt_nilT / WQt_nilAll / WQt_stk_succ / WQt_Utw / R376_of_QtPnil
      → 行376 は `QtPnil : ∀ ks C, Bok C → WQt S ks (pay nil C)` 1 本

    WNd … 枠 1 枚に予算 1 個（一般予算）。荷閉包を外し、兄弟に `p' = []` を許した
      WNd_payE / GOK_chainJdWN / AYdWN / WNd_payT / WNd_chainT /
      AYdTWN_hstep / AYdTWN / WNd_payA / WNd_oneNil / WNd_nilT

    WEd / WEtx … 予算を深さのリスト `List ℕ` に（`WBd` の `m` は順序に出ないので落とす）
      WEd_iff / WEd_step / WEd_congr / WEtx_JkT / WEd_payE / GOK_chainJdWE /
      AYdWE / WEd_payT / WEd_chainT / AYdTWE_hstep / AYdTWE / WEd_payA /
      WEd_oneNil / WEd_nilT

**`WNd_payA` / `WEd_payA` は「隣接 `ftwo`（走り）を表せる族で、荷がどの位置でも
無条件」という初めての結果。** `QRunPay` / `PayNilB` / `QtPnil` 型の壁
（走りの直上の荷）は、族の定義から荷閉包を外せば消える。
`WQd` / `WBd` で壁だったのは、族の定義に荷閉包が入っていて、
A2' の複製鎖の兄弟の荷閉包が**任意の荷**について要り帰納法が回らなかったから。

鍵（`AYdTWE_hstep` / `AYdTWN_hstep`）: 複製鎖の各段は

    WEd_ck i ks T |>.mp hTk (q := q' ++ q) … : WEd (i :: ((q' ++ q) ++ ks)) (two N' T)

で出る。**予算（深さ `i`）は動かず、詰め物 `q'` が積まれるだけ。**
鎖の元は同じ階に並ぶので深さが減らない。だから鎖の長さに上限が付かない。

### 残っている 1 点と、その正体

    WEd_nilF : ∀ i ks, WEd ((i+1) :: ks) Jk1.nil     （走りの直下の空木）

`i = 0`（文脈が `fone` で終わる）は `GOK_twoNilW_gen` で通る（階段は
`replicate m (fone N)`、予算は `hNt` の詰め物 `replicate m 0` でちょうど合う）。
`i ≥ 1` は `GOK_runGNil_gen`（階段 `blkR N Bs j`）が要るが、**文脈の走りの兄弟
`Bs[k]`（深さ `k+1`）の条件の詰め物の上限が `k` しかなく、階段のブロックが
外側に持つ深さ `i` の入り目（`i > k`）を覆えない**。上限を「走りの先頭の深さ」に
すると `dm_app` の測度が下がらない（停止性が壊れる）。

逆に `WQt`（ブロック 1 個が予算 1 個、走りの兄弟は全部同じ上限 `b`）は
階段が通る（`WQt_nilF` は緑）。しかし荷の複製鎖を兄弟として置くとき、
文脈の走り `Ns₂` に 1 本足すので幅が `|Ns₂|+1` になり、節の予算 `b₂` が許す幅は
`|Ns₂|` まで。**ちょうど 1 足りない。** `b₃ > b₂` で開き直すと兄弟 `Ns₂` の条件
（`< b₂`）が届かない。

    WEd … 荷 ✓ / 階段 ✗（兄弟の上限が局所的で階段の外側を覆えない）
    WQt … 階段 ✓ / 荷 ✗（幅が 1 足りない）

**この 2 つは同じ 1 ずれの別の面。** 直すには
「族が幅 `w` を許すなら同じ節で幅 `w+1` も許す」が要る（= 幅の上限を外す）が、
走りの階段は「幅 `w` の走りには長さ `w` の降下列」を要求するので外せない。

### 次に試す形（この順）

1. 予算を対 `(b, w)`（`b` は兄弟の上限、`w` は幅）にして**順序は `b` だけ**で
   測る（`WBd` の `encE` と同じ仕掛け）。幅 `w` が順序に出ないので
   `(b₂, w₂+1)` で開き直せる。ただし「入り目の妥当性 `w ≤ height b`」を
   課すと 1 ずれが戻るので、そこを空木の補題がどう耐えるかを見る。
2. 族の節に**水平鎖そのもの**を入れる
   （`WQt (r++ks) (one U (RunP Ns (twoIt Nl V (m+1))))`）。
   `WQt_iff`（文脈との同値）は壊れるので、文脈族の側に
   「鎖の枠」を入れる形（`Mtwd` に近い）で作り直す必要がある。
3. `DCtx` / `NNo`（`SmallA` 54490、ブロック文脈の族）は
   `Tow_of_NNo` / `NNo_step` / `NNo_one` / `NNo_payU` / `NNo_pay` が緑。
   穴は `NNo nil`（`DCtx` の 2 の枠の兄弟が `JkA` しか課さないので、
   走りの先端の `two Bl nil` が出ない）。`DCtx` の兄弟条件を
   「`NNo` 自身」にすると循環するが、**予算つきの族で同じことをすれば
   循環しない**（それが `WQt` / `WEd`）。

## ★★★★★★★★★★★★ 壁 `Pay2` は落ちた（2026-09-13）

    Pay2_true   : Pay2 = ∀ B, Bok B → GOK (one nil (two nil (two nil (pay nil B))))  ★緑
    ZApp2c_true : ZApp2c                                                              ★緑
    PcB         : 荷つきの水平鎖は、荷の多重集合より上のどの予算にも置ける            ★緑
    R375m61_mem : R375m ++ (6,1,0) ∈ W 0                                              ★緑
    A375m61_gen : A ++ U375a ++ (6,1,0) ∈ W 0（台座一般）                             ★緑

### 何が効いたか（2 点）

**(1) 予算型を `Multiset Ld`（荷の多重集合、DM 順序）にした。**
`WPdT` の `[LinearOrder Bud]` を `[PartialOrder Bud]` に弱めるとエラー 0 だった
（線形性はどこにも使っていない）。DM 順序は線形でないのでこれが要った。
これまでの予算型は `ℕ`（`WPd`）や `Bw = ω^ω`（`WPdT`）などの**固定の**順序数で、
荷の階数が足りなかった（平らな荷の天井 `R600(7,1,0)`）。
`Multiset Ld` なら荷の階数がそのまま予算になる。整礎性は

    Rex' M' M := (¬M が底) ∧ ∃ n ≥ 1, M' = M⟦n⟧   または   M' = [] ∧ M ≠ []
    Acc_Rex' : W 0 ⊆ {M | Acc Rex' M}     （`A2'` に入れるだけ、10 行）
    wf_LdDM  : WellFounded (Multiset.IsDershowitzMannaLT (α := Ld))

から出るので、**証明したい停止性を仮定しない**。

**(2) 命題を「鎖の荷の多重集合より上のどの予算にも置ける」にした。**

    PcB : ∀ Sm L, LdMS L = Sm → (∀ Y ∈ L, Bok Y) →
            ∀ b, DMlt (LdMS L) (unB b) → ∀ ks, WPdT (b :: ks) (ChL L)

`GOK_twoPayZ_DM`（`hcl` を `Rex' Y' Y` に制限した A2'）の複製鎖
`twoIt N (pay nil Y') m` は**長さ無制限**だが荷が `Rex'` で小さいので、
荷の多重集合の DM 帰納の IH でちょうど出る。予算は `a = mkB (LdMS L)`、
結果は `c = b`（外の予算そのもの）で、`a < c` はちょうど仮定 `DMlt (LdMS L) (unB b)`。
**「予算が鎖の長さを縛る」問題は、予算を荷の多重集合にすると消える。**

### 2026-09-13 夕: 荷は 3 つの族で無条件になった。壁は「文脈側の走りの直下の空木」

    WNd_payA / WEd_payA / WVd_payA   ★全部緑（隣接 ftwo を表せる族で荷が無条件）
    WEd_nilF0                        ★緑（深さ 1 の空木）
    WQt_nilF                         ★緑（節から来る走りの直下の空木）

**荷閉包を族の定義に入れないこと**が鍵（`WPdT` と同じ）。入れると A2' の
複製鎖の兄弟の荷閉包が任意の荷について要り、荷の帰納法が回らない。

残る 1 点は **`WVd (b :: ks) nil` の「枠 1 枚の節」**（= 文脈側に走りがある
ときの `two N nil`）。節から走りが来る場合（ブロックの節）は
兄弟の条件の上限が節の入り目 `b` なので階段の入り目 `j < b` が詰め物に入り、
通る（`WQt_nilF`）。文脈側から来る場合は兄弟の上限がそのブロックの入り目
`b₀` で、階段はブロックを内側に積むので `b₀` 自身が尻尾に現れ、覆えない。

### まだ残っているもの

目標行 `R373 (5,3,0)` の展開 `[2] = R375m (6,2,0)` はまだ。
`bms` の順: `R375m(6,1,0) < R375m(6,1,0)(7,1,0) < R375m(6,1,0)(7,2,0) < R375m(6,2,0)`。
`R375m(6,2,0)` は `Tw3`（歩幅 3 の塔、木は `nstQ nil 1 n`）= **縦の鎖**。
`PcB` が落としたのは**横の鎖**（同じ階の 2 の記録が並ぶ）。縦の鎖は
`WPdT_twoOf` が `⊥ ::` しか作れない「1 ずれ」が残る。
同じ手（予算を荷の多重集合に）が縦にも効くかを次に見る。

### 次の一手: `RunNilB` を `GOK_runGNil_gen` で（予算の一般化は要らないかも）

`SmallA` の `WBd`（予算 `List (ℕ × ℕ)`、順序は深さだけ）で残る 1 文は

    RunNilB : ∀ m i ks, WBd ((m, i + 1) :: ks) Jk1.nil
    PayNilB : ∀ ks C, Bok C → WBd ks (Jk1.pay Jk1.nil C)
    RunNilB + PayNilB → WBd_nilAllB → GOK_bdA_ofB → MixTow → 行376   ★全部緑

`WBd_nilF1`（`i = 0`、つまり深さ 1）は緑で、`GOK_twoNilW_gen`（底が `fone`）を使う。
深さ `i+1 ≥ 2` では文脈が `ftwo` で終わるのでその機構が当たらない——**が**
`GOK_runGNil_gen`（`ctx ++ blkC V Bs`、つまり `fone V` のあとに `ftwo` が何枚でも）
が当たる形になっている。実際 `WBtx ((m,i)::ks) ctx` を `i` で開くと

    ctx = ctx0 ++ [Frm.fone V] ++ ftw Bs,  Bs.length = i   （`blkC V Bs`）

の形になる（`i = 1` で `ctx'' ++ [fone U, ftwo N]` を確認した）。
`GOK_runGNil_gen` の階段 `blkR N Bs j`（ブロックを `j` 個足す）に要るのは
`hNt m₂ q'`（`q'` は深さ `< i+1` の**長さ無制限**のリスト）で、
ブロック 1 個ぶんの予算は深さ `i, i-1, …, 1, 0` なので全部 `< i+1` ✓。
**つまり `hNt` の「長さ無制限」でちょうど足りる。予算型の一般化は要らない。**

要る補題（この順に作る）:
1. `WBtx_decomp : WBtx ((m,i)::ks) ctx → ∃ ctx0 V Bs ks', Bs.length = i ∧
     ctx = ctx0 ++ blkC V Bs ∧ (∀ B ∈ Bs, JkA B) ∧ GOK (plug ctx0 V) ∧ …`
   （`i` の帰納。`WBtx_c0` / `WBtx_ck` を開くだけ）
2. `WBtx_blkR : 階段の文脈 ctx0 ++ blkC V Bs ++ blkR N Bs j` が
   `WBtx ((m₂,i) :: q' ++ (q ++ ks))` の形（`q'` はブロック `j` 個ぶんの予算）
3. `RunNilB` を `GOK_runGNil_gen` で
4. `PayNilB` を `PcB` と同じ DM 帰納で（複製鎖はブロックの幅に出るので上限が無い）

なお、深さを一般の整礎な型に持ち上げた `WNd`（`Small.lean` 末尾、核は緑）も
用意してある。1〜4 が `ℕ` の深さで通らなければそちらに移す。

### 次の標的: `PayB`（ブロック文脈の荷）。これで行 376 が出る

    PayB : ∀ ws : List ℕ, ∀ C, Bok C → GOK (plug (BCtx ws) (pay nil C))
    FoneB_of_PayB / GOK_BCtx_nil / R376_of_PayB                           ★既に緑

`Pay2` は `ws = [2]` の場合。`BCtx ws` はブロック `[fone nil] ++ (ftwo nil)^w` の列で、
`Tw3`（縦の鎖）に要るのはちょうどこの文脈（`nstQ nil 1 n` を割ると
`fone nil, ftwo nil, ftwo nil, fone nil, …` が出る）。

`Pay2` と同じ手で行ける見込み: A2' の複製鎖が `htow`
（`GOK (plug (BCtx ws) (two M nil))`）に落ちるので、鎖をブロック文脈に置く
予算族が要る。それが `WQd`（`SmallA` 67307、補題 15 本だけ）。

    WQd ((k+1)::ks) は「幅 Ns.length ≤ k+1 のブロック」を張る
      → 幅が予算で縛られている。まさに `Pay2` で外した形。

手順:
1. `WQd` を一般の予算型に持ち上げる（`WPd → WPdT` と同じ、`[PartialOrder Bud]`）。
   幅の条件 `Ns.length ≤ k+1` は `Scale` を使って `S.nb Ns.length < b` にする。
2. 予算型を `Bml = Multiset Ld` にする。
3. `QRunPay`（`WQd` 層の荷）を荷の多重集合の DM 帰納で出す（`PcB` と同じ形）。
4. `R376_of_QRunPay`（★緑）で行 376。

**以下は `Pay2` が落ちる前の調査。歴史として残す。**

## ★★★★★★★★ 壁は「目標行の展開 [2]」1 行。シート登りはそこに届かない（2026-09-12）

目標行 `R373 (5,3,0)` の展開は

    R373 (5,3,0) [n] = R375m (6,2,0)(7,2,0)…(4+n,2,0)     （2 の鎖）
    [1] = R375m                                            ★緑（`R375_mem`）
    [2] = R375m (6,2,0)                                    ★壁（標準形）

**`bms -c` で測ると、シートで登れる行は全部 [1] と [2] の間に入る。**
`R600 = R375m (6,0,0)`、`Z789 = R600 (7,0,0)(8,0,0)(9,0,0)`、
`U375aG = U375a6 (7,0,0)(8,0,0)(9,0,0)` を何段積んでも（`ZGit`、緑）
`R375m (6,1,0)` すら越えない。つまり**残っているシートの行は実質 1 行**で、
それが `R375m (6,2,0)` = 壁。**登る作業は目標に近づかない。**

### `R375m (6,2,0)` を割ると

展開は `Mtwd 3 R375m [(6,1,0),(7,2,0),(8,2,0)] n`（`bms` で確認）。
木は `nstQ Jk1.nil 1 n`（1,2,2 のブロックが 3 ずつ上がる）で、要るのは

    ∀ k, APd [true] (two nil (two nil (nstQ Jk1.nil 1 k)))

`APd_twoStkGen (p := 1)` がこれを `APd [true] (stk 3)` に変え、
`GOK (one nil (stk 3))` から `R375m (6,2,0) ∈ W 0` が出る。

**残る 1 点: `two nil (two nil X)` の `X` が `nil` でない場合。**

    GOK_stkW_gen    : two N (stkP p (two nil nil))   ← 底が nil なら階段だけで出る
    GOK_oneU_twotwo : one U (stk 2)                  ★緑（下に何も無い）
    Wall2 B = one nil (two nil (two nil (pay nil B)))  ★壁（B = [(0,0,0)] だけ緑 = T6）

`stk 2` は底が `nil` のときだけ無条件。`nstQ nil 1 k` を底に置くと壁に戻る。
`p = 0`（`stk 2`）は `APd_nstN` が階段をくれるので無条件、`p ≥ 1` が壁（Small.lean:4018）。

## ★★★★★★★★ 壁の正体は「階段の機構が `fone` の枠を要求する」（2026-09-12 夜）

`GOK_*_gen` の階段の機構は**全部** 文脈を `ctx0 ++ [Frm.fone V]` の形で要求する:

    GOK_twoNilW_gen    : two N nil                    ← 塔 (fone N)^m N
    GOK_twoTwoNilW_gen : two N (two Wl nil)           ← 階段 nstN2
    GOK_stkW_gen       : two N (stkP p (two nil nil)) ← 階段 nstQ
    GOK_runGNil_gen    : one V (stkP j (two A nil))
    GOK_oneUV_RunSB    : one U (RunS (Bs ++ [B]))

`plug (ctx0 ++ [fone V]) X = plug ctx0 (one V X)` で「字の境目」が取れるからで、
**2 の記録の直上（下の枠が `ftwo N`）だと字の境目が無い**。
だから族をどう作っても同じ所で止まる。

### 族の側の確認（2026-09-12 に測った）

| 族 | 2 の枠の隣接 | 兄弟 | 荷 | `nil` を差す |
|---|---|---|---|---|
| `GCtx`/`APd` | 書けない | 一般 | 緑 | — |
| `WCtx`/`WPd` | 書けない（`0`/`k+1` の節） | 一般 | 緑 | — |
| `TwSt`/`TwOk` | 書けない（`Fter` が弾く） | 一般 | 緑 | — |
| `SCtx`/`SG` | **書ける**（`ftwo nil` 何枚でも） | `nil` 固定 | ★壁 `SPayF` | `SNilT`→`stk q` 全部 |
| `RCtx`/`RG` | **書ける** | 一般（`RFt`） | **★緑 `RP_of_RG`** | `RG (true::ks) nil` ★緑 |

`RCtx` は 2 の枠の隣接も兄弟一般も荷も全部通る。残るのは

    RG (false :: false :: ks) Jk1.nil        ← `RG_nil_false` は `RSp ks` を要求し、
                                               `ks` が `false` で始まると `RSp` は偽

`RSp ks` = 「`RCtx ks` の文脈は必ず `fone V` で終わる」。`m ≥ 1` の場合は
`RSp_ct` で緑なので、**穴は `m = 0`（1 の枠を挟まない）だけ**。

### 次にやること

`ctx0 ++ [Frm.ftwo N]` を底にした階段の機構を 1 本作る。
`GOK_twoNilW_gen` の証明で `fone V` をどこに使っているかを見て、
`ftwo N` 版（字の境目を 1 つ外側に取る）に書き換えられるか調べる。

### 閉じた道（再挑戦しない）

`GOK (plug D nil)` から兄弟の可置性を取り出す道は **閉じた**。
それには `W 0` の下方閉性（`A ≤ B`, `B ∈ W 0` ⟹ `A ∈ W 0`）が要るが、
`Cnf.lean` / `SmallX.lean` / `SmallA.lean` に単調性の補題は 1 つも無く、
これ自体が目標と同程度に難しい。

### 予算の言葉での穴（`WPd`）

    WPd ((k+1) :: ks) (two N Jk1.nil)        ★緑（`WPd_twoA_runB`）
    WPd (0 :: ks) (two N (two nil nil))      ★緑（`WPd_twoOf` + `WPd_run`）
    WPd ((k+1) :: ks) (two N (two nil nil))  ★壁 ← これ 1 本で `stk q` 全部

`WPd_twoOf` の結論は必ず `0 :: ks` なので、鎖を 1 段伸ばすと予算が 0 に落ちる。

## ★★★★★★★ 壁の一番きれいな形（2026-09-13 夜、今日の調査）

    RStepN0 : ∀ D : List Frm,
      (∀ X, JkA X → JkT (plug D (one nil X))) →
      GOK (plug D nil) → GOK (plug D (one nil nil))
    R376_of_RStepN0                                                        ★緑

**「穴に `1` の記録をもう 1 本足してよい」だけ。** `D = []` の場合は `AP0nil`（★緑）。

`RPayN0`（穴に任意の `Bok` の荷を吊るす）とはほぼ同値:

- `RStepN0_of_RPayN0`（★緑）
- 逆向きは `AYs` / `APpayJ`（★緑）。`APpayJ Z Y hZ hY (hAP) : ∀ V, JkT V → GOK V →
  GOK (one V (pay Z Y))` の `hAP : ∀ V, JkT V → GOK V → GOK (one V Z)` が
  ちょうど「`1` の記録をもう 1 本」。`Z = nil` なら `AP0nil` なので
  `GOK_oneB : GOK (one nil (pay nil B))` は**全部の `Bok B` で緑**。

### 今日わかった訂正

**`fone` の位置の snoc 補題は既にある**（`snocYd_mem` の `y ≤ 2` は関係ない）:

    GoodFb_snoc_innerJs0 / GoodFb_snoc_dupJs0   （`plug ctx (one X (pay Z Y))`）★緑
    GoodFb_snoc_innerJt0 / GoodFb_snoc_dupJt0   （`plug ctx (two N (pay Z Y))`）★緑
    flat_mem'' は行 0 しか見ないので y=1 でも y=2 でも通る。

足りないのは `dupJs0` の帰納法の仮定に出てくる**鎖** `itJ (pay Z Y) n X`
（`1` の記録を `n` 本重ねた木）で、それを作るのが `GOK_chainJ` の `hstep`
＝「`1` の記録をもう 1 本」＝ `RStepN0`。**そこだけが循環している。**

### 鎖は `WPdT` の世界では無料

    WPdT_step ks (FrmNT ks U) (WPdT ks U) (WPdT (⊥::ks) V) : WPdT ks (one U V)

なので `WPdT (⊥::ks) T` と `WPdT ks X` があれば `WPdT ks (itJ T n X)` は
`n` の帰納で全部出る。**鎖そのものは壁ではない。**

残る差は **「文脈 `D` が予算リストで書けるか」** の 1 点:
`WCtxU ks D` は「兄弟の木が全部置ける」ことを要求するが、`RStepN0` の仮定は
`GOK (plug D nil)` だけ。**`GOK (plug D nil)` から兄弟の可置性を取り出せれば終わる。**
（取り出せない反例があるのか、取り出せるのに補題が無いだけなのかは未調査。
まずそこを見ること。）

## ★★★★★★ 荷は無料（`WPdT_payA`）。再導出しないこと

    WPdT_payA ks V (FrmNT ks V) (WPdT ks V) C (Bok C) : WPdT ks (pay V C)   ★既存
    AY0 / AYs / APpayJ / AYdT' / AYdWT / AYdTWT                             ★既存
    TwoOk_pay : Bok Y → JkA Z → TwoOk Z → TwoOk (pay Z Y)                   ★既存
    hang5_gen / hang6_gen hA hB : A ++ U375a1 ++ shiftr01 6 0 B ∈ W 0       ★既存

予算リスト（`WPdT`）や `APd` で書ける文脈の中では `Bok` の荷は完全に無料。
`hang6_gen` が `U375a1 = U375a ++ [(5,1,0)]` を要求するのは、末尾の `(5,1,0)` が
`one` の枠を作るから。**`(5,2,0)` の直下（`two` の直上）だけが壁。**

## ★★★★★ 平らな荷の天井は `R600(7,1,0)`

平らな荷は原始数列（PrSS, `ε_0`）。段を 1 つ上げて得られるのは
`R600(7,0,0)(8,0,0)…(6+k,0,0)` の 1 行ずつで、全部やっても `(7,1,0)` の 1 列分。
2026-09-13 に `Wg k`（`= Y0 (1,0,0)(2,0,0)^k`、`Wg 0 = Ap·1`、`Wg 1 = Vs`、`Wg 2 = Ws`）
まで一般化して `R600(7,0,0)(8,0,0)(9,0,0)` まで来た。汎用部品:

    WPdT_twoAY_at / TopLd_of_AtLd / RunLd_of_TopLd / AtLd_iter / AtLd_fam
    LadYv / LadAp / AtLd_Vs / AtLd_Ws / AtLd_VsIt / AtLd_WgS / WgOk_all
    Pws α（指数の型はパラメータ）/ R375m_tower_gen / R600_limit_gen

段 `k` を上げるには指数の型を `BwG` で 1 段足して族を書き直す（約 300 行）。
**天井が低いので割に合わない。**

## ★★★★ 壁は `TwOk` 階層の `Fter` 1 箇所（2026-09-12 深夜）

`SmallA` の `TwOk r m` 階層（`TwSt`/`TwOk`/`NTw`、33000〜33240）は閉性がほぼ全部緑:

    TwOk_nil / TwOk_one / TwOk_pay（**m = 0 も**）/ TwOk_oneNil / TwOk_repN /
    TwOk_itJ / TwOk_twoIt / TwOk_twoNilE / NTw_nil / TwSt_split / TwOk_two

**穴は 1 箇所だけ**:

    TwOk (r+1) 0 (two W Z)   ＝ 2 の記録の直上に 2 の記録（`Fter r m` が弾く）

**荷は壁ではない**（`TwOk_pay_e` が `m = 0` でも緑）。走りだけが壁。

### 今回の新しい道具はその穴を「荷が `nil`」の形で破る

    GOK_twoNW_gen … TwSt (r+1) 0 D = D' ++ [ftwo N] に当てると
                    TwOk (r+1) 0 (two W nil) が出る（階段は TwOk_nstW）

    TwOk_nstW (hN : ∀ r, NTw r N) (hW : ∀ r, TwOk (r+1) 0 W)
      : ∀ k r m, Fter r m → TwOk r m (nstW N W k)                  ★緑
    LOk1_nstW / TwoOk_twoWnil / TwSt_fone                          ★緑

**残る食い違い**: 階段 `nstW N W k` は毎段同じ `N` を使うので `∀ r, NTw r N` が要る。
`TwSt (r+1) 0` の節が与えるのは `NTw r N`（その段だけ）。
直すには兄弟の条件を「全段で良い」に強めた階層 `TwStA` を作る（`TwOk` 階層の写し、
400〜600 行）。ただし `W` にも `∀ r, TwOkA (r+1) 0 W` が要り、鎖
`twoIt W (pay Z Y) m` は荷が `pay` なので `two · nil` の形に入らない。

## ★★★ いま一番先の形（2026-09-12 夜）

新しい語の道具（`SmallA` に無かった）:

    GOK_twoNW_gen (ctx0 V) {N Wt} (hJN) (hJW) (hJT) (hGV : GOK (plug ctx0 V))
      (hstair : ∀ k, GOK (plug (ctx0 ++ [fone V]) (nstW N Wt k)))
      : GOK (plug (ctx0 ++ [fone V]) (two N (two Wt nil)))          ★緑

    nstW N Wt 0 = two N Wt,  nstW N Wt (k+1) = two N (one Wt (nstW N Wt k))
    unQW N Wt D = (D,1,0) :: jk1 D (two N Wt)（歩幅 2、`snocW_of_tower`）

これで `ChBase`（＝ `TwoOk X → TwoOk (two X nil)`）が階段 1 本に落ちた:

    ChStair : ∀ N Wt, JkA N → (N は普遍) → JkA Wt → TwoOk Wt →
                ∀ k, LOk 1 (nstW N Wt k)
    ChBase_of_ChStair / R375m61_of_ChStair                          ★緑

階段の `k = 0` は `TwoOk Wt` そのもの、`k+1` は `TwoOk_one`（緑）で落ちる。
残るのは **`LOk 1 (nstW N Wt k)`** ＝「深さ 1 で 2 の記録を置く」。
`LOk 1 (two N Y) ⟸ LTwo Y`（`LTwo_nil`/`LTwo_pay`/`LTwo_one`/`LTwo_oneNil` は緑）
なので、`LTwo Wt` と `TwM 1 (nstW N Wt k)` に落ちる。`Wt` には `TwoOk` しか
無いのが効くかどうかが焦点。

## ★★ 残る 1 文（2026-09-12。まずここ）

`APd` だけで書ける版（一番読みやすい）:

    StQ : ∀ p k ks, APd (true :: ks) (two nil (stkP p (nstQ nil p k)))
    R376_of_StQ (h : StQ) : R373 ++ [(5,3,0)] ∈ W 0                    ★緑

    nstQ N p 0 = nil,  nstQ N p (k+1) = one nil (two N (stkP p (nstQ N p k)))

`k = 0` は `stk (p+1)` なので `p` の帰納で前の段。中身は `k` の段だけ。
`p = 0` は `nstQ N 0 k = nstN N k` で `APd_nstN`（緑）→ **`stk 2` は無条件**。
**最小の壁は `stk 3`**（`APd_stk3_of` が待っている形）。

層の言葉で書いた同値な版:

    OneRunA : ∀ q Y, JkA Y → (∀ bs, APd (true::bs) Y) →
                ∀ bs, APd (true::bs) (stkP q (one nil Y))
    TwoNilStep : ∀ Z, JkA Z → (∀ bs, APd (true::bs) Z) →
                   ∀ bs, APd (true::bs) (two nil Z)          （`Z` 全称なので強すぎるかも）

## いま無条件で緑な走り

    APd_stk1 / APd_stk2 : ∀ ks, APd (true::ks) (stk 1) / (stk 2)
    APd_twoStkGen (hJN) (p ks) (hst : ∀ k, APd (true::ks) (two N (stkP p (nstQ N p k))))
      : APd (true::ks) (two N (stkP p (two nil nil)))

## 同じ壁の 4 つの顔（2026-09-12 に突き合わせた。どれも中身は同じ）

| 族 | 残る 1 文 | 形 |
|---|---|---|
| `APd` | `StkStep : ∀ q, TwoOk (stk q) → TwoOk (stk (q+1))` | `q=0→1` 緑、`q=1→2` が壁 |
| `APd`（階段版） | `StkStair`（`StkStep` の中身を階段の `k` の段に） | 本ファイル、緑の帰着 |
| `TwoOk` | `ChBase : ∀ X, TwoOk X → TwoOk (two X nil)` | `X=nil` は `TwoOk_twoNil` 緑 |
| `SCtx`/`SG` | `SNilF : ∀ ks, SG (true::false::ks) nil` | `SNilT` の残り 1 形だけ |
| `WPdR` | `OneRunA` / `RunPay` / `HtowR` | 予算つきの層での言い換え |

`SNilF` を開くと: `SCtx ks D₂`、`SG (false::ks) U` に対して

    GOK (plug D₂ (two nil (one U nil)))

`APnil_gen0` で `GOK (plug (D₂ ++ [ftwo nil]) (pay U C))` に落ち、
`GOK_twoPayZ_of` で `∀ N ∈ VCh U, GOK (plug D₂ (two N U))`（＝ `SHtow`）に落ちる。

### `SCtx`/`SG` は「走りの枠を持ち、1 の枠の兄弟が弱い」族（＝ 何度も再発明した族）

    SCtx []            D = ∃ ks, GCtx (true::ks) D
    SCtx (true :: ks)  D = ∃ D' U, SCtx ks D' ∧ (JkA U ∧ SG ks U) ∧ D = D' ++ [fone U]
    SCtx (false :: ks) D = ∃ D', SCtx ks D' ∧ D = D' ++ [ftwo nil]     ← 裸の走りの枠

`RCtx`（2 の枠の兄弟が一般）は階段が回らない。`SCtx` は兄弟を `nil` に固定して
**走り長の帰納**を回す代わりに、2 の枠の直上の荷（`SPayF`）だけを仮定にする。
**`WPdR` の予算つき層はこの再発明。** 新しい族を作らないこと。

### `TwoOk` が閉じている操作（緑）

    TwoOk_nil / TwoOk_twoNil（= `stk 1`） / TwoOk_pay / TwoOk_oneNilA（`one V nil`）
    TwoOk_one（`one W Z`、`Z` は `LOk 1`）
    ChBaseG_pay / ChBaseG_oneNil

閉じていないのは `two W Z` の 1 つだけ（`ChBase` / `ChBaseOne` / `ChBaseTwo`、
`TwoTwo_of` がこの 3 つを合成する）。

## 既知の最短形との接続

`SmallA` の最短形 `StkStep : ∀ q, TwoOk (stk q) → TwoOk (stk (q+1))` の中身は
`APd_twoStkGen` で**階段の `k` の段**だけになる:

    StkStair : ∀ N（普遍）, ∀ q, (∀ ks, APd (true::ks) (two N (stk q))) →
                 ∀ k ks, APd (true::ks) (two N (stkP q (nstQ N q k)))
    StkStep_of_StkStair / R376_of_StkStair                     ★緑

`k = 0` はちょうど仮定。残るのは「走りの上に `one nil` を 1 個載せてまた走りを積む」1 段。

**注意: `R376_of_*` は既に約40個ある。新しい帰着を増やす価値は薄い。**

## 詰まる理由

`APd (false::ks)` の節が作るのは `one U (two N V)`、つまり **2 の記録の直下は必ず
1 の枠**。`two N' (two nil W)`（2 の記録が 2 つ続く）は `APd` の節では作れない。
語のレベルで作るのが `GOK_stkW_gen` だが、**先端が `two nil nil` のときだけ**。
`stk 3` に要るのは先端が一般の `W` の版で、`snocQ_of_tower` / `unQ` / `Mtwd (p+2)` の
一般先端版という新しい語の補題が要る。

注意: 階段を `APd_cf` で `APd (false::ks)` に落としてはいけない。`APd_cf` の `N` の
条件はその `L` だけなので、`APd_twoTwoGen` が要る「`kk` について普遍」より弱い。

## 落とし方（全部緑）

    R376_of_TwoNilStep ← R376_of_OneRunA ← RunAll_of_OneRunA ← WPdR_stkO ← WPdR_stkG

    WPdR_stkG (p ks) (hk : SOkR ks) (hJN : JkA N)
      (htw : ∀ i, WPdR ks (TwG N p i N)) : WPdR ks (stkP p (two N nil))   ★無条件

    TwG N p 0 X = stkP p X,  TwG N p (i+1) X = TwG N p i (one N (stkP p X))
    TwG N p (i+1) X = stkP p (one N (TwG N p i X))
    plug (ctx ++ blkC V (replicate p nil) ++ blkR N (replicate p nil) i) X
      = plug (ctx ++ [fone V]) (TwG N p i X)

`GOK_runGNil_gen` の階段を**木**で書いたので入り目の列が伸びない。
`WPdR_stkO` は入り目 `[]` のまま回るので `SOkR_bot` / `WPdR_nilT` / `RunPay` が要らない。

## もう 1 本の（古い、より大きい）落とし方

    R376_of_HtowR ← R376_of_RunPay ← RunAll_of_RunPay ← WPdR_stkS
    HtowR : ∀ ctx V, JkA V → (typing) → GOK (plug ctx (two nil V)) →
              ∀ N, VCh V N → GOK (plug ctx (two N V))

こちらは「一般の荷を持つ 2 の記録は 1 の枠の**直上**にしか置けない」という壁に当たる
（追記398）。道具は 3 つだけ:

    GOK_twoNilW_gen / GOK_stkW_gen / GOK_runGNil_gen … 先端が `nil` のときだけ
    GOK_twoPayZ_of                                  … 先端が `pay Z Y`（鎖が要る）
    WPdR_twoOf                                      … 荷を予算の節に置く（1 の枠が直下）

## 層 `WPdR`（いま緑の版）

入り目 `(b,p) : Bud ×ₗ ℕ` の 3 種類:

    ⊥ = (⊥,0)      `[fone U]`
    (⊥,p) (p>0)    `replicate p (ftwo nil)`
    (b,p) (b ≠ ⊥)  `[fone U, ftwo N] ++ replicate p (ftwo nil)`

底 `WPdR [] V = ∀ bs, APd (true::bs) V`。DM 測度は `(ks : Multiset (Ekey Bud))`。
主力: `WPdR_nilRun` / `WPdR_stkG` / `AYdWR` / `AYdTWR` / `WPdR_payA` /
`WPdR_oneNil` / `WPdR_stkS`。

## 行列の梯子（`bms -c` 実測、下ほど大きい）

    R600 (7,0,0) の輪の族   ← いまのシート証明済み
    R600 (7,0,0)(7,0,0)     ← いまの証明中
    R600 (7,1,1) / RB / R375m (6,1,0) / R375m (6,2,0)
    行376 = R373 (5,3,0)    ← 最終目標

予算型の在庫: `ℕ`(ω) / `ℕ ×ₗ ℕ`(ω²) / `ℕ ×ₗ (ℕ ×ₗ ℕ)`(ω³) /
`Colex (ℕ →₀ ℕ)`(ω^ω、`import Mathlib.Data.Finsupp.WellFounded`)。

### 緑の主力（再導出しないこと）

    WPdR_nilRun  … `WPdR ((b,p)::ks) nil`（長さ `p+1` の縦の走り、無条件）
    AYdWR / AYdTWR / WPdR_payA (RunPay)   … 荷
    WPdR_oneNil / WPdR_nilT / WPdR_nilB   … 空木
    WPdR_stkS (RunPay) : ∀ q ks, SOkR ks → WPdR ks (stk q)   … 走りの塔
    RunAll_of_RunPay / R376_of_RunPay

### `RunPay` の中身（追記391）

`C` の W 帰納:
- `C = []`: `pay V [] ≅ V` ✓
- 内側の場合: 同じ形の IH ✓（予算も形も動かない）
- 重複の場合 `C = C' ++ [(0,0,0)]`: 鎖 `stkP (p-1) (twoIt nil (pay V C') m)` が要る。
  形は `preRun (p-1) ks`。**ここが最後の 1 点**。

`GOK_twoPayZ_of`（族 `NN` の鎖で W 帰納を回す一般補題）を使うと、
要るのは `htow : ∀ N ∈ VCh V, GOK (plug ctx' (two N V))` だけになる。

### 行列の梯子（`bms -c` 実測、下ほど大きい）

    R600 (7,0,0) の輪の族   ← いまのシート証明済み
    R600 (7,0,0)(7,0,0)     ← いまの証明中
    R600 (7,1,1) / RB / R375m (6,1,0) / R375m (6,2,0)
    行376 = R373 (5,3,0)    ← 最終目標（`RunPay` 1 文）

予算型の在庫: `ℕ`(ω) / `ℕ ×ₗ ℕ`(ω²) / `ℕ ×ₗ (ℕ ×ₗ ℕ)`(ω³) /
`Colex (ℕ →₀ ℕ)`(ω^ω、`import Mathlib.Data.Finsupp.WellFounded`)。

### いま緑になっている主力（再導出しないこと）

    WPd_Tb60u   : ∀ks, WPd (0::ks) Tb60            Tb60 = two nil M0t
    WPd_twoM0   : JkA N → (∀ks, WPd (0::ks) N) → ∀ks, WPd (0::ks) (two N M0t)
    WPd_twoPayM0: ∀B Bok B, ∀N（予算 0 族）, ∀ks, WPd (0::ks) (two N (pay M0t B))
      鍵: 荷 `(0,0,0)` の鎖は `twoIt · (pay nil []) m`＝**空荷**なので
          平らな走り `twoIt nil nil m` と語が同じ（`jk1_pay_nil`）。
          兄弟が「予算 0 の族（全予算）」なら `WPd_twoOf (k := m)` の側条件が
          そのまま出るので、幅 m に上限が要らない。

    hang4_R600 / hang5_R600 : Bok B → R600 ++ B↑4 / B↑5 ∈ W 0
    R600400 / R600410 / R600420 / R600500 / R600510 _mem
    Aok_R600510, Y510*, UJit*, UJitW*   （下の「Aok を取る」参照）

### ★ 1 行証明したら、次は `Aok` を取る（2026-09-12 の教訓）

新しい行 `X ∈ W 0` が緑になったら、まず

    Aok_append_Mid (d := ...) _ hAok_prev (MidD_one ...) hX  : Aok X

を作る。`Aok X` があれば既存の道具が全部乗り、**族がまとめて出る**:

    LwA_of_Aok → LwA_U11 → RunA 0 1 (X ++ U11 0 m) → Aok
      → RunG_snoc2（`(2,2,0)`）/ PkGA + `wordJ 2 2 ws`（junk の語）
      → PkGA_Aok（**また Aok。反復できる** = `UJit` / `UJitW`）
      → LadB_mem（PU の梯子）
    Lv_snoc / Lv_snoc2（`Lv 1 0 A = Aok A`）: `(1,1,0)` / `(1,1,0)(2,2,0)`

実測: 1 段 `(1,1,0)(2,2,1)^m(2,2,0)(3,3,1)^p` は **`p ≤ m` のとき標準形**で、
`(m,p,n)` の 3 パラメータで単調に増える。junk に `AltT i`（i ≥ 1）を入れると
非標準になるので使わない。

### ビルド

`lean/Small.lean` は `lean/SmallA.lean`（安定部分, 78k 行）を import する
小さいファイル。`leanman check Small.lean` は **1 秒**。新しい定理は
`Small.lean` にだけ足す。大きくなったら `SmallB.lean` を作って同じように分ける。

---

## 以下は古い記述（履歴。上と食い違うときは上が正しい）

## いまの状況（先にここを読む）

- **いちばん短い形（2026-09-13）**: `StkStep : ∀q, TwoOk (stk q) → TwoOk (stk (q+1))`。
  `q = 0`（`TwoOk_nil`）と `q = 1`（`TwoOk_twoNil`）は緑なので**壁は `q = 1 → 2`**、
  つまり `TwoOk (stk 2)`＝「走り 3 連を 2 の記録の直上に置く」。`R376_of_StkStep` は緑。
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

  さらに先端 `Z` を一般化すると（追記350）**荷の場合が木の構造帰納から消える**:

      ChBaseG Z := ∀W, JkA W → TwoOk W → TwoOk (two W Z)     （`ChBase` は Z = nil）
      ChBaseG_pay : ChBaseG Z → Bok Y → ChBaseG (pay Z Y)     ★緑
      TwoTwo_of (ChBase) (ChBaseOne) (ChBaseTwo) : TwoTwo     ★緑
      R376_of_TwoTwo : TwoTwo → 行376                         ★緑

  **残るのは荷の無い 3 文 `ChBase` / `ChBaseOne` / `ChBaseTwo` だけ。**

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
| `R376_of_StkStep` | `∀q, TwoOk (stk q) → TwoOk (stk (q+1))` | **いちばん短い。`q = 0,1` は緑、`q = 1 → 2` が壁。2026-09-13** |
| `R376_of_StkTwo` | `∀q, TwoOk (stk q)` | 同上（`q = 2` が壁） |
| `R376_of_TwoTwo` | `∀Z, JkA Z → ∀W, TwoOk W → TwoOk (two W Z)` | 荷の無い 3 文（`ChBase` / `ChBaseOne` / `ChBaseTwo`）に分かれる |
| `R376_of_FoneB` | `∀ws, GOK (plug (BCtx ws) (one nil nil))` | 裸の 1 の記録を 1 個足す（荷すら要らない） |
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
