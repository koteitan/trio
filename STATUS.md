# 現在地（2026-08-30 昼）

**3 行 z<2 バシク行列の停止性は、Lean 上で `CoreCap` 1 本に帰着している。**
`CoreCap` は **`CoreSingleton` と同値**（`Lind.lean:181` / `:195`）で、
**単独で `WellFounded stepRel` を出す**（`Final.lean:573 TRIO_terminates_of_cap`）。

    残核を日本語 1 行にすると:
    **接頭辞を全部 W に持つ文脈 M の、最後の列の行 1・行 2 を「何に」差し替えても W に残る。**
    段の上界 `a` は `(v,z,t)` だけで決まり、**`b, c` には依らない**。
    ＝「親のある列は段を食わない」という原理そのもの。

## ★ `CoreCap` の展開は 3 分岐しかない —— 全部 Lean に無条件の等式がある（§137, R2 実測）

`|M|<=3` の全数 **1,333,584 件**（サンプリングなし、神託ゼロ）で `oper` の計算と照合、**破れ 0**:

    j0 >= 1    24.0%  S⟦n⟧ = S[0] :: (S.tail)⟦n⟧   `oper_cons_nat`（`Wset.lean:2041`）
    j0 = 0     31.0%  S⟦n⟧ = 根つき塔               `oper_cons_tower1/2`（`:2789`/`:3231`）
    noparent   45.0%  S⟦n⟧ = S.dropLast             `oper_eq_pred_of_noParent`

**4 つ目の分岐は無い。** ⟹ **`A ++ B`（独立な 2 元の連結 = `WCat` の形）は
`CoreCap` の展開に現れない。⟹ `CoreCap` は `WCat` を要求しない。**

## ⚠ `rsum` の壁は `CoreCap` には当たらない（私の §131/§133 の枠組みの誤り）

    WSnoc   shTower Q e (n+1) = shTower Q e n ++ shiftr01 (n*e) 0 Q  ← **連結**。rsum が要る
    CoreCap tow v z R (k+1)   = (0,v,z) :: graft R (tow v z R k)     ← **graft**。W_add を通らない

`graft` は末尾の孤児を差し替えるだけで `rsum` の側条件が発生しない。
⟹ L3 の `not_rsum_*`（緑）は**真だが無害**。`W_add` が死んでいても路線は死なない。
⟹ 私が STATUS に書いた「`j0=0` ⟹ rsum が破れる ⟹ 壁」は**誤り。撤回した。**

## ★★ 当たる壁は `TowerOK2`。残る債務は 3 つだけ（R2 実測）

    ⛔ **(2)「`c >= 2` が未処理」と (3)「`argOK` が破れる」は、どちらも撤回された**（§139）。
       (2) L3 が `tower2_stage_fits` を **`z < c`** に一般化 ⟹ `c >= 2` はむしろ**易しい側**
       (3) R2 が起点を数え直し ⟹ 破れる起点は `srow=0` の塔だけで、そこは
           `rsum_self_cons` ＋ `W_flatMap_copies` で**無条件に閉じている**

## ★★★ 残核はこの 1 点（§139）

> **`z = 1` かつ `c = 1` かつ `srow = 2` かつ「親が根でない」**

    `domT R m` ⟹ **m = 2w + c - 1**（w = 末尾の行 1、c = 末尾の行 2）
    要求 `2w + z <= m`  ⟹  **`z < c`**（`tower2_stage_fits_of_lt`, `L105Cap.lean:1093`）
    親が根なら `nextR` が `z < c` を自動で与える（`tower2_root_z_lt`）
    ⟹ **`z=1, c=1` のときだけ根が親の候補から外れ、`z < c` が使えない**

**閉じている枝（全部無条件）:**

    j0 >= 1 (cons)  `oper_cons_nat`（`Wset.lean:2041`）
    noparent        `oper_eq_pred_of_noParent` ＝ `Pred` ＝ `CtxOK` の接頭辞
    srow=0 の塔     `rsum_self_cons`（`:2539`）＋ `W_flatMap_copies`（`:2551`）
    srow=1 の塔     `oper_cons_tower1` ＋ `TowerOK1`（節 3 の与件がある場面）
    srow=2 で親が根 `tower2_stage_fits_of_lt`（`z < c` が自動）

## ⚠ いま確かめている問い（課題 L111 / R92）

親が根でないなら `j0 >= 1` ⟹ **(P1) `oper_cons_nat` の枝**に落ちるはず。
そこは「閉じている」と報告されているが、それは**等式が無条件**という意味であって
**所属が閉じる**という意味ではない。**そこを区別して確かめさせている。**
通れば `CoreCap` は閉じる。通らなければ、止まる場所が本当の残核。

⟹ **`CoreCap` と `TowerOK` は別々の核ではない。`CoreCap` の唯一の難所が `TowerOK2`。**

## ⚠ `CtxOK` は何も落としていない（R2 実測、教訓 16 の警告）

37,044 組すべて装備ずみ（確定 30,348 / 予算切れ 6,696 / **確定した非装備 0**）。
⟹ 「`CtxOK` があるから平坦な `M` は来ない」は**言えない**。

## 段は木のどこでも消費されない（R2 実測、|M|<=2・深さ 9・170 万ノード、破れ 0）

    I1 先頭列が入口の根のまま      破れ 0
    I2 先頭列の lev = 段 a のまま  破れ 0

## ★ 降下の停止性は「孤児への到達」に一意化される（§136）

`W u = lfpS (...)` は**最小**不動点 ⟹ 導出木は整礎。`Aop`（`Wset.lean:170`）の 3 節のうち

    節 1  `|M| <= 1 ∧ lev M 0 = 0`   … 底
    節 2  `∀ n >= 1, M⟦n⟧ ∈ X`      … 段は下がらない
    節 3  `∃ m < u, domT M m ∧ ...`  … **段が厳密に下がる唯一の節**

⟹ 節 2 の枝は必ず節 1 か節 3 に着地する。節 3 には `domT` = **最終列が孤児**が要る。

> **残核 1 行: 「cap した文脈の展開木は、どの枝でも最後に『最終列が孤児』の形に到達するか」**

`srow`（`Trio.lean:81`）は最終列の行 1・行 2 だけで決まる ⟹ `c >= 1` なら `srow = 2`。
⟹ **`CoreCap` の `∀ b c` は `∀ srow` そのもの**（定義 1 行）。

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

## 0. 検算（team-lead が自分で回した、2026-08-29）

    leanman check -C /home/koteitan/proofs/dbms/lean lean/Final.lean  ⟹ **exit 0（緑）**
    `trio_cofinality`（`Core.lean:4602`）は仮定が `ST_TS M` / `ST_TS N` だけ ＝ **無条件**
    `lean/` で `sorry` を含むのは **`Dbms.lean` 1 本だけ**（別路線。この連鎖に入らない）

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
