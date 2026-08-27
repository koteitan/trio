# 課題 L1 の作業ノート（2026-08-28）

Lean の `Conv3.conv3`（`lean/Dbms3.lean` §8）を Python の `tools/dbms/rows3.py`
（conv3 v14 ＋ 課題 H1 の 5 条項）に追いつかせた。

## 0. 出発点

    leanman check -C /home/koteitan/proofs/dbms/lean lean/Dbms3.lean
      -> exit 0 / sorry 0（commit c6ad992）

## 1. `St.prev` の 3 値化は**もう済んでいた**

課題 G3 の報告は「`St.prev : ℕ` は Python の 3 値（None/0/1）を表せない」と
書いていたが、実際の `Dbms3.lean` はすでに

    /-- 直前の分岐列の選択。`0` 浅い / `1` 深い / `2` まだ無い（Python の `None`）。 -/
    prev : ℕ

で、入口 `b2d3` も `⟨[], 2, [], M, 0⟩` で始めていた（commit 5013ac3 の時点から）。
`prev` は `== 0` と `== 1` でしか読まれないので、`2` を `None` と読む符号化で
Python と完全に一致する。**だから 3 値化のための型の変更は要らなかった。**

## 2. 足した条項

### (a) v12 `newterm` ＋ v14 `wterm` / `wterm_anchbefore`

Python は `conv3` の入口で `st['prev']` を**破壊的に** `None` に落とす。
Lean は状態を線形に渡すので、局所の値 `prev0` を 1 つ挟み、以降の
`st.prev` を全部 `prev0` に置き換えた（`sh0` / `sh1` の 3 か所と、
分岐列でない柱・選択肢の無い柱が返す `bp.2` の 2 か所）。

    let prev0 : ℕ :=
      if p.1 = 0 then 2
      else if isWCol (some p) && (par0 st.Mo off == some 0) && !anchBefore st.Mo off then 2
      else st.prev

第 1 の枝が `newterm`（行 0 が 0 の柱は新しい加算項の頭）、第 2 の枝が
`wterm` ＋ `wterm_anchbefore`（根に直付けの「x w」の柱 `(k,0,0)` も加算項の頭。
ただし前にアンカー `(1,1,0)` が 1 本でもあれば効かせない）。

### (b) v14 h1（課題 H1）の 5 条項

新しい定義（どれも `Mo` と添字だけで決まる＝**写しに同変**）:

| Lean | Python |
|---|---|
| `termTopAux` / `termTop` | `term_top` |
| `copyHead` | `copy_head` |
| `topLevel` | `top_level` |
| `anchBefore` | `anch_before` |
| `closesTop` | `closes_top` |
| `hiB2` / `hiBlock2` | `hi_block2` |
| `p0deepOk` | `p0deep_ok` |

`term_top` の Python 側は再帰の深さを 64 で打ち切るが、`par0` は添字を**真に
減らす**ので、Lean では燃料 `j + 1` を渡せば同じ（64 列未満の行列では完全に
同じ。いま扱うのは <=8 列）。

`conv3` の中の変更は 2 か所だけ:

    let hi := hiBlock2 Mo off                       -- hiBlock -> hiBlock2
    let sh0 :=
      if closesTop Mo off nxt then true
      else if (prev0 == 0) && !closesUnit nxt then !(p0deepOk Mo off p nxt)
      else (prev0 == 0) || closesUnit nxt

と、`wchainHeadAux` の「鎖の頭が写しの頭なら `none`」（＝鎖はそこで切れる）。

使わなくなった `pv2` は消した（`closesHiUnit` は v14 で呼ばれない。定義は
記録として残してある）。`hiBlock` も `conv3` からは呼ばれなくなった。

## 3. 既存の証明への波及（3 か所だけ）

1. `conv3_lvl0`（先頭の `(0,0,0)`）: 根は `p.1 = 0` なので `newterm` が発火し、
   子に渡る状態の `prev` が `st.prev` ではなく `2` になる。**言明を直した**。
   `b2d3_diagSeqT` は `conv3_lvl1` を任意の `st` について使うので波及しない。
2. `conv3_lvl1`（`(1,1,1)`）: `simp` に `isWCol` を足した
   （`isWCol (some (1,1,1)) = false` を潰すため）。
3. `conv3_tail_step`（`(k+2,k+2,1)`）: 同上。

`decreasing_by` の停止性証明、`contrOne_nil` / `contrFind_nil`、§10〜§12 は
**1 文字も触っていない**。

## 4. Python との突き合わせ

道具は `lean/l1_sets.py`（入力集合を作る）と `lean/l1_check.py`
（`Dbms3.lean` の本文を貼った使い捨て file に `#eval ... IO.FS.writeFile` を
足して `leanman check` で走らせ、Python の像と行 diff する）。課題 G4 の
`tools/dbms/lean_v13_check.py` と同じやり方で、**Lean に計算させた結果**を
比べている（Lean の定義を Python で書き直してはいない）。

`tools/dbms/*.py` は読むだけなので、旗の切り替えは実行時に
`rows3.V12` / `rows3.V14` の辞書を書き換えて行う（file は触らない）。

    python3 lean/l1_sets.py 7 /tmp/l1work/s7.txt
    python3 lean/l1_check.py gen /tmp/l1work/s7.txt /tmp/l1work/c7
    leanman check -C lean /tmp/l1work/c7/l1check.lean
    python3 lean/l1_check.py diff /tmp/l1work/c7

## 5. 突き合わせの結果

| 集合 | 個数 | 食い違い |
|---|---|---|
| <=6 列 BMS 3 行 z<2 標準形 **全数** | 8387 | **0** |
| 7 列 **全数**（<=6 列と合わせて gen<=7 の 77282 個ぜんぶ） | 68895 | **0** |
| 8 列（縮約発火 2076 ∪ h1 で像が変わる 352 ∪ 無作為 3000） | 5412 | **0** |

旗ごとに「像が変わる行列」を数えた（Python 側の実測、`l1_sets.py`）:

| 旗 | <=6 列 | 7 列 | 8 列 |
|---|---|---|---|
| h1 | **0** | **18** | **352** |
| wterm ＋ wterm_anchbefore | 0 | **0** | **0** |
| mark（v12, **Lean 未移植**） | 0 | **0** | **0** |

`wterm` は <=8 列では像を 1 つも変えない（旗を落としても同じ）。ただし
**枝そのものは発火する**（`is_w_col(p)` かつ `par0(Mo,off) == 0` かつ前に
アンカー無し、という柱を持つ行列は <=7 列で 8913/77282 個ある）ので、
7 列全数の突き合わせで Lean 側の `prev0` の第 2 の枝は十分に叩かれている。

`mark` も <=8 列では像を 1 つも変えないので、Lean に無いことがこの範囲の
突き合わせに影響しない（§7）。

h1 は写しの頭が 1 本も無い行列では元の定義に戻るので、**<=6 列では像が
1 つも変わらない**。だから既存の <=6 列の `#guard` はそのまま通る。

## 6. `#guard`

**h1 で像が変わる行列を全部**入れた（そこが今回の変更点だから）:
7 列の **18 個** ＋ 8 列の **352 個**。`wterm` は像を変えないが、課題 G3 が
名指しした <=8 列の非標準 3 個とその 7 列の接頭辞（`wterm` の枝が実際に発火
する 4 個）も置いた。
7 列で v13 が v12 と違う 290 個からの抜き取りのうち 1 本が h1 で像が変わる
ものだったので、h1 の影響を受けない別の 1 本に差し替えた。

`#guard` を 374 本足しても `leanman check` は 9 秒 -> 17 秒（ファイルは
76 KB -> 154 KB）。<=6 列 8387 個の全数は**入れない**（既存の流儀どおり、
外部の突き合わせ道具 `l1_check.py` で不一致 0 を確かめる）。

## 7. 移植しなかったもの

* **v12 `mark`**（`leaves_mark_local`）。残余なしの縮約を「写しを飲んだ印が
  像に残る」ときだけ許す条項。Python は `st['rec']`（柱ごとに「決める直前の
  `prev`」を記録する辞書）を読むので、Lean に載せるには `St` にもう 1 本
  持ち回りを足す必要がある。課題 L1 のブリーフが「後回しでよい」としたもの。
  <=8 列では像の差 **0**（実測。§5 の表）。だからこの範囲の突き合わせには
  影響しないが、双子（`M ++ (1,1,0) ++ 写し`）や 9 列以上では効くはずなので、
  単射性を Lean で言うときには要る。

* v14 の旗 `chu`（`closes_hi_unit`）は Python 側も既定 off なので、Lean の
  `closesHiUnit` は定義だけ残して呼んでいない（v14 のまま）。

## 8. 次にやるとき

`tools/dbms/rows3.py` は課題 P1/P2/P3 の候補条項（旗 `V15`）を持ち始めた
（2026-08-28 04:35 の版）。**旗は全部既定 off** なので `b2d3` の像は v14 h1 の
ままで、この突き合わせはその版でも食い違い 0 だった（再測ずみ）。`V15` の
どれかが on になったら、この file の §2 と同じ形で Lean に足すこと。

---

# 課題 L2 の作業ノート（2026-08-28）

`ST_D3_conv3_of_parts` が取る 6 つの仮定を、軽い順に `Conv3.b2d3` について
証明していく。出発点は `ConvDiagT3` だけが証明ずみの状態。

## L2 (a) `ImgLenT3` — **証明した**

    ∀ M, ST_TS M → 1 < |M| → 1 < |b2d3 M|

道具 3 本（`Dbms3.lean` §11.4）:

* `Conv3.conv3_ne_nil` 入力が空でなければ像も空でない。`conv3` の本体は
  `cols` に本体の柱 `(dd2, e1, e2)` を**必ず**積むので、`conv3.eq_def` を
  1 回開いて外側の `match` を `split` するだけで出る。
* `Conv3.eq_true_of_ite_some` `(if X then Y else none) = some Z` から `X = true`。
  縮約の枝で `lad0 = true` を取り出すのに使う。**`lad0` の巨大な式を書き下さずに
  済ませる**のが肝（書き下すと 30 行を超える）。
* `Conv3.two_le_app` `cols ++ w ++ w'` の長さの下界。

証明は 2 枝:
* 縮約の枝は `lad0` が真なので `cols` 自身が 2 列以上。
* ふつうの枝は `A ++ B = r ≠ []`（`List.takeWhile_append_dropWhile`）なので
  `A` か `B` の像が 1 列以上。

## L2 (b) `ImgBlockT3` — **仮定 `Conv3.BlkInv` に落とした**（`sorry` は 0）

    ∀ M, ST_TS M → blockok 0 (b2d3 M)
    blockok 0 C = (C ≠ [] → C.headI.1 = 0) ∧ (∀ p ∈ C, 0 ≤ p.1) ∧ steps1 C

### 見つけた不変量

**`d ≤ |st.ST|`**（呼び出しの開始深さは、祖先の鎖の長さ以下）。これ 1 本で
`blockok` がぜんぶ出る。理由:

    lad0 なら ST1 := ST.take d ++ [pw]   |ST1| = d + 1
    dd0    := fit の値（[d, |ST|] に収まる）または d+1
    ST2    := ST1.take dd0 ++ [(base,pl2)]      |ST2| = dd0 + 1
    dd2    := fit の値（[dd1, |ST2|] に収まる）
    st1.ST := ST2.take dd2 ++ [(e1,e2)]         |st1.ST| = dd2 + 1

つまり **「柱を 1 本置くと、置いた柱の行 0 + 1 がちょうど新しい鎖の長さ」**。
そして次に置ける柱の行 0 は「その時点の鎖の長さ」以下。**この 2 つが噛み合って
`steps1`（行 0 の段差 1 以下）になる**。入口は `st.ST = []` なので先頭の柱の
行 0 は 0 以下 = 0。`∀ p ∈ C, 0 ≤ p.1` は ℕ だから自明。

### 証明した土台（`Dbms3.lean` §11.5）

| 名前 | 中身 |
|---|---|
| `Conv3.fitAux_bounds` | `fitAux ST w x k = some y → x ≤ y < x + k` |
| `Conv3.fit_bounds` | `d ≤ |ST| → fit ST d w = some y → d ≤ y ≤ |ST|` |
| `Conv3.fit_getD_bounds` | 既定値こみの版 |
| `Conv3.len_take_app` | `(ST.take d ++ [x]).length = d + 1` |
| **`Conv3.depths_ok`** | **1 本の柱ぶんの深さの計算がぜんぶ満たす性質**（上の表） |
| `Conv3.BlkOK` | 呼び出しごとの不変量（下） |
| `Conv3.BlkOK_nil` | 空の呼び出し |
| **`Conv3.BlkOK_app`** | **連結の補題**（下） |
| `Conv3.getLastD_app` / `getLastD_indep` | その道具 |
| `ImgBlockT3_of_BlkInv` | 入口 `st.ST = []` から `blockok 0` |

    BlkOK d st res :=
      steps1 res.1
      ∧ d ≤ |res.2.ST|
      ∧ (res.1 = [] → |res.2.ST| = |st.ST|)
      ∧ (res.1 ≠ [] → res.1.headI.1 ≤ |st.ST|)
      ∧ (res.1 ≠ [] → (res.1.getLastD).1 + 1 = |res.2.ST|)

`BlkOK_app` は `steps1_append`（`Seqlex.lean`）の継ぎ目条件
「`Y` の先頭 ≤ `X` の末尾 + 1」を、**途中の鎖の長さ**を仲立ちにして埋める:

    Y.headI.1 ≤ |stm.ST| = X.getLastD.1 + 1

### 残り（`Conv3.BlkInv`）と、詰まった点

1. **関数帰納法 `conv3.induct` は使える。** 相互再帰なので `fun_induction` は
   通らない（`No functional induction theorem ... or function is mutually recursive`）が、
   `refine conv3.induct (motive1 := ...) (motive2 := ...) ?_ ?_ ?_ ?_ ?_ ?_` は通る。
   枝は 6 つ（conv3 の空 / 縮約 / ふつう、convResid の空 / 尾が空 / 尾が非空）。
   **枝の中では `intro` を 49 本入れると、`have` で束ねられた局所値
   （`v s2 A B ent base_d base_s base_sd pl2 force1 first1 prev0 bp base lad1 e1 e2
   h1 lad0 ST1 dd0 ST2 dd1 dd2 st1 fc f0 Lb LA FA` ＋ `hcontr LS rA` ＋ 帰納法の
   仮定 3 本 ＋ `hd`）が全部名前つきで手に入る。**
2. 空の枝は `conv3_nil` ＋ `BlkOK_nil` で**閉じた**。
3. **ふつうの枝は `depths_ok` ＋ `BlkOK_app` ×2 で組める**（組み方は上のとおり）。
   ところが最後に `rw [conv3.eq_def]; dsimp only` で目標を開くと項が巨大になり、
   局所値で書いた証明項との defeq 検査が `whnf` で燃え尽きる
   （`maxHeartbeats 2000000` でも足りない。1 回の `leanman check` が 5 分）。
   **次の一手: `conv3` の 1 列ぶんの本体を名前つきの関数
   （`conv3Body` など）に括り出す。** そうすると `conv3.eq_def` が構文的な
   書き換えになり、目標も証明項も小さいままになる。**定義の意味は変えない**ので
   Python 側が動いていても安全（`#guard` が全部通ることで確かめられる）。
4. 縮約の枝には、さらに 2 つの穴がある:
   * **`contr_rd_ok`**: 残余の開始深さ `rd` が `d ≤ rd ≤ |rU.2.ST|` に収まる。
     `rd = d + 1 + e` の側は `dd2 ≥ d`（`depths_ok`）から出る。
     `rd = dmapAt rU.2.dmap (rest2[0].1 - 1)` の側は、**`st.dmap`（もとの深さ ->
     像の深さ）と `st.ST` の関係を不変量にしないと出ない**。
     候補: 「`k < |dmap|` なら `dmap[k] < |ST|`、かつ `dmap` は狭義単調」。
   * **`convResid_blk`**: `convResid` の不変量。残余は**森**なので、次の木に移ると
     開始深さが `rd - (m0 - tail[0].1)` と**下がる**。だから `BlkOK` の第 2 項
     （`d ≤ |res.2.ST|`）は `convResid` については**そのままでは偽**である。
     弱めた形（「最後の木の開始深さ ≤ 終了時の鎖の長さ」）にしたうえで、
     縮約の枝が `rB` に必要とする `d ≤ |rR.2.ST|` を別途出す必要がある。

**これは Python 側に返すべき発見ではない**（`conv3` の設計の欠陥ではなく、
Lean 側の証明の組み方の問題）。実測では `blockok` の破れは <=7 列 77282 個で 0。

## L2 (d) `SandwichUT3` の見積もり（証明はしていない）

    SandwichUT3 f := ∀ A, ST_TS A → 1 < |A| → ∀ n ≥ 1,
                       sle3 (f (A⟦n⟧)) ((f A)⟦n+1⟧)

`oper`（`Trio.lean:98`）は BMS 側と DBMS 側で**同じ関数**なので、この命題は
「変換 `f` と展開 `⟦·⟧` がどれだけ可換か」を測っている。`oper` の形は

    M⟦n⟧ = M.take j0 ++ (n 個の写し)      写しは [j0, j1) を d0/d1 だけ持ち上げたもの

なので、要る補題は次の 5 本になる（依存関係つき）。

### (S1) `oper_split` — 展開は「接頭辞 ＋ 写し」

    M⟦n+1⟧ = M⟦n⟧ ++ (n 番目の写し)

`oper` の定義が `M.take j0 ++ (List.range n).flatMap g` なので
`List.range_succ` と `flatMap_append` だけで出る。**`Cofidx.lean` の
`oper_mono_idx` が実質これ**（`sle3 (M⟦n⟧) (M⟦m⟧)`, `n ≤ m`）。
**依存: なし**（もう手元にある）。

### (S2) `BadRootT3` — 悪い部分の対応

    A の悪い部分 [j0, j1) の像が、conv3 A の悪い部分 [j0', j1') に対応する

具体的には
* `srow (conv3 A) (|conv3 A| - 1)` が `srow A (|A| - 1)` から決まること、
* `parent (conv3 A) i1' (|conv3 A| - 1)` が、`parent A i1 (|A|-1)` の像の位置
  （`st.dmap` の値）と一致すること、
* 持ち上げ幅 `d0'`, `d1'` が `d0`, `d1` から決まること。

**これが本丸**。`conv3` が最後の柱とその祖先をどう綴るかを追う必要がある。
**依存: `ImgBlockT3`**（`parent` / `nextrel0` は行 0 の段差の性質を使う）。
`OrderT3` には依存しない。

### (S3) `PrefixT3` — 接頭辞の像は像の接頭辞

    conv3 (M.take j) が conv3 M の接頭辞に一致する（j が「ユニットの切れ目」なら）

`conv3` は次の柱を覗く（`nxt` / `onx` / `closes_unit` / `closesTop`）ので
**素朴には偽**。切れ目を「加算ユニットの端」（`closesTop` が真になる位置）に
限れば成り立つはず。`oper` の切り口 `j0` は悪いルートなので、この形で足りる
見込み。**依存: なし**（`conv3` の構文だけ）。

### (S4) `CopyEquivT3` — 写しの像は像の写し

    conv3 (M.take j0 ++ 写し) = (conv3 M).take j0' ++ (像の写し)

**これは Python 側の課題 H1 が追っている「写しに同変」そのもの**
（`copy_head` / `term_top` / `closes_top` / `hi_block2` / `wchain_head` /
`p0deep_ok` の 5 条項は、まさにこの同変性を回復するために入れた）。
H1-NOTES §12 の実測では <=7 列 x m<=3 で 54068/… が同変、**壊れているのが 12 対**。
つまり**この補題はいまの `conv3` ではまだ真ではない**。
**依存: (S3)。そして Python 側の族 β（課題 H2）の決着待ち。**

### (S5) `ExtraUnitT3` — 右辺の `n+1` の 1

像は入力より「梯子 2 段」ぶん長い（`ConvDiagT3`: `conv3 (diagSeqT 0 v)
= ddiagSeqT (v+2)`）。その 2 段のぶんだけ、像の側の写しは 1 個多く要る。
`sle3` の等号側ではなく `seqlex` 側（真に小さい）で吸収する形になる。
**依存: (S2), (S4), `ImgLenT3`。**

### まとめ（依存グラフ）

    ImgLenT3 ─────────────┐
    ImgBlockT3 ──> (S2) ──┼──> (S5) ──> SandwichUT3
    (S3) ──> (S4) ────────┘
                  ↑
             課題 H2（族 β）が Python 側で決着してから

* **`OrderT3` には依存しない。**
* **`ImgBlockT3` には依存する**（(S2) 経由）。だから (b) を先に片づけるのが正しい順。
* **(S4) はいまの `conv3` では偽**（<=7 列で 12 対の反例）。
  つまり `SandwichUT3` を Lean で証明する前に、Python 側の H2 が要る。
  ただし C2（`SandwichU` の実測）は <=7 列 386405 対で破れ 0 なので、
  (S4) より弱い形（`sle3` で足りる = 一方向だけ）で回避できる可能性はある。

## L2 (c) `mark` の移植 — 未着手／見積もり

`V12['mark']`（`leaves_mark_local`）を Lean に載せるには:

1. `St` に `rec : List (ℕ × ℕ)`（もとの添字 -> 「決める直前の段」）を足す。
   値の符号: `0` 浅い / `1` 深い / `2` None / `3` tie / `4` 記録なし。
   **`St` に項目を足すと §9/§10 の無名コンストラクタ `⟨STd (k+1), st.prev, …⟩`
   が全部壊れる**ので、そこも直す。
2. `conv3` の分岐列の枝で `rec` に記録する。
3. **`mark` の判定は `contrOne` の中ではなく `conv3` の本体に置ける**。
   Python は `for e in (0,1)` の中で `continue` するが、`mark` が見られるのは
   `rest2 == []` かつ `e == 1` のときだけで、そこは**ループの最後**だから、
   「`contrFind` が返した候補を後から捨てる」形と同値である。
   つまり `contrOne` を `conv3` と相互再帰にする必要は**ない**。
4. ただし判定には下見の `conv3 A …` と `conv3 U …` が要るので、
   `conv3` の本体に再帰呼び出しが 2 本増える。`decreasing_by` は既存の
   `rA` / `rU` と同じ形なので `omega` で閉じる見込み。
5. 突き合わせは **9 列以上の双子**（`M ++ (1,1,0) ++ 写し`）で。
   <=8 列では像が 1 つも変わらない（L1-NOTES §5 の表）。
