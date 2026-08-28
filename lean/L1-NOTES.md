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

## L2 (c) `mark` の移植 — **移植した**

`V12['mark']`（`leaves_mark_local`）を Lean に載せた。

### 何を変えたか

1. `St` に `rc : List (ℕ × ℕ)`（もとの添字 -> 「決める直前の段」）を足した。
   符号は `0` 浅い / `1` 深い / `2` まだ無い（Python の `None`）/
   `3` 選択肢が無い（`'tie'`）/ `4` 記録なし（`'none'`）。
   **項目名を `rec` にすると自動生成の再帰子 `St.rec` とぶつかる**ので `rc`。
2. `conv3` の分岐列の枝で `recNew` に記録し、`st1.rc` に載せる。
   `rc` は像に効かない（読むのは `leavesMark` だけ）。
3. `Conv3.recAt` / `Conv3.leavesMark` を新設。
4. 縮約の門に 1 枚かぶせた（`cfm`）。

### 肝: `contrOne` を相互再帰にしなくてよい

Python は `for e in (0, 1)` の中で `continue` するので、素朴には
`contrOne` が `conv3` を呼ぶ形（＝相互再帰の輪に入る）になる。
ところが **`mark` が見られるのは `rest2 == []` かつ `e == 1` のときだけ**である
（`rest2 == []` かつ `e == 0` はその前の `elif e == 0 or not deep_end: continue`
で落ちる）。`e == 1` はループの最後なので、そこで `continue` することは
「ループが候補なしで終わる」ことと同じ。つまり

    「`contrFind` が返した候補を、あとから `mark` で捨てる」

と**完全に同値**である。だから `contrFind` はそのままでよく、`conv3` の本体に
門を 1 枚かぶせるだけで済んだ。判定の下見に `conv3 A` / `conv3 U` の再帰呼び出しが
2 本増えるが、`decreasing_by` は既存の `rA` / `rU` と同じ形なので `omega` が通る。

### 既存の証明への波及（2 か所）

* §9/§10 の無名コンストラクタ `⟨STd (k+1), st.prev, …, st.nc⟩` に `st.rc` を足した。
  対角 `diagSeqT` には分岐列 `(a,1,0)` が 1 本も無いので `rc` は素通りする
  （`(j, j, min j 1)` が `isBranch` になるには `j = 1` かつ `min j 1 = 0` が要り、
  両立しない）。
* `conv3_lvl0` の `simp` に `isBranch` を足した（根 `(0,0,0)` が分岐列でないことを
  潰すため。`rc` の `if isBranch (0,0,0) …` が残ってしまう）。

### 突き合わせ

| 集合 | 個数 | 食い違い |
|---|---|---|
| **双子** `M ++ (1,1,0) ++ 写し`（<=14 列） | 4003 | **0** |
| 　うち **`mark` で像が変わるもの全部** | 2043 | 0 |
| 　＋ 無作為 | 2000 | 0 |
| <=6 列 全数 | 8387 | **0** |
| 7 列 全数 | 68895 | **0** |
| 8 列（縮約発火 ∪ h1 で像が変わる ∪ 無作為） | 5412 | **0** |

双子は `rows3.twin`（`M ++ (1,1,0) ++ M[1:] の写し`）で、<=7 列 77282 個から作った
（最長 14 列）。`mark` で像が変わるのは 2043 個。**`#guard` 458 本もそのまま通る**
（<=8 列では `mark` は像を変えないので当然）。

### まだ Lean に無いもの

`V12['mark_global']`（`leaves_mark`。2 通り走らせて像を比べる大域版）は
突き合わせ専用で、局所版と gen<=7 で差 0 なので移植しない。
`V14['chu']`（`closes_hi_unit`）は Python 側も既定 off なので、`leavesMark` の
Python にある 3 つ目の枝（`closes_hi_unit` が両方を浅くする）は現れない。


---

# 課題 L3: 残りの証明債務の地図（2026-08-28）

## 0. まず全体の姿

`lean/` は **自前 64299 行、`sorry` 0 個、`axiom` 宣言 0 個**。
だから債務は全部「**`Prop` として定義されて、定理の仮定として開いたまま**」の形をしている。
`grep sorry` で見つかるのは `Dbms.lean:67` と `:74` の**散文**（「sorry は 0 だ」と
書いてある行）だけである。

**トラックは 2 本ある。両者は独立で、いま合流していない。**

| トラック | 目的 | 現状 |
|---|---|---|
| **A. 直接トラック**（`Final.lean` ほか） | 3 行 BMS の停止性そのもの | 残核 **1 本**（15 行の `Prop`） |
| **B. DBMS トラック**（`Dbms3.lean`） | 像が DBMS 3 行標準形であること | 残り 5 本 |

## 1. 最終定理はどこにあるか

**ある。** `lean/Final.lean:57`（3 行 = トリオ）:

```lean
/-- **Trio sequences terminate.** -/
theorem TRIO_terminates (h2 : Wset.TowerGraft2) (he : Wset.TowerExp) :
    WellFounded stepRel := step_terminates (wf_Rnf_holds h2 he)

theorem no_infinite_expansion_holds (h2 : Wset.TowerGraft2) (he : Wset.TowerExp) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion (wf_Rnf_holds h2 he)
```

**いまの頂点**（仮定 1 本）は `Final.lean:358`:

```lean
theorem TRIO_terminates_of_revive_self (h : Subst1gReviveSelf) : WellFounded stepRel
theorem no_infinite_expansion_of_revive_self (h : Subst1gReviveSelf) : ¬ ∃ 無限展開列
```

2 行（ペア数列）は**無条件で完成**している（`Pair/Final.lean:54`
`PSS_terminates_unconditional : WellFounded stepRel`、仮定なし）。

`Reduction.lean:51` の `step_terminates (wfimg : WellFounded Rnf) : WellFounded stepRel`
が「順序数側の整礎性 ⟹ 停止性」の橋で、減少 `m_step_decreases` は証明ずみ。
つまり**停止性 ＝ `WellFounded Rnf`（標準形上の `<o` の整礎性）**である。

## 2. DBMS 3 行の停止性 — **存在しない**

`WellFounded` / `Acc` / `stepRel` と `ST_D` / `ST_D3` を結ぶ定理は**リポジトリに 1 本も無い**。
`ST_D` / `ST_D3` を結論に持つ定理は 15 + 6 本あるが、**全部が「像が標準形である」型**
（`ST_PS M → ST_D (conC M)` / `ST_TS M → ST_D3 (conv3 M)`）である。

### ⚠ 依存の向きに注意（重要）

**DBMS トラックは BMS の整礎性を「入力として消費している」。**

```lean
theorem ST_D3_conv3_holds (h2 : Wset.TowerGraft2) (he : Wset.TowerExp) … :=
  ST_D3_conv3 (wf_olt_ST_TS_holds h2 he) H hd hM
                --  ^^^^^^^^^^^^^^^^^^ BMS 3 行の整礎性
```

`ST_D3_descend`（`Dbms3.lean` §5）は `A` についての**整礎帰納法**である。降下先の
`B` は `translate B <o translate A` としか分からないので、`ST_TS` の構成子に沿った
構造帰納法にはできない（**性質 R が 3 行で偽**だから `B = A⟦n'⟧` に取れない、
`tools/dbms/NOTES.md` §性質 R）。2 行側も同じで、`DbmsStd.lean:1582,1590` が
`wf_olt_ST_PS_holds` と `pss_cofinality_holds` を使っている。

したがって **`ST_D3 (conv3 M)` を完成させても、それだけでは停止性は出ない**。
DBMS トラックの成果物は「像が DBMS 標準形である」という**特徴づけ**であって、
停止性への**還元ではない**。停止性に効かせるには、どちらかが要る:

1. **DBMS 3 行の整礎性を独立に証明する**（いまリポジトリに命題すら無い）。
   そのうえで `OrderT3`（順序埋め込み）で BMS 側に移す。この道なら
   `ST_D3_conv3` を**整礎性を使わずに**（＝ `ReindexT1` を経由せずに）
   出し直す必要がある。
2. あるいは DBMS トラックを「停止性の証明」ではなく「順序数の読みの検証」
   （シート・Y 数列との対応）として位置づける。

**これは Python 側に返す話ではない**（`conv3` の設計の問題ではなく、Lean の
配線の問題）。ただし**課題の目的の再確認が要る**ので報告する。

## 3. 債務の一覧

### A. 直接トラック（停止性そのもの）

| 命題 | いまの状態 | 大きさの見積もり | 依存 |
|---|---|---|---|
| `Reduction.step_terminates` | **証明済み** | — | `WellFounded Rnf` |
| `Pair/Final.PSS_terminates_unconditional`（2 行） | **証明済み・無条件** | — | — |
| `Final.TRIO_terminates_of_revive_self` | **証明済み**（仮定 1 本） | — | `Subst1gReviveSelf` |
| **`Wtower2.Subst1gReviveSelf`** | **未証明・これが唯一の核** | 命題は `Wtower2.lean:3213-3230` の **15 行**。証明の大きさは未知（`PROOF-STATUS.md` §5 が「BM4 展開への新しい数学的入力が要る」と書く壁） | — |
| `Wset.TowerGraft2` / `Wset.TowerExp` | 核から**導出済み**（`towerGraft2_of_liftStage` / `towerExp_of_substG` ほか） | — | `Subst1gReviveSelf` |
| `Lind.CoreSingleton` / `CoreCap`、`Wtower2.WSnoc` / `Row1Mono` / `LowerLastParented`、`Wset.GraftAll` | 別ルートの核（同値な顔） | `RESIDUE-PROBLEM.md` §4.8 が「翻訳しても得は無い」と結論 | — |
| `Gamma.InfEquip` | ⛔ **偽**（`Infcex.not_infEquip` で反証済み） | — | — |

実測（`PROOF-STATUS.md` §4）: `(SUBST1g)` 210201 例 0 違反、`(TOW)` 164 万例 0 違反、
`(GC)` 1221 万例 0 違反。ただし「`W` 所属の判定自体が停止性問題なので決定的でない」
と明記されている。

### B. DBMS トラック（`Dbms3.lean`, `ST_D3_conv3_of_parts` の 6 仮定）

| 命題 | いまの状態 | 大きさの見積もり | 依存 |
|---|---|---|---|
| `ConvDiagT3 Conv3.b2d3` | **証明済み**（§9, §10） | 約 260 行 | — |
| `ImgLenT3 Conv3.b2d3` | **証明済み**（§11.4, 課題 L2 (a)） | 約 45 行 | — |
| `ImgBlockT3 Conv3.b2d3` | **`Conv3.BlkInv` 待ち**（§11.5）。空の枝と**縮約でない枝は証明ずみ** | 土台 約 200 行が済み。残りは縮約の枝 | `BlkInv` |
| └ `Conv3.BlkInv` の残り | **縮約の枝だけ**。2 つの穴（`contr_rd_ok` と `convResid_blk`） | 数十〜数百行（`dmap` と `ST` の関係を不変量に足す） | — |
| `SandwichUT3 Conv3.b2d3` | 未着手 | 5 本 (S1)-(S5) に分解（課題 L2 (d)）。(S2) が本丸 | `ImgBlockT3` ／ Python の H2 |
| `OrderT3 Conv3.b2d3` | 未着手 | **2 行側の対応物が 2533 行**（`Dbms.lean` §5-§8 の `readK_convC` 446 行 ＋ その支え）。3 行は読み `read3` すら未定義で、行 1 と行 2 の 2 種類の影があるので**節が 2 つ**要る。**2 行より大きい** | `ReadT3` ＋ `ImgDokT3` ＋ `ReadLexT3` |
| `ImgCofinalT3 Conv3.b2d3` | 未着手。**Python 側でまだ破れている**（`ImgClosedT` 破れ <=5 列 2 個 / <=6 列 54 個） | 2 行側は `ReindexD` に融合されていて **`DbmsStd.lean` の約 15000 行がまるごとこの証明** | 変換器 `conv3` の設計（Python の課題 H2/H5） |
| `SandwichLT3` | **要らない**（`ReindexT1_of_block` / `_of_cofinal` が使わない） | — | — |
| **DBMS 3 行の停止性** | **命題すら無い**（§2） | 2 行側にも無い。ゼロからの設計 | — |
| `read3` / `dok`（`OrderT3` の道具） | **未定義** | 2 行の `readK` は 67 行（うち `decreasing_by` 47 行） | — |

### C. 2 行 DBMS（参考・全部済み）

| 命題 | 状態 |
|---|---|
| `DbmsStd.reindexD_holds : ReindexD` | **無条件で証明済み**（`DbmsStd.lean:15189`）。約 15000 行 |
| `DbmsStd.ST_D_conC_final` | **無条件で証明済み**（`DbmsStd.lean:15192`） |
| `Dbms.readC_conC_ST`（読みの保存） | **証明済み**（§5-§8 で 2533 行） |
| `Dbms.conC_olt_iff_seqlex` | **証明済み**（3 行）。ただし右辺が **BMS 側の** `seqlex M N` で、`OrderT3` より**弱い** |

**2 行には `SandwichU` / `SandwichL` に当たる命題が無い**。役目は `ReindexD` の中の
`oper_mono`（上）と `m_step_decreases`（下）が直接果たしている。3 行では
`ReindexD` の形（相手が `A⟦n'⟧`）が偽なので、相手を「ある標準形 `B`」に緩めた
`ReindexT1` になり、そこで `oper_mono` が使えなくなった穴を埋めるために
`SandwichUT3` を明示的に立てる必要が出た。**これが 2 行と 3 行の構造的な分岐点。**

## 4. 運用上の注意（発見）

* **`Dbms3.lean` は `lakefile.toml` の `roots` に入っていない。** つまり
  `lake build` はこの file をビルドしない（`leanman check` で単体検査するだけ）。
  `PROOF-STATUS.md` の「自前 40850 行に sorry 0」は**この file を数えていない**。
* `Final.lean:5` の doc は残る仮定を `Wset.TowerOK` と **`Wset.TbOper`** と書くが、
  `TbOper` はリポジトリのどこにも無い（古い記述）。

## 5. 片づけたもの（課題 L3 (3)）: `BlkInv` の**縮約でない枝**

いちばん安いのは `ImgBlockT3` の残り（`BlkInv`）だったので、そこを詰めた。

新しく証明した道具（`Dbms3.lean` §11.5）:

* **`Conv3.depths_le`** — `depths_ok` の深さの部分だけ（`cols` を結論に含まない形）。
  **これが鍵**: `cols` を含む形だと `e2` や `pw` が結論に現れないので、
  単一化がそれらを決められず「implicit argument を合成できない」で止まる。
* **`Conv3.cols_blk`** — `depths_ok` を `BlkOK` の形に包んだもの。

そのうえで、`BlkInv` の帰納の 1 歩のうち **空の枝と縮約でない枝は証明できた**。
戦術の全文（scratch で機械検査ずみ。`· sorry` の 1 か所だけが縮約の枝）:

```lean
set_option maxHeartbeats 2000000 in
/-- `BlkInv` の帰納の 1 歩（**縮約の枝はまだ `sorry`**）。 -/
theorem blk_step (p : Col) (r : TrioSeq) (d : ℕ) (L : List Lent) (F : List Bool)
    (ps pw : ℕ × ℕ) (first force : Bool) (st : St) (nx : Option Col) (off : ℕ)
    (hd : d ≤ st.ST.length)
    (IH : ∀ (M' : TrioSeq), M'.length ≤ r.length → ∀ (d' : ℕ) (L' : List Lent)
        (F' : List Bool) (ps' pw' : ℕ × ℕ) (f1 f2 : Bool) (st' : St)
        (nx' : Option Col) (off' : ℕ),
        d' ≤ st'.ST.length →
        BlkOK d' st' (conv3 M' d' L' F' ps' pw' f1 f2 st' nx' off')) :
    BlkOK d st (conv3 (p :: r) d L F ps pw first force st nx off) := by
  have hA : (r.takeWhile (fun q => decide (p.1 < q.1))).length ≤ r.length :=
    (List.takeWhile_sublist _).length_le
  have hB : (r.dropWhile (fun q => decide (p.1 < q.1))).length ≤ r.length :=
    List.length_dropWhile_le _ r
  rw [conv3.eq_def]
  dsimp only
  split
  · sorry
  · refine BlkOK_app (le_refl d)
      (BlkOK_app ?_ (cols_blk hd rfl rfl rfl rfl rfl rfl rfl)
        (IH _ hA _ _ _ _ _ _ _ _ _ _ ?_)) (IH _ hB _ _ _ _ _ _ _ _ _ _ ?_)
    · exact Nat.le_succ_of_le (depths_le hd rfl rfl rfl rfl rfl).1
    · exact (len_take_app (depths_le hd rfl rfl rfl rfl rfl).2 _).ge
    · exact le_trans (Nat.le_succ_of_le (depths_le hd rfl rfl rfl rfl rfl).1)
        (IH _ hA _ _ _ _ _ _ _ _ _ _
          (len_take_app (depths_le hd rfl rfl rfl rfl rfl).2 _).ge).2.1

```

### 通し方の勘所（課題 L2 で詰まった点の解決）

* **枝の局所値を `intro` してはいけない。** `conv3.induct` の枝で `have` を
  `intro` すると、仮定は fvar で、`conv3.eq_def` で開いた目標は生の式になり、
  `rw` も defeq 検査も通らない（`whnf` が燃え尽きる）。
* 代わりに **`conv3.eq_def` -> `dsimp only` -> `split` で生の項のまま進み、
  補題の implicit を目標との単一化で決めさせる**。`BlkOK_app` / `cols_blk` /
  `depths_le` はどれも結論から implicit が決まる形にしてある。
* 帰納法は `conv3.induct` ではなく、**列数についての強い帰納法**（`IH` を仮定に
  取る形）にする。そうすると枝の `have` が出てこない。
* 側条件は全部 `?_` にして**あとで**片づける（先に書くと metavariable が
  決まっていなくて `Nat.le_succ_of_le` の implicit が合成できない）。

### 残り（縮約の枝の 2 つの穴）

1. **`contr_rd_ok`**: 残余の開始深さ `rd` が `d ≤ rd ≤ |rU.2.ST|` に収まること。
   `rd = d + 1 + e` の側は `depths_le` から出る。
   `rd = dmapAt rU.2.dmap (rest2[0].1 - 1)` の側は
   **`st.dmap` と `st.ST` の関係を `BlkOK` に足さないと出ない**。
   候補: 「`k < |dmap|` なら `dmap[k] < |ST|`、かつ `dmap` は狭義単調」。
2. **`convResid_blk`**: `convResid` の不変量。残余は**森**なので次の木で開始深さが
   `rd - (m0 - tail[0].1)` と**下がる**。`BlkOK` の第 2 項（`d ≤ |res.2.ST|`）は
   `convResid` については**そのままでは偽**なので、弱めた形が要る。

なお `ResidBlk`（`rd` の上界を仮定しない形）は**偽**である: `rd > |st.ST|` だと
`fit` が `none` を返して `dd0 = max rd |ST| = rd` になり、出した柱の行 0 が
`|st.ST|` を超える。だから `rd` の上界は落とせない。


---

# 課題 L4: 直接トラックの残核（2026-08-28）

## 0. 結論を先に

* 残核は **`Wtower2.Subst1gReviveSelf` ただ 1 本**（`Wtower2.lean:3213`、命題は 15 行）。
  古い 2 核 `TowerGraft2` / `TowerExp` は**これから導出済み**。
* 残核は「すべての trio 列について〜」の形なので **Python で列挙できる**。
  ただし中身の `M ∈ Wself` は**一般に有限計算で判定できない**（判定すること自体が
  停止性問題）。既存のプローブは 3 重打ち切りの過大近似で、**すでに大規模に
  0 違反**（1221 万例ほか）。同じ真偽検査を足す限界効用は小さい。
* **DBMS トラックは停止性の道ではない**（下の §4）。位置づけは「検証資産」。

## 1. `W a` とは何か

`W_u` は Buchholz 流の**反復帰納的定義**（`Wset.lean:171-217`）:

    Aop(W, u, X, M) :=
      (1) |M| <= 1 かつ lev(M,0) = 0
      (2) 全ての n >= 1 で M[n] ∈ X
      (3) ある m < u: 末尾列が孤児でレベル m+1、かつ
          全ての z ∈ W_m（根の深さ 0）で graft(M,z) ∈ X
    W_u := lfp(X |-> {M | Aop(W,u,X,M)})

ここで `lev(M,j) := 2*行1 + 行2`（z<2 なので添字対の辞書式を ℕ に詰めたもの）。

`Wchar.lean` の**厳密な**特徴づけ:

    |S| = 0  ->  つねに S ∈ W a
    |S| = 1  ->  S ∈ W a  <->  lev(S,0) <= a
    |S| >= 2 ->  S ∈ W a  <->  全ての n >= 1 で S[n] ∈ W a

つまり **`M ∈ W a` = 「M からどんな括弧の選び方 n1, n2, ... で展開しても、
有限回で 1 列以下（レベル <= a）に潰れる」**。停止性そのものを**下から**
（最小不動点として）組み立てたものである。段 `a` は「根の添字レベルの上限」
だけを意味し、`W_root_stage` で **段はちょうど根のレベル**と分かっている
（だから `Wself := {M | M ∈ W (lev M 0)}` 1 つに潰れる）。

**停止性との関係**: 「全標準形が或る `W u` に属する」＋ 共終性（`trio_cofinality`、
**3 行でも無条件に証明済み**）⟹ `WellFounded stepRel`。
`W u` は最小不動点なので、その上で超限帰納法が回るのが肝
（`Wset.acc_of_W` / `wf_of_cofinality_and_membership`）。

## 2. 3 つの核を行列の言葉で

### 2.1 舞台: 主ブロック `(0,v,z) :: R` と「塔」

    列:   0        1 .. |R|
    行0:  0        R の行 0（全部 > 0 = 全部この根の子孫）
    行1:  v        R の行 1
    行2:  z        R の行 2

これは順序表記の `psi_{v,z}(R の順序数)`（**主ブロック**）。

* `domT R m` = **`R` の末尾列は `R` の中では孤児**（レベル m+1 > 0 なのに
  自分の行に親がいない）。
* `hasParent ((0,v,z)::R) ...` = **根を頭に足した途端、その孤児に親ができる**。
  しかもその親は**根そのもの**（`parent_cons_eq_zero`）。

⟹ バッドルートが列 0 なので、展開は「末尾列を除いたもののコピーを n 個」。
`graft` の形に読み替えると

    ((0,v,z) :: R)[n] = 根 -> R.dropLast -> （より深く）同じものがもう一段 -> ... （n 段）

順序表記では `psi_{v,z}( A + psi_{v,z}( A + ... ) )` の **n 段の塔**。
「n 個のコピーを横に並べる」＝「n 段の塔を縦に積む」が同じ、というのが要点。

### 2.2 核 A `Wset.TowerGraft2`（`Wset.lean:4498`）— 行 2 で潰れる塔

条件に `srow R (|R|-1) = 2`（**行 2 の崩壊**）が付いている版。
このとき BM4 の上昇行列 `A_xy` により `d1 = w - v > 0` で、**コピー k は根の行 1 錐の
上で行 1 を k*(w-v) 持ち上げる**。だから塔の各段に入るのは素の塔ではなく
**持ち上げられた塔** `Lift1 (tow k) (w-v)`。

手元にある道具は接ぎ木閉包「段 `m` のブロックなら差し込んでよい」だけなのに、
リフトすると必要な段が `m + 2*(w-v)` に上がる。**この段のズレが核の正体**。

**現状: `towerGraft2_of_liftStage`（`Wtower2.lean:908`）で (WL) = `LiftStage`
「根リフトは段をちょうど 2d 上げる」から導出済み。**

### 2.3 核 B `Wset.TowerExp`（`Wset.lean:4507`）— 節 2 経由で来た塔

`srow` の指定なし。違うのは**手元のデータ**で、接ぎ木閉包の代わりに
「全ての n >= 1 で `R[n] ∈ Wstar`」しかない。ところが `domT R m` があるので
**`R[n] = R.dropLast`（n によらず同じ）**。つまりデータは実質

    R.dropLast ∈ Wstar

**1 個にしぼんでしまう**。差し替えの権利が一切ない状態で、n 段の塔全体が
`W a` に入ることを示さねばならない。

段なしの一番きれいな顔（`(TOW)`）:

    良い木 Q を深さ q0, q0+e, q0+2e, ... に n 本植えたら、その森も良い

### 2.4 現在の核 `Wtower2.Subst1gReviveSelf`（`Wtower2.lean:3213`）

    良い行列 S（∈ Wself）の第 p 列を、
      * 先頭列の深さが S の第 p 列と同じ
      * 他の列はそれ以上に深い
      * レベル lev(C,0) <= lev(S,p)
    を満たす良いブロック C に丸ごと差し替える。R := S.take p ++ C ++ S.drop(p+1)。

    さらに
      (i)  R の末尾列は R の中では親を持つ
      (ii) その末尾列は、自分の属するブロックの中では孤児
           （S.drop(p+1) が空なら C の中で、空でなければ S.drop(p+1) の中で）
      (iii) R の末尾を除いた部分に行 2 > 0 の列がある

    このとき R ∈ Wself。

一言でいうと **「良い行列のある列の下に、その列のレベル以下で止まる良いブロックを
吊るしてよい」**。未証明なのは (i)(ii)、つまり
**「文脈がブロック内の孤児を復活させてしまう」場合だけ**。それ以外は全部 Lean 済み。
(iii) は行 2 ≡ 0 なら 2 行の定理で無料（`zeroRow2_mem_Wself` / `snoc_zeroRow2`）
なので、実質 **行 2 の印がついた列が末尾より手前にある場合だけ**が残っている。

`W` の定義の節 3 と比べた差は **2 点だけ**:

| | `Aop` 節 3 | 残核 |
|---|---|---|
| 位置 | 末尾列のみ | **任意の位置** |
| ブロックの段 | `lev - 1` | **`lev`**（1 つ上） |

## 3. 3 つの関係と依存の木

**`Subst1gReviveSelf` ⟹ `TowerGraft2` ∧ `TowerExp`**（Lean で証明済み、12 本の鎖）。
**逆向きの証明はどこにも無い**。`Subst*` を結論に持つ定理は 5 本しかなく、全部
`Subst*` を仮定に持つ。だから残核は形の上で**真に強い**。

    Subst1gReviveSelf
      --subst1gRevive_of_self (Wtower2:3231)--> Subst1gRevive
      --subst1g_of_revive     (Wtower2:3424)--> Subst1g
      --substClosedG_of_subst1g (Wtower2:2687)--> SubstClosedG
           |- shiftTowerClosedS_of_substG (Wtower2:3615) -> (TOW)
           |     `- liftStageParented_of_tower (1800) -> liftStage_of_parented (560)
           |         -> (WL) LiftStage -> towerGraft2_of_liftStage (908) -> TowerGraft2
           |- cons_mem_W_of_substG (3709) -> TowerExp の m<a 枝
           `- substClosed_of_substClosedG (2681) -> SubstClosed
                 `- towerExp2Root_of_subst (3829) -> towerExp2Low_of_root (2208)
      --towerExp_of_substG (3803)--> Wset.TowerExp
      --TRIO_terminates_of_tower (Final:159)--> WellFounded stepRel

**わざわざ強い方に乗り換えた理由**（`Subst1g` の doc）: 核が 2 本 → 1 本、
段量詞 `u` が消える、`Aop` 節 3 との差が上の 2 点だけの**紙で読める命題**になる。

**どちらが証明しやすいか**: 実質の残りは `TowerExp`（行 2 塔・節 2 経由）側。
`TowerGraft2` は (WL) から出るところまで来ている。ただし RESIDUE-PROBLEM §5 が
「`(LOW)` / `(REPL)` / `(TOW)` 独立証明 / 多ブロック化はいずれも `TowerExp` 経由で
自分に戻る（循環）」と記録しているので、**顔を変える作業には価値が無い**。

## 4. 2 行はどう閉じたか / 3 行で何が足りないか

### 4.1 2 行の `W` は 3 行と**逐語的に同じ**

`Pair/Wset.lean` の `Aop` / `W` / `Wstar` / `tow` は 3 行版と同型。**塔もある。**
違うのは節 2 のガード `natDom M` があることだけ。

### 4.2 2 行の塔は **8 行**で閉じている

`Pair/Wset.lean:1315 Wstar_closed`（**仮定なし**）の塔の枝:

    have hlift : tow v R k ∈ W m := W_mono hvm ihk

**からくりはこの 1 行**。塔の 1 段前は `W v` に居て、分岐条件が `v <= m` なので
**段の単調性だけ**で `W m` に押し上がり、そのまま節 3 のデータに食わせられる。
リフトも文脈も新しい入力も要らない。

### 4.3 3 行で壊れるのは **ただ 1 点**

`Wset.lean:2694` の doc（逐語）:

> **A row-1 orphan is always dominated by the root.** If the principal root fails
> to revive `R`'s trailing column at row 1, that column's row 1 is at most `v`,
> so its level is at most `2v <= 2v+z` — the orphan is automatically BELOW the
> root's stage. **No such bound holds at row 2** (`no_hasParent_two_of_row1_zero`
> gives permanent orphans of level 1 under a level-0 root), and **that asymmetry
> is exactly why trio needs more than yapss.**

具体的な機構: **`(x,0,1)` 型の列（行 1 = 0, 行 2 = 1）はどんな文脈でも永久に
親を持たない**（`no_hasParent_two_of_row1_zero`, `Wset.lean:1893`）。行 2 の親は
行 1 の祖先でなければならず（`nextrel2` が `le1` を要求）、行 1 が 0 の列に
行 1 の祖先はあり得ないから。

帰結は 3 つ:

1. **二分法が消える。** 2 行は「根が孤児を復活させない ⟺ 孤児のレベル <= 根の段」
   が厳密な二分法。3 行でも `srow = 1` なら同じ（`tower1_le` が `2v+z <= m` を
   自動で出す ⟹ `tower1_mem` は yapss と**逐語的に同じ 8 行**で証明済み）。
   `srow = 2` では孤児のレベル `m` と根の段 `2v+z` の間に何の関係もない。
2. **塔が「リフトされた塔」になる。** 上昇行列 `A_xy` がコピーの行 1 を持ち上げる。
   これが `TowerGraft2`。
3. **`Aop` 節 2 の `natDom` ガードを外さざるを得ない**（行 2 の永久孤児を `Pred` で
   吸収する経路が要る。ガードを戻すと `Wstar_closed` が偽になる反例
   `[(0,0,0),(1,0,1)]` が `GRAFTALL-PLAN §4.5` にある）。その代償が
   「節 2 経由の塔」= `TowerExp` が核として残ること。

### 4.4 済んでいるもの

* **共終性側**（2 行の `argDomCore_holds` に対応する部分）は 3 行でも
  **無条件で証明済み**（`trio_cofinality`）。
* **z = 0（行 2 恒等 0）断片は完済**。`zeroRow2_mem_Wself`（`Wtower2.lean:2950`）が
  lean-yapss の無条件結果をそのまま輸入する。
  **「trio の難所は行 2 の列だけにある」**（doc 逐語）。

⟹ **残っているのは `W` の閉包側、しかも行 2 の崩壊だけ。**

## 5. Python で全数検査できるか

### 5.1 できる部分／できない部分

* 残核は「すべての trio 列 `S`, `C`, 位置 `p` について〜」の形で、
  **順序数も超限概念も出てこない**。だから**列挙はできる**。
* しかし中身の `M ∈ Wself` は **一般に有限計算で判定できない**。
  `|M| = 1` なら `2y+z <= a` で即決だが、`|M| >= 2` は「全ての n >= 1 で
  `M[n] ∈ W a`」という無限分岐の再帰で、**判定すること自体が停止性問題**。
* 実務では 3 重打ち切りの `inW` で 3 値（True / False / **未判定**）近似する:
  `n ∈ {1,2}` のみ、再帰深さ `MAXDEPTH`、列長 `MAXLEN`。
  未判定は成功に数えない。
* 打ち切りが**過大近似**（受理しすぎる向き）である根拠: `oper_prefix_of_le` より
  `n' <= n` なら `M[n']` は `M[n]` の接頭辞で `W` は接頭辞閉 ⟹ **n が大きいほど
  条件が強い** ⟹ `n ∈ {1,2}` は最も緩いチェック。`n <= 3` / `n <= 4` と突合して
  不一致 0（`tools/check_inw_ns.py`: 判定 2209 例 / 524 例）。

### 5.2 既存の計測（**全部 0 違反**）

| 命題 | スクリプト | 規模 |
|---|---|---|
| **残核そのもの** | `tools/probe_subst1g_adv.py` | 78885 決定（別実装の再監査 1201307 決定） |
| `Subst1g` | `tools/probe_subst1g.py` | 210201 |
| `Subst1g` on 実 ST_TS | `tools/audit_subst1g_stts.py` | **判定 651 例で頭打ち** |
| `(GC)` | `tools/probe_gc.py` | 12217217 |
| `(LOW)` | `tools/probe_lowerlast.py` | 5544711 |
| `(TOW)` 段なし形 | `tools/probe_tow_hard.py` | 1642293 決定 / 134699 未判定 |
| `(INS)` | `tools/probe_insert.py` | 1603817 |
| `(REPL)` | — | 1097675 |
| `(CAT)` | `tools/probe_cat.py` | 372290 |
| `(SNOC)` | `tools/probe_snoc.py` | 14455 |
| サンドイッチ | `tools/probe_sandwich.py` | 1920294 x 2 |

⚠ **実 ST_TS 行列では `inW` が判定不能**。決定的な監査ではない。

⟹ **同じ形の真偽検査を足しても限界効用は小さい。**

### 5.3 まだ測っていない 3 本（提案する仕様）

**検査 A（本命）: 残差インスタンスを「既存の証明済み補題で覆えるか」で分類する**

* 入力: `probe_subst1g_adv.py` が出す残差インスタンス
  （`context-revives` 枝。既存 14540 例 ＋ 新規乱択）。
* やること: 各インスタンス `(S, p, C)` について、`R ∈ Wself` が
  **証明済みの補題だけで出るか**を判定してタグを付ける。使える証明済み補題:
  `zeroRow2_mem_Wself`（行 2 ≡ 0）/ `snoc_zeroRow2` / `snoc_orphan`（孤児のままの
  1 列を継ぐ）/ `dropLast_mem_Wself` / `drop_mem_Wself`（接尾辞閉）/
  `oper_mem_Wself`（展開閉）/ `takeC_mem_of_prefixPackage` /
  `W_flatMap_copies`（e = 0 のコピー）/ `W_mono`。
* 出力: 「覆える／覆えない」の分類と、**覆えないものの構造の統計**
  （`|C|`, `|D|`, 行 2 > 0 の列の位置, `srow`, `e = w - v`, 根のレベル差,
  `hasParent` を与えている文脈列の位置）。
* 狙い: 覆えないものが**1 つの形に集中していれば、それが探すべき補題**。
  この「教師データ」型の測定は課題 H1 で実際に効いた（55 素性 -> 3 リテラルの述語）。
* 規模の目安: 1 例あたり `inW` を数回。数万例で数十分。

**検査 B: `(TOW)` の「内容領域」だけを網羅する**

* RESIDUE §4.8 より `(TOW)` が**無料でない**のは
  `|Q| >= 2` かつ `Q` に行 2 > 0 の列があり `e >= 1` のときだけ。
* `probe_tow_hard.py` は 164 万例の**乱択**。同じ領域を **`|Q| <= 4` で全数**に
  切り替え、`e ∈ 1..6`, `n ∈ 2..6` を回す。
* 追加の出力: RESIDUE §4.8 の漸化式（`|Q| = 2` でだけ実機確認ずみ）

      T_n[m] = T_{n-1} ++ (m 列の対角)
      T_n[m] = Q ++ shiftr01 e 0 (T_{n-1}[m])      (n >= 3)

  が**一般の `|Q|` でも成り立つか**を厳密に検査する。
* 狙い: 成り立つなら `(TOW)` は n についての帰納 ＋「`Q` の後ろに根レベルの
  等しい `Wself` 元を深く継ぐ」1 本に落ちる。成り立たない `|Q|` の形が
  見つかれば、そこが本体。

**検査 C: 打ち切りの健全性を残核の領域で確かめ直す**

* `check_inw_ns.py` は**一般の**母集団で `n<=2` vs `n<=3/4` を比べた（不一致 0）。
* **残核の残差インスタンスに限って**同じ突合をやる。残差領域で食い違えば、
  既存の 0 違反はアーティファクトの可能性がある。
* 規模: 残差から数千例。`n<=3` は重いので `|S| <= 4`, `|C| <= 3` に絞る。

**検査できない部分**: `M ∈ Wself` の真の判定（＝停止性そのもの）。
だからどの検査も「反例探し」であって「証明」ではない。

## 6. DBMS トラックの位置づけ — **判定: 2（検証資産）**

### 6.1 `ST_D3_conv3` を整礎性なしで出し直す道は**無い**

`ST_D3` は `diag` と `oper` の 2 構成子だけで生成される帰納的集合で、
**「<=o で下に閉じる」規則が無い**。だから `conv3 M ∈ ST_D3` を示すには
「対角から `conv3 M` へ**有限回の展開で到達する道**」を作らねばならない。

`ST_TS` の導出（`diag` / `oper`）に沿った構造帰納法にできれば整礎性は要らないが、
それには

    conv3 (M[n]) = (conv3 M)[m]        （性質 R）

が要る。**3 行ではこれが偽と確定している**（`NOTES.md` §性質 R。
反例 `M = (0,0,0)(1,1,1)(2,1,0)(3,0,0)`、しかもシートの OCF 欄が独立に裏付け:
BMS 側の基本列は `psi(W_w^n * W)`、DBMS 側は `psi(W_w^m * W_2)` で**別の順序数**）。

だから相手を「ある標準形 `B`」に緩めた `ReindexT1` になり、`B` に降りる帰納法
＝**整礎性が必然的に要る**。2 行側も同じ配線（`DbmsStd.lean:1582,1590` が
`wf_olt_ST_PS_holds` と `pss_cofinality_holds` を使う）。

### 6.2 DBMS 側の整礎性を独立に立てる道も現実的でない

DBMS は**展開規則が BMS と完全に同一**で、違うのは対角だけ
（BMS `(j,j,min j 1)` / DBMS `(j,j-1,min (j-2) 1)`）。だから DBMS の停止性は
**同じ問題の別インスタンス**であり、`W` 相当の機構を丸ごと作り直すことになる。
しかも **2 行 DBMS でさえ整礎性は書かれていない**。
「DBMS のほうが易しい」という前提は**どの行数でも実装されていない**。

### 6.3 行数の見積もり（道 1 を最後までやる場合）

| 部品 | 2 行の対応物 | 3 行の見積もり |
|---|---|---|
| `read3` ＋ `ReadT3` | `readK` 67 行 ＋ `readK_convC` 446 行 ＋ 支え = **2533 行** | 影が行 1 と行 2 の 2 種類、`conv3` は縮約つきで `convC` よりずっと複雑 → **5,000〜10,000 行** |
| `dok` ＋ `ReadLexT3` | **2 行は回避**（`olt_iff_seqlex` を BMS 側に当てて逃げた） | 前例なし → **2,000〜5,000 行** |
| `ImgCofinalT3` | `reindexD_holds` = `DbmsStd.lean` の約 **15,000 行** | 同等以上。しかも**いまの conv3 では偽**（Img 破れ <=6 列 54 個）なので Python 側の H2/H5 が先 → **>= 15,000 行** |
| `SandwichUT3` | 前例なし（`oper_mono` が代行） | **2,000〜5,000 行** |
| `ImgBlockT3` の残り | — | **300〜1,000 行** |
| **DBMS 3 行の整礎性** | **前例なし（2 行にも無い）** | BMS 3 行が 40,850 行 → **数万行**。しかも同じ壁（行 2 の塔）に当たる公算が高い |

合計 **>= 25,000 行 ＋ 前例のない部品 2 つ**。対して直接トラックの残りは
**15 行の Prop 1 本**。

### 6.4 したがって

* **停止性を目指すなら直接トラック。**
* DBMS トラックは
  * `ConvDiagT3`（証明済み）/ `ImgLenT3`（証明済み）/ `ImgBlockT3`（骨組み）
  * シート 1354/1358、BMS <-> DBMS <-> Y 数列の辞書
  という**検証資産**として意味があり、それ自体は完成させる価値がある。
  ただし**停止性への還元ではない**。
* 補強証拠: **`ST_D3_b2d3` は既に `TowerGraft2` / `TowerExp` を仮定に取っている**
  （`Dbms3.lean`）。DBMS トラックの結論そのものが直接トラックの核に依存している。


---

# 課題 L5: 検査 A の結果（2026-08-28）

道具は `tools/probe_residue_cover.py`。seed 20260828、200000 サンプル。
`inW` は既存プローブと同じ 3 重打ち切り（`n ∈ {1,2}` / MAXDEPTH 11 / MAXLEN 44）。

## 0. 結論を先に

1. **`(x,0,1)` 型の永久孤児は「難しさ」を集中させていない。** 期待は外れた。
2. **証明済みの 9 本の補題は、帰納を使わない限り残差をほとんど覆わない**
   （18025 件中 1094 件 = 6%、しかも全部 `|R| = 2` の退化した場合）。
   残核の中身は**丸ごと帰納の 1 歩の中**にある。
3. **★ 残核の側条件 6 本は 1 本も真理値に効いていない**（アブレーション）。
   仮定を全部落とした一般形を反証型で 164760 例ハントして**違反 0**。
4. ⟹ **停止性は仮定 4 つの 1 行の命題に帰着した**（Lean で機械検査ずみ、
   `lean/L5Subst.lean`）:

        SubstFree :=
          ∀ p S C, S ∈ Wself → p < |S| → C ≠ [] → C ∈ Wself →
            S.take p ++ C ++ S.drop (p+1) ∈ Wself

        TRIO.L5.TRIO_terminates_of_substFree : SubstFree → WellFounded stepRel

   **「`Wself` は任意の位置での任意の `Wself` ブロックの差し替えで閉じている」**
   — 深さも、レベルも、孤児の条件も、行 2 の条件も要らない。

## 1. 列挙（Lean の仮定をそのまま写した残差）

    residue                18025      ← **違反 0**
    skip/levC              89736
    skip/i                 50592
    skip/ii                22195
    skip/iii                5983
    skip/SinW               5240
    skip/R undecided        5493
    skip/CinW               2736

## 2. (A) 帰納を使わない補題で覆えるか

`free(M)` = `zeroRow2_mem_Wself` / `snoc_zeroRow2` / `two_col_mem_W` /
`snoc_orphan` / `W_add`(+`rsum`) / `W_flatMap_copies` を**再帰的に**組む探索
（`Aop` 節 2 の展開は使わない）。

    COVERED     1094 (6%)   ← 全部 `two_col`（`|R| = 2`）
    UNCOVERED  16931 (94%)

**⟹ 残差には「証明済みの補題で切り落とせる部分族」が無い。**
`(iii)`（`R[:-1]` に行 2 の列）がちょうど `zeroRow2` 系を殺し、
`(i)`（末尾列が親を持つ）が `snoc_orphan` を殺し、`W_add` の `rsum`
（`D` の根が `R` 全体の最浅）は `S[0]` が深さ 0 なのでほぼ成り立たない。

## 3. (B) 覆えないものの構造

`oper` の分岐データ `(j0, i1, d0, d1)` で見る（`j0` = バッドルート、
`i1` = 崩壊する行、`d0` = 行 0 のずらし、`d1` = 行 1 のリフト）。
`Q := R[j0 .. last-1]` = コピーされる塊。

    i1             1=65%   0=24%   2=10%
    d1             0=89%   1=4%    2=3%   3=1%
    zone_j0        C=57%   takeS=42%   D=0%      ← **バッドルートは D に入らない**
    Q_row2         True=88%
    TOW_free       False=62%  True=37%
    Q_covers_C     True=71%                        ← 塊が C を丸ごと含む
    has_permorph   True=52%  False=47%
    permorph_in_D  False=94%

`TOW_free` は RESIDUE-PROBLEM §4.8 の「`(TOW)` が無料になる 3 条件」
（`|Q| <= 1` / `Q` が行 2 を持たない / `d0 = 0`）。

## 4. (B1) 教師ラベルと 1 リテラルの分離度

ラベル: **「1 歩ほどくと自由領域に落ちるか」**（`n ∈ {1,2}` の展開が両方
`free`）。落ちないものが**本当に帰納を要する**インスタンス。

    覆えない 16931 件 → 1 歩で閉じる 5088 / 帰納が要る 11843

1 リテラルの分離度 `P(帰納が要る | 素性 = 値)`:

| 素性 = 値 | 分離度 | 件数 |
|---|---|---|
| **`i1 = 2`（行 2 の崩壊）** | **1.000** | 1747 / 1747 |
| **`d1 = 1`** | **1.000** | 825 / 825 |
| **`d1 = 2`** | **1.000** | 547 / 547 |
| `lenQ = 7` | 0.939 | 370 / 394 |
| `Q_row2 = False` | 0.852 | 1618 / 1900 |
| ... | | |
| `i1 = 0` / `d0 = 0` | 0.510 | 2092 / 4100 |

**`i1 = 2 ⟺ d1 >= 1`**（`nextrel2` が `le1` を要求するので行 1 は必ず真に増える）。

### ★ 分かったこと 2 つ

* **`i1 = 2`（行 2 の崩壊）は 1747/1747 で必ず帰納を要する。**
  Lean 側の分析（`tower1_mem` は行 1 で証明済み、行 2 だけが核）と**完全に一致**。
* **しかし逆は言えない。** 帰納を要する 11843 件のうち 10096 件は `d1 = 0`
  である。つまり **`d0 > 0` かつ `Q` に行 2 の列があれば、行 1 のリフトが無くても
  1 歩では閉じない**。難所は「行 2 のリフト」だけでなく「**行 2 の列を含む塊を
  ずらしてコピーすること**」そのものにある（RESIDUE §4.8 の `(TOW)` の
  内容領域の記述と一致）。

### 永久孤児 `(x,0,1)` は集中していない（**期待は外れた**）

    has_permorph = True   帰納が要る 6274 / 1 歩で閉じる 2578   → 0.709
    has_permorph = False  帰納が要る 5569 / 1 歩で閉じる 2510   → 0.689

**差は 2 ポイント。分離しない。** `permorph_in_C` / `permorph_in_D` /
`Q_permorph` も同様。永久孤児は「なぜ二分法が壊れるか」の**説明**ではあるが、
残差の中で難しさを**集中させる特徴ではない**。

## 5. (C) 仮定のアブレーション — **側条件は 1 本も効いていない**

残差の仮定を 1 本ずつ落として、他が全部成り立つインスタンスで反例を探す。

| 落とした仮定 | 判定 | **違反** | 未判定 |
|---|---|---|---|
| `lev (C 0) <= lev S p` | 10148 | **0** | 2773 |
| (i) 末尾列が R で親を持つ | 28383 | **0** | 1263 |
| (ii) 自分のブロックでは孤児 | 8720 | **0** | 1348 |
| (iii) `R[:-1]` に行 2 の列 | 3160 | **0** | 722 |
| 頭の深さ `C[0].x = S[p].x` | 2632 | **0** | 675 |
| 深さ `∀q∈C, S[p].x <= q.x` | 739 | **0** | 242 |
| **上の 6 本を全部** | **156247** | **0** | 18244 |

`S ∈ Wself` と `C ∈ Wself` は当然効く（落とすと `inW` が判定できなくなる）。

## 6. (D) 一般形 (SUBST-FREE) の反証型ハント

深さもレベルも自由なブロック `C`（深さ 0..6、レベル 0..9）を使い、
`S ∈ Wself` と `C ∈ Wself` だけを課す。

    判定 164760   **違反 0**   未判定 13411

内訳（判定できたもののうち）:

    頭の深さが違う              137954
    R に行 2 の列あり           155319
    C に浅い列あり               75187
    lev(C 0) > lev(S p)          74261
    |R| >= 5                     95943
    永久孤児 (x,0,1) あり        68552
    行 2 の崩壊 (i1 = 2)         11047

## 7. 陽性対照 — プローブは反例を**見つけられる**

「違反 0」がプローブの盲目のせいでないことを確かめた。同じ母集団で
**段を 1 つ下げた**主張（`R ∈ W (lev R 0 - 1)`）を測ると

    判定 67279   **違反 67279**（100%）

つまり `inW` はこの形の偽な主張を即座に、確実に落とす。
（もう 1 つの対照「`R` を逆順にする」は `ok` が返るが、逆順が所属を保つ場合が
実際に多いので対照にならない。段の対照が決定的。）

## 8. (E) 打ち切りの健全性を**残差の領域で**再確認

`tools/check_inw_ns.py` は一般の母集団で `n<=2` vs `n<=3` を比べていた
（不一致 0）。残差の領域（`|R| <= 7` の 1500 件）で同じ突合をやった:

    n<=3 で判定できた 1146   未判定 354   **n<=2 と食い違い 0**

## 9. 探すべき補題 — **(SUBST-FREE)**

    SubstFree :=
      ∀ p S C, S ∈ Wself → p < |S| → C ≠ [] → C ∈ Wself →
        S.take p ++ C ++ S.drop (p+1) ∈ Wself

**残核を本当に埋めるか: 埋める。** 仮定を 6 本落としただけなので
`SubstFree → Subst1gReviveSelf` は**仮定を忘れるだけ**（3 行）。
Lean で機械検査ずみ（`lean/L5Subst.lean`、`leanman check` exit 0 / sorry 0 /
axioms = `[propext, Classical.choice, Quot.sound]`）:

    theorem TRIO.L5.subst1gReviveSelf_of_free (h : SubstFree) : Subst1gReviveSelf
    theorem TRIO.L5.TRIO_terminates_of_substFree (h : SubstFree) : WellFounded stepRel
    theorem TRIO.L5.no_infinite_expansion_of_substFree (h : SubstFree) : ¬ ∃ 無限展開列

### なぜこれが進展になりうるか

* 残核 `Subst1gReviveSelf` は**帰納の 1 歩**である（RESIDUE §4.5）。帰納を回すと
  展開のたびに側条件を建て直さなければならない。実際
  `GRAFTALL-PLAN.md:3332` は深さ条件を厳格 `<` から非厳格 `<=` に弱めている
  ——「`oper` は厳格性を保たない」から。**側条件を全部落とすのはその極限**で、
  建て直しの手間がゼロになる。
* 側条件が消えると **`D = []` / `D ≠ []` の場合分けも、(i)(ii) の孤児の議論も
  要らなくなる**。`subst1g_of_revive`（`Wtower2.lean:3424`）と
  `end_subst_of_revive`（:3284）の 2 本立ての構造がそのまま 1 本になる可能性がある。

### ⚠ 注意（循環していないか）

* RESIDUE §4.8 が警告するのは**同値な言い換え**（`(GC)` / `(LOW)` / `(TOW)` /
  `(REPL)` / `(SNOC)`）である。`SubstFree` はそれらとは違い、残核より
  **真に強い**（同値ではない）。だから「翻訳して一周する」型ではない。
* **ただし強い命題が易しいとは限らない。** 測定が言えるのは「偽ではない」まで。
* 打ち切りの過大近似（`n ∈ {1,2}`）は残る。§7 の陽性対照と §8 の再確認で
  緩和はしているが、**証明ではない**。

### 次の一手（提案）

1. `SubstFree` を `Wtower2.lean` の帰納（`subst1g_of_revive`）に**そのまま**
   入れてみる。側条件が消えるので、いま `hpre`（接頭辞パッケージ）を
   捨てている箇所（RESIDUE §4.5）が使えるようになるかもしれない。
2. だめなら、6 本のうち**どれを戻すと通るか**を 1 本ずつ試す。
   測定上はどれも要らないので、**証明に要るものだけ**が残る。それが
   「本当の側条件」である。


---

# 課題 L6: `行 2 <= 行 1` は不変量だが、`natDom` ガードは戻らない（2026-08-28）

## 0. 結論を先に

1. **`行 2 <= 行 1` は BMS / DBMS 両方の標準形の不変量。証明した**
   （`lean/L6Inv.lean` と `lean/Dbms3.lean` §1.1、`leanman check` exit 0 / sorry 0）。
   既存の `Wset.zle1`（行 2 ≤ 1）より**真に強い**。
   系として **標準形には永久孤児 `(x,0,1)` が現れない**。
2. **しかし `natDom` ガードは戻らない。** `row2 <= row1` を全列に課しても
   `Wstar_closed` を壊す形が**309 個**残る。最小の反例:

        M = [(0,1,0), (1,1,1)]      （両方の柱で row2 <= row1）

3. 理由: 障害は `(x,0,1)` ではなく **行 1 のタイ**である。
   `nextrel2` は `le1` を要求し、`le1` は行 1 の**真の増加**を要求する。
   `(x,0,1)`（行 1 = 0）はその極端な場合にすぎず、`row2 <= row1` が消すのは
   その 1 点だけ。**行 1 = v >= 1 のタイは残る。**

## 1. 証明した不変量

`lean/L6Inv.lean`（`import Wset`。`Wset.zle1_ST_TS` の写経）:

    TRIO.L6.r21 (M) := ∀ p ∈ M, p.2.2 ≤ p.2.1
    TRIO.L6.r21_ST_TS : ST_TS M → r21 M
    TRIO.L6.no_permanent_orphan_ST_TS : ST_TS M → ∀ p ∈ M, p.2.1 = 0 → p.2.2 = 0
    TRIO.L6.r21_graft / r21_Lift1 / r21_take / r21_drop / r21_dropLast / r21_cons

`lean/Dbms3.lean` §1.1（`Dbms3.lean` は `lakefile.toml` の `roots` に無く
`L6Inv` を import できないので、展開の枝だけ写した）:

    TRIO.r21D_ST_D3 : ST_D3 M → ∀ p ∈ M, p.2.2 ≤ p.2.1
    TRIO.no_permanent_orphan_ST_D3

効くのは 2 点だけ:
* 生成元の対角が満たす（BMS `(j, j, min j 1)` は `min j 1 ≤ j`、
  DBMS `(j, j-1, min (j-2) 1)` も同様）。
* `oper` は行 0 と行 1 に**非負**を足し、**行 2 を逐語コピーする**。
  `Pred` / `take` は柱を落とすだけ。

**機構の道具も保つ**（`L6Inv` で証明）: `graft` は行 0 しか動かさない、
`Lift1` は行 1 に非負を足す、`take` / `drop` / `dropLast` は部分列。

### 実測（生成器の制約を使わず、展開閉包を直に作った）

    BM4  対角 v=0..5 から n∈{1,2,3} で 6 段  2479 個  行2>行1 の柱 0 / (x,0,1) 0
    DBMS 対角 v=0..7 から n∈{1,2,3} で 6 段  2923 個  同上 0 / 0

## 2. `natDom` ガードは戻らない — 反例

`natDom M := ∀ m, ¬ domT M m`（`Wset.lean:83`）＝「末尾列が正のレベルの孤児で
**ない**」。2 行の `Aop` 節 2 はこのガード付き、3 行は外してある。

`GRAFTALL-PLAN §4.5` の反証は `M = [(0,0,0),(1,0,1)]` を使う。これは
`(1,0,1)` が `row2 > row1` なので**新しい不変量で消える**。しかし:

### 反例 `M = [(0,1,0), (1,1,1)]`

* `row2 <= row1`: `(0,1,0)` は `0 ≤ 1`、`(1,1,1)` は `1 ≤ 1`。**満たす。**
* `argOK R` for `R = [(1,1,1)]`（深さ 1 > 0）。**満たす。**
* 末尾列 `(1,1,1)` は `srow = 2`。行 2 の親は「行 2 が小さい**行 1 の祖先**」で
  なければならない。候補は列 0 だけだが `nextrel1 M 0 1` は
  `entry M 1 0 = 1 < entry M 1 1 = 1` を要求して**偽**。
  ⟹ `le1 M 0 1` が偽 ⟹ `nextrel2` の候補なし ⟹ **`¬ hasParent M 2 1`**。
* よって `domT M 2`（`lev M 1 = 2*1+1 = 3 = m+1`）が成り立ち、**`natDom M` は偽**。

`Wstar` は `v = 1, z = 0, a = 2*1+0 = 2` でも `M ∈ W 2` を要求する。
ガード付き `Aop` で `M ∈ W 2` を出そうとすると:

| 節 | 要求 | 結果 |
|---|---|---|
| 1 | `|M| ≤ 1` | `|M| = 2` ✗ |
| 2（ガード付き） | `natDom M` | 偽 ✗ |
| 3 | `∃ m < a = 2, domT M m` | `domT` は `m = 2` を強制、`2 < 2` ✗ |

⟹ **`M ∉ W 2`。`Wstar_closed` は壊れたまま。**
（ガード無しなら節 2 が通る: `hasParent` が偽なので `M⟦n⟧ = Pred M = [(0,1,0)]`
で、これは `lev = 2 ≤ 2` の 1 列。）

### 同じ形は 309 個ある

`row2 <= row1` を全列に課し、`v ≤ 2`, `z ≤ 1`, `|R| ≤ 2`、柱は
深さ 1..3 / 行 1 0..3 / 行 2 0..1 の範囲で全数:

    row2<=row1 を課しても natDom ガードが壊れる形: **309 個**
    最小: v=1 z=0 a=2 m=2  M=[(0,1,0),(1,1,1)]

## 3. なぜ効かないか（1 段落）

障害は **`nextrel2` が `le1` を要求すること**である。`le1` は行 1 の**真の増加**の
連鎖なので、「行 2 が正の柱 `(x,w,c)` に行 2 の親がある」ためには、
その柱の行 0 の祖先の中に**行 1 が `w` より真に小さい**ものが要る。
`(x,0,1)`（`w = 0`）はその極端な場合で、行 1 の祖先が原理的に存在し得ない。
`row2 <= row1` が消すのは**この `w = 0` の 1 点だけ**であり、`w >= 1` で
祖先の行 1 が `w` 以上（＝**行 1 のタイ**）という形は残る。上の反例は
`w = 1` で根の行 1 も `1` という、いちばん小さいタイである。

## 4. さらに測った: タイの 2 つの版

    根とのタイ（row2>0 の柱で root.row1 >= 自分の row1）  0 / 2479 個
    局所タイ（row2>0 の柱で ある行 0 祖先の row1 >= 自分の row1）  **1488** / 2479 個

* **根版は実測で不変量**（0 例）。しかも `oper` が保つ理屈もつく
  （`M⟦n⟧` の根はつねに `M[0]` で、コピーは行 1 に非負を足すだけ）。
  **上の反例 `[(0,1,0),(1,1,1)]` は根版を破る**（根の行 1 = 1、行 2 の柱の
  行 1 = 1）。だから根版を課せば反例は消える。
* **しかし根版は `W` の帰納に通せない。** `mem_of_Aclosed_aux` は列の長さで
  帰納し、`M = A ++ P`（`P = p0 :: R'`）と**任意の最上位位置で切って再基底**する。
  そこで要るのは「`p0` の下の行 2 の柱の行 1 が `p0` の行 1 より真に大きい」＝
  **局所版**であり、局所版は**偽**（同じ閉包で 1488 例）。
  例: `[(0,0,0),(1,1,1),(2,2,0),(3,3,1),(4,4,0),(5,4,0),(6,3,1),…]` で
  `(6,3,1)` の行 0 の親は `(5,4,0)`（行 1 = 4 >= 3）。

これは `PROOF-STATUS.md §5.7` / `RESIDUE-PROBLEM.md §4.9` の壁
「**タイ無しは ST_TS 到達可能性そのもの**」と同じ場所である。
`row2 <= row1` は既知の局所不変量（`r1ok` / `z0ok` / `noninc` / `zle1`）の
リストに**無かった新しいもの**だが、§5.7 の反例
`[(0,0,0),(1,1,0),(2,1,0),(2,2,1)]` は `row2 <= row1` を**満たす**ので、
この不変量でも壁は越えない。

## 5. それでも買えたもの

* **永久孤児 `(x,0,1)` が標準形に無いことの証明**。これまで Lean 上で
  一度も使われていなかった構造事実（`PROOF-STATUS §5.5` が `zle1` について
  言っていたのと同じ意味で、こちらはより強い）。
* 壁の言い換えが 1 段鋭くなった:
  **障害は「行 2 が正の柱の行 1 のタイ」であり、`row2 <= row1` はその
  `行 1 = 0` の境界だけを消す。**
* 機構の道具（`graft` / `Lift1` / `take` / `drop` / `dropLast`）が
  `row2 <= row1` を保つことも証明済みなので、**もしどこかで
  `(x,0,1)` を排除するだけで済む箇所があれば、そこには今すぐ使える**。


---

# 課題 L7: `SubstFree` を `W` の帰納で証明しに行った（2026-08-28）

## 0. 結論を先に

* **`Aop` の節 1 は証明できた**（`lean/L7Subst.lean` の `substProp_of_short`）。
* **`SubstFree` は節 2 ＋ 節 3 に割れる**（`substFree_of_clauses`、機械検査ずみ）。
  そこから `TRIO_terminates_of_clauses (h2 : Clause2) (h3 : Clause3) :
  WellFounded stepRel`。
* **止まる場所は `Subst1gReviveSelf` とまったく同じ「復活の場合」**だった。
  `Wtower2.subst1g_of_revive`（`Wtower2.lean:3424`）が既に同じ帰納をやっており、
  そこも同じところで止まっている。
* ⟹ **側条件 6 本を落として得たのは「帰納のたびに側条件を建て直す手間が消える」
  ことだけで、壁は動かない。**

## 1. 何をしたか

`Wself := {M | M ∈ W (lev M 0)}` で `W u` は `Aop` の最小不動点なので、
`Wset.A2'`（「`Aop`-閉な集合は `W u` を含む」）が使える。

    Ysub := {S | SubstProp S}
    SubstProp S := ∀ p C, p < |S| → C ≠ [] → C ∈ Wself →
                     S.take p ++ C ++ S.drop (p+1) ∈ Wself

`A2'` を当てると `Aop` の 3 節がそのまま 3 つの場合になる（`lean/L7Subst.lean`）:

    theorem substFree_of_clauses (h2 : Clause2) (h3 : Clause3) : SubstFree
    theorem TRIO_terminates_of_clauses (h2 : Clause2) (h3 : Clause3) : WellFounded stepRel

節 1 は証明した:

    theorem substProp_of_short {S} (h : S.length ≤ 1) : SubstProp S

（`p < |S|` から `|S| = 1, p = 0` なので `S.take 0 = []`、`S.drop 1 = []`、
差し替えの結果は `C` そのもの。）

## 2. 節 2 の中身 — 既存の帰納と同じ 4 分割

`Wtower2.subst1g_of_revive` の doc（`Wtower2.lean:3405-3423`）がそのまま当てはまる。
`D := S.drop (p+1)` として:

| 場合 | 条件 | 閉じ方 |
|---|---|---|
| **clause 1** | `|S| ≤ 1` | **証明ずみ** |
| **mirror** | `|D| ≥ 2` かつ `D` の末尾列が `D` の中で親を持つ | `Xbar.oper_append_inner` で `S⟦n⟧ = S.take (p+1) ++ D⟦n⟧`、`R⟦n⟧ = (S.take p ++ C) ++ D⟦n⟧`。帰納法の仮定が直に効く |
| **orphan** | `D ≠ []` かつ `R` の末尾列が `R` の中でも孤児 | `R⟦n⟧ = Pred R = S.take p ++ C ++ D.dropLast` ＝ **接頭辞 `S.dropLast` への差し替え**。接頭辞パッケージが払う |
| **revival** | それ以外（`R` では親を持つのに `D` の中では孤児／`D = []`） | **開いたまま** |

### ⚠ 訂正: 接頭辞パッケージは捨てられていない

`RESIDUE-PROBLEM.md §4.5` は「`hpre : ∀ k, k < |S| → SubstProp u (S.take k)` が
呼び出し地点に実在し**捨てられている**」と書くが、実際には **orphan の場合で
使われている**（`Wtower2.lean:3419-3421` の doc に明記）。捨てられているのは
**revival の場合だけ**である。だから「側条件を落とせばパッケージが使える
ようになる」という私の課題 L5 §9 の期待は**外れ**だった。

## 3. 実測（`S, C ∈ Wself` の 103579 例）

`R` を展開したときのバッドルート `j0` の位置で分類:

| | 割合 | `R⟦n⟧ = subst (S⟦n⟧) p C` か |
|---|---|---|
| `R` が展開しない（`Pred`）＝ **orphan** | **54%** | —（`Pred` で閉じる） |
| `j0` が `D` の中 ＝ **mirror** | 7% | **つねに成り立つ**（6944/6944） |
| `j0` が `S.take p` の中 ＝ **revival** | 14% | 98.4% 成り立たない（14302/14487） |
| `j0` が `C` の中 ＝ **revival** | 25% | 98.5% 成り立たない（25926/26310） |

revival では `R` の展開が「`C` を含む区間の `n` 個のコピー」になるので、
`S⟦n⟧` への **1 ブロックの差し替え**にならない（多ブロックになる）。
しかも `d1 > 0`（コピーに行 1 のリフトが乗る）のが `S.take p` 側で **21%**、
`C` 側で **24%**。そこを塔として処理しようとすると

    C ∈ Wself → （ガード付き行 1 リフトした C）∈ Wself

が要り、これが既知の核 `(WL)` `Wtower2.LiftStage` である。
`RESIDUE-PROBLEM.md §4.8` の「どの顔も同じところに落ちる」と一致する。

## 4. 詰まった場所を命題の形で

    SubstFreeRevive :=
      ∀ p S C, S ∈ Wself → p < |S| → C ≠ [] → C ∈ Wself →
        （R := S.take p ++ C ++ S.drop (p+1) の末尾列が R の中で親を持ち、
          自分のブロック（D = [] なら C、そうでなければ D）の中では孤児）→
        R ∈ Wself

これは `Wtower2.Subst1gReviveSelf` から**側条件 6 本を落としただけ**である
（課題 L6 の `lean/L5Subst.lean` の `SubstFree` と `Subst1gReviveSelf` の関係と同じ）。
つまり

    L5 の測定:  Subst1gReviveSelf の側条件 6 本は真理値に効かない
    L7 の帰納:  その 6 本は帰納の**止まる場所**も動かさない

## 5. 判定

**`SubstFree` は「命題としては真に強く、証明の難易度は同じ」だった。**
利点は残る（側条件の建て直しが消える、`D = []` / `D ≠ []` の場合分けの
うち側条件由来のものが消える）が、**新しい数学的入力にはならない**。
`PROOF-STATUS.md §5` の「BM4 展開への新しい数学的入力が要る」は変わらない。

## 6. 課題 L6（`行 2 <= 行 1`）について

これは課題 L6 で回答ずみ。要点だけ:

* **不変量としては正しく、証明した**（`lean/L6Inv.lean` / `lean/Dbms3.lean` §1.1）。
  `graft` / `Lift1` / `take` / `drop` / `dropLast` が保つことも証明ずみ。
* **しかし `natDom` ガードは戻らない。** `row2 ≤ row1` を課しても
  `Wstar_closed` を壊す形が **309 個**残る（最小 `M = [(0,1,0),(1,1,1)]`）。
* 障害は `(x,0,1)` ではなく**行 1 のタイ**。`row2 ≤ row1` が消すのは
  `行 1 = 0` の境界だけ。


---

# 課題 L7 の続き: 詰まりは「行 1 のタイ」に集中しない（2026-08-28）

課題 L7 の本体（`A2'` の分解・節 1 の証明・`TRIO_terminates_of_clauses`）は
1 つ前の commit `371ca7b` で済んでいる。ここはその続きで、
**「詰まりが行 1 のタイに集中するか」**を測った結果。

## 1. 答え: **集中しない**

`R` の末尾列が崩壊する行 `i1 = srow(R, |R|-1)` で revival の場合を割ると
（`S, C ∈ Wself` の乱択。`tie` = 自分のブロック `B` の中に行 1 の親が無い）:

| | `SubstFree` の revival（(iii) 無し） | **Lean の残核**（(iii) ＋ レベル条件） |
|---|---|---|
| `i1 = 0` | 7793 (20%) | 3834 (**21%**) |
| `i1 = 1` | 21177 (55%) | 10367 (**58%**) |
| `i1 = 2` / tie | 8531 (22%) | 3270 (18%) |
| `i1 = 2` / no-tie | 431 (1%) | 237 (1%) |
| 合計 | 37932 | 17708 |

* **残核の 79% は `i1 <= 1`**。行 2 もタイも関係しない。
* **`i1 = 2` の中では タイが 93%**（3270/3507）。ここは課題 L6 の診断どおり。

⟹ **タイは「`i1 = 2` の中での支配的な形」であって、残核全体の支配的な形ではない。**

## 2. ⟹ ところが `i1 <= 1` は「新しい数学」を要らない

`oper`（`Trio.lean:98`）は `d1 = if 1 < i1 then … else 0` なので、
**`i1 <= 1` なら行 1 のリフトは 0**。さらにバッドルート `j0` は末尾列の
行 0 の親で「間に凹み無し」なので、コピー区間 `[j0, x)` の柱は**全部 `j0` の
行 0 の子孫**であり、`k*d0` が全部に乗る。したがって

> **`i1 <= 1` のとき、`R⟦n⟧` の中に現れる `C` のコピーは
> 「`C` を行 0 に `k*d0` だけずらしたもの」ちょうどである。**

実測（コピー区間が `C` を丸ごと含む revival、`n = 1,2,3` の各回を 1 件）:

    i1 <= 1   コピーは C の行 0 ずらし   57066 / 57066   （**100%、例外なし**）
    i1 = 2    コピーは C の行 0 ずらし    6094 / 14610
    i1 = 2    ちがう（行 1 が持ち上がる）  8516 / 14610   （58%）

行 0 のずらしは `Wset.W_shift` / `Wset.W_shiftl0` で `W u` に戻る。しかも
`lev` は行 1 と行 2 しか見ないので `Wself`（＝根のレベルの段）も動かない。

⟹ **帰納法の不変量を「1 ブロックの差し替え」ではなく「多ブロックの差し替え」に
取れば、`i1 <= 1` の revival は帰納法の仮定だけで閉じる。**
（`R⟦n⟧` は `S⟦n⟧` への、`C` の行 0 ずらしを `n` 箇所に入れた差し替えになる。）

## 3. ⟹ 本当に新しいのは `i1 = 2`（残核の 20%）だけ

`i1 = 2` ではコピーが**行 1 で持ち上がる**（実測 58%）。そこで要るのは

    C ∈ Wself → （ガード付き行 1 リフトした C）∈ Wself

で、これは既知の核 `(WL)` `Wtower2.LiftStage` そのもの。

**これで `Subst*` の残核と `TowerGraft2` の話が初めて噛み合った。**
`Wset.tower1_mem`（行 1 の塔）は証明ずみで `TowerGraft2`（行 2 の塔）だけが核、
という構図（課題 L4 §4.3）に対して、`Subst1gReviveSelf` は一見「行 2 に限らない」
ように見えていた。実際は **`i1 <= 1` の 79% は多ブロック化で落ちる**ので、
両者は同じ「行 2 の崩壊が行 1 をリフトする」1 点に帰着する。

## 4. 提案する狭い残核

    SubstFreeRevive2 :=
      SubstFree の revival の場合を `srow (R, |R|-1) = 2` に制限したもの

⚠ **これを `X → SubstFree → WellFounded stepRel` の鎖として機械検査するには、
多ブロック版の帰納（mirror ＋ orphan ＋ 節 1 ＋ `i1 <= 1` の revival）を
書かないといけない。`Wtower2.subst1g_of_revive` を多ブロックに書き換える作業で、
300〜400 行。今回はやっていない。**

## 5. 判定（正直なところ）

* `SubstFree` / `SubstFreeRevive` は `Subst1gReviveSelf` の**強め**であって、
  仮定が減るぶん**証明は難しくなりこそすれ易しくならない**（課題 L7 本体）。
  **`Subst1gReviveSelf` がいまも最弱の残核である。**
* 今回得た狭め方（`i1 = 2` への制限）は**新しい数学ではなく証明工学**で、
  しかも行き着く先は既知の `(WL)`。
* 陽性対照について: §2 の主張は統計ではなく `oper` の定義から出る恒等式
  （`i1 <= 1 ⟹ d1 = 0`）なので、対照実験ではなく **100% の実測（57066/57066）**で
  裏を取ってある。反例が 1 つでもあれば主張は即死する形の測定である。


---

# 課題 L8: 多ブロックへの一般化は **循環する**（2026-08-28）

## (3) 判定: **循環する。止めるべき。**（最優先の答え）

`Wtower2.lean` に**残核 → `LiftStage`** の鎖が既にある:

    substClosedG_of_subst1g      : Subst1g → SubstClosedG
    shiftTowerClosedS_of_substG  : SubstClosedG → ShiftTowerClosedS        (:3615)
    liftStageParented_of_tower   : ShiftTowerClosedS → LiftStageParented   (:1800)
    liftStage_of_parented        : LiftStageParented → LiftStage           (:560)

一方、課題 L7 の分析で、**多ブロックの帰納で残るのは `i1 = 2` の場合だけ**で、
そこで要るのはちょうど

    C ∈ Wself → Lift1 C d ∈ Wself          （= `Wtower2.LiftStage` の `Wself` 版）
    LiftStage := ∀ m d X, X ∈ W m → Lift1 X d ∈ W (m + 2*d)

つまり私が組もうとしていたのは **`LiftStage` → 残核**。これを足すと

    残核 ⟺ LiftStage

の**輪が閉じるだけ**である。`RESIDUE-PROBLEM.md §5` が
「**多ブロック版に一般化して帰納する**」を「`TowerExp` 経由で自分に戻る」として
却下しているのは、まさにこれ。

### 側条件が落ちた今も循環するか → **する**

循環しているのは**命題の仮定**ではなく**導出グラフ**である。
`SubstClosedG → ShiftTowerClosedS → LiftStageParented → LiftStage` の 3 本は
側条件とは無関係に成り立っているので、側条件 6 本を落としても輪は残る。

さらに `SubstMulti` と `SubstFree` は**命題としては同値**である
（多 ⟸ 単は位置を降順にして右から 1 つずつ当てるだけ。単 = `k = 1`）。
だから**目標を多ブロックに取り替えても命題は 1 ミリも弱くならない**。
強くなるのは「帰納法の**不変量**として使うとき」だけで、そこが `LiftStage` に落ちる。

### `LiftStage` の先も既に地図がある

* `Wtower2.liftStage_of_wconvex' : WConvex → LiftStage`
* `WConvex` の素直な `oper` 帰納は**反証済み**（`tools/probe_wconvex_step.py`、
  単調形 9.4% / 存在形 5.9% 失敗）
* `Wtower2.lean:477` 付近の doc:
  > `le1` 錐 ⊆ `amin` 錐 は**無条件**（`coneV_of_le1`、計測 64808 例 0 例外）。
  > したがって逆包含（`TieFree`）が成り立てば (WL) はその場で無料になる。
* `TieFree`（**行 1 のタイが無い**）は `PROOF-STATUS.md §5.7` によれば
  **ST_TS 到達可能性そのもの**。

⟹ **輪の先は既知の壁**。顔を変える作業に価値はない（課題 L4 §3 の私自身の判断）。

## (1) `SubstMulti` の測定（陽性対照つき）

    SubstMulti（2〜3 ブロック同時、深さもレベルも自由）
      判定 150196   **違反 0**   未判定 23597
      陽性対照（段を 1 つ下げる）  **違反 160882 / 161093**

⟹ 命題としては真（`SubstFree` と同値なので当然）。プローブは盲目ではない。

### Lean の鎖（`lean/L8Multi.lean`、`leanman check` exit 0 / sorry 0）

    TRIO.L8.substFree_of_multi    : SubstMulti → SubstFree
    TRIO.L8.TRIO_terminates_of_multi : SubstMulti → WellFounded stepRel

## (2) リフトの切り分け

課題 L7 続の測定（`oper` の定義から出る恒等式を実測で裏取りしたもの）:

| | コピーが `C` の**行 0 ずらし**ちょうどか |
|---|---|
| `i1 <= 1`（行 1 のリフト `d1 = 0`） | **57066 / 57066（100%、例外なし）** |
| `i1 = 2` | 6094 / 14610（残り 8516 = 58% は行 1 が持ち上がる） |

行 0 のずらしは `Wset.W_shift` / `W_shiftl0` で `W u` に戻り、`lev` は行 0 を
見ないので `Wself` も動かない。⟹ **`i1 <= 1`（残核の 79%）は多ブロックの
帰納法の仮定だけで閉じる。**

リフトそのものの測定:

    C ∈ Wself → Lift1 C d ∈ Wself
      判定 138708   **違反 0**   未判定 11
      陽性対照（段を 1 つ下げる）  **違反 138719 / 138719**

⟹ 狙いの鎖 **`SubstMulti (d1 = 0) ＋ LiftStage ⟹ SubstFree ⟹ 停止性`** は
**形としては正しく、真偽も測れている**。しかしそれは (3) の輪そのものである。

## まとめ: 残っている問題の 1 文の言い換え

課題 L4〜L8 で得た地図を 1 文にすると:

> **3 行バシク（`z<2`）の停止性に残っているのは、「行 1 のタイ」ただ 1 点である。**
> BM4 が実際に施すリフトのマスクは `le1`（悪い根の**添字**の子孫錐）、
> 証明済みのリフト法則のマスクは `amin`（行 1 の**値**の上方集合）。
> 前者 ⊆ 後者は無条件。**逆包含（タイが無いこと）だけが未証明**で、
> それは ST_TS 到達可能性と同値である。

支えている事実（このセッションで足したもの）:

* **課題 L6**: `行 2 <= 行 1` は BMS / DBMS 両方の標準形の不変量（**証明ずみ**）。
  タイのうち `行 1 = 0` の境界（永久孤児 `(x,0,1)`）だけを消す。残りは消さない。
* **課題 L7**: 残核の中でタイが効くのは `i1 = 2` の部分（20%）だけ。
  残り 79%（`i1 <= 1`）は多ブロック化という**証明工学**で落ちる。
* **課題 L8**: その多ブロック化は `LiftStage` に落ちて輪が閉じる。

## 推奨

* **(a) 300〜400 行を書いて残核を `i1 = 2` に狭める** — 循環すると分かったので
  **やらない**。得られるのは「残核 ⟺ LiftStage」の機械検査だけで、
  どちらも既に地図の上にある。
* **(b) `(WL)` / `LiftStage` を直接攻める** — 実質は `TieFree`（タイ無し）を
  攻めることで、それは ST_TS 到達可能性。`W` の枠組みは ST_TS を仮定しない
  設計なので、**枠組みの外から入力が要る**。
* **(c) `PROOF-STATUS §5.5` の `zle1` 改修**（30k 行）— 課題 L6 で
  `行 2 <= 行 1` という**より強い**不変量が手に入ったので、`zle1` を通すより
  こちらを通すほうが買えるものは多い（`(x,0,1)` が消える）。ただし
  課題 L6 の測定どおり、それでもタイは消えない。

⟹ **量詞・側条件・帰納の形をいじる方向は、これで打ち止め**と判断する。
`PROOF-STATUS §5` の「BM4 展開への新しい数学的入力が要る」は、
このセッションの 5 課題（L4〜L8）を経ても変わらなかった。


---

# 課題 L9: 測ってから書く、で 300 行が助かった（2026-08-28）

## 0. 結論

* **(1) `(WL)` `LiftStage` は真**（231244 例 判定 / **違反 0**、陽性対照つき）。
* **(2) しかし多ブロック帰納は書かなかった。書く前の測定で前提が崩れたから。**
  課題 L7/L8 の「`i1 <= 1` の 79% は多ブロック化で落ちる」は**早とちり**だった。
  実際に落ちるのは **その 61%** だけで、39% は帰納法の仮定が届かない。
* 原因は 1 行: **差し替えはバッドルートを動かす。**

## 1. `(WL)` `Wtower2.LiftStage` の測定

    LiftStage := ∀ m d X, X ∈ W m → Lift1 X d ∈ W (m + 2*d)

| | 判定 | 違反 | 未判定 |
|---|---|---|---|
| 段つきの本来の形（`m` を `lev X 0 .. +3` で振る） | **231244** | **0** | 21 |
| `Wself` の形（`m = lev X 0`、課題 L8 で測ったもの） | 138708 | 0 | 11 |

**陽性対照**（結論の段を 1 つ下げた偽の主張）:

| | 違反 |
|---|---|
| 段つきの形 | **57862 / 231257** |
| `Wself` の形（段がぴったりなので必ず落ちるはず） | **138719 / 138719（100%）** |

段つきの形で対照が 25% にとどまるのは正しい挙動である。`lev X 0 < m` と
余裕があるときは段を 1 下げても真のままだからで、余裕が無い（`m = lev X 0`）
ときだけ必ず落ちる。それが `Wself` の形の 100% である。

⟹ **行き先は真。** 証明工学を投じてもよい命題だった。

## 2. ところが前提が崩れた（**課題 L7/L8 の訂正**）

課題 L7/L8 で私はこう書いた:

> `i1 <= 1` なら `R⟦n⟧` の中の `C` のコピーは「`C` を行 0 にずらしたもの」ちょうど
> （57066/57066、例外なし）。だから多ブロック化すれば帰納法の仮定だけで閉じる。

**前半は正しいが、後半は出ない。** 「ブロックが行 0 ずらしである」ことと
「`R⟦n⟧` が `S⟦n⟧` への差し替えになっている」ことは別である。後者を直に測った:

`i1 <= 1` の revival、`n = 1,2,3` の各回を 1 件、**69981 件**:

| | 件数 | |
|---|---|---|
| `R⟦n⟧` が `S⟦n⟧` への多ブロック差し替えになる（＝ 帰納法の仮定が届く） | 43254 | **61%** |
| `S` が展開しない（`R` はする） | 12132 | **17%** |
| バッドルートが `C` の中に移った | 7447 | **10%** |
| バッドルートの位置が違う（その他） | 766 | 1% |
| その他 | 6382 | 9% |

判定は「`Rn` を `Sn` に貪欲に整列させ、食い違ったところで
`Rn[j..j+|C|)` が `C` のずらしで、かつ `Sn[i]` が `S[p]` の同じずらしになって
いるか」を見る（成功したら `Rn` はちょうど「`S[p]` の各コピーを `C` のずらしに
差し替えたもの」）。

### 原因（1 行）

> **差し替えはバッドルートを動かす。**

挿入した `C` の柱が末尾列の新しい行 0 の親になってしまうと、`R` のコピー区間は
`C` の**内側**から始まり、`S⟦n⟧` にはそれに対応するものが無い。実例:

    S = [(0,4,0), (3,0,0)]        p = 0   C = [(0,2,1), (1,1,1), (2,0,0)]
    R = [(0,2,1), (1,1,1), (2,0,0), (3,0,0)]
    S のバッドルート = 0（= p 自身）    R のバッドルート = 2（= C の中）

同じ理由で「`S` は展開しない（末尾列が孤児）のに `R` は展開する」も起きる
（17%）。差し替えが末尾列に**親を作ってしまう**場合である。これは
`probe_subst1g_adv.py` が `residue/insertion-creates-parent` と呼んでいる形と同じ。

## 3. 数字の訂正

| | 課題 L7/L8 で書いた値 | **正しい値** |
|---|---|---|
| 残核のうち多ブロック化で落ちる割合 | 79% | **79% x 61% ≈ 48%** |
| 残るもの | `i1 = 2` だけ（21%）＝ `(WL)` | `i1 = 2`（21%）**＋ `i1 <= 1` の 39%** |

⟹ **多ブロック化しても残核は `(WL)` 1 本にならない。** 300〜400 行を書いても
「`(WL)` ＋ もう 1 本」にしかならず、そのもう 1 本は「差し替えがバッドルートを
動かす場合」＝ 残核そのものである。

## 4. 何が残ったか（1 行で）

> **差し替えが末尾列のバッドルートを動かす（親を作る／親を `C` の中に移す）場合。**

これは `probe_subst1g_adv.py` の残差 3 分類のうち
`insertion-creates-parent` と `inside-copied-region` に当たる
（`context-revives` は 3 つ目）。つまり**残核の 3 つの顔のうち 2 つ**が
そのまま残る。1 つに減らせていない。

## 5. 判定と推奨

* **300〜400 行は書かなかった。** 書く前の測定（(2)）で前提が崩れたため。
  **測ってから書く、という規約がそのまま効いた例**である。
  「分量が読めている作業」だと思っていたものが、実は前提を測っていないだけだった。
* `(WL)` は真だと確かめたので、**`(WL)` を直接攻める**（推奨 (b)）は
  行き先が保証された道である。ただし課題 L8 のとおり、その先は
  `WConvex`（素直な `oper` 帰納は反証済み）→ `TieFree`（＝ ST_TS 到達可能性）。
* いま言えることの総括は課題 L8 の 1 文のまま:

  > 3 行バシク（`z<2`）の停止性に残っているのは「**行 1 のタイ**」ただ 1 点。
  > `le1`（添字の錐）⊆ `amin`（値の上方集合）は無条件で、逆包含だけが未証明、
  > それは ST_TS 到達可能性と同値。


---

# 課題 L10: `TieFree` は構文的不変量にならない（2026-08-28）

## 0. 結論

* **外れました。** `TieFree` は `oper` でも `cons` でも破れる。**1 例で終わり。**
* しかも **「標準形ではタイが起きない」という観察は `TieFree` については空虚**
  だった。標準形の根は 3 行とも 0 なので `TieFree` の前提が常に落ちる（**証明した**）。

## 1. まず `TieFree` の正体（`Wtower2.lean:59`）

    coneV A v j := ∀ y, y は j の行 0 祖先（自身含む）→ v < entry A 1 y
    TieFree X   := ∀ j, coneV X (entry X 1 0 - 1) j → le1 X 0 j

**`Wtower2.liftStage_of_tieFree` は既に証明ずみ**（`1 ≤ entry X 1 0` ＋ `TieFree X`
⟹ `Lift1 X d ∈ W (m + 2d)`）。だから `TieFree` を構文的不変量にできれば
`(WL)` はその場で無料になる。的としては完全に正しい。

⚠ ただしチームリードが提案した形

    ∀ j, entry M 2 j >= 1 → ∃ i < j, entry M 1 i < entry M 1 j ∧ entry M 2 i < entry M 2 j

は `TieFree` ではない。標準形の根は `(0,0,0)` で、課題 L6 の `r21`（行 2 ≤ 行 1）
から `row2 j ≥ 1 → row1 j ≥ 1` なので、**`i = 0` を取れば必ず成り立つ**。
つまりこの述語は `r21_ST_TS` の**自明な系**で、`(WL)` には届かない。

## 2. 測定（陽性対照つき）

    陽性対照   乱択列 60000 個のうち TieFree が偽 18904 個（**31%**）
               ⟹ この述語は簡単に偽になる。測定は盲目でない
    対角       v = 0..11 の 12 個すべて TieFree

| 操作 | 保つ | **破れる** |
|---|---|---|
| `take` | 69585 | **0** |
| `dropLast` | 69585 | **0** |
| **`oper`** | 359108 | **34330（8.7%）** |
| `drop`（再基底つき） | 59273 | 10312（15%） |
| **`cons`**（`(0,v,z) :: R`） | 34772 | **34813（50%）** |

### `oper` の最小の反例

    M    = [(0,1,1), (2,3,0)]      TieFree
    M⟦2⟧ = [(0,1,1), (2,1,1)]      **破れる**

`M` の末尾列 `(2,3,0)` は `srow = 1`、行 1 の親は根（`1 < 3`）。だから
`j0 = 0, d0 = 2, d1 = 0` で、**コピーされる区間は根そのもの**。`d1 = 0` なので
コピー 1 は根の行 1 をそのまま持ち、**根とのタイが生まれる**
（`nextrel1 (M⟦2⟧) 0 1` が `1 < 1` を要求して偽 ⟹ `le1` が切れる）。
一方 `coneV (M⟦2⟧) 0 1` は成り立つ（祖先の行 1 は 1, 1 で両方 > 0）。

これは `PROOF-STATUS.md §5.7` の
「**添字**で決まる錐はコピーで壊れる（コピー `k` は自分自身の錐を持つ）」
の最小形そのものである。

### `cons` の反例（`Wstar` の操作そのもの）

    M = [(0,2,1), (4,1,0)]                        TieFree
    (0,2,0) :: 行 0 を +1 した M
      = [(0,2,0), (1,2,1), (5,1,0)]               **破れる**

新しい根の行 1 が `2`、もとの根も行 1 が `2` ⟹ **タイ**。
`Wstar := {R | argOK R → ∀ v z a, … → (0,v,z) :: R ∈ W a}` は **`v` を全部走る**
ので、`v` が `R` の行 1 の値とぶつかった瞬間にタイができる。

⟹ **`W` の機構を `TieFree` に制限することはできない。**
`Aop` の節 2 が `M⟦n⟧ ∈ X` を要求する以上 `oper` の保存が要り、
`Wstar` が `(0,v,z) :: R` を要求する以上 `cons` の保存が要る。どちらも破れる。

## 3. 「標準形ではタイが起きない」は `TieFree` については**空虚**

`lean/L10Tie.lean` で証明した（`leanman check` exit 0 / sorry 0）:

    TRIO.L10.entry_root_ST_TS : ST_TS M → ∀ i, entry M i 0 = 0
      （標準形の根は 3 行とも 0。`oper_take_prefix`「コピー 0 はずれない」から）
    TRIO.L10.coneV_root_false_ST_TS : ST_TS M → ¬ coneV M (entry M 1 0 - 1) 0

根の行 1 が 0 なので `entry M 1 0 - 1 = 0`（ℕ の切り捨て）、したがって
`coneV M 0 j` は「`j` の行 0 祖先が全部行 1 で**正**」を要求するが、根はそれを
満たさない。実測でも BM4 の展開閉包 2473 個は**全部 `entry M 1 0 = 0`**、
`TieFree` の破れ 0（＝空虚に真）だった。

⟹ **全体の標準形を測っても `TieFree` については何も言えない。**
`TieFree` が中身を持つのは根の行 1 が 1 以上のとき、つまり `Wstar` の
`(0,v,z) :: R`（`v ≥ 1`）や**悪い部分の部分ブロック**に対してだけである。
`Wtower2.liftStage_of_tieFree` が `1 ≤ entry X 1 0` を要求しているのも、
`Wtower2.lean:98` 付近の doc が「実 ST_TS では行 2 崩壊の**悪い部分**の
53634/53642 が窓を満たす」と**悪い部分**について書いているのも、このため。

## 4. 何が残ったか

課題 L6 と同じ構図だった:

| | 課題 L6 | 課題 L10 |
|---|---|---|
| 立てた述語 | `行 2 <= 行 1` | `TieFree` |
| 不変量か | **○（証明した）** | **✗（`oper` も `cons` も破る）** |
| 的に当たるか | ✗（`natDom` は戻らない） | ○（当たれば `(WL)` が無料） |

**「不変量になるもの」と「的に当たるもの」が食い違っている**、というのが
このセッションで繰り返し出た形である。`(WL)` に届く述語（`TieFree`）は
`W` の機構が要求する操作（`oper` / `cons`）で壊れ、機構が保つ述語
（`r21`）は `(WL)` に届かない。

そして `TieFree` が壊れる理由は 1 行で言える:

> **`Wstar` は根の行 1 `v` を全部走り、`oper` はコピーに根の行 1 をそのまま渡す。**
> どちらも「根と同じ行 1 の値を持つ列」を作る操作である。

これは `PROOF-STATUS.md §5.7` の「タイ無しは **ST_TS 到達可能性そのもの**」を、
`W` の機構の側から見た形にすぎない。⟹ 判定は変わらない。


---

# 課題 L11: `TieFree` は**弱められない**（証明した）。塔に絞っても閉じている（2026-08-28）

## 0. 結論を先に

* **(1) `liftStage_of_tieFree` は `TieFree` を `j` の全体で使っている。**
  絞れる `j` の部分集合は無い。証明は 2 行で、`Lift1 X d = mlift X (v0-1) d` を
  `List.map_congr_left` で**列ごと**に示すだけ。`TieFree` はその `if_neg` の枝、
  すなわち **`le1 X 0 j` が偽の `j` すべて**で使う（対偶なのでそれが全内容）。
* **(2) しかし弱められる方向が 1 つあった: `j` ではなく `X` の量詞。**
  `(WL)` が消費されるのは `towerGraft2_of_liftStage` の**ただ 1 行**だけで、
  相手は**塔の族**しかない。Lean で切り出した（`Wtower2.LiftStageTower`、exit 0）。
  実測: **塔の 1 段は `TieFree` を完全に保つ**（30537 サイト x 5〜6 段、
  両向き 0 違反、陽性対照つき）。残るのは**土台だけ**。
* **(3) ところが土台は 29% で偽。しかも `TieFree` は「証明ずみのリフト言語」の
  中では必要条件でもある**（`L11Fam.sliftMatch_iff_tieFree`、exit 0 / sorry 0）。
  ⟹ **この道は完全に閉じた。**

## 1. (1) `TieFree` はどの `j` で使われているか

`Wtower2.liftStage_of_tieFree` の証明は 2 行:

    rw [Lift1_eq_mlift_of_tieFree hv h d]     -- ここだけで TieFree を使う
    exact mlift_mem_W X hX

`Lift1_eq_mlift_of_tieFree` は

    hif : (if le1 X 0 j then d else 0) = (if coneV X (v0-1) j then d else 0)

を `List.map_congr_left` で `j ∈ List.range X.length` の**全体**について示す。
`if_pos` の枝は `coneV_of_le1`（無条件）で片づき、**`TieFree` は `if_neg` の枝
だけ**で使われる。つまり「`le1 X 0 j` が偽である `j`」——対偶なので `TieFree` の
全内容そのもの。**部分集合には絞れない**（絞れば 2 つの列が実際に食い違う）。

## 2. (3) `TieFree` は必要条件でもある — **証明した**

`lean/L11Fam.lean`（`leanman check` exit 0 / sorry 0 / `#print axioms` は
`propext, Classical.choice, Quot.sound` のみ）:

    SliftMatch X d := ∃ φ, Stair φ ∧ slift X φ = Lift1 X d

`Cgraft.slift` は「証明ずみのリフト法則 `Wslift.slift_mem_W_tight` が扱える
リフト**すべて**」で、`mlift` はその特別な場合である。

    TRIO.L11.sliftMatch_iff_tieFree :
      0 < X.length → 1 ≤ d → 1 ≤ entry X 1 0 → (SliftMatch X d ↔ TieFree X)

証明の骨（必要の向き）: 根は自分の行 1 錐に入る（`le1_refl`）ので階段は
`amin 0 = entry X 1 0` でちょうど `d` 持ち上げねばならない。`Stair.step` は
`φ m - m` の単調性を課すので、`amin` が根以上の列（＝ `coneV` の中）でも
持ち上げ量は `d ≥ 1` 以上になる。`Lift1` はそこで `0` しか足さないから、
その列は `le1` 錐に入っていなければならない。∎

⟹ **`L10Tie.maskMatch_iff_tieFree`（閾値 `v` を自由にしても同じ）の一般化。**
閾値どころか**階段そのものを自由にしても** `TieFree` より弱い十分条件は
この言語の中に**存在しない**。「弱い述語を探して `oper`/`cons` の保存率を測る」
という作戦は、**測るまでもなく**この定理で潰れる。

## 3. (2) 弱められる唯一の方向: `X` の量詞 — 塔の族だけ

`Wtower2.towerGraft2_of_liftStage` を読むと `hWL` が現れるのは**1 行だけ**:

    have hmem : Lift1 (M⟦j⟧) d1 ∈ W (2*v+z+2*d1) := hWL _ _ _ ih

`M = (0,v,z) :: R`、`d1 = row1(R[-1]) - v`、`M⟦0⟧ = []`、
`M⟦j+1⟧ = (0,v,z) :: graft R (Lift1 (M⟦j⟧) d1)`（`hstep`）。

Lean 側に切り出した（`Wtower2.LiftStageTower` / `towerGraft2_of_liftStageTower`、
旧い `towerGraft2_of_liftStage` はその系として残してある。`Wtower2.lean`
`Final.lean` とも exit 0）:

    LiftStageTower := ∀ v z m R, argOK R → R ≠ [] → z ≤ 1 → domT R m →
      srow R (R.length-1) = 2 → hasParent ((0,v,z)::R) … R.length →
      ∀ j, ((0,v,z)::R)⟦j⟧ ∈ W (2v+z) →
        Lift1 (((0,v,z)::R)⟦j⟧) d1 ∈ W (2v+z+2*d1)

**これは課題 L10 の測定と量詞が違う。** L10 は `cons` を `∀ v` で盲目に走らせて
50% 破れたが、塔では `v` は塔のデータで固定され、`cons` の相手も
`graft R (Lift1 · d1)` に固定されている。

### 実測（`tools/probe_tiefree_tower.py`）

| | maxlen=3 r0=5 r1=5 J=5 | maxlen=2 r0=6 r1=7 J=6 |
|---|---|---|
| tower-2 サイト（`v ≥ 1`） | 26412 | 4125 |
| 土台 `TieFree ((0,v,z)::R.dropLast)` | 18772 / **破れ 7640（29%）** | 3675 / **破れ 450（11%）** |
| **土台 OK → 全段 OK** | 18772 / **後で破れる 0** | 3675 / **後で破れる 0** |
| **土台 NG → 全段 NG** | 7640 / **途中で直る 0** | 450 / **途中で直る 0** |
| 破れのうち `X_1 ∈ W(2v+z)` | **7640（全部）** | **450（全部）** |
| 窓（`liftStage_of_window`） | 8872 / 破れ 17540 | 2625 / 破れ 1500 |

**陽性対照**（測定は盲目でない）:

| 対照 | 破れ |
|---|---|
| リフト量を `d1 - 1` にする | **9428 / 18772（50%）が「後から破れる」** |
| リフト量を `d1 + 1` にする | 0（多く持ち上げるのは無害。正しい挙動） |
| tower-2 の絞りを外した `(v,z,R)` | **160040 / 498708（32%）** |

⟹ **塔の 1 段は `TieFree` を完全に保つ**（保つ方向も破る方向も 0 違反）。
`d1` をちょうど 1 減らすと壊れるので、`d1` の値そのものが効いている。

### ところが土台が落ちる

土台 `X_1 = (0,v,z) :: R.dropLast` の破れは 29%。しかも

* `X_1 ∈ W (2v+z)` を課しても**1 例も消えない**（7640 / 7640 が W に入る）。
  最小反例 `v=1, z=0, R=[(1,1,0),(1,2,1)]` ⟹ `X_1 = [(0,1,0),(1,1,0)]`。
* タイの正体は **7080/7640 が「`R` の中に行 1 がちょうど `v` の列がある」**。

`TowerGraft2` は `∀ v z` を走るので、**`v` は `R` の行 1 の値を必ず走る**。
これは課題 L10 の `cons` の反例と**同じ理由**であり、塔に絞っても消えない。
窓（`liftStage_of_window`）は `TieFree` より**強い**ので当然覆えない。

## 4. 判定: **打ち止め**

停止性トラックの `(WL)` を「証明ずみのリフト言語」で出す道は、

* 量詞 `j` を絞る → **絞れない**（証明が全称で使う）
* 閾値 `v` を自由にする → **同値**（`L10Tie.maskMatch_iff_tieFree`）
* 階段 `Stair φ` まで自由にする → **同値**（`L11Fam.sliftMatch_iff_tieFree`、新）
* 量詞 `X` を塔の族に絞る → **絞れた。段は保つ。しかし土台が 29% で偽**（新）

の 4 方向すべてで閉じた。課題 L5〜L10 の「量詞・側条件・帰納の形・不変量」と
あわせて **`(WL)` に残る道は `Row1Mono` / `WConvex`（どちらも実測 0 違反の
未証明予想）だけ**である。`PROOF-STATUS §5` の「BM4 展開への新しい数学的入力が
要る」は変わらない。

### 買えたもの（この課題で `lean/` に残るもの）

    lean/L11Fam.lean            SliftMatch と sliftMatch_iff_tieFree（新定理）
    lean/Wtower2.lean           LiftStageTower / towerGraft2_of_liftStageTower
                                （開いた核を塔の族まで狭めた。旧形は系として存置）
    tools/probe_tiefree_tower.py 塔の族の TieFree 測定（陽性対照 4 本つき）

**`sorry` 0 / `axiom` 宣言 0 は維持**（`lean/` 自前 65221 行）。


---

# 課題 L11 (DBMS トラック): `BlkInv` の残りを**測った**（2026-08-28）

停止性トラックを打ち止めにしたので DBMS トラックに移った。担当は
`ImgBlockT3`（＝ `Conv3.BlkInv`）の残り、すなわち**縮約の枝**である。

## 0. 結論を先に

* **書く前に測った。10 本の債務は**全部真**（338 発火・違反 0・陽性対照つき）。**
* **doc の「`convResid` については `BlkOK` の第 2 項はそのままでは偽」は、
  実際に現れる `rd` については観測されない**（訂正した）。
* 連結のときに要る `BlkOK_app'`（開始深さが下がってもよい版）を**証明した**
  （`Dbms3.lean`, exit 0 / sorry 0）。
* 残りは書くだけ。**見積もり 250〜350 行**（内訳は §3）。

## 1. 縮約の枝が要求するもの（コードから読んだ）

    (cols ++ rA.1 ++ rU.1 ++ rR.1 ++ rB.1, { rB.2 with nc := rB.2.nc + 1 })

を `((((cols ++ rA) ++ rU) ++ rR) ++ rB)` と括ると、必要なのは

| # | 債務 | 出どころ |
|---|---|---|
| a | `BlkOK d st (cols, st1)` | `cols_blk`（**証明ずみ**） |
| b | `BlkOK (dd2+1) st1 (rA…)`、`d ≤ dd2+1` | 帰納法の仮定 ＋ `depths_le`（**済**） |
| c | `BlkOK (d+1) rA.2 (rU…)`、`d ≤ d+1` | 帰納法の仮定（**済**） |
| d | `d ≤ rd` と `rd ≤ |rU.2.ST|` | **`contr_rd_ok`（穴 1）** |
| e | `BlkOK rd rU.2 (rR…)` の 5 節 | **`convResid_blk`（穴 2）** |
| f | `d ≤ |rR.2.ST|` | `rB` の帰納法の仮定の入口 |

⚠ `convResid` の中では次の木の開始深さが `rd - (c.1 - tail[0].1)` と**下がる**
ので、`BlkOK_app` の仮定 `d ≤ d'` が**使えない**。`d ≤ d'` は結論の第 2 項
`d ≤ |st'.ST|` を出すためだけに使われているので、それを直に仮定する
**`BlkOK_app'`** を立てて証明した（`Dbms3.lean` §11.5, exit 0）。これで
穴 2 の連結の側は片づく。

## 2. 測定（`lean/l11_blkmeas.py`）

`Dbms3.lean` の本文をそのまま貼った使い捨ての Lean file を作り、縮約の枝に
計測を埋め込む。**埋め込み先は `St.nc`**（縮約の発火回数）で、`nc` は像に一切
効かない（`grep '\.nc'` で読むところが無い）ので安全。10 本の条件を 100 進の
桁に詰めて `#eval` で合計する。

| 桁 | 条件 | <=6 列 全数 | 7 列 縮約発火 |
|---|---|---|---|
| 0 | 発火回数 | **44** | **294** |
| 1 | `d ≤ rd` | 0 | 0 |
| 2 | `rd ≤ |rU.2.ST|` | 0 | 0 |
| 3 | `steps1 rR.1` | 0 | 0 |
| 4 | **`rd ≤ |rR.2.ST|`**（偽と疑われていた） | **0** | **0** |
| 5 | `rR.1 = [] → |rR.2.ST| = |rU.2.ST|` | 0 | 0 |
| 6 | `rR.1 ≠ [] → head.1 ≤ |rU.2.ST|` | 0 | 0 |
| 7 | `rR.1 ≠ [] → last.1 + 1 = |rR.2.ST|` | 0 | 0 |
| 8 | `d ≤ |rR.2.ST|` | 0 | 0 |
| 9 | `dmap` が狭義単調 | 0 | 0 |
| 10 | `dmap` の全要素 `< |ST|` | 0 | 0 |
| 11 | **陽性対照** `rd + 1 ≤ d` | **44 / 44** | **294 / 294** |

母数: `<=6` 列は BMS 3 行 z<2 標準形 **8387 個の全数**、7 列は**縮約が発火する
294 個の全数**。合計 338 発火は `SESSION-2026-08-28.md` の「発火は
338/77282 = 0.4%」と**一致**する（＝ 既知の発火を全部踏んでいる）。

### 訂正 2 つ

1. **`convResid_blk` は弱めなくてよい。** doc の「残余は森なので `BlkOK` の
   第 2 項はそのままでは偽」は、**実際に現れる `rd`** では観測されない
   （桁 4 が 0）。`ResidBlk`（`rd` の上界を仮定しない形）が偽であることとは
   別の話である。弱めた述語を設計する作業は**要らない**。
2. **`dmap` の候補の不変量は真。** 「`k < |dmap|` なら `dmap[k] < |ST|`、かつ
   `dmap` は狭義単調」は 338 発火すべてで成立。`BlkOK` に足してよい。

## 3. 残りの見積もり（行数つき）

| やること | 見積もり | 状態 |
|---|---|---|
| `BlkOK_app'`（開始深さが下がる連結） | 40 行 | **証明ずみ** |
| `BlkOK` に `dmap` の 2 条項を足し、`BlkOK_nil` / `BlkOK_app` / `BlkOK_app'` / `cols_blk` / `ImgBlockT3_of_BlkInv` を追随させる | **120〜150 行** | 未 |
| `contr_rd_ok`（`rd` の両側。`dmapAt` の場合分けと `depths_le`） | **40〜60 行** | 未 |
| `convResid_blk`（`rest` についての構造帰納。`conv3` の IH と `BlkOK_app'`） | **60〜100 行** | 未 |
| 縮約の枝の組み立て（`blk_step` の `· sorry` を埋める） | **30〜40 行** | 未 |
| **合計** | **250〜350 行** | |

`blk_step` の非縮約の枝は課題 L3 で済んでいるので、これで `BlkInv` が閉じ、
`ImgBlockT3 Conv3.b2d3` が**無条件**になる。

## 4. その先（`SandwichUT3` / `OrderT3`）の見積もり

課題 L3 §3 の表を、コードを読み直して更新したもの。

| 命題 | 見積もり | 律速 |
|---|---|---|
| `ImgBlockT3` | **250〜350 行**（上） | 測定ずみ。書くだけ |
| `SandwichUT3` | (S1)-(S5) の 5 本。**(S2) が本丸**。2 行側に対応物が無く、`ReindexT1` の穴埋めのために新しく立てた命題なので**下限が読めない**。まず Python 側（課題 H2）で (S2) を測るべき | `ImgBlockT3` |
| `OrderT3` | **2533 行より大きい**（2 行の `readC_conC_ST` が 2533 行、3 行は読み `read3` が未定義で、行 1 と行 2 の 2 種類の影があるので節が 2 つ要る）。`read3` / `dok` の設計から | `read3` / `dok` |
| `ImgCofinalT3` | 2 行側は `DbmsStd.lean` 約 15000 行がまるごとこれ。**Python 側でまだ破れている**（`ImgClosedT` 破れ <=6 列 54 個）ので**着手できない** | 変換器 `conv3` の設計 |

⟹ **DBMS トラックで次にやる価値があるのは `ImgBlockT3` だけ**である（測って
あるので書けば通る）。その先の `SandwichUT3` / `OrderT3` は 2 行側の 2533〜15000
行に対応する規模で、しかも `ImgCofinalT3` は Python 側の破れが直るまで手が出ない。


---

# 課題 L12: `ImgBlockT3` は**閉じなかった**。見積もりが外れた理由（2026-08-28）

## 0. 結論を先に

* **`ImgBlockT3 Conv3.b2d3` は無条件にならなかった。** `sorry` は 0 のまま
  （通らなかった部分は file に入れていない）。`Dbms3.lean` は exit 0。
* **課題 L11 の見積もり「250〜350 行。測ってある。書くだけ」は外れた。**
  外れた理由は 2 つとも**測定の解釈の誤り**で、今回それを潰した（§2）。
* буквально書けたのは**非縮約の枝だけ**。縮約の枝は
  「証明の穴」ではなく「**成り立たない不変量**」に当たっていた。

## 1. 今回 file に入ったもの（全部 exit 0 / sorry 0）

| 追加 | 中身 |
|---|---|
| `BlkOK` の**節 6** | `∀ c ∈ res.1, d ≤ c.1`（出した柱は全部深さ `d` 以上） |
| `BlkOK_mono` | `d' ≤ d → BlkOK d → BlkOK d'`（節 2 と節 6 が緩むだけ） |
| `BlkOK_app'` | 開始深さが下がってもよい連結（`convResid` の森に要る） |
| `contrFind_e_le` | `contrFind` が返す `e` は `0` か `1` |
| `BlkOK_nil` / `BlkOK_app` / `cols_blk` / `ImgBlockT3_of_BlkInv` | 節 6 に追随 |

**節 6 は新しい実測に基づく**（下）。`depths_ok` が既に 1 列ぶんについて
証明していたものを `BlkOK` に持ち上げただけなので、追随は 40 行で済んだ。

`blk_step`（帰納の 1 歩）の**非縮約の枝は新しい `BlkOK` でも通る**ことを
確認した（scratch, exit 1 = sorry のみ）。縮約の枝の 5 重連結
`cols ++ rA ++ rU ++ rR ++ rB` も、`BlkOK_app` / `BlkOK_app'` / `BlkOK_mono`
（`d' := 0` を明示して `rd` の巨大項を回避）で**組み立てには成功した**。
残ったのは下の 2 つだけである。

## 2. 見積もりが外れた 2 か所（**課題 L11 の訂正**）

### 訂正 A: `dmap` の不変量は**偽**だった

課題 L11 は「候補の `dmap` 不変量（狭義単調・`< |ST|`）は真」と書いた。
これは**縮約の呼び出し点でしか測っていなかった**。今回**すべての `conv3`
呼び出し**（`<=6` 列全数で 48997 回、7 列の縮約発火で 1134 回）で測り直した:

| 不変量 | <=6 列 48997 呼び出し | 7 列 1134 呼び出し |
|---|---|---|
| `dmap` が狭義単調 | **38 違反** | **438 違反** |
| `∀ k ∈ dmap, k < |ST|`（入口） | **6 違反** | **32 違反** |
| `∀ k ∈ dmap, k < |ST|`（出口） | **7 違反** | **38 違反** |
| **`dmap ≠ [] → dmap.last + 1 = |ST|`** | **0** | **0** |
| `d ≤ |st.ST|`（`BlkOK` の前提） | 0 | 0 |
| **`∀ c ∈ 出力, d ≤ c.1`（節 6）** | **0** | **0** |

⟹ `BlkOK` に足せるのは **`dmap.last + 1 = |ST|`** と **節 6** だけ。
`dmapAt` の**範囲内の枝**（`k < |dmap|`）の値 `dmap[k]` を `|ST|` で
抑える道具は無い（単調でも最大でもないから）。

### 訂正 B: `convResid` の節 2 は**やはり偽**（前任者の doc が正しかった）

課題 L11 は「doc の『`convResid` については `BlkOK` の第 2 項はそのままでは
偽』は観測されない」と書いた。**これも誤り**だった。今回 `convResid` の
**森の枝**（`tail ≠ []`）そのものを数えた:

    <=6 列 全数 ＋ 7 列の縮約発火 = 338 発火
      convResid が `tail = []` で終わる … 334
      convResid の**森の枝**        …   **0**
      rest2 = []                     …     4

つまり **森の枝は一度も踏まれない**。だから「呼び出し点では真」だったので
あって、`convResid` の不変量として真なのではない。しかも森の枝は

    tail = (c :: rs).drop (1 + deepGe c.1 rs)

なので `tail.head` は **`c` より必ず浅い**（`deepGe` の定義から）。したがって
次の木の開始深さ `rd - (c.1 - tail.head.1)` は **必ず下がる**。
⟹ **`BlkOK rd` は `convResid` については構造的に偽**であり、
「弱めた形が要る」という前任者の doc が正しい。

## 3. 残っている穴（正確に 2 つ）

`blk_step` の縮約の枝で残るのは、次の 2 つだけである。

    (H1) contr_rd_ok:  d ≤ rd ≤ |rU.2.ST|
         rd = if rest2 = [] ∨ (rest2.head).1 = p.1 + 1 then d + 1 + e
              else dmapAt rU.2.dmap ((rest2.head).1 - 1)

      * `d + 1 + e` の枝（実測 44/44 と 288/294）は**あと 1 歩**で出る:
        `e ≤ 1`（`contrFind_e_le`、**証明ずみ**）＋ `d + 2 ≤ |rU.2.ST|`。
        後者は節 6 と `lad0 = true`（縮約の枝では必ず真）から出るはず。
      * `dmapAt` の枝（実測 0/44 と **6/294**）は**道具が無い**（訂正 A）。
        6 回のうち 4 回は `(rest2.head).1 - 1 = |dmap|` ちょうどの
        「範囲外だが 1 個だけ外」で、`dmap.last + 1 = |ST|` から
        `dmapAt = |ST|` とぴったり出る。残り 2 回が範囲内で、ここが未解決。

    (H2) convResid の block 性
      * 実測では森の枝が 0 回なので、**残余が単一の木**であることさえ言えれば
        `convResid` は 1 回の `conv3` に潰れて (H2) は消える。
      * 「残余が単一の木」は `rest2 = Aq.drop kp` の形から出るはずだが、
        `Aq` の切り方（`deepGe (q.1+1) r2` と `kp`）を追う必要がある。

## 4. 直した見積もり

| やること | 前回 | 今回 |
|---|---|---|
| `BlkOK` 節 6 ＋ 追随 | 120〜150 | **40（済）** |
| `BlkOK_mono` / `BlkOK_app'` / `contrFind_e_le` | — | **60（済）** |
| `blk_step` の非縮約の枝 | 30〜40 | **20（scratch で確認）** |
| 縮約の枝の 5 重連結の組み立て | （上に含む） | **30（scratch で確認）** |
| **(H1) `d+1+e` の枝** | 40〜60 | **40〜60**（`lad0` の取り出しが要る） |
| **(H1) `dmapAt` の枝** | （同上） | **不明。道具が無い** |
| **(H2) 残余が単一の木** | 60〜100 | **80〜150**（`deepGe` と `kp` の追跡） |

⟹ **`ImgBlockT3` は「書くだけ」ではなかった。**
残るのは 2 つとも「`conv3` が残余をどう切るか」という**変換器の設計の性質**で、
`BlkOK` の帰納の外にある。`tools/dbms/rows3.py` 側（課題 H）の知識が要る。

## 5. `SandwichUT3` の (S2) の**測定仕様**（課題 H11 へ）

`SandwichUT3` の 5 分解のうち (S2) `BadRootT3` が本丸で、下限が読めない。
**Lean を書く前に Python で測るべき**なので、仕様だけ書く。

### (S2) の命題（行列の言葉だけ。順序数は使わない）

標準形 `A`（`|A| > 1`）について、BM4 の展開が使う 4 つの量を

    t  = srow A (|A|-1)                 末尾列が崩れる行（1 か 2）
    r  = parent A t (|A|-1)             **バッドルート**（`A` の添字）
    d0 = A[|A|-1].0 - A[r].0            行 0 の持ち上げ幅
    d1 = A[|A|-1].1 - A[r].1            行 1 の持ち上げ幅（`t = 2` のとき）

と書く。像 `B = conv3 A` について同じものを

    t' = srow B (|B|-1),  r' = parent B t' (|B|-1),
    d0' = B[|B|-1].0 - B[r'].0,  d1' = B[|B|-1].1 - B[r'].1

と書く。**(S2) は「`(t', r', d0', d1')` が `(t, r, d0, d1)` から決まる」**である。
測るのは次の 4 本:

    (S2-a)  t' = t                            末尾の崩れる行は像でも同じ
    (S2-b)  r' = img r                        バッドルートは「`A[r]` の本体柱」
    (S2-c)  d1' = d1                          行 1 の持ち上げ幅は変わらない
    (S2-d)  d0' = (B[|B|-1].0) - (B[img r].0) 行 0 の幅は像の段差で決まる

ここで **`img j`** は「入力の第 `j` 列に対して `conv3` が出した柱のうち
**本体**（`(dd2, e1, e2)`、その列が出す最後の柱）の像での添字」である。

### 要る計装（Python 側）

`rows3.b2d3` に**像に影響しない**出力を 1 本足す:

    img : list[int]      img[j] = 入力の第 j 列の本体柱の像での添字

`conv3` は 1 列につき最大 3 本（行 0 の影 / 行 1 の影 / 本体）を出すので、
`cols` を積むところで本体の位置を記録すれば得られる。
**`nc` と同じで像には効かない**（Lean 側の計装 `lean/l11_blkmeas.py` は
`St.nc` を使ったのと同じ流儀）。

### 入力の範囲

    <=6 列  BMS 3 行 z<2 標準形 **8387 個 全数**
    <=7 列  **77282 個 全数**（4 秒で回る土俵と同じ母数）
    `|A| > 1` かつ末尾が孤児でない（＝ 展開が `dropLast` に潰れない）ものだけ

`n` は要らない（(S2) は `A` だけの性質）。ただし (S2) が通ったら
`n = 1..5` で `conv3 (A⟦n⟧)` と `(conv3 A)⟦n+1⟧` の突き合わせに使う。

### 何を「破れ」と数えるか

`A` ごとに (S2-a)〜(S2-d) の 4 本を独立に判定し、**1 本でも外れたら
その `A` を破れ**とする。出力は

    土俵ごとに: 母数 / 破れ数 / 4 本それぞれの破れ数 / 最小の反例 3 個

`t = 1`（行 1 で崩れる）と `t = 2`（行 2 で崩れる）で**必ず分けて数える**。
3 行の困難は行 2 側にあるので、混ぜると効かない。

### 陽性対照（**必須**）

判定が盲目でないことを、**わざと外した予測**で確かめる:

    (P1) `r' = img r` を **`r' = img r + 1`** に変えて数え直す
    (P2) `d1' = d1` を **`d1' = d1 + 1`** に変えて数え直す
    (P3) `img` を**恒等写像**（`img j = j`）に差し替えて数え直す

(P1)(P2) は母数のほぼ全部が破れになるはず。(P3) は「像が入力より長い」
（`ConvDiagT3`: `conv3 (diagSeqT 0 v) = ddiagSeqT (v+2)`、梯子 2 段ぶん長い）
ので、やはりほぼ全部が破れになるはず。**3 本とも破れ数が母数に近づかない
なら、判定が効いていない**ので仕様を見直すこと。

### 期待と、外れたときの意味

C2（`SandwichU` の実測）は `<=7` 列 386405 対で破れ 8 しかないので、
(S2) も**ほぼ通る**はずである。破れが出るとしたら (S4)（写し同変）が
壊れている 12 対と同じ行列であろう。**そこが重なるなら、(S2) の破れは
課題 H1/H2 の「写しの境目で状態が漏れる」病と同じもの**であり、
`SandwichUT3` を Lean で追う前に Python 側を直すのが正しい順である。


---

# 課題 L13: `BlkInv` の帰納を全部通した。残る仮定は 1 本（2026-08-28）

## 0. 結論を先に

* **`blk_step`（帰納の 1 歩）を両方の枝とも証明した。** `leanman check` exit 0 /
  `sorry` 0 / `axiom` 0。`blkInv_aux` / `blkInv_of` / `ImgBlockT3_of_resid` まで配線。
* **`ImgBlockT3 Conv3.b2d3` が依存するのは名前つき 2 本だけ**になった:

      ResidBlkT … `convResid` が開始深さ `rd` の block（**課題 H へ**）
      DmapInT  … `dmapAt` の枝の `k + 1 < |dmap|` の場合（**338 発火で 0 回**）

* **課題 L12 の `(H1)` は全部閉じた。** `d + 1 + e` の枝も、`dmapAt` の枝の
  6 例（4 ＋ 2）も証明で閉じた。残るのは実測で一度も踏まれない場合だけ。

## 1. 縮約の枝の壁は「`split` が巨大項で燃える」だった

課題 L12 で詰まったのは、`he : (if lad0 then … else none) = some w` から
`lad0 = true` を取り出すところだった。`split at he` も `split_ifs at he` も
**識別子の `simp` が `maxSteps` を超えて燃え尽きる**（`conv3` の 1 列ぶんの
`if` の入れ子は数百行の項になる）。

**回避**: 汎用の補題を `he` に**当てて単一化させる**。項に `simp` を当てない。

    cond_of_ite_some : (if b = true then X else none) = some w → b = true
    ite_some_pair    : (if b = true then X else some u) = some w → X = some w ∨ u = w
    ite_some_none    : (if b = true then some u else none) = some w → u = w

これで `lad0 = true` と `contrFind … = some (e, kU, kp, na)` が取り出せ、
`contrFind_e_le` から `e ≤ 1` が出る。**これが課題 L12 で外していた 1 手。**

## 2. 5 重連結は「局所値を全部変数にした補題」に括り出す

`cols ++ rA.1 ++ rU.1 ++ rR.1 ++ rB.1` を `conv3` の本体の中で組み立てようと
すると、側条件の `have` が metavariable を決められない（課題 L2 で前任者が
踏んだのと同じ穴）。**局所値を全部変数にした補題** `blk_contr` に括り出すと、
呼び出し側は巨大項に触らずに済む:

    blk_contr (hddd : d + 1 ≤ dd2) (hst1 : dd2 + 1 ≤ |st1.ST|) (hst1ne : st1.dmap ≠ [])
      (hcols) (hA) (hU) (hR) (hrd) (hB) : BlkOK d st (cols ++ A1 ++ U1 ++ R1 ++ B1, …)

`hU` / `hR` / `hB` は**関数**として受ける（前提を `blk_contr` の中で導出する）。
これで側条件が 1 回ずつしか現れない。`d + 2 ≤ |stU.ST|` は
`BlkOK_ST_ge`（`BlkOK` の節 6 から出る鎖長の下界）で内部導出する。

⚠ **引数の順序が効く**: `rd` は結論に現れないので、`hR`（`rd` を含む
`convResid` の項が結論に現れる側）を `hrd` より**先に**置かないと `rd` が
metavariable のままになる。

## 3. `dmapAt` の枝は 6 例とも閉じた

`BlkOK` に足した節 8（`dmap.last + 1 = |ST|`、課題 L12 で唯一生き残った
`dmap` 不変量）から、`dmapAt dm k` は

| `k` | 値 | 閉じるか |
|---|---|---|
| `k = |dm|`（範囲外がちょうど 1 個外） | `dm.last + 1 = n` | **○** |
| `k = |dm| - 1`（範囲内の最後） | `dm.last = n - 1` | **○** |
| `k + 1 < |dm|` | 不明 | ✗（仮定 `DmapInT`） |

実測（`<=6` 列全数 ＋ 7 列の縮約発火全数 = 338 発火）:

    dmapAt の枝        0 / 6
      k = |dmap|        0 / 4   ← 閉じた
      k = |dmap| - 1    0 / 2   ← 閉じた
      **k + 1 < |dmap|  0 / 0** ← 一度も踏まれない

`k = |dmap| - 1` の 2 例（課題 L12 で「未解決」と報告したもの）:

    (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(3,0,0)
    (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(3,1,0)
    どちらも d = 1, hh = (rest2.head).1 = 3, k = hh - 1 = 2,
             |rU.2.dmap| = 3, dmap[2] = 4, |rU.2.ST| = 5
    ⟹ k = |dmap| - 1 なので dmap[k] = dmap.last = |ST| - 1。閉じる。

## 4. `ImgBlockT3` があと何を待っているか

**`ResidBlkT` 1 本だけ**（`DmapInT` は実測で空虚）。

    ResidBlkT := ∀ rest rd Lr ps pw st nx off, rd ≤ |st.ST| →
                   BlkOK rd st (convResid rest rd Lr ps pw st nx off)

一般には**偽**（森の枝で開始深さが必ず下がる）。真になるのは残余が
**単一の木**のとき、すなわち `convResid` の再帰の枝に入らないとき。
実測では 338 発火で森の枝は **0 回**。⟹ **「残余は常に単一の木」が言えれば
`ImgBlockT3` は無条件になる。** 変換器側（課題 H）の性質である。

## 5. 見積もりの書き方（課題 L11 の反省）

課題 L11 の「250〜350 行。測ってある。書くだけ」が外れたのは
**測定の範囲が呼び出し点に限られていた**からだった。以後、見積もりには

* **どの範囲で測ったか**（呼び出し点だけ / 全呼び出し / 全入力）
* **測っていない場合分けはどれか**

を必ず添える。今回の測定範囲は:

| 測ったもの | 範囲 |
|---|---|
| `BlkOK` の節 6・節 8、`d ≤ |st.ST|` | **全 `conv3` 呼び出し**（`<=6` 列 48997 ＋ 7 列 1134） |
| 縮約の枝の債務 10 本、`dmapAt` の場合分け、`convResid` の森の枝 | **全縮約発火**（`<=6` 列 44 ＋ 7 列 294 = 338 = 既知の全発火） |
| 未測定 | **8 列以上**。`ResidBlkT` の森の枝が 8 列で踏まれる可能性は否定できない |


---

# 課題 L14: 突き合わせの母集団が足りなかった（2026-08-28）

## 0. 結論を先に

* **`gen3` ベースの母集団では Lean（v15）と Python（v16(2)）を区別できない。**
  チームリードの測定を**自分の突き合わせ器で再現した**:

      gen<=7 の 77282 個          … 像の差 **0**
      **展開閉包 20829 個**       … 像の差 **161**（10 列 140 / 15 列 21）

* 原因は 1 行: **`gen3` は展開して伸びた行列を含まない。** v16 で変えた
  `wroot` / `hiblk` / `sibnb` は「写しの中で親の鎖に `x w` 柱が挟まる」形の
  ときに効くので、**写しが 2 枚以上ある行列でしか差が出ない**。
* `lean/l1_sets.py` に **`exp` モード（展開閉包）を足した**。以後の突き合わせは
  こちらを使う。`gen3` 側だけの結果を「一致」と報告してはいけない。

## 1. 母集団の作り方（`python3 lean/l1_sets.py exp <out.txt>`）

    gen3('BMS', 6, zcap=1) の 8387 個
      ＋ その各々を core.expand で n = 1, 2, 3 展開したもの
      = 重複を除いて **20829 個**

    長さの分布
      1..6 : 8387   7 : 2298   8 : 845   9 : 1328   10 : 3282
        11 :  389  12 :  383  13 : 729  15 : 3188

`max z = 1` なので z<2 断片から出ない（生成器の制約と整合）。

## 2. 実測（`lean/l1_check.py`、Lean に計算させた像を行ごとに diff）

    python3 lean/l1_sets.py exp tmp_l1/inexp.txt
    python3 lean/l1_check.py gen tmp_l1/inexp.txt tmp_l1
    leanman check -C /home/koteitan/proofs/dbms/lean tmp_l1/l1check.lean   # 213 秒 exit 0
    python3 lean/l1_check.py diff tmp_l1

    compared 20829  **mismatches 161**

最短の食い違い（10 列）:

    A   0,0,0 1,1,1 2,0,0 1,1,1 1,1,1 1,1,0 2,2,1 3,0,0 2,2,1 2,2,1
    py  … 3,2,1 3,2,1 **3,2,0 4,3,1 5,0,0 4,3,1 4,3,1**   （v16(2)）
    lean… 3,2,1 3,2,1 **2,1,0 3,2,1 4,0,0 3,2,1 3,2,1**   （v15）

**Python 側の 2 版を直に比べても同じ 161 個**（`RS_NOSIBNB=1 RS_NOWROOT=1
`RS_NOHIBLK=1` で v15 に戻して差分を取った）。つまり差は完全に v15/v16(2) の
綴りの違いであって、Lean の写経ミスではない。

## 3. これまでの「一致」の表示について（訂正）

`Dbms3.lean` の doc と課題 L3 の表に

    <=6 列の BMS 3 行 z<2 標準形 8387 個を全数        食い違い 0
    7 列（68895 個）のうち v12 と像が違う 290 個ぜんぶ … 食い違い 0

とあるが、**これは「Lean の conv3 が Python の conv3 と同じ関数だ」の証拠には
ならない**。当時の Python と Lean が同じ版だったことの証拠にはなるが、
母集団が展開を含まないので、**あとで Python 側が v16 に進んでも同じ表示のまま
通ってしまう**。実際そうなった。

⟹ **突き合わせの母集団は「展開閉包」を含むこと。** これは規約とする。

## 4. Lean を v16(2) に追いつかせるか

いまは**追いつかせない**。理由:

* 課題 L13 の `ImgBlockT3`（`blk_step` / `blk_contr` / `BlkOK` の節 6・7・8）は
  **`conv3` の定義の中身に依存しない**。`depths_ok` と `cols_blk` が使うのは
  `dd0` / `dd1` / `dd2` / `ST1` / `ST2` の**形**だけで、`bp`（浅い／深いの選択）
  の中身は一切見ない。v16 の 4 本（`sibnb` / `wroot` / `hiblk` / `conv_resid`）は
  すべて `bp` と `first` / `ps` の読みを変えるものなので、**証明は無傷**である。
* Python 側は課題 H13 が `after_w` を触っているので、追いつかせてもすぐ古くなる。

追いつかせるときに要るのは 4 本:

    sibnb      sibL の「深い側」を分岐列以外にも渡す ＋ 6 リテラルの門 sibnb_ok
    wroot      after_w / wchain の par0(..)==0 を par0_w に
    hiblk      hi_block の頭を is_diag で拾う
    conv_resid first / ps を行列読み first_of / ps_of に

**⚠ ただし `conv_resid` の変更は課題 L13 の `ResidBlkT` に効く可能性がある**
（`convResid` の引数の読み方が変わるので、「残余が単一の木」の議論が変わりうる）。
そこだけは追随のときに測り直すこと。


---

# 課題 L14: `read3` / `dok` の設計 — **この設計では `ReadT3` は出ない**（2026-08-28）

## 0. 結論を先に

* **2 行の `readD` の逐語版は 3 行では原理的に不可能**（最小の反例は対角）。
  像の行 1 は BMS の添字ではなく**行 1 の木での順位**である。
* 順位に直す設計 `read3 := translate ∘ rankify ∘ survivors` を書き（`lean/L14Read.lean`、
  exit 0 / `sorry` 0 / `#guard` 5 本）、**真の `ST_TS` 展開閉包で測った**:
  **415218 個中 406564 一致・破れ 8654（2.1%）**、陽性対照 2 本つき。
* **破れは 2 種類とも構造的で、`ReadT3` はこの形では成り立たない。**
  とくに**縮約が発火した行列は一致が 1 つも無い**（601/601 破れ）。
* ⟹ **`OrderT3` は `SeqEmbT3`（`OrderT3_iff_seqemb` で同値、読みを使わない）から
  攻めるべき。** `read3` の道は縮約を読み戻す仕掛けが要る。

## 1. なぜ逐語版が不可能か（1 例で終わり）

    M   = (0,0,0)(1,1,1)                    translate M = P 0 0 (P 1 1 Z Z) Z
    像  = (0,0,0)(1,0,0)(2,1,0)(3,2,1)
    像の (行1,行2) = (0,0) (0,0) (1,0) (2,1)   ⟹ **(1,1) がどこにも無い**

`translate` は柱の `(行1,行2)` をそのまま添字にするので、どの部分列を選んでも
`P 1 1` は作れない。原因は `conv3` の 1 行:

    e2 = s2                行 2 は**そのまま**書く
    e1 = 梯子の表から計算   行 1 は**そのままではない**

2 行の `convD` は `p.2` をそのまま書くので `readD` が逐語で済んでいた。
**ここが 2 行と 3 行の分かれ目である。**

## 2. 設計（`lean/L14Read.lean`、exit 0）

    survivors B first plev   `readD` と同じ再帰で影を捨てる。節は 2 つ
      行 1 の梯子 … first ∧ (p の段) = plev ∧ 次 = p + (1,1,0)
      行 2 の梯子 … first ∧ p の行 2 = plev の行 2 ∧ 次 = p + (1,1,1)
    rankify B                各行の値を**その行の木での順位**に置き換える
    readMat B := rankify (survivors B true (0,0))
    read3 B   := translate (readMat B)
    dok B     := blockok 0 B ∧ ST_TS (readMat B)

`rankify` は BMS 標準形の上では恒等なので、**`readMat (conv3 M) = M` が言えれば
`ReadT3` は無料**になる。対角では `#guard` で確認ずみ:

    readMat (0,0,0)(1,0,0)(2,1,0)(3,2,1)           = (0,0,0)(1,1,1)
    readMat (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,1)    = (0,0,0)(1,1,1)(2,2,1)
    read3   (0,0,0)(1,0,0)(2,1,0)(3,2,1) = translate (0,0,0)(1,1,1)

## 3. 測定（`tools/probe_read3.py`）— **測定範囲を明記する**

    (INV) readMat (conv3 M) = M          for M in ST_TS

**母集団は「真の `ST_TS` 展開閉包」**（対角 `diag(3,v,zcap=1)` から `n = 1,2,3` の
展開で到達できるもの）。`gen3` の標準形の集合ではない — `ReadT3` の仮定が
`ST_TS M` だからである（`gen3` は `isstd` で、`ST_TS` より広い）。

| | 母数 | 一致 | **破れ** |
|---|---|---|---|
| `v<=4, len<=10` **本番** | 415218 | 406564 | **8654（2.1%）** |
| 陽性対照 1（影を捨てない） | 415218 | 36 | **415182** |
| 陽性対照 2（順位に直さない） | 415218 | 36 | **415182** |

⟹ **影を捨てる段も順位に直す段も、どちらも必須**（対照が両方とも落ちる）。

破れの内訳（`v<=4, len<=9` の 44063 個で分解。破れ 973）:

| | 件数 |
|---|---|
| **縮約が発火した** | **601** |
| 縮約なし | 372 |
| 短い像（`|conv3 M| < |M|`）| 239 |
| 像は十分長い | 734 |
| **一致した中に縮約ありは** | **0 個** |

**測っていない場合分け**: `v>=5` / `len>=11` / `n>=4` の展開。
とくに縮約の発火率は列数とともに上がるので、**破れの割合は 2.1% より
悪くなる可能性がある**（良くはならない）。

## 4. 判定: **この設計では出ない**（1 段落）

`conv3` の**縮約**が発火すると像が `M` より短くなる（実測 239 例）。`translate M`
の節点は `|M|` 個あるので、**1 列 1 節点で読むどんな `read3` でも
`read3 (conv3 M) = translate M` は成り立ちえない**。しかも縮約が発火した行列は
**一致が 1 つも無い**（601/601）。縮約は捨てられない（止めるとシートが
1354 -> 1021 に落ちる）。残る 372 は影の節の**取り違え**で、局所の
「次 = `p + (1,1,1)`」だけでは本体の柱と梯子の柱を分けられない
（`okPlace` 相当の「その深さにその段を直に書けたか」を見ないと決まらない）。
⟹ **`read3` / `dok` の道は、縮約を読み戻せる `read3`（1 列を複数節点に開く）を
設計しないかぎり閉じている。**

## 5. 推奨: `SeqEmbT3` から攻める

`Dbms3.OrderT3_iff_seqemb`（**証明ずみ**）:

    OrderT3 conv3  ↔  SeqEmbT3 conv3
    SeqEmbT3 conv3 := ∀ M N, ST_TS M → ST_TS N → (seqlex M N ↔ seqlex (conv3 M) (conv3 N))

こちらは**読みも項も順序数も出てこない**ので、縮約が像を縮めても関係ない
（辞書式の比較だけ）。実測でも `conv3` は `<=6` 列 8387 個・`<=7` 列 77282 個で
位置ずれ 0・像の重複 0 である。`conv3` の構造帰納法で攻めるのが筋である。
**2533 行の `readC_conC_ST` を写経する道は、少なくとも縮約がある以上、無い。**
