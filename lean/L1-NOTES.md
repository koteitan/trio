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
| 7 列 **全数**（＝これで gen<=7 の 77282 個ぜんぶ） | 68895 | **0** |
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
7 列の **18 個** ＋ 8 列の **352 個**。`wterm` は像を変えないので追加は無い。
7 列で v13 が v12 と違う 290 個からの抜き取りのうち 1 本が h1 で像が変わる
ものだったので、h1 の影響を受けない別の 1 本に差し替えた。

`#guard` を 370 本足しても `leanman check` は 9 秒 -> 17 秒（ファイルは
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
