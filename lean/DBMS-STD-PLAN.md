# 像が DBMS 標準形であることの証明計画

対象: `ST_PS M → ST_D (conC M)`（BMS 2 行標準形の像が DBMS 2 行標準形）。
関連ファイル: `Dbms.lean`（変換と正しさ）、`DbmsStd.lean`（標準形性）。

## 済んでいること

| | 場所 |
|---|---|
| `readC_conC_ST : ST_PS M → readCon (conC M) = translate M` | `Dbms.lean` |
| `conC_olt_iff_seqlex` / `conC_injective`（順序保存・単射） | `Dbms.lean` |
| `conC_diagSeq` / `ST_D_conC_diagSeq`（帰納法の底） | `Dbms.lean` |
| `diag_cofinal`（対角は共終） | `DbmsStd.lean` |
| `ST_D_descend` / `ST_D_conC`（`ReindexD` から標準形性） | `DbmsStd.lean` |
| `reindexD_succ`（REINDEX の succ regime） | `DbmsStd.lean` |
| `convC_getLast_level` / `idx1_conC`（末尾列の段が保たれる） | `DbmsStd.lean` |
| `oper_mono`（基本列は添字について単調） | `DbmsStd.lean` |
| `conC_length_ge_two`（2 列以上なら像も 2 列以上） | `DbmsStd.lean` |
| `convC_plev`（`first = false` の変換は親の段・`force` に依らない） | `DbmsStd.lean` |
| `convC_run`（同じブロックの並びは同じ塊の並びに写る） | `DbmsStd.lean` |
| `oper_repeat`（末尾の段が 0 なら基本列は素直な繰り返し） | `DbmsStd.lean` |
| `convC_force`（`d ≤ plev+1` なら `force` は効かない） | `DbmsStd.lean` |
| `conC_run_top`（`conC (blk^n) = blk'^n`、`blk` の根が `(0,0)`） | `DbmsStd.lean` |
| `oper_one`（`M⟦1⟧ = M.dropLast`、枝によらず） | `DbmsStd.lean` |
| `hasParent_append_of_parent_ge` / `oper_append_of_parent_ge`（**親が接尾辞にあれば局所化**） | `DbmsStd.lean` |
| `convC_getLast_ge` / `convC_getLast_depth`（像の末尾列の深さ） | `DbmsStd.lean` |
| `parent_ge_of_witness` / `oper_append_of_witness`（**証人が 1 つあれば局所化**） | `DbmsStd.lean` |
| `nextrel0_ge` / `nextrel1_ge` / `parent_ge_of_shallow`（浅い列 1 つで親の下界） | `DbmsStd.lean` |
| `oper_append_of_shallow0` / `convC_head_shallow`（段 0 での局所化） | `DbmsStd.lean` |
| `convC_exists_shallow`（**像の中に末尾より浅い列がある**） | `DbmsStd.lean` |
| `oper_append_convC`（**場合 (c) の段 0 が完成**） | `DbmsStd.lean` |
| `oper_append_of_shallow1`（段 > 0 での局所化、証人は `le0` の鎖の上） | `DbmsStd.lean` |
| `rtg_lt_of_floor` / `le0_ge_of_append`（**床の補題**。行 0 の鎖はブロックの頭を越えない） | `DbmsStd.lean` |
| `convC_exists_shallow1`（**段 > 0 の証人の存在**） | `DbmsStd.lean` |
| `oper_append_convC1`（**場合 (c) の段 > 0 が完成**） | `DbmsStd.lean` |
| `exists_greatest_lt` / `le0_head`（**ブロックの頭は中の全部の行 0 の祖先**） | `DbmsStd.lean` |
| `convC_single` / `convC_dropLast_singleton`（末尾ブロックが 1 列） | `DbmsStd.lean` |
| `convC_dropLast_arg` / `_tail` / `_lad_none` / `_contr`（**dropLast の帰納の 4 段**） | `DbmsStd.lean` |
| `range'_map_entry` / `range_append_range'` | `DbmsStd.lean` |
| `convC_dropLast_noParent_aux` / `_noParent`（**場合 (b): 親がなければ dropLast は可換**、`contrOK` つき） | `DbmsStd.lean` |
| `contrOK`（def）/ `contrOK_suffix` / `contrOK_of_last_zero`（段 0 なら自動） | `DbmsStd.lean` |
| `hasParent_last_append` / `noParent_suffix`（親のなさは接尾辞に遺伝） | `DbmsStd.lean` |
| `convC_exists_shallow1` / `oper_append_convC1`（**場合 (c) の段 > 0**） | `DbmsStd.lean` |
| `convC_getLast_min` / `oper_repeat_root` / `conC_cons_zero` / `reindexD_node0`（**場合 (d) の根・段 0**） | `DbmsStd.lean` |
| `noParent_arg_node1` / `convC_dropLast_node1` / `conC_dropLast_node1` | `DbmsStd.lean` |
| `convC_run_first` / `convC_run_lad` / `oper_repeat_at` / `convC_dropLast_min` | `DbmsStd.lean` |
| `reindexD_node0_gen` / `reindexD_node0_lad`（**場合 (d) のブロック版・段 0**、梯子なし／あり） | `DbmsStd.lean` |
| `reindexD_zero_block` / `reindexD_pos_block`（**右端の道に沿った帰納の組み立て**） | `DbmsStd.lean` |
| `reindexD_holds_of_res` / `ST_D_conC_holds_of_res`（**残余 `RDzeroRes` / `RDposRes` から結論**） | `DbmsStd.lean` |
| `adj3` / `noAdj3` / `noAdj3_ST_PS`（**BMS 標準形に禁止形 `(0,0)(1,1)(2,1)(3,2)` 型は現れない**） | `DbmsStd.lean` |
| `headPatOK` / `argPatOK` / `argPatOK_ST_PS`（禁止形のブロック版） | `DbmsStd.lean` |
| `convC_force_head` / `convC_arg_force_eq` / `convC_force_ne` / `convC_force_arg_ne`（`force` を消す道具） | `DbmsStd.lean` |

いずれも sorry 0。

## 残っているもの: `ReindexD`

```
ReindexD : ∀ A, ST_PS A → 1 < A.length → ∀ n ≥ 1,
  ∃ m ≥ 1, ∃ n' ≥ n, (conC A)⟦m⟧ = conC (A⟦n'⟧)
```

（`translate (A⟦n⟧) ≤o translate (A⟦n'⟧)` は `oper_mono` から出るので条件から外せた。）
regime ごとの取り方: succ は `m=1, n'=n`、id は `m=n, n'=n`、
shift は `m=n, n'=n+1`、contr は `m=n+1, n'=n`。

実測（`tools/dbms/reindex.py`）:

```
lim=10  標準形 2073826  regime {id: 1556322, succ: 295014, shift: 222309, contr: 180}  違反 0
```

## 局所化は使える（2026-08-25 に解決）

当初「DBMS 側で局所化が破れる」と書いたが、**破れていたのは `rsum` を仮定する
`oper_append_gen` が使えないだけ**だった。`Pair/Column.lean` の `hasParent_append_right`
は `entry T 0 0 = 0`（接尾辞の頭が最浅）を仮定するが、これは

    「親が接尾辞の中にある」

に置き換えられる。`hasParent` は一意性つきなので、親が接尾辞にあれば
**どの `nextR` の始点も接尾辞に入る**からである。これで

```
oper_append_of_parent_ge :
  2 ≤ |T| → 末尾が (0,0) でない → hasParent (A ++ T) i (|A| + j1) →
  |A| ≤ parent (A ++ T) i (|A| + j1) → (A ++ T)⟦n⟧ = A ++ T⟦n⟧
```

が仮定なしで出る（`DbmsStd.lean`、証明済み）。実測でも
「BMS の親が `B` の中 ⟺ DBMS の親が `convC B` の中」は例外 0 なので、
場合 (c) の帰納は両側で回る。

### もとの観察（なぜ `rsum` が効かないか）

`A = p :: (Arg ++ B)` で梯子を敷いた段では、影の列が `convC B` の頭より浅いので
`rsum` が偽になる（≤8 列で梯子ありの 11437 段中 7134 段）。実例:

```
M = (1,1)(2,1)(1,1)(2,1)          (d=1, plev=0, first, force)
convC M = (1,0)(2,1)(3,1)(2,1)(3,1)
末尾 (3,1) の行 1 の親は影の (1,0)（index 0）。B の像は index 3 からなので親は外。
BMS 側は (1,1) の行 1 が 1 なので親がなく Pred。
```

実測（`convC` の再帰の全段、≤7 列）: 梯子なし 4537 段は全部局所化できる。
梯子あり 1777 段のうち 352 段で DBMS 側が破れる。

## 通りそうな道: 悪いブロックの対応

`Pair/Decrease.lean` の `oper_bad_blocks` は BMS 側にこの分解を与える:

```
M      = G ++ ((v0,w0) :: R) ++ [lp]          （R は全部 v0 より深い、v0 < lp.1）
M⟦n⟧   = G ++ (range n).flatMap (k ↦ ((v0,w0)::R) を行 0 に k*d0 ずらしたもの)
```

つまり**悪い部分は「親の張るブロックそのもの」**で、展開はそれを n 個並べる。
必要なのは DBMS 側の同じ分解と、両者の対応。実測でわかったこと:

* 末尾列の**段は保たれる**（`idx1` が両側で一致する）
* 末尾列に親があるかどうかも、標準形の全体では両側で一致する（≤7 列で反例なし）
* `T = A.drop jB`（BMS の悪いブロック）は `convC` の再帰の呼び出しとして現れ、
  その出力開始位置 `off` と DBMS の親 `jD` の差は 0 か 1（まれに 3, 5）。
  差 1 は「ブロックの頭が梯子を要る」場合で、BMS のコピー k=0 が
  DBMS では梯子＋影に化ける。**これが shift regime の正体。**

### 末尾列の段による分割（実測、≤9 列）

```
lp = (0,0)          → succ  44653          （証明済み）
lp の段 = 0, ≠(0,0) → id 123323 / contr 49  （d0 = 0、両側ともコピーは素直な繰り返し）
lp の段 > 0         → id  94373 / shift 32615（shift ⟺ lp = (1,1)）
```

**段が 0 の場合はコピーが素直な繰り返しになる**（`d0 = 0`）。BMS 側は `oper_repeat`、
DBMS 側も `idx1_conC` から同じく `d0' = 0`。変換側は `convC_run` が
「同じブロックの並び → 同じ塊の並び」を与える。残るのは前置きの因子化:

```
conC (G ++ X) = P ++ convC X d plev first force      （P と params は G だけで決まる）
```

これは縮約が経路上で発火しない限り成り立つ（実測: `T not a call` は縮約の場合だけ）。

### shift regime の親（実測、≤9 列）

`shift`（末尾列 = `(1,1)`）のとき、BMS の親 `jB` は**末尾の直前にある最後の `(0,0)` の位置**。
`jB = 0` が大半（≤9 列で 25455 / 32615）だが、`(0,0)` が再び現れる形では `jB > 0`:

```
(0,0)(1,1)(2,2)(0,0)(1,1)(1,1)      jB = 3
```

良い部分は必ず `(conC A)⟦0⟧ = conC (A⟦0⟧) ++ [影]`（`+1 列`、≤8 列で例外 0）。
`id` では `一致`（20738）と `+1 列`（11527）が混在し、`contr` では縮約のぶん短くなる。
つまり「良い部分が 1 列長い」だけでは regime は決まらない。

### shift regime の仕組み（手で追った例）

```
A = (0,0)(1,1)(2,2)(3,3)(3,2)(1,1)
    BMS の親は index 0 の (0,0)。blk = (0,0)(1,1)(2,2)(3,3)(3,2)、d0 = 1

N = conC A = (0,0)(1,0)(2,1)(3,2)(4,3)(4,2)(2,1)
    DBMS の親は index 1 の (1,0) — これは**影**（内側ブロックの梯子）。
    blk' = (1,0)(2,1)(3,2)(4,3)(4,2)、d0' = 1
```

BMS の親 `(0,0)` に対応するのは、DBMS では**影の列** `(1,0)` である。
コピーを並べると:

```
A[1] = blk                        conC = (0,0) ++ blk'              = N[1]   g(1)=1
A[2] = blk ++ (blk+1)             conC = (0,0) ++ blk' ++ blk'      ≠ N[2]
A[3] = blk ++ (blk+1) ++ (blk+2)  縮約が最初の 2 コピーを 1 つに潰す
                                  conC = (0,0) ++ blk' ++ (blk'+1)  = N[2]   g(2)=3
```

**縮約（梯子の二役）がコピーを 1 つ飲み込む。** これが shift regime の正体。
`A[2]` で縮約が起きないのは `rest2` が空になるからで、コピーが 3 つ以上あって
初めて発火する。

したがって要る補題は「コピーの補題」:

```
ブロックの頭が梯子を要らない  … conC (G ++ blk を n 個) = G' ++ blk' を n 個      （id）
ブロックの頭が梯子を要る      … conC (G ++ blk を n+1 個) = G' ++ blk' を n 個    （shift）
```

### regime の引き金（実測、≤10 列 2073826 個）

* `succ`  ⟺ `A` の末尾列 = `(0,0)`
* `shift` ⟺ `A` の末尾列 = `(1,1)`（このとき BMS の親は index 0 の `(0,0)`、`d0 = 1`、
  `G = []` なので `A⟦n⟧` は `A.dropLast` のコピー n 個そのもの）
* `contr` ⟺ 末尾で梯子が二役（180 個／≤10 列）
* `id`    ⟺ それ以外

DBMS 側の親の列は、`shift` と `contr` では**必ず影**（≤9 列で例外なし）。
ただし `id` でも影のことがある（≤9 列で 125012 / 217696）ので、
「親が影か」だけでは regime は決まらない。

### regime の対応表（≤10 列の実測）

| regime | 引き金 | g(m) | 個数（≤10 列） |
|---|---|---|---|
| succ | 末尾列 = (0,0) | 0 | 295014 |
| id | 大多数 | m | 1556322 |
| shift | 末尾列 = (1,1)（ブロックの頭に梯子） | m+1 | 222309 |
| contr | 末尾で梯子が二役 | m-1 | 180 |

## 証明の骨組み（2026-08-25 の改訂）

前置きの因子化 `conC (G ++ X) = P ++ convC X ...` は、**縮約が経路上で発火すると崩れる**。
`convC` の再帰の各段で `X ⊆ B` かつ `first = true` のとき、縮約の判定が `X` を覗くため。

そこで**各段での場合分け**に切り替える。`convC M d plev first force` の各段で:

```
(a) M の末尾列 = (0,0)          → 両側とも Pred          （succ、証明済みの形）
(b) M の末尾列に親がない        → BMS は Pred、DBMS は m=1
(c) 展開が Arg または B に閉じる → その部分列に帰納
(d) 親がこの段にある            → 基底（コピーの対応）
```

(b) の実例（局所化が破れた例と同じもの）:

```
M = (1,1)(2,1)(1,1)(2,1)        d=1, plev=0, first, force
BMS: 末尾 (2,1) の段 1 に対し段 0 の祖先がない → Pred M = (1,1)(2,1)(1,1)
DBMS: convC M = (1,0)(2,1)(3,1)(2,1)(3,1)、末尾の親は影の (1,0)（index 0）
      (convC M)[1] = (1,0)(2,1)(3,1)(2,1) = convC (Pred M)     ← m=1 で一致
```

### 各段での親の対応（実測、右端の道だけ、≤8 列）

節点の「実列」の位置を `base`（梯子なら 1、なければ 0）として分類する。

```
梯子なし
  SHORT ↔ SHORT   43637     1 列（展開なし）
  ZERO  ↔ ZERO     9632     succ
  中    ↔ 中       39737     部分列に帰納
  節点  ↔ 節点     20719     基底
  節点  ↔ 中       10817     基底（DBMS の親は「子の梯子の影」）
  親なし ↔ 親なし   37419     両側 Pred
梯子あり
  SHORT ↔ 影         938
  中    ↔ 中       13337     部分列に帰納
  節点  ↔ 節点      5803     基底
  親なし ↔ 影       9879     BMS は Pred、DBMS は m=1
  親なし ↔ 親なし    5551     両側 Pred
縮約あり
  中 ↔ 中 34 / 中 ↔ 影 23 / 親なし ↔ 親なし 21
```

**BMS が「中」なら DBMS も必ず「中」**（例外 0）。だから (c) の帰納は回る。
BMS が「節点」のとき DBMS は「節点」か「子の梯子の影」の 2 通り。これが
良い部分の `一致` / `+1 列` に対応する。

### `oper_one` から出ること

`M⟦1⟧ = M.dropLast` はどの枝でも成り立つ（縮約の枝でも `k=0` のコピーはずれない）。
したがって

```
g(1) = 1  ⟺  conC (A.dropLast) = (conC A).dropLast
```

実測（≤9 列 295013 個）: 可換 289379 / 非可換 5634。
非可換は「末尾列が梯子を敷く」場合（5585）と縮約の場合（49）。
末尾 2 列が `(a,b)(a+1,b+1)` の形かどうかでは判定できない
（その形でも可換なものが 20885 ある）。梯子が立つかは `ladOf` の文脈次第。

## 4 つの場合の詰め方

### (a) 末尾 = `(0,0)`
`reindexD_succ` で証明済み（`convC_snoc_zero` + `oper_snoc_zero`）。

### (b) BMS の親がない
`M⟦n⟧ = Pred M = M.dropLast`（`1 < |M|`）。DBMS 側は `oper_one` で
`(convC M)⟦1⟧ = (convC M).dropLast`。だから要るのは

```
convC (M.dropLast) d plev first force = (convC M d plev first force).dropLast
```

これは**末尾列が梯子を敷かないとき**に成り立つ（実測: 非可換 5634 / 295013 は
すべて梯子か縮約）。そして case (b) では末尾列は梯子を敷かない:
梯子の頭は「段 = 親の段 + 1」で、その親ノードは行 1 の祖先だから `hasParent` が立つ。
親がないなら梯子頭ではない。

**実測では場合 (b) の dropLast の可換は例外 0**（`tools/dbms/bcase.py`、
`convC` の再帰の各段・右端の道、≤8 列で 52870 / 52870）。理由は 2 つ:

* 梯子頭には親が立つので、親がないなら梯子頭でない（差 2 にならない）
* 縮約が消える状況（`Bq = []` かつ `|rest2| = 1`）では、そこでの親は「中」にある
  （例: `(0,0)(1,1)(1,0)(2,1)(2,0)` の末尾 `(2,0)` の行 0 の親は `(1,0)`）

dropLast の帰納の部品は**全部揃った**:

```
convC_dropLast_singleton  末尾ブロックが 1 列 → 像でも 1 列（縮約は発火しない）
convC_dropLast_arg        B が空 → 引数 A に帰着（縮約は発火しない）
convC_dropLast_tail       梯子なし → 兄弟 B に帰着
convC_dropLast_lad_none   梯子あり・縮約なし → 兄弟 B に帰着
convC_dropLast_contr      梯子あり・縮約あり・Bq ≠ [] → Bq に帰着
convC_dropLast_contr2     梯子あり・縮約あり・Bq = [] かつ |rest2| ≥ 2 → rest2 に帰着
```

**壊れるのは `Bq = []` かつ `|rest2| = 1` のときだけ。** そのとき末尾列は
`rest2` のただ 1 列で、深さ `p.1+1`・段 `< p.2`。

実測（`tools/dbms/badcontr.py`、BMS 標準形 ≤9 列、右端の道）:

```
('BAD', 段0=True, 親='中'): 49      ← 壊れる場合はすべて段 0 で親が「中」
```

**壊れる場合は必ず段 0 で、親が「中」にある。** 段 0 なら `q`（深さ `p.1`）が
行 0 の親になるので、親は必ず存在し、しかも `q` は節点より後ろなので「中」。
だから場合 (b)（親なし）と場合 (d)（親が節点）では壊れる場合は起きない。

段 > 0 で壊れる場合が起きない理由:

壊れるには節点で梯子が要る。梯子は `s = plev+1` かつ `d ≤ s`（または `force`）。
DBMS は段 `s` の列を深さ `s+1` 以上に置くので `s ≤ d`、あわせて `d = s`。
段 2 の節点を `d = 2` で呼ぶには親の `dd` が 1、つまり段 1 の列を深さ 1 に置く
ことになり DBMS では不可能。残るのは `force` 経由だけで、それには

    段 1 の節点の親の段も 1（`s == plev`）

が要る。ところがそういう形は BMS 標準形にならない:

```
(0,0)(1,1)(2,1)       標準形
(0,0)(1,1)(2,1)(3,2)  標準形でない
```

つまり **`plev = 0` すなわち `s = 1` の場合しか梯子は立たず、
`rest2.headI.2 < 1` から段は 0 に強制される**。
実測も ≤9 列で 49 件すべて段 0（`tools/dbms/badcontr.py`）。

`convC_dropLast_contr` の要点は「`Bq ≠ []` なら縮約は消えない」:

* `unitsLen p (B.dropLast) = unitsLen p B`（`unitsLen_append_units` を 2 回）
* `(B.dropLast).drop k = q :: r2.dropLast`、`r2.dropLast = Aq ++ Bq.dropLast`
* `pre` も `rest2` も変わらないので `contrLen` は `some (rest2, Bq.dropLast)`

残るのは**組み立て**（右端の道に沿った帰納）と、
`convC_dropLast_lad_none` の仮定「`B.dropLast` でも縮約が起きない」の始末。

なので (b) は

    (convC M)⟦1⟧ = (convC M).dropLast = convC (M.dropLast) = convC (M⟦n⟧)

で片付く。

### (b) 完了（2026-08-26）と、要った 1 つの仮定 `contrOK`

`DbmsStd.lean` に次を追加した（すべて sorry 0）:

```
convC_dropLast_noParent_aux : contrOK M → 末尾列に親がない → 1 < |M| →
  convC (M.dropLast) d plev first force = (convC M d plev first force).dropLast
convC_dropLast_noParent     : 上の、計画書の形（blockok / colOK / descOK / bd ≤ d つき）
reindexD_noParent           : 系。m = 1, n' = n で (conC M)⟦1⟧ = conC (M⟦n⟧)
```

本体は **blockok / colOK / descOK / bd ≤ d を一切使わない**。右端の道の
すべての行き先（`A`, `B`, `Bq`, `Bq = []` のときの `rest2`）は `M` の**接尾辞**なので、
「末尾列に親がない」も仮定 `contrOK` も接尾辞に遺伝する
（`noParent_suffix` / `contrOK_suffix`。前者は `Wset.hasParent_one_iff` /
`hasParent_zero_iff` で行 0・行 1 の親を接尾辞から全体へ持ち上げる）。

**当初の目標（`contrOK` なし）は偽だった。** 反例:

```
M = (2,2)(2,1)(3,2)(3,1)      d = 2, plev = 1, first = true, force = false
blockok 2 M / colOK M / descOK M / bd ≤ d / 末尾 (3,1) に親なし  … 全部成り立つ
convC M            = (2,1)(3,2)(3,1)
(convC M).dropLast = (2,1)(3,2)
convC (M.dropLast) = (2,1)(3,2)(2,1)(3,2)        ← 一致しない
```

これは「梯子あり・縮約あり・`Bq = []` かつ `|rest2| = 1`」の壊れる形そのもので、
末尾列 `(3,1)` の**段が正**なので行 0 の親が立たず、局所の仮定だけでは排除できない
（末尾列の行 0 の祖先は `(2,1)` の 1 つだけで、その段 1 は `< 1` でない）。
計画書の「梯子は `s = 1` でしか立たない」は `force` 経由の道
（節点の段 = 親の段、その引数の頭の段 = +1）を BMS 標準形が禁じることに依るので、
局所の帰納では出せない。そこで局所仮定として切り出したのが

```
def contrOK (M : PairSeq) : Prop :=
  ∀ t p x r, M.drop t = p :: r →
    contrLen p (r.dropWhile (p.1 < ·)) (unitsLen p (r.dropWhile (p.1 < ·)))
      (r.takeWhile (p.1 < ·)) = some ([x], []) → x.2 = 0
```

「縮約が『読み直しの先が 1 列・外の後続が空』で発火するなら、その段は 0」。
実測（`tools/dbms/badcontr.py`、≤9 列）で 49 件すべて段 0 なので成り立つはずで、
**残る仕事は `ST_PS M → contrOK M`**（＝「(0,0)(1,1)(2,1)(3,2) 型が標準形でない」）。
上の反例 `(2,2)(2,1)(3,2)(3,1)` は `contrOK` を破る（`x = (3,1)`, `x.2 = 1 ≠ 0`）。

途中で要った補助（すべて sorry 0）:

```
hasParent_last_append / noParent_suffix   親は接尾辞から全体へ、親なしは全体から接尾辞へ
contrOK_suffix                            contrOK は接尾辞に遺伝
convC_single_ne / convC_dropLast_arg_single   B = [] かつ |A| = 1（梯子が立てば親が立つ）
convC_dropLast_arg'                       convC_dropLast_arg の ih を必要な 2 つに絞った版
contrLen_dropLast_none                    縮約が起きないなら末尾を落としても起きない
```
「親がない」は右端の道を下っても保たれる
（部分列の `nextR` は `nextR_append_right` で全体に持ち上がるので、
全体に祖先がなければ部分列にもない）。

### (c) 親が `Arg` / `B` の中
両側とも `oper_append_of_parent_ge` で局所化して帰納できる。**道具は揃った。**
残る穴はただ 1 つ:

```
BMS の親が B の中  →  |cols ++ convC Arg| ≤ parent (convC M ...) i (末尾)
```

（実測では例外 0。`convC B` の中に「段がより小さい行 0 の祖先」があることを言えばよい。
`nextR` の始点は一意なので、**接尾辞の中に 1 つ証人を出せば**それが親になる
（`parent_ge_of_witness` / `oper_append_of_witness`、証明済み）。

段 0 の場合（`i = 0`）なら「`convC B` の中に末尾より浅い列がある」で足りる。
`convC_getLast_depth` で末尾は深さ `d` より深いとわかるので、
`convC B` の先頭の深さ `ddOf b d s false false` が `d` なら先頭が証人。
`b + 1` になるのは `0 < b ∧ d ≤ b` のときだけで、
`colOK` の `s ≤ bd`、`descOK` の `b ≤ s`、仮定の `bd ≤ d` を合わせると

    s ≤ bd ≤ d ≤ b ≤ s   すなわち   b = d = s = bd ≥ 1

に限られる。つまり**節点が対角の列 `(bd,bd)` で、`B` の先頭もそれと同じ列**という
狭い場合だけが残る。

証人の道具は揃った:

```
nextrel0_ge / nextrel1_ge   親は「浅い列」より後ろ（nextR の最大性）
parent_ge_of_shallow        浅い列 1 つで親の下界
oper_append_of_shallow0     段 0 のとき、接尾辞に浅い列があれば局所化
convC_head_shallow          像の先頭が深さ d なら、それが証人
```

`b = d = s = bd` の場合も含めて `convC_exists_shallow` で片付いた（兄弟の鎖に沿った帰納）。
**場合 (c) の段 0 は `oper_append_convC` で完成**。）

**(c) は段 0（`oper_append_convC`）・段 > 0（`oper_append_convC1`）とも完成。**
(b) は 2026-08-26 に完成、(d) も同日に**段 0 が完成**（`reindexD_node0`）。
残るのは (d) の段 > 0。

### (c) の段 > 0（2026-08-26 完成）

局所化の道具 `oper_append_of_shallow1` はあり、証人も出た。要ったのは:

```
convC_exists_shallow1 :
  B の中に「le0 の鎖の上で段が末尾より小さい列」があれば、
  convC B d plev false false の中にも同じものがある
```

段 0 版（`convC_exists_shallow`）は深さだけで済んだので兄弟の鎖に沿った帰納で
閉じたが、段 > 0 では BMS 側の証人がどこにあるかで分かれる:

```
証人が B の先頭        → 像の先頭が証人（le0 D 0 (|D|-1) を示す必要がある）
証人が兄弟の鎖の中     → 鎖に帰納（le0 は le0_append_right_of で持ち上がる）
証人が引数ブロックの中 → 引数の再帰は first = true なので梯子・縮約が出る ← ここが重い
```

**当初心配した「証人が引数ブロックの中で、末尾は兄弟の中」は起きない。**
理由が**床の補題**である:

```
rtg_lt_of_floor / le0_ge_of_append :
  T の頭の深さが bd、G の列が全部深さ bd 以上なら、
  le0 (G ++ T) k j かつ |G| ≤ j ⟹ |G| ≤ k
```

`blockok bd B` から「B の列は全部深さ bd 以上」、兄弟ブロックの頭は深さちょうど
`bd`。行 0 の辺 `a → b` が `a < |G| ≤ b` をまたぐには
`entry 0 a < entry 0 b ≤ entry 0 |G| = bd ≤ entry 0 a` が要り矛盾する。
だから**末尾が兄弟の中なら証人も兄弟の中**で、右端の道の帰納がそのまま回る。

場合分けは 4 つ:

```
兄弟が空          → 証人は節点の列（梯子なら影 (d,plev)）か引数の中     shallow1_nil
兄弟が続く        → 証人は兄弟の中                                      shallow1_step
縮約あり Bq ≠ []  → 証人は Bq の中
縮約あり Bq = []  → 証人は q か rest2 の中。q のときは q.2 = plev なので
                    像の影の列（index 0）がそのまま証人
```

縮約の `Bq = []` の場合だけ床の補題を 2 回使う（1 回目は深さ `bd` の `q` で、
2 回目は `q` の引数の中で深さ `bd+1` の `rest2` の頭で）。
`pre` の列は全部深さ `bd+1` 以上なので、`pre` から `rest2` へは鎖が入れない。

必要な仮定は **`blockok bd B` だけ**（`colOK` / `descOK` / `bd ≤ d` は要らない）。
Python の全数検査（`blockok` の列 ≤5 列、`d`/`plev` ≤ 3、`bd` ≤ 2）で 2482560 例、違反 0。

### (d) 親がこの段
親が節点そのものなら `G = []` で、`M⟦n⟧` は `M.dropLast` のコピー n 個。
段 0（`d0 = 0`）なら素直な繰り返しなので `convC_run` / `conC_run_top` が使える。
DBMS 側も同じ形にするには

```
D.dropLast = 節点の列 :: (引数の像).dropLast
```

が要り、これは **(b) と同じ「dropLast の可換」** に帰着する。

### (d) の段 0 完了（2026-08-26）

`DbmsStd.lean` に追加（すべて sorry 0）:

```
entry_of_mem        列は添字で読める
getLastD_cons_ne    空でない末尾の getLastD は頭を無視する
convC_getLast_min   末尾列が最浅で段 0 なら、像の末尾列の深さはちょうど d
oper_repeat_root    親が先頭の列で段 0 なら M⟦n⟧ = (replicate n M.dropLast).flatten
conC_cons_zero      conC ((0,0) :: L) = (0,0) :: convC L 1 0 true false（L が全部深いとき）
reindexD_node0      (conC M)⟦n⟧ = conC (M⟦n⟧)
reindexD_node0_shape  ReindexD の形（m = n, n' = n）
```

`reindexD_node0` の仮定は

```
1 < |M|, contrOK M, M.headI = (0,0),
entry M 1 (|M|-1) = 0        … 末尾列の段が 0
nextrel0 M 0 (|M|-1)         … 行 0 の親が先頭の (0,0)
```

道筋:

* BMS 側 … 親が index 0・段 0 なので `d0 = 0`、`oper_repeat` で
  `M⟦n⟧ = (replicate n M.dropLast).flatten`（`oper_repeat_root`）
* 像の形 … `M = (0,0) :: A` で `A` の列は全部末尾列と同じかそれより深いので
  `conC M = (0,0) :: convC A 1 0 true false`（`conC_cons_zero` + `convC_force`）
* DBMS 側の親 … `idx1_conC` で段 0、`convC_getLast_min` で像の末尾列の深さは
  ちょうど 1、`convC_ge'` で他の列は 1 以上、先頭は `(0,0)` なので
  親は index 0。よって `oper_repeat_root` が DBMS 側にもそのまま効く
* `dropLast` の可換 … `A` の末尾列には**親がない**（`A` の列はどれも末尾と
  同じかそれより深いので `entry A 0 j0 < entry A 0 (末尾)` を満たす `j0` がない）。
  だから (b) の `convC_dropLast_noParent_aux` がそのまま使える
  （`contrOK` は `A <:+ M` から遺伝）。`|A| = 1` のときは末尾列の段が 0 なので
  梯子が立たず、像も 1 列
* 仕上げ … `conC_run_top` で `conC ((replicate n ((0,0) :: A.dropLast)).flatten)`
  を `n` 個の塊に割り、両辺が一致

実測（`/tmp` の使い捨てスクリプト、BMS 標準形 ≤8 列）: 場合 (d) の段 0 は 5362 個、
`n = 1,2,3` で `(conC M)⟦n⟧ = conC (M⟦n⟧)` の違反 0（空の場合ではない）。

**残るのは (d) の段 > 0**（`d0 > 0`）。コピーが入れ子になるので
`oper_repeat` が使えず、`shift` regime（末尾列 = `(1,1)`、`m+1`）と
`id` regime が混ざる。

### (d) の段 > 0 の実測（2026-08-26、BMS 標準形 ≤9 列）

親が節点（`nextrel0`/`nextrel1` の始点が index 0）の場合を段で分けて数えた。

```
段 0（idx1 = 0）  33734    ← reindexD_node0 で証明済み
段 > 0（idx1 = 1）64592
```

段 > 0 では**末尾列は必ず `(a, 1)`**（段は必ず 1）で、`d0 = a`。regime は
`a` だけで決まる（≤8 列 9491 個）:

```
lp = (1,1)  a = 1  shift  3922   g = (1, なし, 2, 3)   … n' = n+1（n ≥ 2）
lp = (a,1)  a ≥ 2  id     5569   g = (m)               … n' = n
```

DBMS 側の親は**必ず index 1 の影の列 `(1,0)`**（行 1 で探す）で、
**`d0D = d0`**（≤9 列で例外 0）。つまり

```
conC M      = (0,0) :: X                     X = convC A 1 0 true false, A = M.tail
(conC M)⟦m⟧ = (0,0) :: （X.dropLast を行 0 に k*d0 ずらしたコピー m 個）
M⟦n⟧        = （M.dropLast を行 0 に k*d0 ずらしたコピー n 個）
```

また、場合 (d) では（段 0 でも段 > 0 でも）**根以外の列は全部深さ > 0**
（≤9 列で例外 0）なので `conC_cons_zero` が使える。

### (d) の段 > 0 で済んだこと（2026-08-26）

```
noParent_arg_node1   引数ブロック A = M.tail の末尾列には親がない
convC_dropLast_node1 よって (b) の convC_dropLast_noParent_aux が効き、dropLast が可換
conC_dropLast_node1  conC (M.dropLast) = (conC M).dropLast
```

「`A` に親がない」の理由: `A` の中の親候補は行 0 の鎖ごと `M` に持ち上がる
（`le0_append_right_of`）ので、`nextrel1 M 0 (|M|-1)` の最小性
（`0 < j` かつ `le0 M j (|M|-1)` なら `entry M 1 (|M|-1) ≤ entry M 1 j`）に反する。

### (d) の段 > 0 に残っている壁: **ずれたコピーの補題**

段 0 と違い、コピーは**入れ子になる**。コピー `k` の頭は `(k*d0, 0)` で
深さが増えていくので、コピー `k+1` はコピー `k` の木の中（`convC` の再帰では
どこかの兄弟の位置）に入る。したがって要るのは

```
conC ((range n).flatMap (fun k => (k*a, 0) :: shift0 (k*a) R))
  = (0,0) :: (range n).flatMap (fun k => shift0 (k*a) (convC R 1 0 true false))
      （a ≥ 2、shift0 t L = L.map (fun c => (c.1 + t, c.2))、R = A.dropLast）
```

という「**行 0 を一様にずらしたコピーの並び**」の補題（計画書 §次にやる補題 の 4）。
`M⟦n+1⟧ = M.dropLast ++ shift0 a (M⟦n⟧)` と書けるので `n` の帰納には乗るが、
1 段ぶんが**前置きの因子化** `conC (G ++ X) = P ++ convC X ...` そのもので、
`first = true` の道で縮約が `X` を覗くと崩れる（§証明の骨組み）。
`a = 1`（shift regime）では実際に崩れて、縮約がコピーを 1 つ飲み込む
（`g(m) = m+1` の正体）。**ここが (d) の段 > 0 の唯一の壁。**

### (b)(d) の共通の核: `conC (A.dropLast)` と `conC A`

実測（`tools/dbms/droplast.py`、BMS 標準形 ≤9 列 295013 個）:

```
接頭辞・差 1        289379   可換（求める場合）
接頭辞・差 2          5585   末尾列が梯子を敷く（影の分だけ 2 列長い）
接頭辞でない            49   末尾列を落とすと縮約が消え、像がかえって長くなる
```

**接頭辞性は縮約の場合を除いて必ず成り立つ。** 可換（差 1）になるのは
「末尾列が梯子頭でない」かつ「縮約が消えない」とき。
(b) では前者は自動（梯子頭には親が立つ）。

## 次にやる補題（順に）

1. ~~`convC_getLast_level`~~ **済み**（`DbmsStd.lean`）。系として
   `idx1_conC : idx1 (conC M) ((conC M).length - 1) = idx1 M (M.length - 1)`。
   `oper` がどちらの行で親を探すかが両側で一致する。
2. `conC` の像の親の特徴づけ … 影が親になるのはどういうときか
3. 悪いブロックの対応 … `A = G ++ T` に対する `conC A = P ++ convC T ...` と `jD - off ∈ {0,1}`
4. コピーの対応 … `convC` が「行 0 を一様にずらしたコピーの並び」をどう写すか
5. 4 つの regime を合わせて `ReindexD`

## 検証スクリプト

| | |
|---|---|
| `tools/dbms/reindex.py` | REINDEX の全数検査（≤10 列 2073826 個、違反 0） |
| `tools/dbms/scan_std.py` | 像が DBMS 標準形かの全数走査（≤10 列、違反 0） |
| `tools/dbms/localize.py` | 局所化が DBMS 側で破れることの検査 |
| `tools/dbms/rows2.py` | 変換の参照実装（Lean と同じ） |

## 2026-08-26（続き）: `contrOK` が段 0 で消え、場合 (c) の降下が 4 通りとも揃った

### 1. `contrOK` は段 0 では自動（`contrOK_of_last_zero`）

`contrOK` が問題にする縮約の形 `some ([x], [])` では、`rest2 = [x]` と `Bq = []` から
`r2 = pre ++ [x]` になり、**`x` は `M` の末尾列そのもの**である
（`contr_single_getLast`）。したがって

    entry M 1 (|M|-1) = 0  ⟹  contrOK M

が無条件に出る。これで場合 (b)(d) の局所仮定 `contrOK` は、**末尾列の段が 0 の
場合には完全に消えた**。段 > 0 のためだけに `ST_PS M → contrOK M` が残る。

### 2. 上位の組み立て（`reindexD_holds_of`）

```
reindexD_last_zero   末尾列 = (0,0)                     … (a)、無条件
reindexD_root_zero   段 0 かつ 親が根                    … (d) の段 0、無条件（contrOK 不要）
ReindexD_mid         残り（場合 (c) と (d) の段 > 0）     … 未証明の Prop
reindexD_holds_of : ReindexD_mid → ReindexD
ST_D_conC_holds_of : ReindexD_mid → ∀ M, ST_PS M → ST_D (conC M)
```

標準形では末尾列が `(0,0)` でなければ必ず親がある（`Pair/Column.lean` の `hp_last`）
ので、**上位では場合 (b) は起きない**。

### 3. 場合 (c) の降下（1 段）が 4 通りとも揃った

```
reindexD_descend    因子化 + 両側の局所化 + 帰納法の仮定 → 1 段
reindexD_step_gen   降下の統一形（因子化の条件 P を引数に取る）
reindexD_arg_nolad  梯子なしで引数へ
reindexD_arg_lad    梯子つきで引数へ（兄弟が空なので縮約は起こりようがない）
reindexD_sib_nolad  梯子なしで兄弟へ
reindexD_sib_lad    梯子つきで兄弟へ（その段で縮約が起きないことを仮定）
```

要った道具（すべて sorry 0）:

```
oper_headI / oper_depth_gt      展開は先頭列を変えず、列を深くしかしない
hasParent1_of_exists            行 1 版の親の存在（証人の最大元が親）
idx1_convC                      idx1_conC の一般版
convC_factor_sib / _arg         梯子なしの因子化（前置き C は T に依らない）
convC_factor_sib_lad / _arg_lad 梯子つきの因子化
contrLen_nil                    contrLen p [] k A = none
convC_exists_shallow_gen        段 0 の証人（first/force が一般）
oper_append_convC_gen           段 0 の局所化（first/force が一般）
oper_append_convC_auto / 1_auto 親の存在も証人から作るので仮定に要らない
```

**要点**: 梯子が立つのは `first = true` の段（根と引数ブロックの頭）だけで、
そこで縮約が発火するには兄弟が空でないことが要る。引数へ降りる段では兄弟が空なので
`contrLen p [] k A = none` により縮約は起こりようがない。したがって
**縮約が邪魔をするのは「梯子つきで兄弟へ降りる段」だけ**である。

### 4. 降下が止まる場合（ブロック版）

```
reindexD_succ_gen        末尾が (0,0)（深さ 0 のブロック）      … (a)
reindexD_noParent_gen    末尾列に親がない（contrOK つき）       … (b)
reindexD_noParent_zero   同上、段 0 なら仮定なし
```

### 5. 残っていること

1. **場合 (d) のブロック版（節点が親）**。いまあるのは根での段 0
   （`reindexD_node0`）だけ。ブロック版には「コピーの補題」が要る:

   ```
   convC ((replicate n (p :: R)).flatten) d plev true force = ?
   ```

   `convC_run` は `first = false` 版しかない。`first = true` では最初のコピーだけ
   梯子・`force` を受け取るので、影の列 1 本ぶんずれる（これが shift regime）。
   段 0 でも、引数への `force = first && (p.2 == plev)` が最初のコピーだけ
   `true` になりうるので、素直な `convC_run` では閉じない。

2. **右端の道に沿った帰納の組み立て**。1 段の降下 4 通りと止まる場合 3 通りは
   揃ったので、残るのは
   * 節点ごとの場合分け（親が節点／引数の中／兄弟の中）
   * 「末尾が兄弟の中なら親は引数の中にない」（床の補題 `le0_ge_of_append` の適用）
   * `blockok` / `colOK` / `descOK` / `bd ≤ d` / `hz` の不変量の引き回し
   * 添字の変換（ブロック内の添字 ↔ 全体の添字）

3. **梯子つきで兄弟へ降りる段の縮約**（`reindexD_sib_lad` の仮定 `hnc`）。
   実測では ≤10 列で 180 個だけの `contr` regime に対応する。

4. **`ST_PS M → contrOK M`**（段 > 0 のためだけに要る）。
   `r1ok` では出ない（`x.2 ≤ q.2 + 1` しか言えず、`x.2 = 0` は出ない）ので、
   BMS 標準形のもっと強い性質が要る。

## 2026-08-26（続き 2）: 右端の道の帰納が閉じ、`ReindexD` は残り 2 つの Prop に

### 到達点

```
reindexD_holds_of_res : RDzeroRes → RDposRes → ReindexD
ST_D_conC_holds_of_res : RDzeroRes → RDposRes → ST_PS M → ST_D (conC M)
```

**右端の道に沿った帰納（計画書の「組み立て」）は完全に閉じた。**
場合分け・不変量の引き回し・添字の変換・床の補題の適用は全部済み。
残っているのは局所の 5 つの事実だけで、それを 2 つの `Prop` に括り出してある。

### 新しく証明したもの（すべて sorry 0）

場合 (d) のブロック版（段 0）:

```
convC_run_first        最初のコピーだけ first/force を受け取る繰り返し（梯子なし）
reindexD_node0_gen / _shape      梯子なし版（hfr: 引数への force が立たない）
oper_repeat_at         親の位置が一般の oper_repeat（梯子の段では親が index 1）
unitsLen_replicate     同じブロックの並びはユニットで埋め尽くされる
contrLen_of_drop_nil   だから縮約は起きようがない
convC_dropLast_min     末尾列が最浅・段 0 なら dropLast は像と可換
convC_run_lad          梯子つきの繰り返し（d = p.2 のとき）
reindexD_node0_lad / _shape      梯子あり版
```

`convC_run_lad` の `d = p.2` は、`colOK`（`p.2 ≤ p.1`）・`blockok bd`（`bd = p.1`）・
`bd ≤ d` と梯子の条件 `d ≤ p.2`（`force = false` の道）を合わせると

    p.1 ≤ d ≤ p.2 ≤ p.1     すなわち     d = p.2 = p.1 = bd

として自動的に出る（組み立ての中でそう使っている）。

組み立て:

```
dropWhile_head_not     dropWhile の先頭は述語を満たさない
RDzeroRes (def)        段 0 で残っている 2 つの場合
reindexD_zero_block    段 0 のブロック版の帰納
reindexD_zero          段 0 の入口（標準形 → conC）
ReindexD_pos (def)     段が正の場合
reindexD_holds_of_zero : RDzeroRes → ReindexD_pos → ReindexD
RDposRes (def)         段が正のときに残っている 3 つの場合
reindexD_pos_block     段 > 0 のブロック版の帰納
reindexD_pos_of        : RDposRes → ReindexD_pos
reindexD_holds_of_res / ST_D_conC_holds_of_res
```

### 段 0 の帰納（`reindexD_zero_block`）

`B = p :: (A ++ T)`（`A` = 引数ブロック、`T` = 兄弟ブロック）で場合分けする。

```
|B| = 1              段 0 なら梯子が立たないので像も 1 列、両側とも動かない
末尾列 = (0,0)        (a) reindexD_succ_gen（bd = 0 ⟹ d = 0 の不変量が要る）
親がない              (b) reindexD_noParent_zero（contrOK は段 0 で自動）
T = [] かつ 親 = 節点  (d) reindexD_node0_gen / reindexD_node0_lad
T = [] かつ 親 ∈ A    (c) reindexD_arg_nolad / reindexD_arg_lad で降りる
T ≠ []               親は必ず T の中（下の理由）→ reindexD_sib_nolad / _lad
```

`T ≠ []` で親が `p` や `A` に入れない理由（行 0 なので床の補題は要らない）:
親があるなら `entry B 0 (親) ≥ bd` と `entry B 0 (親) < entry B 0 (末尾)` から
`entry B 0 (末尾) > bd`。ところが `T` の頭は深さ `≤ bd` で末尾より手前（または
末尾そのもの）なので、`nextrel0` の最小性に反する。

不変量は `blockok bd B`, `colOK B`, `descOK B`, `bd ≤ d`, `bd = 0 → d = 0`,
`entry B 1 (|B|-1) = 0` の 6 つ。最後から 2 番目は (a) のために要る
（深さ 0 の列があるブロックは根のブロックしかなく、そこでは `d = 0`）。

### 段 > 0 の帰納（`reindexD_pos_block`）

不変量は `blockok`, `colOK`, `descOK`, `bd ≤ d`, `2 ≤ |B|`,
`0 < entry B 1 (|B|-1)`。`2 ≤ |B|` が要るのは、**1 列のブロックで梯子が立つと
ブロック単位の主張が偽になる**から（像が `[(d,plev),(d+1,p.2)]` の 2 列になり、
その基本列は元に戻らない）。降りる先は必ず 2 列以上なので不変量は保たれる:

* 引数へ降りるのは `1 ≤ 親 < |A|` のときなので `|A| ≥ 2`
* 兄弟へ降りるのは `|p::A| ≤ 親 < |A|+|T|` のときなので `|T| ≥ 2`

**`T ≠ []` なら親は必ず `T` の中**。これが床の補題 `le0_ge_of_append` の出番で、
`G = p :: A` の列は全部深さ `bd` 以上、`T` の頭はちょうど `bd` なので、
行 0 の鎖は `G` と `T` の境をまたげない。`nextrel1` は `le0` を含むので
行 1 の親にもそのまま効く。

### 残っている 5 つ

```
RDzeroRes（段 0、2 つ）
  1. 梯子つきの段で縮約が起こりうる           contr regime（実測 ≤10 列で 180 個）
  2. 場合 (d) で force か first && (p.2 == plev) が立っている

RDposRes（段 > 0、3 つ）
  3. 梯子つきの段で縮約が起こりうる           同上
  4. 親がない                                contrOK B が要る（段 0 では自動）
  5. 親が節点                                ずれたコピーの補題が要る（shift regime）
```

**2 と 4 は同じ BMS 標準形の事実に帰着する。** すなわち

    節点の段 = その親の段（`p.2 = plev`）かつ その引数ブロックの頭の段 = `p.2 + 1`

という形は BMS 標準形に現れない（`(0,0)(1,1)(2,1)(3,2)` 型）。
これが言えれば、2 では `convC_force`（`force` は効かない）が使え、
4 では `contrOK` が出る（縮約が `some ([x],[])` で発火するには梯子が要り、
梯子が立つには上の形が要る）。

**5 が唯一の新しい計算**である。段 0 と違いコピーが入れ子になるので

```
conC ((range n).flatMap (fun k => (k*a, 0) :: shift0 (k*a) R))
  = (0,0) :: (range n).flatMap (fun k => shift0 (k*a) (convC R 1 0 true false))
```

という「行 0 を一様にずらしたコピーの並び」の補題が要る（§(d) の段 > 0 の壁）。

**1 と 3 は同じ**（`reindexD_sib_lad` の仮定 `hnc`）。

## 2026-08-26（続き 3）: BMS 標準形の局所的な事実を証明、`RDposRes` は偽と判明

### 1. 証明したもの（`DbmsStd.lean`、sorry 0、`leanman check` exit 0）

```
adj3 / noAdj3          隣り合う 3 列の禁止形（深さ狭義増加・中の段 = 左の段・右の段 = 中の段 + 1）
noAdj3_of_agree        列が一致する短い列に遺伝
noAdj3_take            接頭辞に遺伝
noAdj3_diagSeq         対角には現れない
entry1_last_le_of_lt   末尾の直前が浅ければ行 0 の親 → nextrel1 の最小性
noAdj3_ST_PS           ★ BMS 2 行標準形には禁止形が現れない
noAdj3_infix           連続部分列に遺伝
headPatOK / argPatOK   ブロック版の言い換え（各節点で「子の段 = 自分の段 ⟹ 孫の段 ≠ 子の段 + 1」）
argPatOK_of_noAdj3     noAdj3 → argPatOK
argPatOK_ST_PS         ★ 標準形は argPatOK
convC_force_head       force が効かない条件を頭の列だけに弱めた版（convC_force の一般化）
convC_arg_force_eq     headPatOK があれば引数へ渡る force は効かない
```

`noAdj3_ST_PS` が計画書で「BMS 標準形のより強い性質」と書いていたものである。
これは
「節点の段 = その親の段 かつ その引数ブロックの頭の段 = 節点の段 + 1」
（`(0,0)(1,1)(2,1)(3,2)` 型）の**隣接による言い換え**で、
節点が引数ブロックの頭なら親は直前の列・その引数ブロックの頭は直後の列だから
純粋に局所的な形になる。

証明は `oper` についての帰納（`oper_bad_blocks` の `copyExp` 分解を使う）:

* コピーの内側では行 0 が一様にずれるだけなので形がそのまま元の行列に移る
* `Pred` の枝は接頭辞なので `noAdj3_take`
* コピーの境をまたぐ形は、いずれも
  「`entry M 0 (j1-1) < entry M 0 j1` ⟹ `nextrel0 M (j1-1) j1` ⟹ `le0`
  ⟹ `nextrel1` の最小性で `entry M 1 j1 ≤ entry M 1 (j1-1)`」
  と `entry M 1 j0 < entry M 1 j1` の矛盾で潰れる（`d0 = 0` の枝は
  `∀ x ∈ R, v0 < x.1` だけで潰れる）
* ブロックが 1 列のときは行 1 が全部 `w0` なので「+1」になれない

実測: ≤10 列 2073826 個で違反 0。

### 2. **`RDposRes` は偽**（重要）

`DbmsStd.lean` の `RDposRes` はそのままでは証明できない。反例:

```
B = (1,1)(2,2)(2,1)(3,2)(3,1)      bd = 1, d = 1, plev = 1, first = true
```

`blockok 1 B`, `colOK B`, `descOK B`, `bd ≤ d`, `p.1 = bd`, `2 ≤ |B|`,
`0 < entry B 1 (|B|-1)` をすべて満たし、末尾列 `(3,1)` に行 1 の親がない
（段が 0 の列がない）ので残余条件 `¬ hasParent` も満たす。ところが

```
convC B 1 1 true force  = (2,1)(3,1)(4,2)(4,1)          （4 列）
B⟦n⟧ = (1,1)(2,2)(2,1)(3,2)  （n に依らない）
convC (B⟦n⟧) 1 1 true force = (2,1)(3,1)(4,2)(3,1)(4,2) （5 列）
```

で、左辺の末尾 `(4,1)` にも行 1 の親がないから `(convC B)⟦m⟧` は
`dropLast` で 3 列になるしかなく、5 列には決してならない。

**この反例は `headPatOK B plev` が偽であることで排除される**:
`p.2 = 1 = plev` なのに引数ブロックの頭 `(2,2)` の段が `p.2 + 1 = 2`。
つまり `noAdj3` で禁じた形そのものである。

同じことが `contrOK` でも起きる。標準形の中の「親なし・末尾の段 > 0」の
ブロック 64419 個（≤8 列）のうち **142 個で `contrOK` が破れる**
（例: `(4,4)(4,3)(5,4)(5,3)`）。したがって
「段 > 0 では `ST_PS M → contrOK M`」は**偽**で、
`convC_dropLast_noParent_aux` の仮定は
「実際に梯子が立つ位置でしか縮約を見ない」形に弱める必要がある。

### 3. 次にやること

1. `reindexD_pos_block` / `reindexD_zero_block` を、不変量に
   `first = true → headPatOK B plev` と（遺伝のための）`argPatOK B` を足して
   作り直す。引数ブロックへ降りるときの `headPatOK A p.2` は
   `argPatOK_cons` の第 1 成分そのもの、兄弟ブロックは `first = false` なので
   要らない（`force` は `first = false` の枝では立たない）。
   根だけは `d = 0 ≤ plev + 1` なので `convC_force` で片付く。
2. `RDposRes` / `RDzeroRes` を上の不変量つきに書き直す
   （いまの形は偽なので `reindexD_holds_of_res` の仮定は充足できない）。
3. `reindexD_node0_gen` の `hfr` を `convC_arg_force_eq` で消した版を作る（場合 (d) の `force`）。
4. `convC_dropLast_noParent_aux` の `contrOK` を梯子つきの位置だけに弱める（段 > 0 の場合 (b)）。
5. 場合 (d) の段 > 0（ずれたコピーの補題、shift regime）と、
   梯子つきの段の縮約（`reindexD_sib_lad` の `hnc`）は手つかずのまま。

### 4. 検証スクリプト（このセッションで使ったもの）

| | |
|---|---|
| 禁止形の全数走査 | `rows2.gen('BMS',10)` の 2073826 個で違反 0 |
| `RDposRes` の反例探索 | ブロックを全列挙して `(convC B)⟦m⟧ = convC (B⟦n'⟧)` を探索（≤5 列） |
| `contrOK` の反例 | 標準形の全ブロックで `contrLen … = some ([x],[])` を検査 |

## 2026-08-26（検証）: 現状のまとめ

`leanman check -m verify -C lean DbmsStd.lean` は **exit 0（green）**、`sorry` は 0、
`#print axioms` は全部 `[propext, Classical.choice, Quot.sound]`（`sorryAx` なし）。
`DbmsStd.lean` は 5587 行。

### いま証明できている一番強い形

```
ST_D_conC_holds_of_res : RDzeroRes → RDposRes → ∀ M, ST_PS M → 1 < |M| → ST_D (conC M)
```

つまり **`ReindexD` は条件つきでしか出ていない**。無条件の `reindexD_holds` は未証明で、
しかも現在の `RDposRes` はそのままでは**偽**（反例 `B = (1,1)(2,2)(2,1)(3,2)(3,1)`、
「続き 3」参照）。ただしその反例は今回証明した `headPatOK` / `noAdj3_ST_PS` で
排除されるので、直し方は分かっている。

### 残り作業（優先順）

1. `reindexD_zero_block` / `reindexD_pos_block` の不変量に
   `argPatOK B` と `first = true → headPatOK B plev` と
   `force = true → (B.headI).2 ≠ plev + 1` を足した**新しい版**を書く
   （`DbmsStd.lean` は追記のみなので既存版は残したまま別名で作る）。
   これに合わせて `RDzeroRes` / `RDposRes` も書き直す。道具は全部揃っている:
   引数ブロックへ降りるときの `headPatOK` は `argPatOK_cons` の第 1 成分、
   兄弟ブロックは `first = false` なので `force` が立たず不要、
   根は `d = 0 ≤ plev + 1` で `convC_force`。各 200 行程度の機械的な作業。
2. `convC_dropLast_noParent_aux` の仮定 `contrOK` を「梯子が実際に立つ位置でしか
   縮約を見ない」形に弱める（段 > 0 の場合 (b)）。
   **`ST_PS M → contrOK M` は偽**（標準形 ≤8 列の「親なし・段 > 0」ブロック 64419 個中
   142 個が反例、例 `(4,4)(4,3)(5,4)(5,3)`）なので、この弱化は避けられない。
3. **ずれたコピーの補題**（場合 (d) の段 > 0、shift regime）:

   ```
   conC ((range n).flatMap (fun k => (k*a, 0) :: shift0 (k*a) R))
     = (0,0) :: (range n).flatMap (fun k => shift0 (k*a) (convC R 1 0 true false))
   ```

   `a = d0 ≥ 2`、`R = A.dropLast`。段 0 と違いコピーの頭の深さが増えるので
   コピー `k+1` はコピー `k` の木の中（兄弟の位置）に入る。
   `M⟦n+1⟧ = M.dropLast ++ shift0 a (M⟦n⟧)` なので `n` の帰納には乗るが、
   1 段ぶんが前置きの因子化 `conC (G ++ X) = P ++ convC X …` そのもので、
   `first = true` の道で縮約が `X` を覗くと崩れる。
4. **梯子つきの段で縮約が起こる場合**（`reindexD_sib_lad` の仮定 `hnc`、contr regime）。
   実測では ≤10 列 2073826 個のうち 180 個だけ。

### 実測の裏づけ（すべて違反 0）

| | |
|---|---|
| `ReindexD` 本体（`tools/dbms/reindex.py`） | 標準形 ≤10 列 2073826 個 |
| 禁止形 `noAdj3`（`rows2.gen('BMS',10)`） | 同上 |
| 場合 (c) の証人の存在 | `blockok` ブロック ≤5 列、`d`/`plev` ≤ 3、`bd` ≤ 2 で 2482560 例 |
| 場合 (d) の段 0 の可換性 | 標準形 ≤8 列の該当 5362 個、`n = 1,2,3` |

## 2026-08-26（続き 4）: 段 > 0 の帰納を不変量つきで作り直し、残余は 3 つ（すべて真）

### 到達点

```
reindexD_pos_block2 : RDlad2 → RDnopar → RDnode → （ブロック版の帰納・不変量つき）
reindexD_pos_of2    : CtrRes → RDlad2 → RDnopar → RDnode → ReindexD_pos
reindexD_holds_of_res2  : CtrRes → RDzeroRes2 → RDposRes2 → ReindexD
ST_D_conC_holds_of_res2 : 同上 → ST_PS M → ST_D (conC M)
```

`RDposRes2 = RDlad2 ∧ RDnopar ∧ RDnode`。**旧 `RDposRes` は偽だったが、
新しい 3 つはすべて全数検査で反例 0**（下の表）。`leanman check` は exit 0、`sorry` 0。

### 段 0 でなかった不変量が 3 つ要った

段 0 側（`reindexD_zero_block2`）の `argPatOK` / `hpOK` / `fOK` だけでは足りない。
全数検査で反例を出しながら次の 3 つを足した:

| 不変量 | これが無いときの反例 |
|---|---|
| `adjLev M`（隣で深さが 1 上がるなら段は高々 +1。`r1ok` の隣接版） | `B = (1,0)(2,2)`, `d = 1`（場合 (d) が 872 件壊れる） |
| `dpOK bd d plev first`（`d = bd` なら `plev = 0` か `plev + 1 < bd`） | `B = (2,2)(2,1)(3,2)(3,1)`, `d = 2`, `plev = 1`（梯子・親なしの両方） |
| `hcOK B plev first`（`ctrHeadOK`: 縮約の前置きが揃えば縮約は必ず発火する） | `B = (1,1)(1,0)(2,1)(2,1)`, `d = 1`, `plev = 0`, `first`（梯子つき兄弟） |

* `adjLev` は `r1ok_ST_PS` から**証明済み**（`adjLev_of_r1ok` / `adjLev_ST_PS`）。
  連続部分列に遺伝する（`adjLev_infix`）。
* `dpOK` は `ddOf` の場合分けだけで伝播する（`dpOK_arg`）。根では自明。
* `ctrHeadOK` だけ BMS 標準形の性質として未証明なので `CtrRes` に括り出した。

### `CtrRes`（新しい残余）

```
def CtrRes : Prop := ∀ {M : PairSeq}, ST_PS M → argCtrOK M
```

`argCtrOK` は「どの**引数ブロックの頭** `p` でも、その段が親の段 + 1 なら
`ctrHeadOK` が成り立つ」という再帰的な述語（`argPatOK` と同じ形）。
`ctrHeadOK B plev` は `contrLen' = contrLen`、すなわち

    縮約の前置き `contrPre p U A` が兄弟 `q`（`q.2 + 1 = p.2`, `q.1 = p.1`）の
    引数ブロックの接頭辞と一致し、その直後の列の深さが `p.1 + 1` なら、
    その列の段は必ず `p.2` より小さい（＝縮約が本当に発火する）

**引数ブロックの頭に限る**のが要点。無条件版（全部の節点で `ctrHead`）は**偽**で、
≤7 列の標準形 7256 個中 21 個が反例（例 `(0,0)(1,1)(2,1)(1,1)(1,0)(2,1)(2,1)`。
この反例のブロックは兄弟の位置＝`first = false` にしか現れない）。

`CtrRes` は `Pair/ArgDom.lean` の `argDomCoreOn_ST_PS` から出るはずである。
実際、`(u,w)` を `p` の親、`(u+e,w)` を `q`（`e = 1`）に取ると `A1 = p :: A ++ U` で
`contrPre p U A = shiftr0 1 A1` なので、`sle B (shiftr0 1 (A1 ++ q :: (B ++ A2)))` は
前置き `pre` の直後で `rest2.headI ≤ (p.1+1, p.2-1)` を強いる。これがちょうど
「段が下がる」である。列で比べる `sle` から取り出す作業が残っている。

### 残っている 4 つ（すべて真、実測で確認済み）

| | 内容 | 実測 |
|---|---|---|
| `CtrRes` | BMS 標準形は `argCtrOK` | 標準形 ≤9 列 295014 個で違反 0 |
| `RDzeroRes2` | 段 0・梯子つきの段での縮約 | ブロック ≤5 列 `bd ≤ 2` の 6374 例で反例 0 |
| `RDlad2` | 段 > 0・梯子つきで兄弟へ降りる段での縮約（contr regime） | 710 例で反例 0 |
| `RDnopar` | 段 > 0・末尾列に行 1 の親がない（弱めた `contrOK`） | 77950 例で反例 0 |
| `RDnode` | 段 > 0・末尾列の親が節点（shift regime、ずれたコピーの補題） | 14827 例で反例 0 |

`contrPre_eq_shiftr0`（`contrPre p U A = shiftr0 1 (p :: (A ++ U))`）は証明済み。

（`RDlad2` / `RDnopar` / `RDnode` の実測はブロック ≤5 列・`bd ≤ 2`・`plev ≤ 3`、
`d` は `bd`〜`bd+2`、`first` / `force` は両方。検査は `∃ m ≤ 14, ∃ n' ≤ n+5` で
`n = 1,2,3` について。スクリプトは会話中の `check4.py` / `checkzero.py`。）

広げた検査も反例 0: ≤6 列・`bd ≤ 1`（node 45555 / nopar 91230 / poslad 5062 / zero2 9150）、
≤5 列・`bd ≤ 3`・`plev ≤ 4`（node 34471 / nopar 360839 / poslad 710 / zero2 1302）。

「本当に偽ではないか」の対照実験もした。**`parPatOK`**（行 0 の親の段が自分と同じ節点は
引数の頭の段が自分 + 1 にならない = `noAdj3` を親が隣でない場合に広げたもの）は
`ctrHeadOK` の代わりになりそうに見えるが**偽**で、≤7 列 7256 個中 567 個が反例。
`ctrHead` を全部の節点に課す版（引数ブロックの頭に限らない版）も**偽**で 21 個が反例。
だから `argCtrOK`（引数ブロックの頭だけ・段が親 + 1 のときだけ）がちょうどの強さである。

さらに「標準形の右端の道の全節点でブロックの主張が成り立つ」ことも直接確かめた:
標準形 ≤8 列 44653 個の右端の道の節点 115244 個（重複除去）で破れ 0。

### 要らなかった不変量

`hlOK`（頭の段 ≤ 親の段 + 1）、`plev ≤ d`、`d ≤ bd + 1` はどれも真で伝播もするが、
残余を真にするのには不要だったので入れていない（抜き差しの実験で確認）。

### 次にやること

1. **`CtrRes` を `ArgDomCore` から証明する**（いちばん大きい残り）。
2. `RDnode`（shift regime、ずれたコピーの補題）。
3. `RDnopar`（`convC_dropLast_noParent_aux` の `contrOK` を梯子の位置だけに弱める）。
4. `RDzeroRes2` / `RDlad2`（梯子つきの段での縮約）。


## 2026-08-26（続き 8）: `RDnode` の道具立て。regime を実測で確定

`RDnopar` は続き 7 で証明済み（`rdNopar`）。このセッションはその green を確認した
うえで、残る 2 つの残余のうち **`RDnode`（段 > 0・末尾列の親が節点）** の道具を作った。
`leanman check` は exit 0、`sorry` 0、`sorryAx` なし。

### 追加した定理（すべて `DbmsStd.lean` 末尾、branch dbms）

| commit | 定理 | 内容 |
|---|---|---|
| 7cde883 | `range'_map_entry_shift` / `oper_tower` / `rdNode_bms_shape` | 末尾列の行 1 の親が頭（index 0）なら `M⟦n⟧ = copies d0 M.dropLast n`（`copies` は `Pair/Cnf.lean`）。段 0 の `oper_repeat_root`（`d0 = 0`）の一般化 |
| b9db6a2 | `lad_false_of_two_le` / `convC_append_tail` | 「`M` のうしろに深さ `ν` で始まるブロック `Z` を継ぎ足しても `M` の像は変わらず、`Z` の像は `Z` に依らない `(d', plev', first', force')` で書ける」 |
| a22d584 | `takeWhile_append_head` / `headPatOK_prefix` / `blockok_prefix` / `argPatOK_prefix` | 不変量が接頭辞に遺伝する（`R = A.dropLast` に上を当てるため） |
| 73ef145 | `levLt` / `lad_false_of_levLt` / `ddOf_of_levLt` / `convC_depth_shift` | **`convC` は深さパラメタの平行移動に共変**（跳ばない範囲で） |
| 300f0c9 | `oper_tower_at` | 一般の位置での階段（`oper_repeat_at` の段 > 0 版） |
| 52ea717 | `convC_append_tail_shift` | 上の継ぎ足しの「`d` を `E` ずらすと `d'` も `E` ずれるだけ」版 |

### `convC` の平行移動共変性（いちばん再利用できる）

`ddOf s d plev first force = if lad then d+1 else if (0 < s ∧ d ≤ s) then s+1 else d` の
**まん中の枝（段へ跳ぶ）だけが絶対的な深さを書く**ので、平行移動をこわすのはそこだけ。

```
levLt M d : M ≠ [] → (M.headI).2 < d      -- 頭の段 < 深さ（跳ばない）
convC_depth_shift : blockok / colOK / adjLev / descOK / levLt M d / argPatOK /
                    hpOK / fOK ⟹ convC M (d+e) plev first force
                                  = shiftr0 e (convC M d plev first force)
```

`levLt` が再帰で保たれるのは
* 引数は深さ `d+1`、頭の段は `adjLev` から「親の段 + 1」以下
* 兄弟は深さ `d`、頭の段は `descOK` から「親の段」以下

だから。さらに `fOK` があると `d ≤ s` が偽なので梯子も立たない（`lad_false_of_levLt`）。
跳ぶのは **`c = (bd, bd)` かつ `d = bd`（対角の節点でぴったり）** のときだけである。

### `RDnode` の regime（実測で確定）

`B = p :: A`（`T = []`）、`W = B.dropLast = p :: R`（`R = A.dropLast`）、
`lp = A` の末尾、`ν = lp.1`、`d0 = ν - p.1 ≥ 1`、`dd = ddOf p.2 d plev first force`。
BMS 側は `B⟦n⟧ = copies d0 W n`（`rdNode_bms_shape`）。像について

```
convC (B⟦n⟧) d plev first force = copies e (convC W d plev first force) n      … (★)
```

が成り立つかを、ブロック ≤5 列・`bd ≤ 2`・`plev ≤ 2`・不変量つきの 5051 組で全数検査した
（`tools/dbms/node_regime.py`）。結果は**きれいに一致**する:

| 条件 | 件数 | (★) |
|---|---|---|
| `ladOf p.2 d plev first force = false` かつ `levLt R (dd+1)` | 4919 | **成立** |
| `levLt R (dd+1)` が偽（＝ `bd = 0, p = (0,0), d = 0, R.headI = (1,1)`） | 180 | 不成立（縮約 regime） |
| `ladOf p.2 d plev first force = true` | 152 | 不成立 |

* **正則 regime**（`(★)` が成り立つ）: `m = n` で `(convC B)⟦m⟧ = convC (B⟦n⟧)` になる。
  DBMS 側の親は index 0、`(convC B).dropLast = convC W`、ずれは同じ `e`。
* **縮約 regime**: `p = (0,0)`・`R.headI = (1,1)` で `R` の頭に梯子が立ち、
  2 個目以降のコピーで `contrLen` が発火してコピーを 1 つ食う（`m = n - 1`）。
  例 `B = (0,0)(1,1)(2,2)(1,1)`, `d = plev = 0`:
  `convC (B⟦3⟧)` は 9 列（`B⟦3⟧` は 12 列）。
* **梯子 regime**: `p = (1,1)`・`bd = d = 1`・`plev = 0`・`first = true`（`lad_diag`）。

### 正則 regime の証明の筋（次のセッション用）

`copies_succ_front`（`Pair/Cnf.lean`）から `copies d0 W (n+1) = W ++ shiftr0 d0 (copies d0 W n)`、
すなわち `B⟦n+1⟧ = p :: (R ++ Z_n)`、`Z_n := shiftr0 d0 (copies d0 W n)`。
`Z_n` は深さ `ν` 以上・頭の深さちょうど `ν` なので `convC_append_tail_shift` が使えて

```
convC (B⟦n+1⟧) (d+E) plev first force
  = [(dd+E, p.2)] ++ convC R (dd+1+E) p.2 true φ ++ convC (copies d0 W n) (d'+E) plev' first' force'
                                                    （最後は convC_shiftr0）
```

（`φ = first && (p.2 == plev)`）。あとは

1. `Ψ(n) := convC (copies d0 W n) d' plev' first' force'` が `shiftr0 e (Φ(n))` であること
   （`e := dd' - dd`）。`n` についての帰納で、頭の 1 列は `ddOf` の差、残りは
   `convC_depth_shift`（`R` について）と帰納法の仮定でつく。
2. そのために `(d', plev', first', force')` が「同じ種類のパラメタ」に留まること。
   実測（`tools/dbms/node_params.py`、正則 regime の 4919 組）では

   ```
   ν ≤ d'                                              4919/4919
   first' ∧ (p.2 = plev')  ⟹  R = [] ∨ R.headI.2 ≠ p.2+1   例外 0
   ```

   後者はちょうど「`Z` の側の `hpOK` / `fOK`」で、**`convC_append_tail_shift` の結論に
   `ν ≤ d'` と この 2 つを付け足せば**帰納が回る見込み。導出には
   `argPatOK (M ++ Z)`（＝ 階段の `argPatOK`）が要りそうで、
   「不変量が `copies` で保たれる」補題群（`blockok` / `colOK` / `adjLev` / `descOK` /
   `argPatOK`）を作るのが素直。`blockok` の継ぎ目は `steps1 B` から
   `ν ≤ W.getLast.1 + 1`、`adjLev` の継ぎ目は `p.2 < lp.2 ≤ W.getLast.2 + 1` で出る。
3. DBMS 側: `convC B = convC W ++ convC [lp] d' plev' first' force'` なので
   `(convC B).dropLast = convC W`（末尾の像が 1 列のとき）。
   末尾列の行 1 の親が index 0 であること（`nextrel1 (convC B) 0 (len-1)`）を示せば
   `oper_tower_at` で `(convC B)⟦m⟧ = copies e (convC W) m` になり、`m = n` で一致する。

### 追加した検査スクリプト

| | |
|---|---|
| `tools/dbms/node_copies.py` | `(★)` を `e` を探しながら全数検査 |
| `tools/dbms/node_regime.py` | `(★)` が成り立つ regime の特定（上の表） |
| `tools/dbms/node_params.py` | `convC_append_tail` の `(d', plev', first', force')` を再現して段 1 のフラグを見る |

## 2026-08-26（続き 7）: `CtrRes` と `RDnopar` を証明。残余は 2 つ

### 到達点

```
reindexD_holds_of_res9  : CtrPres2 → RDnode → ReindexD
ST_D_conC_holds_of_res9 : 同上 → ST_PS M → ST_D (conC M)
```

`leanman check` は exit 0、`sorry` 0、`sorryAx` なし。`DbmsStd.lean` は 11966 行。

| | 状態 |
|---|---|
| `CtrRes`（BMS 標準形は `argCtrOK`） | **証明した**（`ctrRes_holds`） |
| `RDnopar`（段 > 0・末尾列に行 1 の親がない） | **証明した**（`rdNopar`） |
| `CtrPres2`（縮約が発火しない状態は展開で保たれる） | 残余（場合 2b が未確定） |
| `RDnode`（段 > 0・末尾列の親が節点＝ずれたコピー） | 残余 |

### `CtrRes` は `ArgDomCore` の 1 発

`ctrHeadOK` の中身は「縮約の前置きが揃えば、その次の列の段は必ず下がる」。
節点 `c = (u, w)` の引数ブロックの頭を `p` とすると、`ctrHeadOK` の仮定は
`p.2 = w + 1`、`steps1` から `p.1 = u + 1`。縮約の前置きが揃うとは
「兄弟 `q = (u+1, w)` の引数が `contrPre p U A = shiftr0 1 (p :: (A ++ U))` で始まる」。

ここで **`c` と `q` は行 1 の値が同じ `w` で、深さが `u` と `u+1`（`e = 1`）**。
間の列 `A1 = p :: (A ++ U)` はすべて深さ `≥ u+1` なので `SpineOK A1 (u+1) w` は空虚。
したがって `ArgDomCore`（`Pair/ArgDom.lean` の `argDomCore_holds`、証明済み）が

```
sle (q の引数) (shiftr0 1 (A1 ++ q :: (q の引数 ++ A2)))
```

を与える。`shiftr0 1 A1 = contrPre p U A`（`contrPre_eq_shiftr0`）なので、
共通の前置き `pre` を `seqlex_append_cancel` で消すと

```
sle rest2 ((u+2, w) :: …)
```

が残る。`rest2` の頭の深さは `p.1 + 1 = u+2` なので列辞書式順序から段は `w` 以下、
`p.2 = w + 1` より `(rest2.headI).2 < p.2`。これが `ctrHeadOK`。

追加した定理: `contrLen'_spec`、`contrLen_eq_of_head_lt`、`ctrHead_lt_core`、
`ctrHeadOK_arg_of_ST`、`argCtrOK_of_nodes`、`ctrRes_holds`。

### **梯子が立つ条件はほとんど一意**（この節がいちばん再利用できる）

```
lad_diag       : blockok / colOK / bd ≤ d / fOK + 梯子 ⟹
                 first = true ∧ d = p.2 ∧ p.2 = p.1 ∧ p.1 = bd ∧ p.2 = plev + 1
lad_lev_le_one : さらに dpOK を足すと p.2 ≤ 1
```

理由: 梯子は `d ≤ p.2 ∨ force` を要求し、`force` の場合は `fOK` が
`d ≤ plev + 1 = p.2` を与える。`colOK` の `p.2 ≤ p.1 = bd ≤ d` と合わせて
**`d = p.2 = bd = p.1`**。さらに `dpOK` は `first ∧ d = bd` のとき
`plev = 0 ∨ plev + 1 < bd` を要求するが、`plev + 1 = p.2 = bd` なので後者は偽、
よって `plev = 0`、すなわち `p.2 = 1`。

つまり **梯子は `p = (1,1)`・`bd = d = 1`・`plev = 0`・`first = true` でしか立たない**。
実測でも、全不変量を満たす呼び出し（ブロック ≤5 列・`bd ≤ 3`・`plev ≤ 4`）のうち
梯子が立つ組は `((1,1), bd=1, d=1, plev=0, first=true)` の 1 通りだけだった
（`force` は両方あり）。根 `(0,0)` の引数ブロックがちょうどこれ。

### `RDnopar`: `contrOK` は本当に偽になりうる

`convC_dropLast_noParent_aux` は `contrOK M`（「縮約が `some ([x], [])` の形で
発火することがどの接尾辞でも起きない」）を要求するが、これは
**`RDnopar` の入力で実際に破れる**。反例 `B = (2,2)(2,1)(3,2)(3,1)`:
`p = (2,2)`, `q = (2,1)`, `pre = [(3,2)]`, `rest2 = [(3,1)]`, `Bq = []` で
`x = (3,1)`、`x.2 = 1 ≠ 0`。しかもこの `B` は `RDnopar` の仮定を満たす
（末尾列 `(3,1)` の行 0 の祖先は `(2,1)` だけで段 `1 ≥ 1` なので行 1 の親はない）。

壊れる形は `x.2 < p.2` を要求するので `p.2 ≥ 2` が要る。ところが上の
`lad_lev_le_one` から**梯子が立つ段では `p.2 ≤ 1`**。したがって壊れる形は
不変量つきの再帰では決して現れない。そこで `contrOK` を

```
blockok bd M / colOK M / bd ≤ d / argPatOK M / dpOK bd d plev first /
hpOK M d plev first force / fOK M d plev force
```

に置き換えた `convC_dropLast_noParent_aux2` を作った（元の証明の構造そのままで、
5 か所の再帰に不変量を配る）。配り方:

| 降り先 | パラメタ | 道具 |
|---|---|---|
| 引数 `A` | `(bd+1, d+2 または ddOf+1, p.2, true, …)` | `blockok_arg'` / `dpOK_arg` / `hpOK_of_headPatOK` / `fOK` は `hpOK` から |
| 兄弟 `B` | `(bd, d, p.2, false, false)` | `blockok_sib'` / `dpOK_false` / `hpOK_false` / `fOK_false` |
| `rest2` | `(bd+1, d+1, p.2, false, false)` | `argPatOK_drop` を 2 回（`U` を剥がす・`pre` を剥がす） |
| `Bq` | `(bd, d, p.2, false, false)` | `argPatOK_drop`（`U` を剥がす）＋ `argPatOK_cons` |

`d + 2` の枝の `dpOK` は `d + 2 = bd + 1` が `bd ≤ d` と矛盾するので空虚。

追加した定理: `lad_lev_le_one`、`lad_diag`、`blockok_arg'`、`blockok_sib'`、
`steps1_suffix`、`colOK_of_suffix`、`convC_dropLast_noParent_aux2`、`rdNopar`。

### 残っている 2 つ

#### `CtrPres2`（場合 2b）

`CtrPres2` は**梯子が立つ枝でしか使われない**（`reindexD_zero_block5` /
`reindexD_pos_block4` の `hlad` の中）。だから上の `lad_diag` / `lad_lev_le_one` を
使えば `p.1 = p.2`（`dpOK` があれば `p = (1,1)`, `bd = d = 1`, `plev = 0`）に
特殊化した `CtrPres3` にできる。ただしそれだけでは場合 2b の 9 例は消えない
（どの例も `p = (1,1)` か `(2,1)` か `(2,2)` で `p.1 = p.2` または `p.2 = 1`）。

場合 2b の 9 例（ブロック ≤7 列・`bd ≤ 2`）は**きれいに 3 族**:

```
B = (v,w)^a ++ [(v,w-1)] ++ (v+1,w)^b ++ [(v+2,·)]     (A = [] , a ∈ {2,3})
```

たとえば `B = (1,1)(1,1)(1,0)(2,1)(3,0)`, `n = 3`:
`T = (1,1)(1,0)(2,1)(3,0)`、`T⟦3⟧ = (1,1)(1,0)(2,1)(2,1)(2,1)`、
`U_n = [(1,1)]`, `q_n = (1,0)`, `pre_n = (2,1)(2,1)`, `rest2 = [(2,1)]`。
**`rest2` の頭の段は `1 = p.2`** なので段が下がらず `contrLen = none` になる。

9 例の**構造は完全に一様**（`tools/dbms/case2b.py` の追加出力で確認）:

```
L = j1 - j0 = 1,  d0 = 0,  A = [],  z = S[J-1],  U_n.getLast = p,  z.2 = p.2
```

つまり `T` の悪い部分は 1 列だけで、`S = T⟦n⟧ = T.dropLast ++ [c]^(n-1)`
（`c = T.dropLast` の末尾列）。だから `z = S[J] = S[J-1] = pre_n` の末尾。

**証明の筋（この形なら通る）**: `k_n ≥ 1` なら `pre_n = contrPre p U_n A` の末尾は
`shift1 (U_n.getLast)`、すなわち `S[J-1] = (U_n.getLast.1 + 1, U_n.getLast.2)`。
いま `z = S[J-1]` で、発火条件は `z.1 = p.1 + 1` だから `U_n.getLast.1 = p.1`。
`U_n` は `p` のユニット列なので深さ `p.1` の列はユニットの頭 `= p` だけ、
よって `U_n.getLast = p`、したがって `z.2 = p.2`。発火条件 `z.2 < p.2` に矛盾。

残るのは「場合 2b では必ず `z = S[J-1]`」（＝悪い部分が 1 列で `d0 = 0`）を
示すこと。実測ではブロック ≤7 列・`bd ≤ 2` の 9 例すべてでそうなっている。

#### `RDnode`（ずれたコピー）

`T = []`・`parent B 1 (末尾) = 0`・段 > 0。このとき行 1 の親が節点 `p` 自身なので
`d0 = x.1 - p.1 ≥ 1` で、

```
B⟦n⟧ = W ++ shiftr0 d0 W ++ shiftr0 (2 d0) W ++ …    (W = B.dropLast)
```

という**ずれたコピーの階段**になる（段 0 の `reindexD_node0_gen2` は `d0 = 0` で
素直な繰り返しだった）。像の側も同じ形の階段になるが、DBMS 側の親は index 0
ではなく **`convC A` の先頭**（実測）で、`m = n` で合う例が大半、
`n' > n` を取る必要がある例もある。

使えそうな道具は `convC_shift1`（**`convC` は `shift1` で不変**）。これを繰り返せば
`convC (shiftr0 e X) d plev first force = convC X d plev first force` になる。
つまりコピーの像は「ずれ」に依らず `(d, plev, first, force)` だけで決まる。

なお `¬ hasParent` の場合は `rdNopar` と同じ議論で片付く（`RDnode` は
`hasParent` を仮定していないので、まずそこで場合分けする）。

### 追加した検査スクリプト

| | |
|---|---|
| `tools/dbms/nodeprobe.py`（会話中） | 梯子が立つパラメタの列挙と `RDnode` の `n ↔ m` |
| `tools/dbms/case2b.py`（会話中） | `CtrPres2` の場合 2b の全例を詳細表示 |


## 2026-08-26（続き 6）: 梯子つきの縮約は**完全に消えた**。残余は 4 つ

### 到達点

```
reindexD_holds_of_res7  : CtrRes → CtrPres2 → RDnopar → RDnode → ReindexD
ST_D_conC_holds_of_res7 : 同上 → ST_PS M → ST_D (conC M)
```

**旧 `RDzeroRes2` / `RDlad2`（梯子つきの段での縮約）は残余から消えた。**
`leanman check` は exit 0、`sorry` 0、`sorryAx` なし。`DbmsStd.lean` は 11277 行。

### 縮約が発火する段の扱い（全部証明済み）

縮約が発火するとき兄弟ブロックは必ず `T = U ++ q :: ((pre ++ rest2) ++ Bq)` の形で
（`contrLen_shape`）、`L` を取り替えても縮約はまったく同じように発火する
（`contrLen_of_shape` / `convC_factor_contr`）。降り先は 3 通り:

| | 降り先 | 道具 |
|---|---|---|
| `Bq ≠ []` | `q` の兄弟 `Bq` | `reindexD_sib_contr`（親は必ず `Bq` の中） |
| `Bq = []`・親が `rest2` の中 | `rest2` | `reindexD_rest_contr` |
| `Bq = []`・親が縮約の内側 | （降りない） | `rdZeroStop` / `rdPosStop2` |

* **段 > 0 の Stop は起こらない**（`rdPosStop2`）。行 1 の親は `q` より後ろの
  `rest2` の中に入る。使う道具は `le0_ge_of_append`・`le0_interval_gt` と
  **`descOK_level_le_head`**（同じ深さの鎖では段が増えない）。
* **段 0 の Stop は本当に起こる**が、そのときは親が必ず `q` の位置で
  （`zeroStop_shape`）、展開は `oper_repeat_at` でコピーの並びになる:

  ```
  B⟦n⟧ = (p :: (A ++ U)) ++ (replicate n (q :: (pre ++ rest2.dropLast))).flatten
  ```

  DBMS 側は像の末尾列が深さ `d+1`・段 0 でその手前に深さ `d` 以下の列が
  先頭の `(d, plev)` しかないので、**DBMS 側の親は index 0**。したがって

  ```
  (convC B)⟦m⟧ = (replicate m ((convC B).dropLast)).flatten
  ```

  で、`rest2` が 2 列以上なら `m = n`、1 列なら `m = n + 1`（計画書のいう
  `g(m) = m - 1`）で合う（`rdZeroStop`）。

### そのために証明した汎用の補題

| | |
|---|---|
| `convC_shift1` | **`convC` は平行移動（`shift1`）で変わらない**（`RDnode` でも使えるはず） |
| `contrLen_shift1` / `unitsLen_shift1` / `contrPre_shift1` | その土台 |
| `convC_first_false` | `first = false` なら `plev` / `force` は像に効かない |
| `convC_units_append` | ユニット列のうしろで像が切れる |
| `convC_units_depth` | `d = p.2` ならユニット列の像は深さパラメタ +1 で変わらない |
| `convC_contrPre` | `contrPre p U A` の像 = 梯子の本体 + `A` の像 + `U` の像 |
| `convC_run_contr` | コピーの並びの像はブロックの像の並び |
| `descOK_level_le_head` | ブロックの中で頭と同じ深さの列は頭より段が高くない |
| `contrLen_of_shape_nil` | 前置きのあとに何も残らなければ縮約は発火しない |

### 残っている 4 つ

| | 内容 | 実測 |
|---|---|---|
| `CtrRes` | BMS 標準形は `argCtrOK` | 標準形 ≤9 列 295014 個で違反 0 |
| `CtrPres2` | 縮約が発火しない状態は展開で保たれる（`ctrHeadOK` つき） | ブロック ≤7 列 `bd ≤ 2` の 447 万例で反例 0 |
| `RDnopar` | 段 > 0・末尾列に行 1 の親がない | 77950 例で反例 0 |
| `RDnode` | 段 > 0・末尾列の親が節点（ずれたコピー） | 14827 例で反例 0 |

### `CtrPres2` の証明の筋（続き 5 の分析のまとめ・**場合 2b だけ未確定**）

`W := T.dropLast` は `T` と `T⟦n⟧` の共通の接頭辞（`|W| = |T| - 1`）。
`T⟦n⟧` での発火の証拠は接頭辞 `U_n ++ [q] ++ pre_n ++ [z]` だけで決まり
（`|pre_n| = 1 + |A| + |U_n|`）、`z` の位置を `J := |U_n| + 1 + |pre_n|` とすると

* **場合 1**（`J < |W|`）: 証拠がまるごと `W` の中 ⟹ `T` でも同じ証拠 ⟹ 矛盾（実測 0 件）
* **場合 2a**（`J = |W|`）: `z` は 2 個目のコピーの頭 `(v0 + d0, w0)`。
  `lp` の段 > 0 なら `v0 + d0 = lp` の深さなので `T` で構造条件が揃い `ctrHeadOK` で矛盾。
  `lp` の段 = 0 なら `d0 = 0` で親 `T[r]` は `pre` の中の深さ `p.1+1` の列だが、
  `pre = (p.1+1,p.2) :: shift1 A ++ shift1 U` の深さ `p.1+1` の列は
  `pre[0]` と `shift1 U` のユニットの頭だけで**どれも段が `p.2`**。
  段が下がる条件 `w0 < p.2` に矛盾（実測 17 件）
* **場合 2b**（`J > |W|`）: `z` がコピーの奥（実測 9 件、例
  `B = (1,1)(1,1)(1,0)(2,1)(3,0)`, `n = 3`）。どの例も `z` の段が `p.2` と同じ。
  前置きの一致は `T⟦n⟧[s+i] = shift1 (T⟦n⟧[i])`（`s = |U_n| + |A| + 2`, `i < |U_n|`）
  という自己相似を強いるので、コピーの周期性と合わせれば潰せるはずだが**未確定**。


## 2026-08-26（続き 5）: 梯子つきの縮約を潰した。残余は 5 つ

### 到達点

```
reindexD_holds_of_res6  : CtrRes → CtrPres2 → RDzeroStop2 → RDnopar → RDnode → ReindexD
ST_D_conC_holds_of_res6 : 同上 → ST_PS M → ST_D (conC M)
```

**旧 `RDzeroRes2` と `RDlad2`（梯子つきの段での縮約）は消えた。**
代わりに入ったのは `CtrPres2`（両側で共通）と `RDzeroStop2`（段 0 だけ）で、
段 > 0 側の対応物 `RDposStop2` は**定理として証明した**（`rdPosStop2`）。
`leanman check` は exit 0、`sorry` 0、`sorryAx` なし。`DbmsStd.lean` は 9794 行。

### 何が分かったか

`reindexD_sib_lad` は「**どんな** `L` でも縮約が起きない」を要求していたが、
因子化に実際に要るのは `T` と `T⟦n⟧` の 2 つだけである（`reindexD_sib_lad2`）。
しかも `¬(∀ L, contrLen … = none)` は `p.2 ≥ 1` とほぼ同値なので、
旧 `RDzeroRes2` は「梯子つきで兄弟がある場合」全部（標準形 ≤9 列の右端の道で
52443 節点）を抱えていた。新しい割り方だと縮約が実際に発火する 151 節点だけになる。

**縮約が発火する段では兄弟ブロックは必ず**

```
T = U ++ q :: ((pre ++ rest2) ++ Bq)      pre = contrPre p U A
```

の形で（`contrLen_shape`）、`L` を取り替えても縮約はまったく同じように発火する
（`contrLen_of_shape` / `convC_factor_contr`）。だから

* `Bq ≠ []` → `q` の兄弟ブロック `Bq` へ降りる（`reindexD_sib_contr`）
* `Bq = []` → `rest2` へ降りる（`reindexD_rest_contr`）

で `reindexD_step_gen` に乗る。降りられないのは「末尾列の親が縮約の内側にある」
場合だけで、これが `RDzeroStop2` / `RDposStop2` である。

`Bq ≠ []` のときは親が必ず `Bq` の中に入る（`Bq` の頭の深さが `bd`、
末尾列の深さが `bd` より大きいことから）。

### `rdPosStop2`（段 > 0 の Stop は起こらない）

段 > 0 では行 1 の親 `j0` が縮約の内側に来ることはない:

1. `q` は深さ `bd` なのでブロックの中に行 0 の親を持たない。よって
   `le0_ge_of_append` で `j0 ≥ (p :: (A ++ U)).length`（= `q` の位置）。
2. `pre` の列は深さ `bd + 1` 以上。`le0_interval_gt` を `k = |G2|`
   （`rest2` の頭、深さ `bd+1`）に当てると `entry0 j0 < bd+1`、つまり `j0` の深さは
   `bd`。深さ `bd` の列は `q` の位置までしかないので `j0 = q` の位置。
3. `j0 = q` の位置なら `q.2 < entry1 x`、つまり `entry1 x ≥ p.2`。
   一方、鎖の最初の一歩 `y` は深さ `bd+1` で `rest2` の中にあり、
   `nextrel1` の最小性から `entry1 x ≤ entry1 y`、
   `descOK`（同じ深さの鎖では段が増えない = **`descOK_level_le_head`**）から
   `entry1 y ≤ rest2.headI.2 < p.2`。矛盾。

段 0 では 3 が効かない（`x` の段が 0 なので `q.2 < entry1 x` が出ない）ので、
`RDzeroStop2` は本物の場合として残る（標準形 ≤9 列の右端の道で 67 節点、
ブロック ≤7 列・`bd ≤ 2` で 113 例）。

### 残っている 5 つ

| | 内容 | 実測 |
|---|---|---|
| `CtrRes` | BMS 標準形は `argCtrOK` | 標準形 ≤9 列 295014 個で違反 0 |
| `CtrPres2` | 縮約が発火しない状態は展開で保たれる（`ctrHeadOK` つき） | ブロック ≤7 列 `bd ≤ 2` の 447 万例で反例 0 |
| `RDzeroStop2` | 段 0・縮約が発火して親が縮約の内側（コピー regime） | 113 例で反例 0 |
| `RDnopar` | 段 > 0・末尾列に行 1 の親がない | 77950 例で反例 0 |
| `RDnode` | 段 > 0・末尾列の親が節点（ずれたコピー） | 14827 例で反例 0 |

### `CtrPres2` について分かっていること

**`ctrHeadOK` を落とすと偽**（反例 `B = (1,1)(1,0)(2,1)(2,1)`, `n = 2`:
`T` では `rest2` の頭の段が `p.2` と同じなので発火しないが、`T⟦2⟧` では下がる）。
`ctrHeadOK` を足すとブロック ≤7 列・`bd ≤ 2` の 447 万例で反例 0
（`tools/dbms/ctrpres_check.py`）。

**構造だけの版（`contrLen'`）も偽**（26 例。`tools/dbms/ctrpres_cases.py`）。
つまり段が下がる条件を使わないと証明できない。

証明の筋（`W := T.dropLast` は `T` と `T⟦n⟧` の共通の接頭辞、`|W| = |T| - 1`）:
発火の証拠は `T⟦n⟧` の接頭辞 `U_n ++ [q] ++ pre_n ++ [z]` だけで決まる
（`|pre_n| = 1 + |A| + |U_n|`）。`J := |U_n| + 1 + |pre_n|` を `z` の位置として

* **場合 1**（`J < |W|`）: 証拠がまるごと `W` の中 ⟹ `T` でも同じ証拠が立つので
  `contrLen T ≠ none`。仮定に矛盾。**（実測 0 件。証明も簡単）**
* **場合 2a**（`J = |W|`）: `z` は `T⟦n⟧` では 2 個目のコピーの頭
  `(v0 + d0, w0)`、`T` では末尾列 `lp`。
  * `lp` の段 > 0 なら `v0 + d0 = lp` の深さなので、深さの条件は `lp` にも成り立ち、
    `T` で構造条件が揃う ⟹ `ctrHeadOK` から `contrLen T ≠ none`。矛盾。
  * `lp` の段 = 0 なら `d0 = 0` で `v0 = p.1 + 1`。親 `T[r]` は `pre` の中の
    深さ `p.1+1` の列だが、`pre = (p.1+1, p.2) :: shift1 A ++ shift1 U` の
    深さ `p.1+1` の列は `pre[0]` と `shift1 U` のユニットの頭だけで、
    **どれも段が `p.2`**。段が下がる条件 `w0 < p.2` に矛盾。
  **（実測 17 件。上の筋で潰せるはず）**
* **場合 2b**（`J > |W|`）: `z` がコピーの奥。実測 9 件（例
  `B = (1,1)(1,1)(1,0)(2,1)(3,0)`, `n = 3`, `T⟦3⟧ = (1,1)(1,0)(2,1)(2,1)(2,1)`）。
  どの例も `z` の段が `p.2` と同じで段が下がらない。**ここだけ筋が未確定。**

### `RDzeroStop2` について分かっていること

配置は必ずこうなる（`hasParent` を足した版で証明できるはず）:
`Bq = []`、末尾列の深さ = `bd + 1`、**親 = `q` の位置**。したがって
`oper_repeat_at` で

```
B⟦n⟧ = (p :: (A ++ U)) ++ (List.replicate n V).flatten,  V = q :: (pre ++ rest2.dropLast)
```

DBMS 側は `convC B = C0 ++ convC rest2 (d+1) p.2 false false` で
（`C0 = (d,plev) :: (d+1,p.2) :: (convC A (d+2) p.2 true false ++ convC U (d+1) p.2 false false)`）、
像の末尾列は深さ `d+1`・段 0、その手前で深さが `d` 以下なのは先頭の `(d, plev)` だけなので
**DBMS 側の親は index 0**。よって

```
(convC B)⟦m⟧ = (List.replicate m ((convC B).dropLast)).flatten
```

一方
* `|rest2| ≥ 2`: `convC (B⟦n⟧) = D ++ convC ((replicate (n-1) V).flatten) d p.2 false false`
  で `D = (convC B).dropLast`。`m = n` で合う。
* `|rest2| = 1`: `T⟦n⟧` では縮約が発火せず
  `convC (B⟦n⟧) = C0' ++ convC (U ++ (replicate n V).flatten) d p.2 false false`。
  `d ≤ p.2` なら `ddOf p.2 d p.2 false false = ddOf p.2 (d+1) p.2 false false = p.2 + 1`
  なので `convC U d p.2 false false = convC U (d+1) p.2 false false` となり、
  結局 `(replicate (n+1) D).flatten`。`m = n + 1` で合う（計画書のいう `g(m) = m - 1`）。

要るのは「ユニット列のコピーの並びの `convC`」の補題（`convC_run_lad` の親戚）と
「`convC` の深さパラメタを 1 増やしてもユニット列の像は変わらない」補題。

### 追加した検査スクリプト

| | |
|---|---|
| `tools/dbms/walk_contr.py` | 標準形の右端の道で縮約が発火する節点を分類 |
| `tools/dbms/ctrpres_check.py` | `CtrPres` / `CtrPres2` の全数検査 |
| `tools/dbms/ctrpres_cases.py` | `CtrPres2` の場合 1 / 2a / 2b の分類 |
| `tools/dbms/stop_check.py` | `Stop` の配置（段 0 / 段 > 0）を数える |
| `tools/dbms/zerostop_check.py` | `RDzeroStop2` の配置と目標の恒等式の検査 |
