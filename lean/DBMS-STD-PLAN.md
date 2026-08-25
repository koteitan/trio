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
| `range'_map_entry` / `range_append_range'` | `DbmsStd.lean` |

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

残る穴: 縮約が `M.dropLast` で変わりうること（shift regime の
`A⟦2⟧` と `A⟦3⟧` の違いがまさにこれ）。

### (c) 親が `Arg` / `B` の中
両側とも `oper_append_of_parent_ge` で局所化して帰納できる。**道具は揃った。**
残る穴はただ 1 つ:

```
BMS の親が B の中  →  |cols ++ convC Arg| ≤ parent (convC M ...) i (末尾)
```

（実測では例外 0。`convC B` の中に「段がより小さい行 0 の祖先」があることを言えばよい。
`nextR` の始点は一意なので、**接尾辞の中に 1 つ証人を出せば**それが親になる。
段 0 の場合（`i = 0`）なら「`convC B` の中に末尾より浅い列がある」で足りる。
`convC_getLast_depth` で末尾は深さ `d` より深いとわかるので、
`convC B` の先頭が深さ `d` なら先頭が証人になる。残るのは先頭が `b+1` の場合。）

もう 1 つ、`convC ((p :: Arg) ++ B⟦n⟧) = cols ++ convC Arg ++ convC (B⟦n⟧)` も要る。
`B⟦n⟧` の先頭は `B` の先頭と同じなので切り分けは同じだが、縮約の判定が変わりうる。

### (d) 親がこの段
基底。コピーの対応（`convC_run` / `conC_run_top` が段 0 の場合の道具）。

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
