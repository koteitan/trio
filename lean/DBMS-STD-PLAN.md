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

いずれも sorry 0。

## 残っているもの: `ReindexD`

```
ReindexD : ∀ A, ST_PS A → 1 < A.length → ∀ n ≥ 1,
  ∃ m n' ≥ 1, (conC A)⟦m⟧ = conC (A⟦n'⟧) ∧ translate (A⟦n⟧) ≤o translate (A⟦n'⟧)
```

実測（`tools/dbms/reindex.py`）:

```
lim=10  標準形 2073826  regime {id: 1556322, succ: 295014, shift: 222309, contr: 180}  違反 0
```

## 通らなかった道: ブロックごとの局所化

`A = p :: (Arg ++ B)` で `B` に局所化して帰納、が素直だが **DBMS 側で破れる**。
破れるのは梯子を敷いた段だけで、原因は影の列（`tools/dbms/localize.py`）:

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

### regime の対応表（≤9 列の実測）

| regime | 引き金 | g(m) | 個数（≤10 列） |
|---|---|---|---|
| succ | 末尾列 = (0,0) | 0 | 295014 |
| id | 大多数 | m | 1556322 |
| shift | 末尾列 = (1,1)（ブロックの頭に梯子） | m+1 | 222309 |
| contr | 末尾で梯子が二役 | m-1 | 180 |

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
