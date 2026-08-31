# tss2dbms

[← 戻る](../../README.md) | [2 行版は bms2dbms](README.md)

トリオ数列（Trio Sequence System = BMS 3 行、`z ≤ 1`）と DBMS 3 行を変換する CLI。

```
BMS 3 行標準形  --conv3-->  DBMS 3 行標準形
                 b2d3
                <--d2b3---
```

## 変換関数

MrredsharkFan 氏の `bmsToDbms` を使う。出所は
<https://github.com/MrredsharkFan/w-Y-global-lngi> の `conv.js`。
このリポジトリには純 Python 版 `bms2dbms/tools/mrf3.py` があり、
`≤7` 列の BMS 標準形 77282 個・DBMS 標準形 3514 個で元の JS と食い違い 0。

## ⚠ 2 行版との違い

`bms2dbms.py`（2 行）は Lean で正しさが証明ずみだが、**この 3 行版は証明されていない**。

| | 2 行 `bms2dbms.py` | 3 行 `tss2dbms.py` |
|---|---|---|
| 変換 | `conC`（`rows2.convC`） | `mrf3.b2d` |
| Lean の定理 | `ST_D_conC_final`、`conC_injective`（仮定なし） | 無し |
| シート BM4-Analysis | 236/236 一致 | 1353/1358 一致（外す 5 行はシート側の誤記） |
| 逆変換 | `untranslate ∘ readCon`、往復が証明ずみ | `mrf3.d2b`、証明なし |

だから `--no-verify` を付けない限り、変換のたびに次の 2 つをその場で確かめる。
どちらかが破れると **exit 2** で報告する（結果自体は出す）。

1. 像が DBMS 標準形か
2. 往復するか（`d2b3 (b2d3 M) = M`）

## 必要なもの

Python 3 だけ。

```
bms2dbms/tools/tss2dbms.py    このコマンド
bms2dbms/tools/mrf3.py        変換関数の純 Python 版（b2d / d2b）
bms2dbms/tools/rows3.py       BMS の読み translate3 など
bms2dbms/tools/core.py        展開規則と標準形判定（BMS / DBMS 共通）
```

## 使い方

```
tss2dbms.py [-r] [-c] [-t] [-q] [-f] [--no-verify] "行列" ...
```

行列を渡さないと標準入力を 1 行 1 件として読む（`#` で始まる行は無視）。

| オプション | 意味 |
|---|---|
| `-r`, `--reverse` | DBMS → BMS（`mrf3.d2b`） |
| `-c`, `--check` | 変換せず、標準形かどうかだけ報告する |
| `-t`, `--tree` | BMS 側の項（`translate3`）も表示する |
| `-q`, `--quiet` | 結果の行列だけを出す |
| `-f`, `--force` | 標準形でなくても、`z ≥ 2` でも変換する |
| `--no-verify` | 上の検算 2 つを省く |

終了コード: `0` 正常 / `1` 標準形でない・`z ≥ 2` / `2` 検算が破れた / `3` 使い方の誤り。

### 入力の書き方

* `"(0,0,0)(1,1,1)"` —— ふつうの 3 行。
* `"(0)(1)(2,1)(3,2,1)"` —— 列ごとに行数が違う書き方（シートの E 列の綴り）も受ける。
  足りない行は 0 で埋める。
* `"(0,0,0)(1,1,1)[4]"` —— 末尾の `[n]` は先に展開する。`[2][1]` のように並べてもよい。
* 2 行以下の行列は行 2 を 0 で埋めて 3 行として扱う。埋め込みは展開と可換で
  （`lean/Pair/Bridge.lean` の `oper_emb`）、像は 2 行の `convC` の像に 0 行を足したものに
  一致する（`≤7` 列 7256 個で違反 0）。

## 例

```console
$ python3 tss2dbms.py "(0,0,0)(1,1,1)"
(0,0,0)(1,1,1)  ->  (0,0,0)(1,0,0)(2,1,0)(3,2,1)

$ python3 tss2dbms.py "(0,0,0)(1,1,1)[4]"
(0,0,0)(1,1,0)(2,2,0)(3,3,0)  ->  (0,0,0)(1,0,0)(2,1,0)(3,2,0)(4,3,0)

$ python3 tss2dbms.py -r "(0)(1)(2,1)(3,2,1)"
(0,0,0)(1,0,0)(2,1,0)(3,2,1)  ->  (0,0,0)(1,1,1)

$ python3 tss2dbms.py -c "(0,0,0)(1,1,1)" "(0,0,0)(2,2,2)"
standard	(0,0,0)(1,1,1)
non-standard	(0,0,0)(2,2,2)

$ python3 tss2dbms.py -t "(0,0,0)(1,1,1)(2,1,0)"
(0,0,0)(1,1,1)(2,1,0)  ->  (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,1,0)
  BMS   P(0, 0)(P(1, 1)(P(1, 0)(Z,Z),Z),Z)

$ printf '(0,0,0)(1,1,1)\n(0,0,0)(1,1,0)\n' | python3 tss2dbms.py -q
(0,0,0)(1,0,0)(2,1,0)(3,2,1)
(0,0,0)(1,0,0)(2,1,0)
```

検算が破れると、結果は出したうえで exit 2 を返す。

```console
$ python3 tss2dbms.py "…" ; echo $?
tss2dbms: 像が DBMS 標準形でない: …
…  ->  …
2
```

`gen3(BMS, 6, zcap=1)` の 8387 個を `-q` で流したところ、警告 0・exit 0（3.5 秒）。

## 実測した性質

| 性質 | 母数 | 結果 |
|---|---|---|
| 単射 | `≤7` 列 77282 個 | 衝突 0 |
| 全射 | `≤8` 列の DBMS 標準形 27932 個 | 外れ 0 |
| 順序保存 | `ST_TS` 展開閉包 583466 個 | 破れ 0 |
| `ImgClosedT` | `≤7` 列 231843 対 | 破れ 0 |
| BM4-Analysis シート | 1358 行 | 1353 一致（外す 5 行はシート側の誤記） |

いずれも測定であって証明ではない。詳しくは `bms2dbms/results.md` と
`bms2dbms/mrredsharkfan/README.md`。

