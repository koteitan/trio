# bms2dbms —— BMS から DBMS への翻訳器

[← trio 全体](../README.md)

## このサブプロジェクトは何か

トリオ数列（TSS = BMS 3 行）は挙動が複雑で、拡張ブーフホルツ psi との対応表
（`ebp2bms/`）を作る途中で非標準形が出るなどして破綻した。
そこで **BMS の亜種である Dimensional BMS（DBMS）の 3 行版 = DTSS に移せば
挙動が簡単にならないか**を調べているのがここである。

そのために作るのが変換関数

```
conv3 : BMS 3 行標準形  ->  DBMS 3 行標準形
```

である。対象は `z ≤ 1`（行 2 が 0 か 1）の断片。

変換関数は MrredsharkFan 氏の `bmsToDbms` を使う
（<https://github.com/MrredsharkFan/w-Y-global-lngi> の `conv.js`）。
測った範囲（`≤8` 列）で単射・全射・順序保存であり、BMS 標準形と DBMS 標準形の間の
順序同型になっている。詳しくは [results.md](results.md) と
[mrredsharkfan/README.md](mrredsharkfan/README.md)。

**現状: 残るのは DBMS 側の整礎性 `WellFounded RD3` で、こちらは未証明。**
2 行版（`conC`、`psi_0(Omega_omega)` 未満）は Lean で証明が完成している。

## ディレクトリ

```
lean/           Lean 4 / Mathlib による形式化（Dbms3.lean が 3 行の器）
tools/          Python の参照実装・CLI・検証スクリプト
mrredsharkfan/  他実装との突き合わせ
results.md      このサブプロジェクトの成果
```

Lean は別パッケージ `bms2dbms` で、`lean/lakefile.toml` の
`[[require]] name = "trio", path = "../../lean"` で親（BMS 停止性証明）を参照する。
依存は一方向で循環は無い。`leanman build -C bms2dbms/lean` で緑（808 jobs）。

## 成果

- [results.md](results.md) —— **このサブプロジェクトの成果**。
  3 行 DBMS の器、変換に課す 7 つの性質、シート BM4-Analysis との一致
  （`(0,0,0)(1,1,1)` / `psi_0(Λ)` / `(0,0,0)(1,1,1)(2,2,2)` で区切った 3 区間ごと）、
  `(0,0,0)(1,1,1)` 未満の 2 行への帰着、反証ずみの命題。
- [../results.md](../results.md) —— 親プロジェクト（BMS 3 行 `z ≤ 1` の停止性証明）の成果。
  こちらの `TRIO_terminates_of_dbms_wf` はその主定理と繋がっている。

## 道具

- [tools/README.md](tools/README.md) —— CLI `bms2dbms` / `dbms2yseq` / `bms2yseq`
  （BMS **2 行** <-> DBMS <-> Y 数列）。正しさは Lean で証明ずみ。
  （[English](tools/README-en.md)、アルゴリズムは [algorithm.md](tools/algorithm.md)）
- [tools/README-tss.md](tools/README-tss.md) —— CLI `tss2dbms`
  （トリオ数列 = BMS **3 行** <-> DBMS 3 行）。証明は無いので、変換のたびに
  「像が DBMS 標準形か」「往復するか」をその場で検算する。

作業ノートは `tools/BRIEF-v14.md`（現在地と残る的）、`tools/H1-NOTES.md`、
`tools/NOTES.md`、`tools/R1-NOTES.md`。

## 他実装との突き合わせ

- [mrredsharkfan/README.md](mrredsharkfan/README.md) ——
  [MrredsharkFan/w-Y-global-lngi](https://github.com/MrredsharkFan/w-Y-global-lngi) の
  `conv.js` にある `bmsToDbms` との比較。**同じ DBMS を相手にしている**（ω-DBMS ではない）。
  独立に書かれた 2 つの変換器がシート 1358 件のうち 1357 件で同じ像を出し、
  **外す 4 行まで一致する**。区間ごとの一致度と、差異が起こる最小の BMS を全部載せてある。
