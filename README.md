# trio

トリオ数列（3 行バシク行列, BM4）の停止性の構文的証明(未完成です)。
[lean-yapss](https://github.com/koteitan/yet-another-pss-proof)（2 行 = ペア数列、完成）の続編。

対象は一旦 z < 2 の断片。生成元は z 頭打ち対角列
`(0,0,0)(1,1,1)(2,2,1)...(v,v,1)` で、これは完全な BM4 の
`(0,0,0)(1,1,1)(2,2,2)[v]` に等しい。この断片は BM4-Analysis の
psi(K)（弱コンパクト）までの主脈を含む。

```
lean/    Lean 4 / Mathlib による形式化
tools/   実行可能な BM4 モデルと検証
```

展開規則の出典: ユーザーブログ:Koteitan/バシク行列の数式的定義（BM4 の節、上昇行列 A_xy を含む）。

## 資料

- [bms2dbms/tools/README.md](bms2dbms/tools/README.md) — CLI `bms2dbms` / `dbms2yseq` / `bms2yseq`
  （BMS 2 行標準形 <-> DBMS 標準形 <-> Y 数列）の使い方（[English](bms2dbms/tools/README-en.md)）、
  [algorithm.md](bms2dbms/tools/algorithm.md) — 変換アルゴリズムと証明されていること
  （[English](bms2dbms/tools/algorithm-en.md)）
- [dom.md](dom.md) — 拡張ブーフホルツ OCF の `dom` 関数と BM4 展開分岐の対応
- `tools/normalize_sheet.py` — BM4-Analysis シートのラベルを形式だけ正規化して
  `tmp/fixed-sheet/`（バージョン管理外）と `tools/omega_alpha_rows.tsv` を作る
- 拡張ブーフホルツ psi ↔ **DBMS 3 行**
  — 対応表 [α < ε₀](ebp2dbms/sheet/1/README.md) / [ε₀ ≤ α](ebp2dbms/sheet/2/README.md)
  （[English](ebp2dbms/sheet/1/README-en.md)）。変換関数は
  [MrredsharkFan 氏の `bmsToDbms`](https://github.com/MrredsharkFan/w-Y-global-lngi)
- 拡張ブーフホルツ psi ↔ トリオ数列
  — 対応表
  [M ≤ ψ0(Ω_ω)](ebp2bms/sheet/0/README.md) /
  [ψ0(Ω_ω) ≤ M < ψ0(Ω_ε₀)](ebp2bms/sheet/1/README.md) /
  [ψ0(Ω_ε₀) ≤ M ≤ ψ0(Ω_Λ)](ebp2bms/sheet/2/README.md)、
  アルゴリズム [α < ε₀](ebp2bms/algorithm/1/README.md) / [ε₀ ≤ α < Λ](ebp2bms/algorithm/2/README.md)
  （[English](ebp2bms/sheet/0/README-en.md)）
