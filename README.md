# trio

トリオ数列（3 行バシク行列, BM4）の停止性の構文的証明。
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

- [dom.md](dom.md) — 拡張ブーフホルツ OCF の `dom` 関数と BM4 展開分岐の対応
- 拡張ブーフホルツ psi ↔ トリオ数列 対応表
  — [1](ebp2bms-1.md) [2](ebp2bms-2.md)（[English](ebp2bms-1-en.md)）
