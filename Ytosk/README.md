# Ytosk — 翻訳写像（BMS → 拡張 Buchholz）による停止性

[← 戻る](../README.md)

トリオ数列（3 行の BMS）の行列を、Ytosk 氏の翻訳写像で拡張 Buchholz の項に移して停止性を示す、という道の作業場。
trio の Lean（`../lean`）とは独立に、ゼロから書く。

停止性は次の 3 段で出る（SRO 未満の行列について）。

1. **下がること**: 標準形の行列 M について eval(M[n]) < eval(M)。
2. **整礎性**: 拡張 Buchholz の標準形の項の順序が整礎。
3. 1 と 2 から、SRO 未満では展開が止まる。

SRO = ψ_0(Ω_Ω_Ω_…) は拡張 Buchholz の極限で、シートの psi(I) = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0) にあたる。
trio の z<2 断片はこれより上まである（生成元 (0,0,0)(1,1,1)(2,2,1) の方が大きい）ので、この道で届くのは SRO 未満の部分。

## ファイル

| ファイル | 中身 |
|---|---|
| [`lean/Ytosk/Term.lean`](lean/Ytosk/Term.lean) | 項 `T ::= z \| psi a b c`（ψ_a(b)+c）、辞書式順序 `lt`、和、ω 冪、標準形 SF |
| [`lean/Ytosk/Eval.lean`](lean/Ytosk/Eval.lean) | 翻訳写像 `eval : Mat → Option T`（Ytosk 氏の v, o）。循環すると `none` |
| [`lean/Ytosk/OT.lean`](lean/Ytosk/OT.lean) | 標準形 `isOT`（成分 G_u による Buchholz 流の条件を、添字が項の場合に広げたもの） |
| [`lean/Run.lean`](lean/Run.lean) | 標準入力の行列を評価する実行ファイル（`tools/probe_ebocf.py` が使う） |

翻訳写像の出典は Ytosk 氏のブログ記事
[Algorithm that changes BMS matrices into ordinals up to SRO](https://googology.fandom.com/wiki/User_blog:Ytosk/Algorithm_that_changes_BMS_matrices_into_ordinals_up_to_SRO)。
実行の読みは JavaScript 版 https://github.com/hemisemidemipresent/bms に合わせ、シートの 4767 行全部で同じ結果を出す。

ビルド: `lake build`（`lean/` で）。Mathlib は trio のパッケージを通して借りるだけで、trio のモジュールは import しない。

## 測った事実（シートの 4767 行）

- 翻訳が値を返す 4756 行の値は、**全部 `isOT`**（標準形の定義が Ytosk 氏の SF と合っている）。残り 11 行は循環で値なし。
- 隣り合う行の 4755 組で、行列の大小（`bms -c`）と翻訳した項の大小（`lt`）が 4713 組で一致。
  合わない 42 組は、**どれもシートの非標準の行列を含む**。両方とも標準形の組では全部一致する。
  これは段 1 の数値上の裏づけになる。

## 段 2（整礎性）の見通し

Buchholz の記法（添字が自然数と ω）の整礎性は、pss-proof
（https://github.com/koteitan/pss-proof の `lean/OTB-well-founded-syntactic`）で構文的に機械検証済み。
方法は Buchholz (1987) のもの:

- 段 u ごとの集合 W_u を、下の段の W_m（m < u）を添字域にした最小不動点として、u の小さい方から定める。
- 基本列 a[z] と Bachmann の共終性（b < a なら、ある z で b ≤ a[z]）で、W_u の元が可到達であることを示す。
- 項の構造についての帰納法で、段 u 未満の項は全部 W_u に入ることを示す（Buchholz 1987 の補題 2.8）。

**拡張版にそのまま移すと、ここで詰まる:**

- 添字が項なので、W_u も項 u で添字づけになる。W_u を「下の段から順に」定めるには、添字の順序が整礎である必要がある。
  それはまさに証明したいことそのもの。
- 回り道として、W_u を「可到達だと分かっている u」についてだけ定める手がある。
  ところが補題 2.8 を項 x に使うには、x の中に出てくる**すべての添字**の W が要る。
- Ω_1 より下の項（可算の項）には、任意の v について ψ_0(Ω_v) がある。
  だから Ω_1 が可到達であることを示すだけで、すべての v の可到達性が要る。循環する。
- 自然数の添字なら、添字の集合が外から与えられているので、この循環は起きない。

これは、反復の長さそのものを先に整礎と示しながら反復する、「自律的な」反復帰納的定義の形をしている
（Pohlers, *Subsystems of set theory and second order number theory*, Handbook of Proof Theory, 1998 の Aut-ID の節）。
この形の記法の整礎性の証明には、Buchholz の「区別された集合（distinguished sets）」のような非可述的な道具が使われる。
Lean の論理はそれを行うのに十分強いが、pss-proof の移植では済まず、証明の設計からやり直しになる。

別の道として、Mathlib の順序数で ψ を意味論的に定義し、`lt` が値の順序と一致することを示せば、整礎性は確実に出る。
ただしこれは構文的な証明ではない。
