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
| [`lean/Ytosk/WF.lean`](lean/Ytosk/WF.lean) ほか | **段 2: 標準形の順序の整礎性 `wf_OT`（証明済み）**。詳しくは [wf.md](wf.md) |
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

## 段 2（整礎性）— 証明済み

**標準形の項の上の辞書式順序 `<` は整礎**（`Ytosk.wf_OT`、`sorry` なし、公理は Lean 標準の 3 つだけ）。
順序数への評価は使わない構文的な証明。証明の組み立ては [wf.md](wf.md)。

- Buchholz の記法（添字が自然数と ω）の整礎性は pss-proof
  （https://github.com/koteitan/pss-proof の `lean/OTB-well-founded-syntactic`）で証明済みで、方法は Buchholz (1987) の
  段ごとの集合 W_u を下の段から再帰で作るもの。拡張版では添字が項なので、この再帰には添字の順序の整礎性が先に要り、循環する
  （Ω_1 の下に任意の v について ψ_0(Ω_v) がある）。
- そこで Buchholz の「区別された集合」を使った。再帰を使わずに「自分の下では正しい W になっている集合」として定義し、その合併 W が
  最大の区別された集合になる。組み立ては Arai の
  [Wellfoundedness proof with the maximal distinguished set](https://arxiv.org/abs/2211.08619) と
  [Lectures on Ordinal Analysis](https://arxiv.org/abs/2304.00246) の 3 節に倣った。
- 拡張 Buchholz では主項の比較が (添字, 引数) の辞書式なので、Arai の証明で重い部分（Mahlo 次数、G_κ 集合、反射原理）はいらず、
  鍵の補題は数行の場合分けで済んだ。

## 次: 段 1（下がること）

標準形の行列 M（SRO 未満）について eval(M[n]) < eval(M) と、eval(M) が標準形であること。
段 2 と合わせると、SRO 未満の行列から始めた展開は止まる。
