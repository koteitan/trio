# BMS 2 行標準形から DBMS 標準形への変換

## 1. 記法

**列**とは $`p = (p_0, p_1) \in \mathbb{N}^2`$ のことで、$`p_0`$ を深さ、$`p_1`$ を段と呼ぶ。**行列**とは列の有限列

```math
\mathrm{Seq} := (\mathbb{N}^2)^{<\omega}
```

のことである。空列を $`\varepsilon`$、連結を $`\frown`$、長さを $`|M|`$、第 $`i`$ 成分を $`M_i`$、区間を $`M[i,j) := (M_i, \dots, M_{j-1})`$ と書く。$`M_{i,0}, M_{i,1}`$ は $`M_i`$ の第 0, 1 成分。

$`M \in \mathrm{Seq}`$ と列 $`p`$ に対し

```math
\mathrm{arg}_p(M) := M[0, k), \qquad \mathrm{sib}_p(M) := M[k, |M|), \qquad
k := \min \{\, i \le |M| \mid i = |M| \lor M_{i,0} \le p_0 \,\}
```

とおく。$`M = \mathrm{arg}_p(M) \frown \mathrm{sib}_p(M)`$ であり、$`\mathrm{arg}_p(M)`$ は「$`p`$ より真に深い列だけからなる最長の接頭辞」である。深さの平行移動を

```math
\sigma^e(M) := \bigl((M_{0,0}+e,\ M_{0,1}),\ \dots,\ (M_{|M|-1,0}+e,\ M_{|M|-1,1})\bigr),
\qquad \sigma := \sigma^1
```

と書く。真偽値は $`\top, \bot`$。

## 2. 標準形

BMS と DBMS は展開規則が同一で、対角だけが異なる。2 行では

```math
\mathrm{diag}_{\mathrm{B}}(x) = (x,\ x), \qquad
\mathrm{diag}_{\mathrm{D}}(x) = (x,\ \max(x-1,\ 0)).
```

$`\mathrm{ST}_{\mathrm{B}}, \mathrm{ST}_{\mathrm{D}} \subseteq \mathrm{Seq}`$ をそれぞれの標準形の集合とすると

```math
M \in \mathrm{ST}_{\mathrm{B}} \implies \forall i\ (M_{i,1} \le M_{i,0}),
\qquad
M \in \mathrm{ST}_{\mathrm{D}} \implies \forall i\ (M_{i,0} = 0 \lor M_{i,1} < M_{i,0}).
```

BMS は $`(x,x)`$ を許すが DBMS は許さない。段 $`s \gt 0`$ の列は DBMS では深さ $`s+1`$ 以上に置くしかない。これが変換の内容のすべてである。

## 3. 木

```math
\mathcal{T} \ni t ::= Z \ \mid\ P(s;\ t_1,\ t_2) \qquad (s \in \mathbb{N})
```

$`P(s; t_1, t_2)`$ は「段 $`s`$ の節点、引数が $`t_1`$、兄弟が $`t_2`$」を表す。

### 3.1 $`\mathrm{b2t} : \mathrm{Seq} \to \mathcal{T}`$

```math
\mathrm{b2t}(\varepsilon) := Z, \qquad
\mathrm{b2t}(p \frown r) := P\bigl(p_1;\ \mathrm{b2t}(\mathrm{arg}_p(r)),\ \mathrm{b2t}(\mathrm{sib}_p(r))\bigr)
```

### 3.2 $`\mathrm{t2b} : \mathcal{T} \times \mathbb{N} \to \mathrm{Seq}`$

```math
\mathrm{t2b}(Z, d) := \varepsilon, \qquad
\mathrm{t2b}\bigl(P(s; t_1, t_2),\ d\bigr) := \bigl((d, s)\bigr) \frown \mathrm{t2b}(t_1,\ d+1) \frown \mathrm{t2b}(t_2,\ d)
```

$`\mathrm{b2t}`$ は深さを捨て、$`\mathrm{t2b}`$ は入れ子の深さから復元する。同じ 2 本が DBMS 行列にもそのまま使える（$`\mathrm{b2t}(N)`$ を DBMSThree と呼ぶ）。

## 4. $`\mathrm{b2d} : \mathrm{Seq} \to \mathrm{Seq}`$

補助関数 $`\Gamma^{f,\varphi}_{d,\ell} : \mathrm{Seq} \to \mathrm{Seq}`$ を使う。$`d`$ は現在のブロックの深さ、$`\ell`$ は親の段、$`f`$ はブロック先頭か、$`\varphi`$ は親からの「影の形で書け」という指示。

```math
\mathrm{b2d}(M) := \Gamma^{\top,\bot}_{0,0}(M)
```

### 4.1 ユニット

```math
\mathrm{u}_p(\varepsilon) := 0, \qquad
\mathrm{u}_p(q \frown r) := \begin{cases}
  |\mathrm{arg}_p(r)| + 1 + \mathrm{u}_p(\mathrm{sib}_p(r)) & (q = p) \cr
  0 & (q \ne p)
\end{cases}
```

**ユニット**とは「$`p`$ そのもの 1 本とその引数ブロック」であり、$`\mathrm{u}_p(B)`$ は $`B`$ の先頭から取れるユニットの総列数である。

### 4.2 記号

$`M = p \frown r`$ のとき

```math
s := p_1, \qquad A := \mathrm{arg}_p(r), \qquad B := \mathrm{sib}_p(r)
```

```math
\lambda := f \land (s = \ell + 1) \land (d \le s \lor \varphi)
```

```math
d' := \begin{cases}
  d + 1 & (\lambda) \cr
  s + 1 & (\lnot\lambda \land 0 \lt s \land d \le s) \cr
  d & (\text{otherwise})
\end{cases}
```

さらに $`\lambda = \top`$ のとき

```math
U := B[0,\ \mathrm{u}_p(B)), \qquad
B^{\ast} := B[\mathrm{u}_p(B),\ |B|), \qquad
\pi := \bigl((p_0+1,\ p_1)\bigr) \frown \sigma(A) \frown \sigma(U)
```

とおき、$`B^{\ast} = q \frown r^{\ast}`$ と書けるとき

```math
\alpha := \mathrm{arg}_q(r^{\ast}), \qquad
\beta := \mathrm{sib}_q(r^{\ast}), \qquad
R := \alpha[\,|\pi|,\ |\alpha|)
```

```math
\kappa := (B^{\ast} \ne \varepsilon) \land (q_1 + 1 = s) \land (q_0 = p_0)
  \land \bigl(\alpha[0, |\pi|) = \pi\bigr) \land (R \ne \varepsilon)
  \land (R_{0,0} = p_0 + 1) \land (R_{0,1} \lt s)
```

とおく。

### 4.3 場合分け

- $`M = \varepsilon`$ の場合:

  $`\Gamma^{f,\varphi}_{d,\ell}(\varepsilon) = \varepsilon`$

- $`M = p \frown r`$ の場合:
  - $`\lambda = \top`$ の場合（梯子を立てる）:
    - $`\kappa = \top`$ の場合（縮約する）:

      $`\Gamma^{f,\varphi}_{d,\ell}(p \frown r) = \bigl((d,\ell),\ (d+1,s)\bigr) \frown \Gamma^{\top,\bot}_{d+2,\ s}(A) \frown \Gamma^{\bot,\bot}_{d+1,\ s}(U) \frown \Gamma^{\bot,\bot}_{d+1,\ s}(R) \frown \Gamma^{\bot,\bot}_{d,\ s}(\beta)`$

    - $`\kappa = \bot`$ の場合（縮約しない）:

      $`\Gamma^{f,\varphi}_{d,\ell}(p \frown r) = \bigl((d,\ell),\ (d+1,s)\bigr) \frown \Gamma^{\top,\bot}_{d+2,\ s}(A) \frown \Gamma^{\bot,\bot}_{d,\ s}(B)`$

  - $`\lambda = \bot`$ の場合（素通り、または段へ跳ぶ）:

    $`\Gamma^{f,\varphi}_{d,\ell}(p \frown r) = \bigl((d',\ s)\bigr) \frown \Gamma^{\top,\ f \land (s = \ell)}_{d'+1,\ s}(A) \frown \Gamma^{\bot,\bot}_{d,\ s}(B)`$

$`\lambda = \top`$ で書かれる $`\bigl((d,\ell),(d+1,s)\bigr)`$ が**梯子**である。$`(d,\ell)`$ は段が親と同じなので木には残らない足場（影）で、$`(d+1,s)`$ が本体。$`\kappa = \top`$ の場合は $`q`$ とその前置き $`\pi`$ をまるごと書かずに中身だけを続ける。これが**縮約**であり、DBMS では 1 本の柱が 2 つの節点を兼ねられることに対応する[^1]。

## 5. $`\mathrm{d2t} : \mathrm{Seq} \to \mathcal{T}`$

補助関数 $`\Delta^{f}_{\ell} : \mathrm{Seq} \times \mathcal{T} \to \mathcal{T}`$ を使う。第 2 引数 $`k`$ は「列を読み切った先に置く木」（継続）。

```math
\mathrm{d2t}(l) := \Delta^{\top}_{0}(l,\ Z)
```

### 5.1 記号

$`l = p \frown \mathit{rest}`$ のとき

```math
\mu := f \land (p_1 = \ell) \land (\mathit{rest} \ne \varepsilon)
  \land \bigl(\mathit{rest}_0 = (p_0 + 1,\ p_1 + 1)\bigr)
```

さらに $`\mu = \top`$ のとき $`\mathit{rest} = t \frown \mathit{tail}`$ と書き

```math
a := \mathrm{arg}_t(\mathit{tail}), \qquad
c := \mathrm{sib}_t(\mathit{tail}), \qquad
S := c[0,\ \mathrm{u}_t(c)), \qquad
R := c[\mathrm{u}_t(c),\ |c|)
```

```math
\nu := (R \ne \varepsilon) \land (R_{0,0} = t_0) \land (R_{0,1} \lt t_1)
```

```math
R^{-} := R[0, m), \qquad R^{+} := R[m, |R|), \qquad
m := \min \{\, i \le |R| \mid i = |R| \lor R_{i,0} \lt t_0 \,\}
```

とおく。

### 5.2 場合分け

- $`l = \varepsilon`$ の場合:

  $`\Delta^{f}_{\ell}(\varepsilon,\ k) = k`$

- $`l = p \frown \mathit{rest}`$ の場合:
  - $`\mu = \bot`$ の場合（素通り）:

    $`\Delta^{f}_{\ell}(p \frown \mathit{rest},\ k) = P\bigl(p_1;\ \Delta^{\top}_{p_1}(\mathrm{arg}_p(\mathit{rest}),\ Z),\ \Delta^{\bot}_{p_1}(\mathrm{sib}_p(\mathit{rest}),\ k)\bigr)`$

  - $`\mu = \top`$ の場合（$`p`$ は影）:
    - $`\nu = \bot`$ の場合（影を捨てるだけ）:

      $`\Delta^{f}_{\ell}(p \frown t \frown \mathit{tail},\ k) = P\bigl(t_1;\ \Delta^{\top}_{t_1}(a,\ Z),\ \Delta^{\bot}_{t_1}(c,\ k)\bigr)`$

    - $`\nu = \top`$ の場合（二役をほどく）:

      $`\Delta^{f}_{\ell}(p \frown t \frown \mathit{tail},\ k) = P\Bigl(t_1;\ \Delta^{\top}_{t_1}(a,\ Z),\ \Delta^{\bot}_{t_1}\bigl(S,\ P\bigl(p_1;\ \Delta^{\top}_{p_1}(t \frown a \frown S \frown R^{-},\ Z),\ \Delta^{\bot}_{\ell}(R^{+},\ k)\bigr)\bigr)\Bigr)`$

$`\mu = \top`$ で $`p`$（影）が消える。$`\nu = \top`$ の場合は 1 本の柱 $`t`$ が段 $`t_1`$ の節点と段 $`p_1`$ の節点を兼ねているので、$`t \frown a \frown S \frown R^{-}`$ を組み直して読み直すことで 2 つに戻す。継続 $`k`$ が要るのは、DBMS 行列で横に並ぶ兄弟が木の上では別の場所に来るためである。

## 6. 定理

すべて Lean 4 / Mathlib で証明済み。`sorry` なし、追加公理なし。$`A\langle n \rangle`$ は添字 $`n`$ の基本列、$`\lt_o`$ は木の順序、$`\lt_{\mathrm{lex}}`$ は行列の順序。

```math
M \in \mathrm{ST}_{\mathrm{B}} \implies \mathrm{d2t}(\mathrm{b2d}(M)) = \mathrm{b2t}(M)
\tag{T1}
```

```math
M \in \mathrm{ST}_{\mathrm{B}} \implies \mathrm{b2d}(M) \in \mathrm{ST}_{\mathrm{D}}
\tag{T2}
```

```math
M, N \in \mathrm{ST}_{\mathrm{B}},\ M \ne N \implies
\bigl(\mathrm{d2t}(\mathrm{b2d}(M)) <_o \mathrm{d2t}(\mathrm{b2d}(N))
\iff M <_{\mathrm{lex}} N\bigr)
\tag{T3}
```

```math
M, N \in \mathrm{ST}_{\mathrm{B}},\ \mathrm{b2d}(M) = \mathrm{b2d}(N) \implies M = N
\tag{T4}
```

(T2) の要は次の補題である[^2]。

```math
A \in \mathrm{ST}_{\mathrm{B}},\ |A| > 1,\ n \ge 1 \implies
\exists m \ge 1\ \exists n' \ge n\ \bigl(\mathrm{b2d}(A)\langle m \rangle = \mathrm{b2d}(A \langle n' \rangle)\bigr)
\tag{R}
```

未証明のもの。

```math
N \in \mathrm{ST}_{\mathrm{D}} \implies \exists M \in \mathrm{ST}_{\mathrm{B}}\ \bigl(\mathrm{b2d}(M) = N\bigr)
\tag{S}
```

$`\mathrm{ST}_{\mathrm{D}}`$ の $`|N| \le 7`$ の 1740 個すべてで成立を確認済み（違反 0）[^3]。

## 7. 例

### 7.1 梯子

```math
M = \bigl((0,0),(1,1)\bigr), \qquad \mathrm{b2d}(M) = \bigl((0,0),(1,0),(2,1)\bigr)
```

```math
\begin{aligned}
\mathrm{b2t}(M) &= P(0;\ P(1; Z, Z),\ Z) \cr
\mathrm{b2t}(\mathrm{b2d}(M)) &= P(0;\ P(0;\ P(1;Z,Z),\ Z),\ Z) \cr
\mathrm{d2t}(\mathrm{b2d}(M)) &= P(0;\ P(1;Z,Z),\ Z)
\end{aligned}
```

$`(1,1)`$ は $`\mathrm{ST}_{\mathrm{D}}`$ に置けないので段 1 を深さ 2 へ押し下げ、足場 $`(1,0)`$ を挟む。$`\mathrm{d2t}`$ の「$`\nu = \bot`$ の場合」がその足場を捨てる。

### 7.2 縮約

```math
M = \bigl((0,0),(1,1),(1,0),(2,1),(2,0)\bigr), \qquad
\mathrm{b2d}(M) = \bigl((0,0),(1,0),(2,1),(2,0)\bigr)
```

```math
\begin{aligned}
\mathrm{b2t}(M) &= P\bigl(0; P(1; Z, P(0; P(1; Z, P(0;Z,Z)), Z)), Z\bigr) \cr
\mathrm{b2t}(\mathrm{b2d}(M)) &= P\bigl(0; P(0; P(1; Z, P(0;Z,Z)), Z), Z\bigr)
\end{aligned}
```

節点が 5 個から 4 個に減る。$`\mathrm{d2t}`$ の「$`\nu = \top`$ の場合」が 1 本の柱を 2 つの節点にほどいて $`\mathrm{b2t}(M)`$ を復元する。

## 8. 実装との対応

| 本稿 | Lean（`lean/`） | Python（`rows2.py`） |
|---|---|---|
| $`\mathrm{arg}_p, \mathrm{sib}_p`$ | `takeWhile` / `dropWhile` | `split` |
| $`\sigma^e`$ | `shift1` / `shiftr0` | `shift1` |
| $`\mathrm{u}_p`$ | `unitsLen` | `units_split` |
| $`\pi`$ | `contrPre` | `contrPre` |
| $`\lambda`$ | `ladOf` | `lad` |
| $`d'`$ | `ddOf` | `dd` |
| $`\kappa`$ | `contrLen` | 直書き |
| $`\Gamma^{f,\varphi}_{d,\ell}`$ | `convC` | `convC` |
| $`\mathrm{b2d}`$ | `conC` | `convC M 0 0 True False` |
| $`\mathrm{b2t}`$ | `translate`（`Pair/Term.lean`） | `translate` |
| $`\mathrm{t2b}`$ | — | `untranslate` |
| $`\Delta^{f}_{\ell}`$ | `readK` | `readC` |
| $`\mathrm{d2t}`$ | `readCon` | `readC` |
| (T1) | `readC_conC_ST` | |
| (T2) | `ST_D_conC_final` | |
| (T3) | `conC_olt_iff_seqlex` | |
| (T4) | `conC_injective` | |
| (R) | `reindexD_holds` | |

CLI は [`bms2dbms.py`](bms2dbms.py)、使い方は [README.md](README.md)。

## 注釈

[^1]: (R) を無条件に証明するのが全体で最も重く、`DbmsStd.lean` は 15471 行になった。
    素直に閉じないのは $`\kappa = \top`$（縮約）の枝だけで、残りは右端の道に沿った帰納で片付く。
    経緯は [`lean/DBMS-STD-PLAN.md`](../../lean/DBMS-STD-PLAN.md) に残してある。

[^2]: 命名について。この文書では変換を $`\mathrm{src2dst}`$ の形で呼ぶ。
    Lean 側の `translate` / `conC` / `readCon` はこの規約より前の名前で、
    どれが何から何への写像か名前から読めない。

[^3]: 逆写像を作らず両側の共終性だけで全単射を出す道（Naruyoko 氏が $`\mathrm{Trans}`$ で
    使ったもの）が使えると見込んでいる。その 2 条件は $`\mathrm{ST}_{\mathrm{B}}`$ の
    $`|M| \le 7`$ の 7256 個で違反 0（`cofinal_check.py`）。
    出典: ユーザーブログ:Naruyoko/ペア数列システムの停止性証明に用いられた変換写像の全単射性。
