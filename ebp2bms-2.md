# 拡張ブーフホルツ psi ↔ トリオ数列（BMS 3 行）対応表 その 2: $`\varepsilon_0 \le \alpha`$

[その 1（$`\alpha \lt \varepsilon_0`$）](ebp2bms.md) の続き。
$`\psi_0(\Omega_\alpha)`$ とトリオ数列（z<2 断片）の標準形行列の対応。
生成: `tools/probe_eps_range.py`（BM4-Analysis シートと照合、
w-CNF + $`\varepsilon_0`$ 原子の 135 行中 131 一致、
残り 4 は [dom.md](dom.md) に記録した既知の不一致行）。

$`\alpha`$ の定義域: 本ページの生成器は $`\omega`$ と原子
$`\varepsilon_0 = \psi_0(\Omega_1)`$ から $`+, \cdot, {}^\wedge`$ で作れる範囲。
原理上の上限は $`\alpha \lt \Lambda`$（最小 $`\Omega`$ 不動点）。

表記: 行列は**ユニットごとに分けて**並べる（括弧 1 組 = ユニット $`U_i`$）。

| $`\alpha`$ | $`\psi_0(\Omega_\alpha)`$ | トリオ数列（括弧 1 組 = ユニット） |
|---|---|---|
| $`\varepsilon_0`$ | $`\psi_0(\Omega_{\varepsilon_0})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0+1`$ | $`\psi_0(\Omega_{\varepsilon_0+1})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0+\omega`$ | $`\psi_0(\Omega_{\varepsilon_0+\omega})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 1\end{pmatrix}`$ |
| $`\varepsilon_0+\omega^2`$ | $`\psi_0(\Omega_{\varepsilon_0+\omega^2})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}\begin{pmatrix}2 & 3 & 4\cr 1 & 2 & 2\cr 0 & 1 & 1\end{pmatrix}`$ |
| $`\varepsilon_0+\omega^\omega`$ | $`\psi_0(\Omega_{\varepsilon_0+\omega^\omega})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}\begin{pmatrix}2 & 3 & 4 & 5\cr 1 & 2 & 2 & 0\cr 0 & 1 & 1 & 0\end{pmatrix}`$ |
| $`\varepsilon_0\cdot 2`$ | $`\psi_0(\Omega_{\varepsilon_0\cdot 2})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}\begin{pmatrix}2 & 3 & 4 & 5 & 6\cr 1 & 2 & 2 & 0 & 1\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0\cdot\omega`$ | $`\psi_0(\Omega_{\varepsilon_0\cdot\omega})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 2\cr 0 & 1 & 1 & 0 & 1 & 1\cr 0 & 1 & 1 & 0 & 0 & 1\end{pmatrix}`$ |
| $`\varepsilon_0\cdot\omega^\omega`$ | $`\psi_0(\Omega_{\varepsilon_0\cdot\omega^\omega})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 2 & 3\cr 0 & 1 & 1 & 0 & 1 & 1 & 0\cr 0 & 1 & 1 & 0 & 0 & 1 & 0\end{pmatrix}`$ |
| $`\varepsilon_0^2`$ | $`\psi_0(\Omega_{\varepsilon_0^2})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0 & 1 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0^\omega`$ | $`\psi_0(\Omega_{\varepsilon_0^\omega})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 3\cr 0 & 1 & 1 & 0 & 1 & 0\cr 0 & 1 & 1 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0^{\varepsilon_0}`$ | $`\psi_0(\Omega_{\varepsilon_0^{\varepsilon_0}})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 3 & 4\cr 0 & 1 & 1 & 0 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0^{\varepsilon_0^\omega}`$ | $`\psi_0(\Omega_{\varepsilon_0^{\varepsilon_0^\omega}})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 4\cr 0 & 1 & 1 & 0 & 1 & 0\cr 0 & 1 & 1 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0^{\varepsilon_0^{\varepsilon_0}}`$ | $`\psi_0(\Omega_{\varepsilon_0^{\varepsilon_0^{\varepsilon_0}}})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 4 & 5\cr 0 & 1 & 1 & 0 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0 & 0 & 0\end{pmatrix}`$ |

## 一般式

その 1 の文法と**同一**で、変わるのは指数スロットの中身だけである。
$`\alpha = \sum_i \omega^{\beta_i}`$、$`1 + \beta_i' = \beta_i`$、
$`\beta_i' = \sum_j \omega^{\gamma_{ij}}`$ と 2 段組みに書き、加算項をユニットとして並べる。

```math
M(\alpha) = U_1 +\!\!+ U_2 +\!\!+ \cdots +\!\!+ U_m .
```

### 構造

- ユニット $`U_i = \omega^{\beta_i}`$
  - アンカー
  - 根 — $`\beta_i`$ の先頭の $`1`$ を担う
  - サブユニット $`S_{ij} = \omega^{\gamma_{ij}}`$
    - 桁
    - **OT 埋め込み** $`\mathrm{B}(\gamma_{ij})`$
- ユニット $`U_i = 1`$（$`\beta_i = 0`$ のとき）
  - アンカー
  - z0 列

その 1 との違いは 1 点だけ: サブユニットの下が
「原始数列埋め込み $`\mathrm{PrSS}`$」から
「**OT 埋め込み** $`\mathrm{B}`$」に一般化される。
$`\gamma \lt \varepsilon_0`$ では $`\mathrm{B}(\gamma) = \mathrm{PrSS}(\gamma)`$ なので
その 1 は本ページの特殊ケースである。

### ユニット（加法）

その 1 と同一。状態 $`r`$（直前ユニットの根の $`x`$ 座標）を $`-1`$ で初期化して

```math
\begin{aligned}
U_i &= (r{+}1,\ i{-}1,\ 0) +\!\!+ \mathrm{body}(\beta_i,\ r{+}2,\ i), & r &:= r+2
  &&(\beta_i \ge 1)\cr
U_i &= (r{+}1,\ i{-}1,\ 0) +\!\!+ (r{+}2,\ i,\ 0)
  &&&&(\beta_i = 0,\ \beta_{i-1} \ge 1)\cr
U_i &= (x_t{+}1,\ i,\ 0)
  &&&&(\beta_i = \beta_{i-1} = 0,\ \text{直前列} = (x_t, i{-}1, 0))
\end{aligned}
```

### 根とサブユニット（乗法）

$`1 + \beta' = \beta`$、$`\beta' = \omega^{\gamma_1} + \cdots + \omega^{\gamma_k}`$ として

```math
\mathrm{body}(\beta,\ x_0,\ y) = \underbrace{(x_0,\ y,\ 1)}_{\text{根}}
  +\!\!+ \big[\, \underbrace{(x_0{+}1,\ y,\ 1)}_{\text{桁}}
  +\!\!+ \mathrm{B}(\gamma_j,\ x_0{+}2) \,\big]_{j=1}^{k} .
```

### OT 埋め込み（冪・崩壊）

$`\gamma`$ を Buchholz の順序数表記の項として読み、そのまま列に写す。
加算項 $`\omega^\delta`$ ごとに $`\psi_0`$ ノード $`(x,0,0)`$ を置き、
その行 0 子として引数 $`\mathrm{arg}(\delta)`$ を書く:

```math
\mathrm{B}(\gamma,\ x) = \big[\, (x,\ 0,\ 0)
  +\!\!+ \mathrm{arg}(\delta_j,\ x{+}1) \,\big]_{j=1}^{k},
\qquad \gamma = \omega^{\delta_1} + \cdots + \omega^{\delta_k} .
```

```math
\mathrm{arg}(\delta,\ x) = \begin{cases}
\varepsilon & (\delta = 0)\cr
(x,\ 1,\ 0) +\!\!+ \mathrm{B}(\delta \ominus \varepsilon_0,\ x)
  & (\delta = \varepsilon_0 + \delta')\cr
\mathrm{B}(\delta,\ x) & (\text{otherwise})
\end{cases}
```

第 2 段が**逆崩壊**である。$`\delta \lt \varepsilon_0`$ では
$`\omega^\delta = \psi_0(\delta)`$ なので引数はそのまま $`\delta`$ を書けばよいが、
$`\delta \ge \varepsilon_0`$ では $`\omega^\delta`$ は $`\psi_0(\delta)`$ ではない。
$`\varepsilon_0 = \psi_0(\Omega_1)`$、
$`\varepsilon_0 \cdot \omega = \omega^{\varepsilon_0+1} = \psi_0(\Omega_1+1)`$ のように、
**引数の先頭の $`\varepsilon_0`$ を $`\Omega_1`$ の葉 $`(x,1,0)`$ に戻す**。
$`\delta \ominus \varepsilon_0`$ は先頭の $`\varepsilon_0`$ を 1 つ落とした残り。

**まとめ**: 3 つの行が担うものは変わらない —
行 1 のレベル階段が**加法**、z1 列の木が**乗法**、
$`\mathrm{B}`$ の入れ子が**冪と崩壊**。$`y`$ 行は $`\Omega`$ の添字を担い
（$`(x,1,0) = \Omega_1`$、$`(x,1,0)(x{+}1,2,0) = \Omega_2`$、
$`(x,1,1) = \Omega_\omega`$）、その添字自身がまた同じ文法で書かれる。

## 例

用語は [その 1](ebp2bms.md) と同じ（ア = アンカー、$`S`$ = サブユニット、
$`\mathrm{B}`$ = OT 埋め込み）。

### 例: $`\alpha = \varepsilon_0`$

$`\varepsilon_0 = \omega^{\varepsilon_0}`$ なのでユニット 1 つ、サブユニット 1 つ、
その指数は $`\varepsilon_0`$ 自身。$`\mathrm{B}(\varepsilon_0)`$ =
$`\psi_0`$ ノード＋$`\Omega_1`$ 葉:

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3 & 4\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\mathrm{B}}}_{S}
```

### 例: $`\alpha = \varepsilon_0 + \omega^2`$

ユニット 2 つ。$`U_2`$ はその 1 の文法そのまま（$`\gamma = 1`$ の
サブユニットが 1 つで $`\mathrm{B}(1)`$ はノード 1 本）:

```math
\overbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3 & 4\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\mathrm{B}}}_{S}}^{U_1}
\overbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}}_{S}}^{U_2}
```

### 例: $`\alpha = \varepsilon_0^\omega`$

$`\varepsilon_0^\omega = \omega^{\omega^{\varepsilon_0+1}}`$ なので
$`\gamma = \omega^{\varepsilon_0+1}`$。逆崩壊が効いて
$`\mathrm{arg}(\varepsilon_0+1) = \Omega_1 + 1`$ となり、
$`\mathrm{B}(\gamma)`$ は $`\psi_0(\Omega_1+1)`$ の形になる:

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3 & 4 & 3\cr 0 & 1 & 0\cr 0 & 0 & 0\end{pmatrix}}_{\mathrm{B}}}_{S}
```

### 例: $`\alpha = \varepsilon_0^{\varepsilon_0^{\varepsilon_0}}`$

$`\gamma = \omega^{\varepsilon_0 \cdot 2}`$。引数は先頭の $`\varepsilon_0`$ だけが
$`\Omega_1`$ に戻り、残りの $`\varepsilon_0`$ は $`\psi_0(\Omega_1)`$ のまま書かれる
（$`\mathrm{arg}(\varepsilon_0 \cdot 2) = \Omega_1 + \psi_0(\Omega_1)`$）:

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3 & 4 & 4 & 5\cr 0 & 1 & 0 & 1\cr 0 & 0 & 0 & 0\end{pmatrix}}_{\mathrm{B}}}_{S}
```
