# 拡張ブーフホルツ psi ↔ トリオ数列（BMS 3 行）対応表


$`\psi_0(\Omega_\alpha)`$ とトリオ数列（z<2 断片）の標準形行列の対応。
生成: `tools/build_omega_alpha.py`（BM4-Analysis シートと全数照合済み。
不一致 4 行あり、軌道法則の監査ではビルダー側に一致 — 詳細は [dom.md](dom.md)）。

$`\alpha`$ の定義域: 原理上は拡張ブーフホルツ OT の項全体（$`\alpha \lt \Lambda`$ =
最小 $`\Omega`$ 不動点）。本表の生成器が現在対応するのは
$`\alpha \lt \varepsilon_0`$（$`\omega`$ の CNF で書ける範囲）。

表記: 行列は**ユニットごとに分けて**並べる（括弧 1 組 = ユニット $`U_i`$）。
ユニットの中身（アンカー・根・サブユニット）の区切りは例の節の underbrace を参照。

| $`\alpha`$ | $`\psi_0(\Omega_\alpha)`$ | トリオ数列（括弧 1 組 = ユニット） |
|---|---|---|
| $`\omega`$ | $`\psi_0(\Omega_{\omega})`$ | $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}`$ |
| $`\omega+1`$ | $`\psi_0(\Omega_{\omega+1})`$ | $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 0\end{pmatrix}`$ |
| $`\omega+2`$ | $`\psi_0(\Omega_{\omega+2})`$ | $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 0\end{pmatrix}\begin{pmatrix}4\cr 3\cr 0\end{pmatrix}`$ |
| $`\omega\cdot 2`$ | $`\psi_0(\Omega_{\omega\cdot 2})`$ | $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 1\end{pmatrix}`$ |
| $`\omega\cdot 2+1`$ | $`\psi_0(\Omega_{\omega\cdot 2+1})`$ | $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 1\end{pmatrix}\begin{pmatrix}4 & 5\cr 2 & 3\cr 0 & 0\end{pmatrix}`$ |
| $`\omega\cdot 2+2`$ | $`\psi_0(\Omega_{\omega\cdot 2+2})`$ | $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 1\end{pmatrix}\begin{pmatrix}4 & 5\cr 2 & 3\cr 0 & 0\end{pmatrix}\begin{pmatrix}6\cr 4\cr 0\end{pmatrix}`$ |
| $`\omega\cdot 2+3`$ | $`\psi_0(\Omega_{\omega\cdot 2+3})`$ | $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 1\end{pmatrix}\begin{pmatrix}4 & 5\cr 2 & 3\cr 0 & 0\end{pmatrix}\begin{pmatrix}6\cr 4\cr 0\end{pmatrix}\begin{pmatrix}7\cr 5\cr 0\end{pmatrix}`$ |
| $`\omega\cdot 3`$ | $`\psi_0(\Omega_{\omega\cdot 3})`$ | $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 1\end{pmatrix}\begin{pmatrix}4 & 5\cr 2 & 3\cr 0 & 1\end{pmatrix}`$ |
| $`\omega\cdot 4`$ | $`\psi_0(\Omega_{\omega\cdot 4})`$ | $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 1\end{pmatrix}\begin{pmatrix}4 & 5\cr 2 & 3\cr 0 & 1\end{pmatrix}\begin{pmatrix}6 & 7\cr 3 & 4\cr 0 & 1\end{pmatrix}`$ |
| $`\omega^2`$ | $`\psi_0(\Omega_{\omega^2})`$ | $`\begin{pmatrix}0 & 1 & 2\cr 0 & 1 & 1\cr 0 & 1 & 1\end{pmatrix}`$ |
| $`\omega^2+1`$ | $`\psi_0(\Omega_{\omega^2+1})`$ | $`\begin{pmatrix}0 & 1 & 2\cr 0 & 1 & 1\cr 0 & 1 & 1\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 0\end{pmatrix}`$ |
| $`\omega^2+\omega`$ | $`\psi_0(\Omega_{\omega^2+\omega})`$ | $`\begin{pmatrix}0 & 1 & 2\cr 0 & 1 & 1\cr 0 & 1 & 1\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 1\end{pmatrix}`$ |
| $`\omega^2\cdot 2`$ | $`\psi_0(\Omega_{\omega^2\cdot 2})`$ | $`\begin{pmatrix}0 & 1 & 2\cr 0 & 1 & 1\cr 0 & 1 & 1\end{pmatrix}\begin{pmatrix}2 & 3 & 4\cr 1 & 2 & 2\cr 0 & 1 & 1\end{pmatrix}`$ |
| $`\omega^3`$ | $`\psi_0(\Omega_{\omega^3})`$ | $`\begin{pmatrix}0 & 1 & 2 & 2\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 1\end{pmatrix}`$ |
| $`\omega^\omega`$ | $`\psi_0(\Omega_{\omega^\omega})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 0\cr 0 & 1 & 1 & 0\end{pmatrix}`$ |
| $`\omega^\omega+1`$ | $`\psi_0(\Omega_{\omega^\omega+1})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 0\cr 0 & 1 & 1 & 0\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 0\end{pmatrix}`$ |
| $`\omega^{\omega+1}`$ | $`\psi_0(\Omega_{\omega^{\omega+1}})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 2\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 1\end{pmatrix}`$ |
| $`\omega^{\omega^\omega}`$ | $`\psi_0(\Omega_{\omega^{\omega^\omega}})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 0\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}`$ |

## 一般式（$`\alpha \lt \varepsilon_0`$）

$`\Omega_\alpha`$ の $`\alpha`$ を 2 段組みのカントール標準形として捉える
（係数は展開して並べる。$`1 + \beta_i' = \beta_i`$ は先頭の $`1`$ を外した残り）:

```math
\begin{aligned}
\alpha &= \sum_i \omega^{\beta_i}, & \beta_1 &\ge \beta_2 \ge \cdots \ge \beta_m \cr
\beta_i' &= \sum_j \omega^{\gamma_{ij}}, & \gamma_{i1} &\ge \gamma_{i2} \ge \cdots
\end{aligned}
```

行列は加算項 $`\omega^{\beta_i}`$ を**ユニット** $`U_i`$ として並べたもの
（$`+\!\!+`$ は列リストの連結）:

```math
M(\alpha) = U_1 +\!\!+ U_2 +\!\!+ \cdots +\!\!+ U_m .
```

### 構造

- ユニット $`U_i = \omega^{\beta_i}`$
  - アンカー
  - 根 — $`\beta_i`$ の先頭の $`1`$ を担う
  - サブユニット $`S_{i1} = \omega^{\gamma_{i1}}`$
    - 桁
    - 原始数列埋め込み $`\mathrm{PrSS}(\gamma_{i1})`$
  - サブユニット $`S_{i2} = \omega^{\gamma_{i2}}`$
    - 桁
    - 原始数列埋め込み $`\mathrm{PrSS}(\gamma_{i2})`$
  - …
- ユニット $`U_i = 1`$（$`\beta_i = 0`$ のとき）
  - アンカー
  - z0 列

すなわち**ユニットはアンカーと根とサブユニットからなり、サブユニットは桁と
原始数列埋め込みからなる**（$`\beta_i = 0`$ のユニットだけは根もサブユニットも
持たず、アンカーと z0 列 1 本）。

### 用語

列 $`(x, y, z)`$ を $`z`$ の値で呼び分ける —
**z1 列** = $`z = 1`$ の列、**z0 列** = $`z = 0`$ の列。
列の行 0 親は BM の通常の読み（**それより左で $`x`$ が真に小さい直近の列**。
$`x`$ は左から単調ではなく、下がって戻ることがある）。

- **ユニット** $`U_i`$: $`\alpha`$ の加算項 $`\omega^{\beta_i}`$ 一つ分に当たる列の区間。
  - レベル $`y = i`$ に住む。
- **アンカー**: ユニットの先頭に置く z0 列（下のユニット規則の $`(r{+}1,\ i{-}1,\ 0)`$）。
  - 直前ユニットの番地を z0 の形で作り直し、新しいユニットをぶら下げる足場になる
    （z1 の極限標識には後続を直接ぶら下げられない）。
  - 先頭ユニット $`U_1`$ のアンカーは $`(0,0,0)`$ 自身（直前の番地 = $`0`$、地面）。
- **根**: アンカーの次に置く z1 列。
  - 分解 $`1 + \beta_i' = \beta_i`$ の先頭の $`1`$ を担う。
- **サブユニット** $`S_{ij}`$: $`\beta_i'`$ の加算項 $`\omega^{\gamma_{ij}}`$ 一つ分。
  - 桁と原始数列埋め込みからなる。
- **桁**: サブユニットの先頭の z1 列。
  - 根の $`x`$ を $`x_0`$ とすると桁の $`x`$ は全部 $`x_0{+}1`$ で、
    全部 根の行 0 子になる。
- **原始数列埋め込み** $`\mathrm{PrSS}(\gamma_{ij})`$: 桁の下（行 0 子孫）に
  ぶら下がる $`y = 0`$ の z0 列の森。
  - 指数 $`\gamma_{ij}`$ を担う。

状態として直前のユニットの根の $`x`$ 座標 $`r`$ を持ち回る。

### ユニット（加法）

状態 $`r`$ は $`-1`$ で初期化する（$`U_1`$ のアンカーが $`(0,0,0)`$ になる）。

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

すなわち $`\beta_i = 0`$ のユニットはアンカーと素の z0 列でレベルを 1 段登り、
それが続く間はアンカーを共有して z0 の鎖で登り続ける。

### 根とサブユニット（乗法）

$`1 + \beta' = \beta`$ と分解する
（$`\beta \ge \omega`$ なら $`\beta' = \beta`$、有限 $`k`$ なら $`\beta' = k-1`$）。
$`\beta' = \omega^{\gamma_1} + \cdots + \omega^{\gamma_k}`$ として

```math
\mathrm{body}(\beta,\ x_0,\ y) = \underbrace{(x_0,\ y,\ 1)}_{\text{根}}
  +\!\!+ \big[\, \underbrace{(x_0{+}1,\ y,\ 1)}_{\text{桁}}
  +\!\!+ \mathrm{PrSS}(\gamma_j,\ x_0{+}2) \,\big]_{j=1}^{k} .
```

根が 1 列、サブユニットが $`\beta'`$ の加算項 1 つにつき 1 組
（桁 1 列＋その原始数列埋め込み）。

### 原始数列埋め込み（冪）

$`\gamma = \omega^{\delta_1} + \cdots + \omega^{\delta_l}`$ として

```math
\mathrm{PrSS}(\gamma,\ x) = \big[\, (x,\ 0,\ 0)
  +\!\!+ \mathrm{PrSS}(\delta_j,\ x{+}1) \,\big]_{j=1}^{l},
\qquad \mathrm{PrSS}(0,\ x) = \varepsilon .
```

これは $`\gamma`$ の 1 行バシク行列（原始数列）そのもので、常に $`y = z = 0`$ の列に住む。

**まとめ**: 3 つの行が CNF の 3 つの演算をそのまま担う —
行 1 のレベル階段が**加法**（ユニットごとに 1 段）、z1 列の木が**乗法**（$`\omega`$ 因子）、
z0 の原始数列埋め込みが**冪**（指数の原始数列）。

### 例: $`\alpha = \omega^2 + \omega + 1`$

ユニット 3 つ。ア = アンカー。桁と原始数列埋め込みの組は
さらに underbrace で括って**サブユニット**とし、ラベルはその値 $`\omega^{\gamma_{ij}}`$:

```math
\overbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}}_{1}}^{U_1}
\overbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}}^{U_2}
\overbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}5\cr 3\cr 0\end{pmatrix}}_{{+}1}}^{U_3}
```

### 例: $`\alpha = \omega^{\omega^\omega}`$

ユニット 1 つ。$`\mathrm{P}(\gamma) = \mathrm{PrSS}(\gamma)`$（原始数列埋め込み）。
サブユニット $`\omega^\omega`$ = 桁 + $`\mathrm{P}(\omega)`$:

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3 & 4\cr 0 & 0\cr 0 & 0\end{pmatrix}}_{\mathrm{P}(\omega)}}_{\omega^{\omega}}
```

### 例: $`\alpha = \omega^{\omega^{\omega^\omega}}`$

一つ前の例との違いは原始数列埋め込みだけ。$`\mathrm{P}`$ の節が 1 つ増えるごとに
指数の塔が 1 段上がる（$`(3,0,0)`$ で $`g=1`$、$`(4,0,0)`$ を継いで $`g=\omega`$、
$`(5,0,0)`$ を継いで $`g=\omega^\omega`$）:

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3 & 4 & 5\cr 0 & 0 & 0\cr 0 & 0 & 0\end{pmatrix}}_{\mathrm{P}(\omega^{\omega})}}_{\omega^{\omega^{\omega}}}
```

### 例: $`\alpha = \omega^{\omega^{1+1}+\omega^{1+1}}`$

$`\beta = \omega^2 + \omega^2`$ は加算項 2 つなのでサブユニットが 2 つ。
各サブユニットの指数 $`\gamma = 2`$ は $`\mathrm{PrSS}`$ の節 2 つ（兄弟、同じ $`x`$）。
$`\mathrm{P}`$ の中では兄弟（同じ $`x`$）が $`+1`$、子（$`x{+}1`$）が塔 1 段:

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3 & 3\cr 0 & 0\cr 0 & 0\end{pmatrix}}_{\mathrm{P}(2)}}_{\omega^{2}}\underbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3 & 3\cr 0 & 0\cr 0 & 0\end{pmatrix}}_{\mathrm{P}(2)}}_{\omega^{2}}
```

### 例: $`\alpha = \omega^{\omega^{\omega^{\omega^5+\omega^4}+\omega^3}+\omega^2}`$

サブユニット 2 つ。サブユニット 1 の指数
$`\gamma_{11} = \omega^{\omega^5+\omega^4} + \omega^3`$ の原始数列埋め込みは
$`\mathrm{P}`$ の再帰で書かれる:

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3 & 4 & 5 & 5 & 5 & 5 & 5 & 4 & 5 & 5 & 5 & 5 & 3 & 4 & 4 & 4\cr 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0\cr 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0\end{pmatrix}}_{\mathrm{P}(\omega^{\omega^{5}+\omega^{4}}+\omega^{3})}}_{\omega^{\omega^{\omega^{5}+\omega^{4}}+\omega^{3}}}\underbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3 & 3\cr 0 & 0\cr 0 & 0\end{pmatrix}}_{\mathrm{P}(2)}}_{\omega^{2}}
```

サブユニット 1 の原始数列埋め込みの入れ子（列は全部 $`y = z = 0`$ なので $`x`$ だけ書く）:

```math
\underbrace{(3)\overbrace{(4)\overbrace{(5)(5)(5)(5)(5)}^{\mathrm{P}(5)}(4)\overbrace{(5)(5)(5)(5)}^{\mathrm{P}(4)}}^{\mathrm{P}(\omega^5+\omega^4)}\ (3)\overbrace{(4)(4)(4)}^{\mathrm{P}(3)}}_{\mathrm{P}(\omega^{\omega^5+\omega^4}+\omega^3)}
```

原始数列埋め込みの中身は指数の $`\mathrm{CNF}`$ をそのまま 1 行 BM に写した入れ子で、
どの深さでも同じ文法が繰り返される。
