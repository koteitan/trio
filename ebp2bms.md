# 拡張ブーフホルツ psi ↔ トリオ数列（BMS 3 行）対応表


$`\psi_0(\Omega_\alpha)`$ とトリオ数列（z<2 断片）の標準形行列の対応。
生成: `tools/build_omega_alpha.py`（BM4-Analysis シートと全数照合済み、
シート誤記 4 行は軌道法則で監査済み — 詳細は [dom.md](dom.md)）。

$`\alpha`$ の定義域: 原理上は拡張ブーフホルツ OT の項全体（$`\alpha \lt \Lambda`$ =
最小 $`\Omega`$ 不動点）。本表の生成器が現在対応するのは
$`\alpha \lt \varepsilon_0`$（$`\omega`$ の CNF で書ける範囲）。

縦線の凡例: 二重実線 $`\|`$ = 単位境界、点線 = z1 根の両側（アンカー・桁との境）、
実線 $`|`$ = 桁境界。

| $`\alpha`$ | $`\psi_0(\Omega_\alpha)`$ | トリオ数列 |
|---|---|---|
| $`\omega`$ | $`\psi_0(\Omega_{\omega})`$ | $`\left(\begin{array}{c:c}0 & 1\cr 0 & 1\cr 0 & 1\end{array}\right)`$ |
| $`\omega+1`$ | $`\psi_0(\Omega_{\omega+1})`$ | $`\left(\begin{array}{c:c||c:c}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 2\cr 0 & 1 & 0 & 0\end{array}\right)`$ |
| $`\omega+2`$ | $`\psi_0(\Omega_{\omega+2})`$ | $`\left(\begin{array}{c:c||c:c||c}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 2 & 3\cr 0 & 1 & 0 & 0 & 0\end{array}\right)`$ |
| $`\omega\cdot 2`$ | $`\psi_0(\Omega_{\omega\cdot 2})`$ | $`\left(\begin{array}{c:c||c:c}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 2\cr 0 & 1 & 0 & 1\end{array}\right)`$ |
| $`\omega\cdot 2+1`$ | $`\psi_0(\Omega_{\omega\cdot 2+1})`$ | $`\left(\begin{array}{c:c||c:c||c:c}0 & 1 & 2 & 3 & 4 & 5\cr 0 & 1 & 1 & 2 & 2 & 3\cr 0 & 1 & 0 & 1 & 0 & 0\end{array}\right)`$ |
| $`\omega\cdot 2+2`$ | $`\psi_0(\Omega_{\omega\cdot 2+2})`$ | $`\left(\begin{array}{c:c||c:c||c:c||c}0 & 1 & 2 & 3 & 4 & 5 & 6\cr 0 & 1 & 1 & 2 & 2 & 3 & 4\cr 0 & 1 & 0 & 1 & 0 & 0 & 0\end{array}\right)`$ |
| $`\omega\cdot 2+3`$ | $`\psi_0(\Omega_{\omega\cdot 2+3})`$ | $`\left(\begin{array}{c:c||c:c||c:c||c||c}0 & 1 & 2 & 3 & 4 & 5 & 6 & 7\cr 0 & 1 & 1 & 2 & 2 & 3 & 4 & 5\cr 0 & 1 & 0 & 1 & 0 & 0 & 0 & 0\end{array}\right)`$ |
| $`\omega\cdot 3`$ | $`\psi_0(\Omega_{\omega\cdot 3})`$ | $`\left(\begin{array}{c:c||c:c||c:c}0 & 1 & 2 & 3 & 4 & 5\cr 0 & 1 & 1 & 2 & 2 & 3\cr 0 & 1 & 0 & 1 & 0 & 1\end{array}\right)`$ |
| $`\omega\cdot 4`$ | $`\psi_0(\Omega_{\omega\cdot 4})`$ | $`\left(\begin{array}{c:c||c:c||c:c||c:c}0 & 1 & 2 & 3 & 4 & 5 & 6 & 7\cr 0 & 1 & 1 & 2 & 2 & 3 & 3 & 4\cr 0 & 1 & 0 & 1 & 0 & 1 & 0 & 1\end{array}\right)`$ |
| $`\omega^2`$ | $`\psi_0(\Omega_{\omega^2})`$ | $`\left(\begin{array}{c:c:c}0 & 1 & 2\cr 0 & 1 & 1\cr 0 & 1 & 1\end{array}\right)`$ |
| $`\omega^2+1`$ | $`\psi_0(\Omega_{\omega^2+1})`$ | $`\left(\begin{array}{c:c:c||c:c}0 & 1 & 2 & 2 & 3\cr 0 & 1 & 1 & 1 & 2\cr 0 & 1 & 1 & 0 & 0\end{array}\right)`$ |
| $`\omega^2+\omega`$ | $`\psi_0(\Omega_{\omega^2+\omega})`$ | $`\left(\begin{array}{c:c:c||c:c}0 & 1 & 2 & 2 & 3\cr 0 & 1 & 1 & 1 & 2\cr 0 & 1 & 1 & 0 & 1\end{array}\right)`$ |
| $`\omega^2\cdot 2`$ | $`\psi_0(\Omega_{\omega^2\cdot 2})`$ | $`\left(\begin{array}{c:c:c||c:c:c}0 & 1 & 2 & 2 & 3 & 4\cr 0 & 1 & 1 & 1 & 2 & 2\cr 0 & 1 & 1 & 0 & 1 & 1\end{array}\right)`$ |
| $`\omega^3`$ | $`\psi_0(\Omega_{\omega^3})`$ | $`\left(\begin{array}{c:c:c|c}0 & 1 & 2 & 2\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 1\end{array}\right)`$ |
| $`\omega^\omega`$ | $`\psi_0(\Omega_{\omega^\omega})`$ | $`\left(\begin{array}{c:c:cc}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 0\cr 0 & 1 & 1 & 0\end{array}\right)`$ |
| $`\omega^\omega+1`$ | $`\psi_0(\Omega_{\omega^\omega+1})`$ | $`\left(\begin{array}{c:c:cc||c:c}0 & 1 & 2 & 3 & 2 & 3\cr 0 & 1 & 1 & 0 & 1 & 2\cr 0 & 1 & 1 & 0 & 0 & 0\end{array}\right)`$ |
| $`\omega^{\omega+1}`$ | $`\psi_0(\Omega_{\omega^{\omega+1}})`$ | $`\left(\begin{array}{c:c:cc|c}0 & 1 & 2 & 3 & 2\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 1\end{array}\right)`$ |
| $`\omega^{\omega^\omega}`$ | $`\psi_0(\Omega_{\omega^{\omega^\omega}})`$ | $`\left(\begin{array}{c:c:ccc}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 0\cr 0 & 1 & 1 & 0 & 0\end{array}\right)`$ |

## 一般式（$`\alpha \lt \varepsilon_0`$）

$`\alpha`$ を係数を展開した CNF（単位の列、非増加）で書く:

```math
\alpha = \omega^{\beta_1} + \omega^{\beta_2} + \cdots + \omega^{\beta_m},
\qquad \beta_1 \ge \beta_2 \ge \cdots \ge \beta_m .
```

行列は列リストの連結（$`+\!\!+`$）で与えられる:

```math
M(\alpha) = U_1 +\!\!+ U_2 +\!\!+ \cdots +\!\!+ U_m .
```

**用語**: 列 $`(x, y, z)`$ を $`z`$ の値で呼び分ける —
**z1 列** = $`z = 1`$ の列、**z0 列** = $`z = 0`$ の列。
列の行 0 親は BM の通常の読み（**それより左で $`x`$ が真に小さい直近の列**。
$`x`$ は左から単調ではなく、下がって戻ることがある）。

- **単位** $`U_i`$: $`\alpha`$ の CNF の加法項 $`\omega^{\beta_i}`$ 一つ分に当たる列の区間。
  - アンカーと本体からなる。
  - レベル $`y = i`$ に住む。
- **アンカー**: 単位の先頭に置く z0 列（下の単位規則の $`(r{+}1,\ i{-}1,\ 0)`$）。
  - 直前単位の番地を z0 の形で作り直し、新しい単位をぶら下げる足場になる
    （z1 の極限標識には後続を直接ぶら下げられない）。
  - 先頭単位 $`U_1`$ のアンカーは $`(0,0,0)`$ 自身（直前の番地 = $`0`$、地面）。
- **本体**: 単位のアンカー以外の残り。
  - $`\omega^\beta`$（$`\beta \ge 1`$）の単位では z1 列の並び＋閉包子
    （後述の $`\mathrm{body}`$）。
  - $`+1`$ 単位では z0 列 1 本。
- **z1 根**: 本体の先頭の z1 列。
  - 分解 $`1 + \beta' = \beta`$ の先頭の $`1`$ を担う。
- **桁**: 本体内の z1 根以外の z1 列。
  - $`\beta'`$ の CNF の加法項 $`\omega^g`$ 一つにつき 1 列（下の $`\mathrm{body}`$ 参照）。
  - z1 根の $`x`$ を $`x_0`$ とすると桁の $`x`$ は全部 $`x_0{+}1`$ で、
    全部 z1 根の行 0 子になる。
- **閉包子**: 桁の下（行 0 子孫）にぶら下がる $`y = 0`$ の z0 列。
  - その全体（後述の $`\mathrm{PrSS}`$）が桁の指数 $`g`$ を担う。

状態として直前の単位の z1 根の $`x`$ 座標 $`r`$ を持ち回る。

**単位（加法）**:

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

すなわち $`+1`$ 単位はアンカーと素の z0 列でレベルを 1 段登り、$`+1`$ が続く間は
アンカーを共有して z0 の鎖で登り続ける。

**本体（乗法）**: $`1 + \beta' = \beta`$ と分解する
（$`\beta \ge \omega`$ なら $`\beta' = \beta`$、有限 $`k`$ なら $`\beta' = k-1`$）。
$`\beta' = \omega^{g_1} + \cdots + \omega^{g_k}`$（単位の列、非増加）として

```math
\mathrm{body}(\beta,\ x_0,\ y) = (x_0,\ y,\ 1)
  +\!\!+ \big[\, (x_0{+}1,\ y,\ 1) +\!\!+ \mathrm{PrSS}(g_j,\ x_0{+}2) \,\big]_{j=1}^{k} .
```

z1 根が 1 つ、z1 子が $`\beta`$ の桁 1 つにつき 1 列。桁 $`\omega^{g}`$ の指数 $`g`$ は
子の閉包子森 $`\mathrm{PrSS}(g)`$ が担う。

**閉包子森（冪）**: $`g = \omega^{h_1} + \cdots + \omega^{h_l}`$（単位の列）として

```math
\mathrm{PrSS}(g,\ x) = \big[\, (x,\ 0,\ 0) +\!\!+ \mathrm{PrSS}(h_j,\ x{+}1) \,\big]_{j=1}^{l},
\qquad \mathrm{PrSS}(0,\ x) = \varepsilon .
```

これは $`g`$ の 1 行バシク行列（原始数列）そのもので、常に $`y = z = 0`$ の列に住む。

**まとめ**: 3 つの行が CNF の 3 つの演算をそのまま担う —
行 1 のレベル階段が**加法**（単位ごとに 1 段）、z1 列の木が**乗法**（$`\omega`$ 因子）、
z0 閉包子森が**冪**（指数の原始数列）。

### 例: $`\alpha = \omega^2 + \omega + 1`$

```math
\underbrace{(0,0,0)(1,1,1)(2,1,1)}_{U_1:\ \text{アンカー+body}(\omega^2)}
\underbrace{(2,1,0)(3,2,1)}_{U_2:\ \text{アンカー+body}(\omega)}
\underbrace{(4,2,0)(5,3,0)}_{U_3:\ \text{アンカー+z0}\ (+1)}
```

### 例: $`\alpha = \omega^{\omega^\omega}`$

単位 1 つ。$`\beta' = \omega^\omega`$ の桁は $`\omega^{g}`$（$`g = \omega`$）1 つで、
$`\mathrm{PrSS}(\omega) = (x,0,0)(x{+}1,0,0)`$:

```math
\underbrace{(0,0,0)}_{\text{アンカー}}
\underbrace{(1,1,1)}_{\text{z1 根}}
\underbrace{(2,1,1)}_{\text{桁}}
\underbrace{(3,0,0)(4,0,0)}_{\mathrm{PrSS}(\omega)}
```

### 例: $`\alpha = \omega^{\omega^{\omega^\omega}}`$

一つ前の例との違いは閉包子森だけ。桁の指数が $`g = \omega^\omega`$ に上がり、
$`\mathrm{PrSS}(\omega^\omega)`$ は鎖が 1 節伸びる:

```math
\underbrace{(0,0,0)}_{\text{アンカー}}
\underbrace{(1,1,1)}_{\text{z1 根}}
\underbrace{(2,1,1)}_{\text{桁}}
\underbrace{(3,0,0)(4,0,0)(5,0,0)}_{\mathrm{PrSS}(\omega^\omega)}
```

（$`\mathrm{PrSS}`$ の節が 1 つ増えるごとに指数の塔が 1 段上がる:
$`(3,0,0)`$ で $`g=1`$、$`(4,0,0)`$ を継いで $`g=\omega`$、
$`(5,0,0)`$ を継いで $`g=\omega^\omega`$。）

### 例: $`\alpha = \omega^{\omega^{1+1} + \omega^{1+1}}`$

指数 $`\beta = \omega^2 + \omega^2`$ は加法項 2 つなので**桁が 2 列**。
各桁の指数 $`g = 2 = 1 + 1`$ は閉包子 2 節（兄弟、同じ $`x`$）:

```math
\underbrace{(0,0,0)}_{\text{アンカー}}
\underbrace{(1,1,1)}_{\text{z1 根}}
\underbrace{(2,1,1)}_{\text{桁}}
\underbrace{(3,0,0)(3,0,0)}_{\mathrm{PrSS}(2)}
\underbrace{(2,1,1)}_{\text{桁}}
\underbrace{(3,0,0)(3,0,0)}_{\mathrm{PrSS}(2)}
```

$`\mathrm{PrSS}`$ の中では**兄弟（同じ $`x`$）が $`+1`$、子（$`x{+}1`$）が塔 1 段**、
という 1 行 BM そのままの読みになっている。桁の並びも同様に、
兄弟の桁（同じ $`x_0{+}1`$）が指数の加法項 1 つずつを担う。

### 例: $`\alpha = \omega^{\omega^{\omega^{\omega^5+\omega^4}+\omega^3}+\omega^2}`$

指数 $`\beta = \omega^{\omega^{\omega^5+\omega^4}+\omega^3} + \omega^2`$ で桁は 2 列。
縦線は表と同じ凡例（点線 = z1 根の両側、実線 = 桁境界。桁は自分の閉包子森を
連れて 1 区画になる）:

```math
\left(\begin{array}{c:c:ccccccccccccccccc|ccc}0 & 1 & 2 & 3 & 4 & 5 & 5 & 5 & 5 & 5 & 4 & 5 & 5 & 5 & 5 & 3 & 4 & 4 & 4 & 2 & 3 & 3\cr 0 & 1 & 1 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 1 & 0 & 0\cr 0 & 1 & 1 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 1 & 0 & 0\end{array}\right)
```

桁 1 の指数 $`g_1 = \omega^{\omega^5+\omega^4} + \omega^3`$ の閉包子森
（$`x = 3`$ の節 2 つ = 加法項 2 つ）は $`\mathrm{PrSS}`$ の再帰で書かれる:

```math
\underbrace{(3)\overbrace{(4)\overbrace{(5)(5)(5)(5)(5)}^{\mathrm{PrSS}(5)}(4)\overbrace{(5)(5)(5)(5)}^{\mathrm{PrSS}(4)}}^{\mathrm{PrSS}(\omega^5+\omega^4)}\ (3)\overbrace{(4)(4)(4)}^{\mathrm{PrSS}(3)}}_{\mathrm{PrSS}(\omega^{\omega^5+\omega^4}+\omega^3)}
```

（閉包子は全部 $`y = z = 0`$ なので $`x`$ だけ書いた。）
閉包子森の中身は指数の $`\mathrm{CNF}`$ をそのまま 1 行 BM に写した入れ子で、
どの深さでも同じ文法が繰り返される。
