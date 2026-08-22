# 拡張ブーフホルツ psi ↔ トリオ数列 アルゴリズム: ε₀ ≤ α < Λ

[← 戻る](../../../README.md) | [Japanese](README.md) | [English](README-en.md) | [α < ε₀](../1/README.md) | [ε₀ ≤ α < Λ](README.md)

$`\psi_0(\Omega_\alpha)`$ に対応するトリオ数列（z<2 断片）の標準形行列を作る一般式、$`\varepsilon_0 \le \alpha \lt \Lambda`$（$`\Lambda`$ = 最小 $`\Omega`$ 不動点）。

具体的な行列は[対応表](../../sheet/2/README.md)にある。

[α < ε₀ 版](../1/README.md)の文法と**同一**で、変わるのは指数スロットの中身だけである。
$`\alpha = \sum_i \omega^{\beta_i}`$、$`1 + \beta_i' = \beta_i`$、
$`\beta_i' = \sum_j \omega^{\gamma_{ij}}`$ と 2 段組みに書き、加算項を加算ユニットとして並べる。

```math
M(\alpha) = U_1 +\!\!+ U_2 +\!\!+ \cdots +\!\!+ U_m .
```

### 構造

- 加算ユニット $`U_i = \omega^{\beta_i}`$
  - アンカー
  - 根 — $`\beta_i`$ の先頭の $`1`$ を担う
  - 乗算ユニット $`S_{ij} = \omega^{\gamma_{ij}}`$
    - 桁
    - **OT 埋め込み** $`\mathrm{B}(\gamma_{ij})`$
- 加算ユニット $`U_i = 1`$（$`\beta_i = 0`$ のとき）
  - アンカー
  - z0 列

[α < ε₀ 版](../1/README.md)との違いは 1 点だけ: 乗算ユニットの下が
「原始数列埋め込み $`\mathrm{PrSS}`$」から
「**OT 埋め込み** $`\mathrm{B}`$」に一般化される。
$`\gamma \lt \varepsilon_0`$ では $`\mathrm{B}(\gamma) = \mathrm{PrSS}(\gamma)`$ なので
α < ε₀ 版は本ページの特殊ケースである。

### 加算ユニット（加法）

α < ε₀ 版と同一。状態 $`r`$（直前の加算ユニットの根の $`x`$ 座標）を $`-1`$ で初期化して

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

### 根と乗算ユニット（乗法）

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

### $`\alpha`$ が崩壊値 $`\psi_0(\Omega_X)`$ のとき

添字 $`X`$ の行列がそのまま入る:

```math
M(\psi_0(\Omega_X)) = (0,0,0)(1,1,1)(2,1,1) +\!\!+ \mathrm{shift}(M(X),\ 3).
```

**$`M(X)`$ のアンカーが、$`x`$ シフトされて $`\psi_0`$ ノード $`(3,0,0)`$ になる**
（アンカーと $`\psi_0`$ ノードは同じ列で、役目が二重になっている）。
$`X`$ の中身は $`x`$ をずらすだけで一切書き換えない。

例: $`M(\omega) = (0,0,0)(1,1,1)`$ なので
$`M(\psi_0(\Omega_\omega)) = (0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)`$。
$`M(\omega^\omega) = (0,0,0)(1,1,1)(2,1,1)(3,0,0)`$ なので
$`M(\psi_0(\Omega_{\omega^\omega})) = (0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)(5,1,1)(6,0,0)`$。

$`\alpha = \Omega_1`$ のときは $`\psi_0`$ を通さないので別扱いで、
$`M(\Omega_1) = (0,0,0)(1,1,1)(2,1,1)(3,1,0)`$。

### $`\alpha = \Omega_v`$ 自身（$`v \ge 2`$）

$`\alpha`$ が非可算のときは $`\psi_0`$ ノードが立たず、行列は
$`B = (0,0,0)(1,1,1)(2,1,1)(3,1,0) = M(\Omega_1)`$ を単位として作られる。
持ち上げ $`\mathrm{L}(x,y,z) = (x{+}1,\ y{+}1,\ z)`$ を使うと、**有限の $`v`$** では

```math
M(\Omega_v) = B +\!\!+ \mathrm{L}(B) +\!\!+ \mathrm{L}^2(B) +\!\!+ \cdots +\!\!+ \mathrm{L}^{v-1}(B)
```

（$`v = 1,\dots,5`$ でシートと一致）。基数の後続 1 段が持ち上げ 1 回に対応する。

極限側はシートの観測値（法則の一般形は未確定）:

| $`v`$ | $`M(\Omega_v)`$ | 読み |
|---|---|---|
| $`\omega`$ | $`B +\!\!+ M(\omega)[1{:}]`$ | 対角化（$`\mathrm{L}`$ の鎖の極限） |
| $`\Omega_1`$ | $`B +\!\!+ M(\Omega_1)[1{:}]`$ | 同上 |
| $`\Omega_2`$ | $`M(\Omega_{\Omega_1}) +\!\!+ \mathrm{L}(M(\Omega_{\Omega_1}))`$ | 持ち上げ 1 回（基数の後続） |

$`\Omega_{\Omega_2}`$ の行が示すとおり、**添字の側でも「後続 = 持ち上げ、極限 = 対角化」
という同じ文法が繰り返される**。

#### 一般の $`v`$（レベル列への $`B`$ 挿入）

$`M(v)`$ を行 0 の森として読み、**レベル列**に注目する。レベル列とは
$`z = 0`$、$`y \ge 1`$ の列のうち、行 0 親が

- 無いか z0 列（ただし親が根のアンカー以外の $`\psi_0`$ ノードなら除く = $`\Omega`$ 葉）、または
- z1 列であってそれが**根**（親が z0）であるもの（親が**桁**なら除く = $`\Omega`$ 葉）

を満たすもの、すなわちアンカーと $`{+}1`$ 標識である。すると

1. $`M(v)`$ の末尾列がレベル列ならそれを削除する。
2. 根のアンカーと残る各レベル列 $`c`$ の直下に、$`B`$ の尾
   $`(1,1,1)(2,1,1)(3,1,0)`$ を $`y`$ だけ $`c_y`$ 持ち上げて挿す。
3. 行 0 深さを $`x`$ として書き出す。

これで $`\alpha = \Omega_v`$ のシート 87 行中 **80 行が一致**する。
添字が入れ子の $`\Omega`$（$`\Omega_{\Omega_{\Omega_{\Omega_\Omega}}}`$ まで）も含む。
有限 $`v`$ では上の持ち上げ鎖の閉じた形と一致することを機械検査している。

残る 7 行（$`v = \omega\cdot 5`$, $`\omega^2{+}\omega{+}2`$, $`\omega^2{+}\omega\cdot 2`$,
$`\omega^2{+}\omega\cdot 3`$, $`\omega^2\cdot 2`$, $`\Omega_3`$ ほか）は、挿入の直後に来る列の
$`x`$ が 1 だけずれる。$`\omega^2\cdot 2`$ の行はラベル重複（同じラベルの別行は一致）で、
[dom.md](../../../dom.md) に記録した既知の不一致行と同種の可能性がある。未解決。

**まとめ**: 3 段の入れ子が担うものは変わらない —
**加算ユニットの個数が加法**、**乗算ユニットの個数が乗法**（因子 1 つずつ）、
**$`\mathrm{B}`$ の入れ子が冪と崩壊**。$`y`$ 行は $`\Omega`$ の添字を担い
（$`(x,1,0) = \Omega_1`$、$`(x,1,0)(x{+}1,2,0) = \Omega_2`$、
$`(x,1,1) = \Omega_\omega`$）、その添字自身がまた同じ文法で書かれる。
