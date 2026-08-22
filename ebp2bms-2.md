# 拡張ブーフホルツ psi ↔ トリオ数列（BMS 3 行）対応表 その 2: $`\varepsilon_0 \le \alpha`$

[← 戻る](README.md) | [Japanese](ebp2bms-2.md) | [English](ebp2bms-2-en.md) | [α < ε₀](ebp2bms-1.md) [ε₀ ≤ α < Λ](ebp2bms-2.md)

[その 1（$`\alpha \lt \varepsilon_0`$）](ebp2bms-1.md) の続き。
$`\psi_0(\Omega_\alpha)`$ とトリオ数列（z<2 断片）の標準形行列の対応。
生成: `tools/probe_eps_range.py`（BM4-Analysis シートと照合、
w-CNF + $`\varepsilon_0`$ 原子の 135 行中 131 一致（残り 4 は
[dom.md](dom.md) に記録した既知の不一致行）、崩壊値 $`\psi_0(\Omega_X)`$ 系 16 行は全一致）。

$`\alpha`$ の定義域: 本ページの生成器が対応するのは
(1) $`\omega`$ と原子 $`\varepsilon_0 = \psi_0(\Omega_1)`$ から $`+, \cdot, {}^\wedge`$ で
作れる範囲、および (2) 崩壊値 $`\psi_0(\Omega_X)`$ と $`\Omega_1`$（添字 $`X`$ は
再帰的に同じ範囲）。原理上の上限は $`\alpha \lt \Lambda`$（最小 $`\Omega`$ 不動点）。
(3) $`\Omega_v`$ 自身（有限 $`v`$ は法則で生成、極限 $`v`$ はシート観測値）。
未対応: 添字の外での演算（$`(\Omega_\omega)^2`$ など）と極限 $`v`$ の一般法則。

表記: 行列は**加算ユニットごとに分けて**並べる（括弧 1 組 = 加算ユニット $`U_i`$）。

| $`\alpha`$ | $`\psi_0(\Omega_\alpha)`$ | トリオ数列（括弧 1 組 = 加算ユニット） |
|---|---|---|
| $`\varepsilon_0 = \psi_0(\Omega_1)`$ | $`\psi_0(\Omega_{\varepsilon_0})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0+1`$ | $`\psi_0(\Omega_{\varepsilon_0+1})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}\begin{pmatrix}2 & 3\cr 1 & 2\cr 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0+\omega^2`$ | $`\psi_0(\Omega_{\varepsilon_0+\omega^2})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}\begin{pmatrix}2 & 3 & 4\cr 1 & 2 & 2\cr 0 & 1 & 1\end{pmatrix}`$ |
| $`\varepsilon_0\cdot 2`$ | $`\psi_0(\Omega_{\varepsilon_0\cdot 2})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}\begin{pmatrix}2 & 3 & 4 & 5 & 6\cr 1 & 2 & 2 & 0 & 1\cr 0 & 1 & 1 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0\cdot\omega`$ | $`\psi_0(\Omega_{\varepsilon_0\cdot\omega})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 2\cr 0 & 1 & 1 & 0 & 1 & 1\cr 0 & 1 & 1 & 0 & 0 & 1\end{pmatrix}`$ |
| $`\varepsilon_0^2`$ | $`\psi_0(\Omega_{\varepsilon_0^2})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0 & 1 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0^\omega`$ | $`\psi_0(\Omega_{\varepsilon_0^\omega})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 3\cr 0 & 1 & 1 & 0 & 1 & 0\cr 0 & 1 & 1 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0^{\varepsilon_0}`$ | $`\psi_0(\Omega_{\varepsilon_0^{\varepsilon_0}})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 3 & 4\cr 0 & 1 & 1 & 0 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0^{\varepsilon_0^{\varepsilon_0}}`$ | $`\psi_0(\Omega_{\varepsilon_0^{\varepsilon_0^{\varepsilon_0}}})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 4 & 5\cr 0 & 1 & 1 & 0 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\psi_0(\Omega_2)`$ | $`\psi_0(\Omega_{\psi_0(\Omega_2)})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 5\cr 0 & 1 & 1 & 0 & 1 & 2\cr 0 & 1 & 1 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\psi_0(\Omega_3)`$ | $`\psi_0(\Omega_{\psi_0(\Omega_3)})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 5 & 6\cr 0 & 1 & 1 & 0 & 1 & 2 & 3\cr 0 & 1 & 1 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\psi_0(\Omega_\omega)`$ | $`\psi_0(\Omega_{\psi_0(\Omega_\omega)})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 1\end{pmatrix}`$ |
| $`\psi_0(\Omega_{\omega+1})`$ | $`\psi_0(\Omega_{\psi_0(\Omega_{\omega+1})})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 5 & 6\cr 0 & 1 & 1 & 0 & 1 & 1 & 2\cr 0 & 1 & 1 & 0 & 1 & 0 & 0\end{pmatrix}`$ |
| $`\psi_0(\Omega_{\omega\cdot 2})`$ | $`\psi_0(\Omega_{\psi_0(\Omega_{\omega\cdot 2})})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 5 & 6\cr 0 & 1 & 1 & 0 & 1 & 1 & 2\cr 0 & 1 & 1 & 0 & 1 & 0 & 1\end{pmatrix}`$ |
| $`\psi_0(\Omega_{\omega^2})`$ | $`\psi_0(\Omega_{\psi_0(\Omega_{\omega^2})})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 5\cr 0 & 1 & 1 & 0 & 1 & 1\cr 0 & 1 & 1 & 0 & 1 & 1\end{pmatrix}`$ |
| $`\psi_0(\Omega_{\omega^\omega})`$ | $`\psi_0(\Omega_{\psi_0(\Omega_{\omega^\omega})})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 5 & 6\cr 0 & 1 & 1 & 0 & 1 & 1 & 0\cr 0 & 1 & 1 & 0 & 1 & 1 & 0\end{pmatrix}`$ |
| $`\psi_0(\Omega_{\varepsilon_0})`$ | $`\psi_0(\Omega_{\psi_0(\Omega_{\varepsilon_0})})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 5 & 6 & 7\cr 0 & 1 & 1 & 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 1 & 1 & 0 & 0\end{pmatrix}`$ |
| $`\psi_0(\Omega_{\psi_0(\Omega_\omega)})`$ | $`\psi_0(\Omega_{\psi_0(\Omega_{\psi_0(\Omega_\omega)})})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 5 & 6 & 7\cr 0 & 1 & 1 & 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 1 & 1 & 0 & 1\end{pmatrix}`$ |
| $`\psi_0(\Omega_{\psi_0(\Omega_{\psi_0(\Omega_\omega)})})`$ | $`\psi_0(\Omega_{\psi_0(\Omega_{\psi_0(\Omega_{\psi_0(\Omega_\omega)})})})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4 & 5 & 6 & 7 & 8 & 9 & 10\cr 0 & 1 & 1 & 0 & 1 & 1 & 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 1 & 1 & 0 & 1 & 1 & 0 & 1\end{pmatrix}`$ |
| $`\Omega_1`$ | $`\psi_0(\Omega_{\Omega_1})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 0\end{pmatrix}`$ |
| $`\Omega_2`$ | $`\psi_0(\Omega_{\Omega_2})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 0\end{pmatrix}\begin{pmatrix}1 & 2 & 3 & 4\cr 1 & 2 & 2 & 2\cr 0 & 1 & 1 & 0\end{pmatrix}`$ |
| $`\Omega_3`$ | $`\psi_0(\Omega_{\Omega_3})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 0\end{pmatrix}\begin{pmatrix}1 & 2 & 3 & 4\cr 1 & 2 & 2 & 2\cr 0 & 1 & 1 & 0\end{pmatrix}\begin{pmatrix}2 & 3 & 4 & 5\cr 2 & 3 & 3 & 3\cr 0 & 1 & 1 & 0\end{pmatrix}`$ |
| $`\Omega_5`$ | $`\psi_0(\Omega_{\Omega_5})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 0\end{pmatrix}\begin{pmatrix}1 & 2 & 3 & 4\cr 1 & 2 & 2 & 2\cr 0 & 1 & 1 & 0\end{pmatrix}\begin{pmatrix}2 & 3 & 4 & 5\cr 2 & 3 & 3 & 3\cr 0 & 1 & 1 & 0\end{pmatrix}\begin{pmatrix}3 & 4 & 5 & 6\cr 3 & 4 & 4 & 4\cr 0 & 1 & 1 & 0\end{pmatrix}\begin{pmatrix}4 & 5 & 6 & 7\cr 4 & 5 & 5 & 5\cr 0 & 1 & 1 & 0\end{pmatrix}`$ |
| $`\Omega_\omega`$ | $`\psi_0(\Omega_{\Omega_\omega})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 0\end{pmatrix}\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}`$ |
| $`\Omega_{\Omega_1}`$ | $`\psi_0(\Omega_{\Omega_{\Omega_1}})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 0\end{pmatrix}\begin{pmatrix}1 & 2 & 3\cr 1 & 1 & 1\cr 1 & 1 & 0\end{pmatrix}`$ |
| $`\Omega_{\Omega_2}`$ | $`\psi_0(\Omega_{\Omega_{\Omega_2}})`$ | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 0\end{pmatrix}\begin{pmatrix}1 & 2 & 3\cr 1 & 1 & 1\cr 1 & 1 & 0\end{pmatrix}\begin{pmatrix}1 & 2 & 3 & 4\cr 1 & 2 & 2 & 2\cr 0 & 1 & 1 & 0\end{pmatrix}\begin{pmatrix}2 & 3 & 4\cr 2 & 2 & 2\cr 1 & 1 & 0\end{pmatrix}`$ |

## 一般式

その 1 の文法と**同一**で、変わるのは指数スロットの中身だけである。
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

その 1 との違いは 1 点だけ: 乗算ユニットの下が
「原始数列埋め込み $`\mathrm{PrSS}`$」から
「**OT 埋め込み** $`\mathrm{B}`$」に一般化される。
$`\gamma \lt \varepsilon_0`$ では $`\mathrm{B}(\gamma) = \mathrm{PrSS}(\gamma)`$ なので
その 1 は本ページの特殊ケースである。

### 加算ユニット（加法）

その 1 と同一。状態 $`r`$（直前の加算ユニットの根の $`x`$ 座標）を $`-1`$ で初期化して

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
[dom.md](dom.md) に記録した既知の不一致行と同種の可能性がある。未解決。

**まとめ**: 3 段の入れ子が担うものは変わらない —
**加算ユニットの個数が加法**、**乗算ユニットの個数が乗法**（因子 1 つずつ）、
**$`\mathrm{B}`$ の入れ子が冪と崩壊**。$`y`$ 行は $`\Omega`$ の添字を担い
（$`(x,1,0) = \Omega_1`$、$`(x,1,0)(x{+}1,2,0) = \Omega_2`$、
$`(x,1,1) = \Omega_\omega`$）、その添字自身がまた同じ文法で書かれる。

## 例

用語は [その 1](ebp2bms-1.md) と同じ（ア = アンカー、$`S`$ = 乗算ユニット、
$`\mathrm{B}`$ = OT 埋め込み）。

### 例: $`\alpha = \varepsilon_0`$

$`\varepsilon_0 = \omega^{\varepsilon_0}`$ なので加算ユニット 1 つ、乗算ユニット 1 つ、
その指数は $`\varepsilon_0`$ 自身。$`\mathrm{B}(\varepsilon_0)`$ =
$`\psi_0`$ ノード＋$`\Omega_1`$ 葉:

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3 & 4\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\mathrm{B}}}_{S}
```

### 例: $`\alpha = \varepsilon_0 + \omega^2`$

加算ユニット 2 つ。$`U_2`$ はその 1 の文法そのまま（$`\gamma = 1`$ の
乗算ユニットが 1 つで $`\mathrm{B}(1)`$ はノード 1 本）:

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

### 例: $`\alpha = \psi_0(\Omega_\omega)`$

$`\alpha`$ は崩壊値なので $`\omega^\alpha = \alpha`$、加算ユニット 1 つ・乗算ユニット 1 つで
その指数は $`\alpha`$ 自身。$`\mathrm{B}(\alpha)`$ は $`\psi_0`$ ノード＋$`\Omega_\omega`$ ブロック。

添字 $`\omega`$ 側: $`M(\omega) = `$ $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}`$
を丸ごと $`x`$ に $`{+}3`$ して埋め込む。そのアンカー $`(0,0,0)`$ が $`(3,0,0)`$ に写り、
これが $`\psi_0`$ ノードそのものになる。

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3\cr 0\cr 0\end{pmatrix}}_{\psi_0}\underbrace{\begin{pmatrix}4\cr 1\cr 1\end{pmatrix}}_{\Omega_\omega}
```

### 例: $`\alpha = \psi_0(\Omega_{\omega^\omega})`$

添字 $`\omega^\omega`$ 側: $`M(\omega^\omega) = `$ $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 0\cr 0 & 1 & 1 & 0\end{pmatrix}`$
を丸ごと $`{+}3`$ シフト。アンカーが $`\psi_0`$ ノード $`(3,0,0)`$ になる。

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3\cr 0\cr 0\end{pmatrix}}_{\psi_0}\underbrace{\begin{pmatrix}4 & 5 & 6\cr 1 & 1 & 0\cr 1 & 1 & 0\end{pmatrix}}_{\Omega_{\omega^\omega}}
```

### 例: $`\alpha = \psi_0(\Omega_{\psi_0(\Omega_\omega)})`$

添字がまた崩壊値。**添字が何段深くなっても同じ規則が繰り返される**。

添字 $`\psi_0(\Omega_\omega)`$ 側: $`M(\psi_0(\Omega_\omega)) = `$ $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 1\end{pmatrix}`$
を丸ごと $`{+}3`$ シフト。前の例の行列がそのまま尻尾に入る。

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3\cr 0\cr 0\end{pmatrix}}_{\psi_0}\underbrace{\begin{pmatrix}4 & 5 & 6 & 7\cr 1 & 1 & 0 & 1\cr 1 & 1 & 0 & 1\end{pmatrix}}_{\Omega_{\psi_0(\Omega_\omega)}}
```

### 例: $`\alpha = \Omega_1`$

$`\alpha`$ が非可算のとき、$`\mathrm{B}`$ には $`\psi_0`$ ノードが立たず
$`\Omega_1`$ の葉が直接置かれる（$`\Omega_1`$ は $`\psi_0`$ の値ではないから）。
$`M(\Omega_1)`$ は 4 列で終わる:

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3\cr 1\cr 0\end{pmatrix}}_{\Omega_1}
```

### 例: $`\alpha = \Omega_2`$

$`B = M(\Omega_1) = `$ $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 0\end{pmatrix}`$ に持ち上げ $`\mathrm{L}(B)`$ を 1 つ継ぐ。
$`\mathrm{L}`$ は $`x`$ と $`y`$ を同時に $`{+}1`$ するので、$`B`$ のアンカー $`(0,0,0)`$ は
$`(1,1,0)`$ に、$`\Omega_1`$ 葉 $`(3,1,0)`$ は $`(4,2,0)`$ に写る:

```math
\underbrace{\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 0\end{pmatrix}}_{B}
\underbrace{\begin{pmatrix}1 & 2 & 3 & 4\cr 1 & 2 & 2 & 2\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}(B)}
```

### 例: $`\alpha = \Omega_3`$

$`B = M(\Omega_1) = `$ $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 0\end{pmatrix}`$
を持ち上げながら並べる。持ち上げ 1 回が基数の後続 1 段:

```math
\underbrace{\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 1\cr 0 & 1 & 1 & 0\end{pmatrix}}_{B}
\underbrace{\begin{pmatrix}1 & 2 & 3 & 4\cr 1 & 2 & 2 & 2\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}(B)}
\underbrace{\begin{pmatrix}2 & 3 & 4 & 5\cr 2 & 3 & 3 & 3\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}^2(B)}
```

### 例: $`\alpha = \Omega_\omega`$

$`M(\omega) = `$ $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}`$ にレベル列は無い（$`(1,1,1)`$ は根）。
根のアンカーの下に $`B`$ の尾を挿すだけ:

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1 & 2 & 3\cr 1 & 1 & 1\cr 1 & 1 & 0\end{pmatrix}}_{B}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{M(\omega)\ \text{の残り}}
```

### 例: $`\alpha = \Omega_{\omega+1}`$

$`M(\omega+1) = `$ $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 2\cr 0 & 1 & 0 & 0\end{pmatrix}`$。
$`(2,1,0)`$ がレベル列（アンカー）、$`(3,2,0)`$ は末尾のレベル列なので**削除**され、
代わりに $`(2,1,0)`$ の下に $`B`$ の尾が $`y`$ を $`{+}1`$ して挿さる:

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1 & 2 & 3\cr 1 & 1 & 1\cr 1 & 1 & 0\end{pmatrix}}_{B}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\begin{pmatrix}2\cr 1\cr 0\end{pmatrix}}_{\text{レベル列}}\underbrace{\begin{pmatrix}3 & 4 & 5\cr 2 & 2 & 2\cr 1 & 1 & 0\end{pmatrix}}_{B{+}(2,1)}
```

### 例: $`\alpha = \Omega_{\Omega_1}`$

$`M(\Omega_1) = B`$ にレベル列は無い（末尾 $`(3,1,0)`$ は桁の子なので $`\Omega`$ 葉）。
よって根のアンカーの下に $`B`$ の尾が 1 つ挿さるだけで、$`B`$ が 2 つ並ぶ形になる:

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1 & 2 & 3\cr 1 & 1 & 1\cr 1 & 1 & 0\end{pmatrix}}_{B}\underbrace{\begin{pmatrix}1 & 2 & 3\cr 1 & 1 & 1\cr 1 & 1 & 0\end{pmatrix}}_{M(\Omega_1)\ \text{の残り}}
```
