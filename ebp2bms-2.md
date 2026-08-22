# 拡張ブーフホルツ psi ↔ トリオ数列（BMS 3 行）対応表 その 2: $`\varepsilon_0 \le \alpha`$

[その 1（$`\alpha \lt \varepsilon_0`$）](ebp2bms.md) の続き。
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

表記: 行列は**ユニットごとに分けて**並べる（括弧 1 組 = ユニット $`U_i`$）。

| $`\alpha`$ | $`\psi_0(\Omega_\alpha)`$ | トリオ数列（括弧 1 組 = ユニット） |
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

### $`\Omega_v`$ ブロック

$`\mathrm{arg}`$ の中に現れる $`\Omega_v`$ は次で書かれる:

```math
\mathrm{Om}(v,\ x) = \mathrm{shift}\big(M(v)\ \text{のアンカーを外したもの},\ x\big).
```

$`\mathrm{Om}(1) = (x,1,0)`$、$`\mathrm{Om}(2) = (x,1,0)(x{+}1,2,0)`$、
$`\mathrm{Om}(\omega) = (x,1,1)`$、$`\mathrm{Om}(\omega^\omega) = (x,1,1)(x{+}1,1,1)(x{+}2,0,0)`$。
アンカーを外すのは、その役目を上の $`\psi_0`$ ノードが果たしているため。
$`\alpha`$ が崩壊値 $`\psi_0(\Omega_X)`$ のときはこれで

```math
M(\psi_0(\Omega_X)) = (0,0,0)(1,1,1)(2,1,1)(3,0,0) +\!\!+ \mathrm{Om}(X,\ 4)
```

となり、$`\alpha = \Omega_1`$ のときは $`\psi_0`$ ノードが立たず
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

#### $`v \ge \omega`$ の一般法則（部分的、調査中）

$`M(v)`$ の**レベル列**（アンカーと $`{+}1`$ 標識。$`z = 0`$、$`y \ge 1`$ で、
行 0 親が z0 列か「根」である列。$`\Omega`$ 葉と $`\psi_0`$ ノードは除く）に注目すると:

- 末尾の列がレベル列なら、それを削除する。
- 残る各レベル列 $`c = (x, y, 0)`$ を $`c +\!\!+ (B[1{:}] + (x,y))`$ に置き換える。
- 得られた列を $`B`$ の後ろに継ぐ。

これで $`\alpha = \Omega_v`$ のシート 87 行中 **48 行が一致**する
（$`v = \omega`$, $`\omega+1`$, $`\omega+2`$, $`\omega\cdot 2`$, $`\omega^2`$,
$`\omega^\omega`$, $`\varepsilon_0`$, $`\Omega_1`$, $`\Omega_2`$, $`\Omega_{\Omega_1}`$ など）。
残り 39 行のずれは**挿入で後続列の $`x`$ が押し出される分の帳尻**で
（例: $`v = \omega^2+\omega+2`$ でレベル列が $`(6,3,0)`$ になるべきところ $`(5,3,0)`$）、
後処理ではなく生成時に $`x`$ を追跡すれば直るはず。未完。

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

### 例: $`\alpha = \psi_0(\Omega_\omega)`$

$`\alpha`$ は崩壊値なので $`\omega^\alpha = \alpha`$、ユニット 1 つ・サブユニット 1 つで
その指数は $`\alpha`$ 自身。$`\mathrm{B}(\alpha)`$ は $`\psi_0`$ ノード＋$`\Omega_\omega`$ ブロック。

添字 $`\omega`$ 側: $`M(\omega) = `$ $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}`$
であり、アンカー $`(0,0,0)`$ を外した $`\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}`$ を $`x`$ シフトして埋め込む。

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3\cr 0\cr 0\end{pmatrix}}_{\psi_0}\underbrace{\begin{pmatrix}4\cr 1\cr 1\end{pmatrix}}_{\Omega_\omega}
```

### 例: $`\alpha = \psi_0(\Omega_{\omega^\omega})`$

$`\Omega_v`$ のブロックは **$`M(v)`$ からアンカーを外したもの**である。

添字 $`\omega^\omega`$ 側: $`M(\omega^\omega) = `$ $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 0\cr 0 & 1 & 1 & 0\end{pmatrix}`$
であり、アンカー $`(0,0,0)`$ を外した $`\begin{pmatrix}1 & 2 & 3\cr 1 & 1 & 0\cr 1 & 1 & 0\end{pmatrix}`$ を $`x`$ シフトして埋め込む。

```math
\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{ア}}\underbrace{\begin{pmatrix}1\cr 1\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\begin{pmatrix}2\cr 1\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}3\cr 0\cr 0\end{pmatrix}}_{\psi_0}\underbrace{\begin{pmatrix}4 & 5 & 6\cr 1 & 1 & 0\cr 1 & 1 & 0\end{pmatrix}}_{\Omega_{\omega^\omega}}
```

### 例: $`\alpha = \psi_0(\Omega_{\psi_0(\Omega_\omega)})`$

添字がまた崩壊値。**添字が何段深くなっても同じ規則が繰り返される**。

添字 $`\psi_0(\Omega_\omega)`$ 側: $`M(\psi_0(\Omega_\omega)) = `$ $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 1 & 1 & 0 & 1\end{pmatrix}`$
であり、アンカー $`(0,0,0)`$ を外した $`\begin{pmatrix}1 & 2 & 3 & 4\cr 1 & 1 & 0 & 1\cr 1 & 1 & 0 & 1\end{pmatrix}`$ を $`x`$ シフトして埋め込む。

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
