# 拡張ブーフホルツ psi ↔ DBMS 3 行 対応表: ε₀ ≤ α

[← 戻る](../../../README.md) | [Japanese](README.md) | [English](README-en.md) | [α < ε₀](../1/README.md) | [ε₀ ≤ α](../2/README.md)

$`\Omega_v`$ の族はここで**構造が変わる**。BMS では

```
Omega_v = B ++ L(B) ++ … ++ L^(v-1)(B)        B は 4 列、全部で 4v 列
```

だったが、DBMS では**ブロックが 1 つ減る**。

```
Omega_v = shift(B) ++ shift(L(B)) ++ … ++ shift(L^(v-2)(B))      v >= 2
          6 列        4 列                4 列                   全部で 4v-2 列
```

$`v = 2,\dots,8`$ で確認した。縮約（DBMS では 1 列が 2 度の役を兼ねる）が
最後のブロックを吸収するためである。

$`\Omega_1`$ だけは特別で、長さは $`\Omega_2`$ と同じ 6 列だが末尾の柱の段が 1 低い
（$`\begin{pmatrix}5\cr 1\cr 0\end{pmatrix}`$、$`\Omega_2`$ は
$`\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}`$）。

$`\Omega_X`$（$`X`$ が極限）は $`\mathrm{shift}(B)`$ のあとに $`X`$ 自身の行列を
平行移動して繋いだ形になる。


| $`\alpha`$ | DBMS 3 行 |
|---|---|
| $`\Omega_1`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{アンカー}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{梯子}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}5\cr 1\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{乗算ユニット}}}_{\text{加算ユニット}}`$ |
| $`\Omega_2`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{アンカー}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{梯子}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{乗算ユニット}}}_{\text{加算ユニット}}`$ |
| $`\Omega_3`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{アンカー}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{梯子}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{乗算ユニット}}\underbrace{\begin{pmatrix}3 & 4 & 5 & 6\cr 2 & 3 & 3 & 3\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}(B)}}_{\text{加算ユニット}}`$ |
| $`\Omega_4`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{アンカー}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{梯子}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{乗算ユニット}}\underbrace{\begin{pmatrix}3 & 4 & 5 & 6\cr 2 & 3 & 3 & 3\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}(B)}\underbrace{\begin{pmatrix}4 & 5 & 6 & 7\cr 3 & 4 & 4 & 4\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}^{2}(B)}}_{\text{加算ユニット}}`$ |
| $`\Omega_5`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{アンカー}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{梯子}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{乗算ユニット}}\underbrace{\begin{pmatrix}3 & 4 & 5 & 6\cr 2 & 3 & 3 & 3\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}(B)}\underbrace{\begin{pmatrix}4 & 5 & 6 & 7\cr 3 & 4 & 4 & 4\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}^{2}(B)}\underbrace{\begin{pmatrix}5 & 6 & 7 & 8\cr 4 & 5 & 5 & 5\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}^{3}(B)}}_{\text{加算ユニット}}`$ |
| $`\Omega_\omega`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{アンカー}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{梯子}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{乗算ユニット}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{B}}_{\text{加算ユニット}}`$ |
| $`\Omega_{\omega^2}`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{アンカー}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{梯子}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{乗算ユニット}}\underbrace{\begin{pmatrix}3 & 4\cr 2 & 2\cr 1 & 1\end{pmatrix}}_{B}}_{\text{加算ユニット}}`$ |
| $`\Omega_{\Omega_1}`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{アンカー}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{梯子}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{乗算ユニット}}\underbrace{\begin{pmatrix}3 & 4 & 5\cr 2 & 2 & 1\cr 1 & 1 & 0\end{pmatrix}}_{B}}_{\text{加算ユニット}}`$ |
| $`\Omega_{\Omega_{\Omega_1}}`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{アンカー}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{梯子}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{乗算ユニット}}\underbrace{\begin{pmatrix}3 & 4 & 5 & 3 & 4 & 5\cr 2 & 2 & 2 & 2 & 2 & 1\cr 1 & 1 & 0 & 1 & 1 & 0\end{pmatrix}}_{B}}_{\text{加算ユニット}}`$ |
| $`\psi_0(\Omega_1)`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{アンカー}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{梯子}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}5 & 6\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\mathrm{P}}}_{\text{乗算ユニット}}}_{\text{加算ユニット}}`$ |
| $`\psi_0(\Omega_\omega)`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{アンカー}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{梯子}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}5 & 6 & 7\cr 0 & 1 & 2\cr 0 & 0 & 1\end{pmatrix}}_{\mathrm{P}}}_{\text{乗算ユニット}}}_{\text{加算ユニット}}`$ |
| $`\psi_0(\Omega_{\omega^2})`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{アンカー}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{梯子}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{根}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{桁}}\underbrace{\begin{pmatrix}5 & 6 & 7 & 8\cr 0 & 1 & 2 & 2\cr 0 & 0 & 1 & 1\end{pmatrix}}_{\mathrm{P}}}_{\text{乗算ユニット}}}_{\text{加算ユニット}}`$ |
