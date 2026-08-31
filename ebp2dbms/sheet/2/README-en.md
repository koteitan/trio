# Extended Buchholz psi <-> DBMS 3 rows: eps_0 <= alpha

[← Back](../../../README.md) | [Japanese](README.md) | [English](README-en.md) | [α < ε₀](../1/README-en.md) | [ε₀ ≤ α](../2/README-en.md)

The $`\Omega_v`$ family is where the **structure changes**. In BMS

```
Omega_v = B ++ L(B) ++ … ++ L^(v-1)(B)        B is 4 columns, 4v in total
```

but in DBMS **one block disappears**.

```
Omega_v = shift(B) ++ shift(L(B)) ++ … ++ shift(L^(v-2)(B))      v >= 2
          6 cols      4 cols              4 cols                 4v-2 in total
```

Checked for $`v = 2,\dots,8`$. The contraction (one DBMS column doing double duty)
absorbs the last block.

$`\Omega_1`$ is special: same length as $`\Omega_2`$ (6 columns) but its last column sits
one level lower ($`\begin{pmatrix}5\cr 1\cr 0\end{pmatrix}`$ against
$`\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}`$).

For a limit $`X`$, $`\Omega_X`$ is $`\mathrm{shift}(B)`$ followed by the shifted matrix of
$`X`$ itself.


| $`\alpha`$ | DBMS 3 rows |
|---|---|
| $`\Omega_1`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{anchor}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{ladder}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{root}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{digit}}\underbrace{\begin{pmatrix}5\cr 1\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{multiply unit}}}_{\text{add unit}}`$ |
| $`\Omega_2`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{anchor}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{ladder}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{root}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{digit}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{multiply unit}}}_{\text{add unit}}`$ |
| $`\Omega_3`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{anchor}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{ladder}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{root}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{digit}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{multiply unit}}\underbrace{\begin{pmatrix}3 & 4 & 5 & 6\cr 2 & 3 & 3 & 3\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}(B)}}_{\text{add unit}}`$ |
| $`\Omega_4`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{anchor}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{ladder}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{root}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{digit}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{multiply unit}}\underbrace{\begin{pmatrix}3 & 4 & 5 & 6\cr 2 & 3 & 3 & 3\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}(B)}\underbrace{\begin{pmatrix}4 & 5 & 6 & 7\cr 3 & 4 & 4 & 4\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}^{2}(B)}}_{\text{add unit}}`$ |
| $`\Omega_5`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{anchor}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{ladder}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{root}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{digit}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{multiply unit}}\underbrace{\begin{pmatrix}3 & 4 & 5 & 6\cr 2 & 3 & 3 & 3\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}(B)}\underbrace{\begin{pmatrix}4 & 5 & 6 & 7\cr 3 & 4 & 4 & 4\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}^{2}(B)}\underbrace{\begin{pmatrix}5 & 6 & 7 & 8\cr 4 & 5 & 5 & 5\cr 0 & 1 & 1 & 0\end{pmatrix}}_{\mathrm{L}^{3}(B)}}_{\text{add unit}}`$ |
| $`\Omega_\omega`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{anchor}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{ladder}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{root}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{digit}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{multiply unit}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{B}}_{\text{add unit}}`$ |
| $`\Omega_{\omega^2}`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{anchor}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{ladder}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{root}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{digit}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{multiply unit}}\underbrace{\begin{pmatrix}3 & 4\cr 2 & 2\cr 1 & 1\end{pmatrix}}_{B}}_{\text{add unit}}`$ |
| $`\Omega_{\Omega_1}`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{anchor}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{ladder}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{root}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{digit}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{multiply unit}}\underbrace{\begin{pmatrix}3 & 4 & 5\cr 2 & 2 & 1\cr 1 & 1 & 0\end{pmatrix}}_{B}}_{\text{add unit}}`$ |
| $`\Omega_{\Omega_{\Omega_1}}`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{anchor}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{ladder}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{root}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{digit}}\underbrace{\begin{pmatrix}5\cr 2\cr 0\end{pmatrix}}_{\Omega_1}}_{\text{multiply unit}}\underbrace{\begin{pmatrix}3 & 4 & 5 & 3 & 4 & 5\cr 2 & 2 & 2 & 2 & 2 & 1\cr 1 & 1 & 0 & 1 & 1 & 0\end{pmatrix}}_{B}}_{\text{add unit}}`$ |
| $`\psi_0(\Omega_1)`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{anchor}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{ladder}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{root}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{digit}}\underbrace{\begin{pmatrix}5 & 6\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\mathrm{P}}}_{\text{multiply unit}}}_{\text{add unit}}`$ |
| $`\psi_0(\Omega_\omega)`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{anchor}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{ladder}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{root}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{digit}}\underbrace{\begin{pmatrix}5 & 6 & 7\cr 0 & 1 & 2\cr 0 & 0 & 1\end{pmatrix}}_{\mathrm{P}}}_{\text{multiply unit}}}_{\text{add unit}}`$ |
| $`\psi_0(\Omega_{\omega^2})`$ | $`\underbrace{\underbrace{\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}}_{\text{anchor}}\underbrace{\begin{pmatrix}1 & 2\cr 0 & 1\cr 0 & 0\end{pmatrix}}_{\text{ladder}}\underbrace{\begin{pmatrix}3\cr 2\cr 1\end{pmatrix}}_{\text{root}}\underbrace{\underbrace{\begin{pmatrix}4\cr 2\cr 1\end{pmatrix}}_{\text{digit}}\underbrace{\begin{pmatrix}5 & 6 & 7 & 8\cr 0 & 1 & 2 & 2\cr 0 & 0 & 1 & 1\end{pmatrix}}_{\mathrm{P}}}_{\text{multiply unit}}}_{\text{add unit}}`$ |
