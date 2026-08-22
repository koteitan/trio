# Extended Buchholz psi <-> trio sequence, algorithm: ε₀ ≤ α < Λ

[← Back](../../../README.md) | [Japanese](README.md) | [English](README-en.md) | [α < ε₀](../1/README-en.md) | [ε₀ ≤ α < Λ](README-en.md)

The general formula that builds the standard form of the trio sequence system (the z<2
fragment) corresponding to $`\psi_0(\Omega_\alpha)`$, for $`\varepsilon_0 \le \alpha \lt \Lambda`$ ($`\Lambda`$ is the least $`\Omega`$ fixed point).

The matrices themselves are in the [table](../../sheet/2/README-en.md).

The grammar is **the same** as in the [α < ε₀ page](../1/README-en.md); only the contents of the exponent slot change.
Write $`\alpha = \sum_i \omega^{\beta_i}`$, $`1 + \beta_i' = \beta_i`$,
$`\beta_i' = \sum_j \omega^{\gamma_{ij}}`$ as a two-level CNF and lay the summands out as
add units.

```math
M(\alpha) = U_1 +\!\!+ U_2 +\!\!+ \cdots +\!\!+ U_m .
```

### Structure

- add unit $`U_i = \omega^{\beta_i}`$
  - anchor
  - root — carries the leading $`1`$ of $`\beta_i`$
  - multiply unit $`S_{ij} = \omega^{\gamma_{ij}}`$
    - digit
    - **OT embedding** $`\mathrm{B}(\gamma_{ij})`$
- add unit $`U_i = 1`$ (when $`\beta_i = 0`$)
  - anchor
  - a z0 column

Exactly one thing differs from the [α < ε₀ page](../1/README-en.md): what sits below a multiply unit is generalized from the
primitive-sequence embedding $`\mathrm{PrSS}`$ to the **OT embedding** $`\mathrm{B}`$. For
$`\gamma \lt \varepsilon_0`$ we have $`\mathrm{B}(\gamma) = \mathrm{PrSS}(\gamma)`$, so
the α < ε₀ page is the special case of this one.

### Units (addition)

Same as the α < ε₀ page. Initialize the state $`r`$ (the $`x`$ of the previous add unit's root) to $`-1`$:

```math
\begin{aligned}
U_i &= (r{+}1,\ i{-}1,\ 0) +\!\!+ \mathrm{body}(\beta_i,\ r{+}2,\ i), & r &:= r+2
  &&(\beta_i \ge 1)\cr
U_i &= (r{+}1,\ i{-}1,\ 0) +\!\!+ (r{+}2,\ i,\ 0)
  &&&&(\beta_i = 0,\ \beta_{i-1} \ge 1)\cr
U_i &= (x_t{+}1,\ i,\ 0)
  &&&&(\beta_i = \beta_{i-1} = 0,\ \text{previous column} = (x_t, i{-}1, 0))
\end{aligned}
```

### Root and multiply units (multiplication)

With $`1 + \beta' = \beta`$ and $`\beta' = \omega^{\gamma_1} + \cdots + \omega^{\gamma_k}`$,

```math
\mathrm{body}(\beta,\ x_0,\ y) = \underbrace{(x_0,\ y,\ 1)}_{\text{R}}
  +\!\!+ \big[\, \underbrace{(x_0{+}1,\ y,\ 1)}_{\text{D}}
  +\!\!+ \mathrm{B}(\gamma_j,\ x_0{+}2) \,\big]_{j=1}^{k} .
```

### OT embedding (exponentiation and collapse)

Read $`\gamma`$ as a term of Buchholz's ordinal notation and copy it into columns as is.
For each summand $`\omega^\delta`$ place a $`\psi_0`$ node $`(x,0,0)`$ and write its
argument $`\mathrm{arg}(\delta)`$ as its row-0 children:

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

The second clause is the **uncollapse**. For $`\delta \lt \varepsilon_0`$ we have
$`\omega^\delta = \psi_0(\delta)`$, so the argument is just $`\delta`$; but for
$`\delta \ge \varepsilon_0`$, $`\omega^\delta`$ is not $`\psi_0(\delta)`$. Since
$`\varepsilon_0 = \psi_0(\Omega_1)`$ and
$`\varepsilon_0 \cdot \omega = \omega^{\varepsilon_0+1} = \psi_0(\Omega_1+1)`$, the rule
**turns the leading $`\varepsilon_0`$ of the argument back into an $`\Omega_1`$ leaf
$`(x,1,0)`$**. Here $`\delta \ominus \varepsilon_0`$ is what remains after dropping one
leading $`\varepsilon_0`$.

### When $`\alpha`$ is a collapse value $`\psi_0(\Omega_X)`$

The matrix of the subscript $`X`$ goes in unchanged:

```math
M(\psi_0(\Omega_X)) = (0,0,0)(1,1,1)(2,1,1) +\!\!+ \mathrm{shift}(M(X),\ 3).
```

**The anchor of $`M(X)`$, once shifted, is the $`\psi_0`$ node $`(3,0,0)`$** — anchor and
$`\psi_0`$ node are the same column, carrying both roles. Nothing inside $`X`$ is rewritten;
only $`x`$ moves.

For instance $`M(\omega) = (0,0,0)(1,1,1)`$ gives
$`M(\psi_0(\Omega_\omega)) = (0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)`$, and
$`M(\omega^\omega) = (0,0,0)(1,1,1)(2,1,1)(3,0,0)`$ gives
$`M(\psi_0(\Omega_{\omega^\omega})) = (0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)(5,1,1)(6,0,0)`$.

When $`\alpha = \Omega_1`$ no $`\psi_0`$ is applied, so that case is separate:
$`M(\Omega_1) = (0,0,0)(1,1,1)(2,1,1)(3,1,0)`$.

### $`\alpha = \Omega_v`$ itself ($`v \ge 2`$)

When $`\alpha`$ is uncountable no $`\psi_0`$ node is raised, and the matrix is built out of
$`B = (0,0,0)(1,1,1)(2,1,1)(3,1,0) = M(\Omega_1)`$ as its add unit. With the lift
$`\mathrm{L}(x,y,z) = (x{+}1,\ y{+}1,\ z)`$, **finite $`v`$** gives

```math
M(\Omega_v) = B +\!\!+ \mathrm{L}(B) +\!\!+ \mathrm{L}^2(B) +\!\!+ \cdots +\!\!+ \mathrm{L}^{v-1}(B)
```

(matching the sheet for $`v = 1,\dots,5`$). One cardinal successor step corresponds to one
lift.

On the limit side, here is what the sheet shows:

| $`v`$ | $`M(\Omega_v)`$ | reading |
|---|---|---|
| $`\omega`$ | $`B +\!\!+ M(\omega)[1{:}]`$ | diagonalization (the limit of the $`\mathrm{L}`$ chain) |
| $`\Omega_1`$ | $`B +\!\!+ M(\Omega_1)[1{:}]`$ | ditto |
| $`\Omega_2`$ | $`M(\Omega_{\Omega_1}) +\!\!+ \mathrm{L}(M(\Omega_{\Omega_1}))`$ | one lift (a cardinal successor) |

As the $`\Omega_{\Omega_2}`$ row shows, **the same grammar — successor = lift, limit =
diagonalization — repeats on the subscript side as well**.

#### General $`v`$: inserting $`B`$ under level columns

Read $`M(v)`$ as a row-0 forest and look at its **level columns**: those with $`z = 0`$ and
$`y \ge 1`$ whose row-0 parent is

- absent, or a z0 column (excluding the case where that parent is a $`\psi_0`$ node other
  than the root anchor — then the column is an $`\Omega`$ leaf), or
- a z1 column that is a **root** (its own parent is z0); if the parent is a **digit** the
  column is an $`\Omega`$ leaf and is excluded.

These are exactly the anchors and the $`{+}1`$ markers. Then:

1. if the last column of $`M(v)`$ is a level column, delete it;
2. directly below the root anchor and below every remaining level column $`c`$, insert the
   tail of $`B`$, namely $`(1,1,1)(2,1,1)(3,1,0)`$, with $`y`$ raised by $`c_y`$;
3. emit the result using the row-0 depth as $`x`$.

This matches **80 of the 87 sheet rows** with $`\alpha = \Omega_v`$, including nested
$`\Omega`$ subscripts up to $`\Omega_{\Omega_{\Omega_{\Omega_\Omega}}}`$. For finite $`v`$
it is machine-checked to agree with the closed lift-chain form above.

In the remaining 7 rows ($`v = \omega\cdot 5`$, $`\omega^2{+}\omega{+}2`$,
$`\omega^2{+}\omega\cdot 2`$, $`\omega^2{+}\omega\cdot 3`$, $`\omega^2\cdot 2`$,
$`\Omega_3`$ and others) the column right after an insert has its $`x`$ off by one. The
$`\omega^2\cdot 2`$ row is a duplicate label (another row with the same label does match), so
it may be of the same kind as the known mismatch rows recorded in [dom.md](../../../dom.md).
Unresolved.

**Summary**: what the three nesting levels carry does not change — **the number of add units is
addition**, **the number of multiply units is multiplication** (one factor each), and **the nesting
of $`\mathrm{B}`$ is exponentiation and collapse**. Row $`y`$ carries the subscript of $`\Omega`$
($`(x,1,0) = \Omega_1`$, $`(x,1,0)(x{+}1,2,0) = \Omega_2`$,
$`(x,1,1) = \Omega_\omega`$), and that subscript is again written by the same grammar.
