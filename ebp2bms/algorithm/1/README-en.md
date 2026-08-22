# Extended Buchholz psi <-> trio sequence, algorithm: α < ε₀

[← Back](../../../README.md) | [Japanese](README.md) | [English](README-en.md) | [α < ε₀](README-en.md) | [ε₀ ≤ α < Λ](../2/README-en.md)

The general formula that builds the standard form of the trio sequence system (the z<2
fragment) corresponding to $`\psi_0(\Omega_\alpha)`$, for $`\alpha \lt \varepsilon_0`$ (what the Cantor normal form of $`\omega`$ can write).

The matrices themselves are in the [table](../../sheet/1/README-en.md).

Read the $`\alpha`$ of $`\Omega_\alpha`$ as a two-level Cantor normal form (coefficients
expanded into repeated summands; $`\beta_i'`$ is what remains after peeling the leading
$`1`$, i.e. $`1 + \beta_i' = \beta_i`$):

```math
\begin{aligned}
\alpha &= \sum_i \omega^{\beta_i}, & \beta_1 &\ge \beta_2 \ge \cdots \ge \beta_m \cr
\beta_i' &= \sum_j \omega^{\gamma_{ij}}, & \gamma_{i1} &\ge \gamma_{i2} \ge \cdots
\end{aligned}
```

The matrix lays out each summand $`\omega^{\beta_i}`$ as a **add unit** $`U_i`$
($`+\!\!+`$ is concatenation of column lists):

```math
M(\alpha) = U_1 +\!\!+ U_2 +\!\!+ \cdots +\!\!+ U_m .
```

### Structure

- add unit $`U_i = \omega^{\beta_i}`$
  - anchor
  - root — carries the leading $`1`$ of $`\beta_i`$
  - multiply unit $`S_{i1} = \omega^{\gamma_{i1}}`$
    - digit
    - primitive-sequence embedding $`\mathrm{PrSS}(\gamma_{i1})`$
  - multiply unit $`S_{i2} = \omega^{\gamma_{i2}}`$
    - digit
    - primitive-sequence embedding $`\mathrm{PrSS}(\gamma_{i2})`$
  - …
- add unit $`U_i = 1`$ (when $`\beta_i = 0`$)
  - anchor
  - a z0 column

That is, **an add unit consists of an anchor, a root and multiply units, and a multiply unit consists of a
digit and a primitive-sequence embedding** (only a $`\beta_i = 0`$ add unit has neither root nor
multiply unit: it is an anchor plus a single z0 column).

The value of one add unit is the product of the root's $`\omega`$ and the multiply units' factors:

```math
\omega^{\beta_i} = \omega^{1 + \sum_j \omega^{\gamma_{ij}}}
  = \omega \cdot \prod_j \omega^{\omega^{\gamma_{ij}}} .
```

Since $`\omega^{a+b} = \omega^a \cdot \omega^b`$, **a sum inside the exponent is a product of
values**. One multiply unit is one factor, and the embedding carries the $`\gamma_{ij}`$ appearing
in that factor's size $`\omega^{\omega^{\gamma_{ij}}}`$. For instance $`\omega^3`$ is the root
$`\omega`$ plus two multiply units with $`\gamma = 0`$, giving
$`\omega \cdot \omega \cdot \omega`$.

### Terminology

Columns $`(x, y, z)`$ are named by their $`z`$: a **z1 column** has $`z = 1`$, a
**z0 column** has $`z = 0`$. The row-0 parent of a column is the usual BM reading — **the
nearest column to its left with strictly smaller $`x`$** ($`x`$ is not monotone from the
left; it can drop and come back).

- **add unit** $`U_i`$: the run of columns for one summand $`\omega^{\beta_i}`$ of $`\alpha`$.
  - lives at level $`y = i`$.
- **anchor**: the z0 column at the head of an add unit (the $`(r{+}1,\ i{-}1,\ 0)`$ of the add unit
  rule below).
  - it rebuilds the previous add unit's address in z0 form, giving the new add unit a foothold to
    hang from (a z1 limit marker cannot carry a successor directly).
  - the anchor of the first add unit $`U_1`$ is $`(0,0,0)`$ itself (previous address = $`0`$,
    the ground).
- **root**: the z1 column right after the anchor.
  - carries the leading $`1`$ of the split $`1 + \beta_i' = \beta_i`$.
- **multiply unit** $`S_{ij}`$: one summand $`\omega^{\gamma_{ij}}`$ of $`\beta_i'`$.
  - consists of a digit and a primitive-sequence embedding.
- **digit**: the leading z1 column of a multiply unit.
  - writing $`x_0`$ for the root's $`x`$, every digit sits at $`x_0{+}1`$ and is a row-0
    child of the root.
- **primitive-sequence embedding** $`\mathrm{PrSS}(\gamma_{ij})`$: the forest of $`y = 0`$
  z0 columns hanging below a digit (its row-0 descendants).
  - it carries the exponent $`\gamma_{ij}`$.

The generator carries one piece of state: $`r`$, the $`x`$ of the previous add unit's root.

### Units (addition)

Initialize $`r := -1`$, so that the anchor of $`U_1`$ comes out as $`(0,0,0)`$.

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

So a $`\beta_i = 0`$ add unit climbs one level with an anchor plus a bare z0 column, and while
such add units continue they share the anchor and keep climbing as a z0 chain.

### Root and multiply units (multiplication)

Split $`1 + \beta' = \beta`$ (if $`\beta \ge \omega`$ then $`\beta' = \beta`$; for finite
$`k`$, $`\beta' = k-1`$). Writing
$`\beta' = \omega^{\gamma_1} + \cdots + \omega^{\gamma_k}`$,

```math
\mathrm{body}(\beta,\ x_0,\ y) = \underbrace{(x_0,\ y,\ 1)}_{\text{R}}
  +\!\!+ \big[\, \underbrace{(x_0{+}1,\ y,\ 1)}_{\text{D}}
  +\!\!+ \mathrm{PrSS}(\gamma_j,\ x_0{+}2) \,\big]_{j=1}^{k} .
```

one column for the root, and one multiply unit (a digit column plus its primitive-sequence
embedding) per summand of $`\beta'`$.

### Primitive-sequence embedding (exponentiation)

Writing $`\gamma = \omega^{\delta_1} + \cdots + \omega^{\delta_l}`$,

```math
\mathrm{PrSS}(\gamma,\ x) = \big[\, (x,\ 0,\ 0)
  +\!\!+ \mathrm{PrSS}(\delta_j,\ x{+}1) \,\big]_{j=1}^{l},
\qquad \mathrm{PrSS}(0,\ x) = \varepsilon .
```

This is literally the 1-row Bashicu matrix (primitive sequence) of $`\gamma`$, and it always
lives in columns with $`y = z = 0`$.

**Summary**: the three nesting levels carry the three operations of the CNF — **the number of
add units is addition** (one step of the row-1 staircase each), **the number of multiply units is
multiplication** (one factor each), and **the shape of the embedding is exponentiation** (the
primitive sequence of the exponent $`\gamma`$).
