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

## Arithmetic on $`\Omega`$

So far $`\Omega`$ appeared inside $`\alpha`$ as at most one atom. In the region where
$`\alpha`$ itself is a sum, product or power of $`\Omega_v`$, **the grammar above carries
over unchanged once the atoms are widened to two families**. Implementation:
`tools/probe_eps_range.py` (CLI: `tools/build_omega_alpha.py`).

### Atoms

| atom | meaning |
|---|---|
| $`\Omega_v`$ | the $`v`$-th uncountable cardinal |
| $`\psi_v(X)`$ | a collapse value ($`\varepsilon_0 = \psi_0(\Omega_1)`$ is the special case) |

Both are fixed points of $`x \mapsto \omega^x`$, so CNF cannot take them apart; they sit in
an exponent slot as a single symbol. The $`v`$ with
$`\Omega_v \le \alpha \lt \Omega_{v+1}`$ is the **level** $`\mathrm{lvl}(\alpha)`$ of
$`\alpha`$ (fixed by the leading exponent alone; no level means countable).

### The base $`M(\Omega_v)`$

When $`\alpha`$ is uncountable no $`\psi_0`$ node is raised, and the matrix is built out of
$`B = (0,0,0)(1,1,1)(2,1,1)(3,1,0) = M(\Omega_1)`$ as its unit. With the lift
$`\mathrm{L}(x,y,z) = (x{+}1,\ y{+}1,\ z)`$, **finite $`v`$** closes up:

```math
M(\Omega_v) = B +\!\!+ \mathrm{L}(B) +\!\!+ \mathrm{L}^2(B) +\!\!+ \cdots +\!\!+ \mathrm{L}^{v-1}(B)
```

so one cardinal successor is one lift.

General $`v`$ is built by **insertion** into $`M(v)`$. Read $`M(v)`$ as a row-0 forest and
call a column a **level column** when $`z = 0`$, $`y \ge 1`$ and its row-0 parent is

- absent or a z0 column (but not a $`\psi_0`$ node other than the root anchor — that is an
  $`\Omega`$ leaf), or
- a z1 column that is a **root** (parent z0); if the parent is a **digit** it is an
  $`\Omega`$ leaf instead.

That is, the anchors and the $`{+}1`$ markers. Then

1. if the last column of $`M(v)`$ is a level column, drop it;
2. under the root anchor and under every remaining level column $`c`$, insert the tail of
   $`B`$, namely $`(1,1,1)(2,1,1)(3,1,0)`$, with $`y`$ lifted by $`c_y`$;
3. write out row-0 depth as $`x`$.

For finite $`v`$ this is machine-checked against the closed form above ($`v = 1,\dots,6`$).
Of the 132 sheet rows with $`\alpha = \Omega_v`$ exactly, **124 agree** (including nested
subscripts up to $`\Omega_{\Omega_{\Omega_\Omega}}`$).

Rules 1-10 below are how a general $`\alpha`$ containing $`\Omega_v`$ is written.

### Rule 1: row 1 is a copy of row 0 one storey up

An add term $`\omega^\delta`$ becomes **one column** whose children spell the remainder:

```math
\mathrm{strip}(\delta) = \begin{cases}
X + \psi_v(X)\cdot(c{-}1) + \rho & (\delta = \psi_v(X)\cdot c + \rho)\cr
\Omega_v\cdot(c{-}1) + \rho & (\delta = \Omega_v\cdot c + \rho)\cr
\delta & (\text{otherwise — absorbed})
\end{cases}
```

The first branch is the general form of the reverse collapse ($`\mathrm{arg}`$) above; the
second is new. For $`\delta \lt \Omega_1`$ the column is a $`\psi_0`$ node $`(x,0,0)`$; for
$`\delta \ge \Omega_1`$ it is a level-$`v`$ column representing
$`\omega^{\Omega_v + d} = \Omega_v \cdot \omega^{d}`$.
**Only the $`1`$ is replaced by $`\Omega_v`$: row 1 repeats the structure of row 0.**

Examples (in a $`\psi_0`$ argument, written from $`x`$):
$`\Omega`$ → $`(x,1,0)`$, $`\Omega\cdot2`$ → $`(x,1,0)(x,1,0)`$,
$`\Omega^2 = \omega^{\Omega\cdot2}`$ → $`(x,1,0)(x{+}1,1,0)`$,
$`\Omega^\Omega`$ → $`(x,1,0)(x{+}1,1,0)(x{+}2,1,0)`$.

### Rule 2: $`\alpha \ge \Omega_v`$ stacks on top of $`M(\Omega_v)`$

```math
M(\alpha) = M(\Omega_v) +\!\!+ \big[\,U_1 +\!\!+ U_2 +\!\!+ \cdots\,\big]
\qquad (v = \mathrm{lvl}(\alpha),\ \alpha \neq \Omega_v)
```

The add units are laid out exactly as above; only the initial state comes from the base.
With $`R`$ the **last root** of the base (the last z1 column whose row-0 parent is z0), the
level is $`R_y`$ and the first anchor's $`x`$ is given by rule 7. For $`\alpha = \Omega_v`$
exactly, the answer is the base itself.

That $`\Omega+\delta`$ puts a "bridge" $`\Omega`$ unit right after $`B`$ is a consequence of
this rule, not a special case: the first add unit of $`\Omega+\delta`$ is $`\omega^\Omega`$.

### Rule 3: a level is an address, not the value of $`y`$

The level a column names is not the number in row 1 but the **depth of its z0 ancestor
chain** — its address. The context already supplies the first $`1+k`$ columns of that chain,
so writing $`\Omega_v`$ only writes the remainder $`M(v)[1+k:]`$ ($`k`$ = how far the
anchor staircase agrees with $`M(v)`$). The copy lands $`d-k`$ deeper, because the context
spent $`d-k`$ steps on something else, so **only the row-1 values that track the unit's
level (z1 columns and level columns) are lifted by $`d-k`$**; columns naming an absolute
level ($`\Omega`$ leaves, $`\psi`$ nodes) are not.

The same $`\Omega_2`$ is written differently by context: in the argument of
$`\psi_0(\Omega_2)`$ ($`d=0`$) it is $`(x,1,0)(x{+}1,2,0)`$, inside a level-2 unit
($`d=2`$) it is the single column $`(x,2,0)`$.

### Rule 4: a unit's leaf only names the level (one column)

A unit's leaf — the place where $`\Omega_v`$ is written as the child of a digit — is
**always one column**, whatever the depth. Its row-1 value is the row-1 value of the **last
column of $`M(v)`$**, written $`\mathrm{leaf\_y}(v)`$, and row 2 is $`0`$.

| $`v`$ | last column of $`M(v)`$ | leaf |
|---|---|---|
| $`1`$ | $`(1,1,0)`$ | $`(x,1,0)`$ |
| $`2`$ | $`(2,2,0)`$ | $`(x,2,0)`$ |
| $`\omega`$ | $`(1,1,1)`$ | $`(x,1,0)`$ |
| $`\omega+1`$ | $`(3,2,0)`$ | $`(x,2,0)`$ |
| $`\omega\cdot2`$ | $`(3,2,1)`$ | $`(x,2,0)`$ |
| $`\omega^2`$ | $`(2,1,1)`$ | $`(x,1,0)`$ |

Only a collapse argument (the child of a $`\psi`$ column) still spells $`M(v)`$ as in
rule 3. That is why $`\Omega_\omega`$ is $`(x,1,1)`$ in the argument of
$`\psi_0(\Omega_\omega)`$ but $`(x,1,0)`$ as a unit's leaf.

### Rule 5: the upgrade effect (a mark at the end)

Rule 4 cannot tell $`\Omega_\omega`$ from $`\Omega_1`$ — both leaves are $`(x,1,0)`$. The
sheet distinguishes them by **appending a mark at the end of the matrix**. The mark is
whatever follows the last z0 column of $`M(v)`$, i.e. its trailing z1 columns:

```math
\mathrm{suffix}(v) = M(v)[\,i{+}1:\,],\qquad i = \max\{\,j \mid M(v)[j]_z = 0\,\}
```

$`\mathrm{suffix}(\omega) = (1,1,1)`$, $`\mathrm{suffix}(\omega^2) = (1,1,1)(2,1,1)`$,
$`\mathrm{suffix}(\omega\cdot2) = (3,2,1)`$,
$`\mathrm{suffix}(1) = \mathrm{suffix}(\omega+1) = \varepsilon`$.

The mark appears only when that leaf is the **last column of the matrix**; anything written
after it absorbs the mark. Its $`x`$ matches where the same mark already stands in that
matrix.

```
M(Omega_w)         = M(Omega_1) ++ (1,1,1)
M(Omega_w + W)     = ...(7,1,0)                 no mark (the last leaf is Omega_1)
M(Omega_w * 2)     = ...(7,1,0)(1,1,1)          mark (the last leaf is Omega_w)
M(Omega_w * 2 + 1) = ...(7,1,0)(6,3,0)(7,4,0)   the +1 absorbs the mark
```

This is the writer's side of what Hexirp calls the **upgrade effect**.

### Rule 6: storeys — relaying the ladder

In a limit-level region a leaf reaches only as deep as the region's own leaf,
$`\mathrm{leaf\_y}(v)`$. To name a level beyond that, or once the ladder is used up, one
**lifted copy of the matrix (of the previous storey)** is inserted:

```math
\mathrm{storey}(C,\ y) = \mathrm{L}(C)\ \text{with the row-1 value of its last column set to } y
```

This is a row that really exists in the sheet: for $`C = M(\beta)`$,
$`C +\!\!+ \mathrm{storey}(C)`$ is the row of
$`\psi_0(\Omega_\beta + \psi_1(\Omega_\beta))`$. The $`B +\!\!+ \mathrm{L}(B)`$ of the
$`\Omega_1`$ region and the 26-column row of the $`\Omega_\omega+\Omega`$ region have the
same shape.

Four things trigger a storey:

| trigger | example |
|---|---|
| a leaf names a level deeper than the region (one storey per level) | $`\Omega_\omega+\Omega_2`$, $`\Omega_\omega+\Omega_3`$ |
| the next add unit, after the previous leaf used the region's own leaf | $`\Omega_\omega+\Omega+1`$ |
| the same, between two digits of one unit | $`\Omega_\omega+\Omega\cdot\omega`$ |
| the same, between two columns inside one digit | $`\Omega_\omega+\Omega^\Omega`$ |

The second and later storeys lift the **previous storey**, not the whole matrix (the same
stacking as $`M(\Omega_v) = B +\!\!+ \mathrm{L}(B) +\!\!+ \mathrm{L}^2(B) \cdots`$). A
storey laid inside one add unit serves the rest of that add unit.

### Rule 7: the next anchor's $`x`$ — does the base close on a leaf?

With $`R`$ the root of the base's last add unit, the anchor that follows it has

```math
x = R_x + \begin{cases} 0 & (\text{the base's last column is a z0 leaf}) \cr 1 & (\text{it ends in a mark or a digit}) \end{cases}
```

For $`B`$ (closing on the leaf $`(3,1,0)`$) that is $`x=1`$, the same as the root; for
$`M(\Omega_\omega) = B +\!\!+ (1,1,1)`$ (ending in a mark) it is $`x=2`$; for
$`M(\Omega_{\omega^2}) = B +\!\!+ (1,1,1)(2,1,1)`$ (ending in a digit) it is also $`x=2`$.

### Rule 8: an uncountable subscript names its level by copying the base

When $`v`$ itself is uncountable ($`\Omega_\Omega`$, $`\Omega_{\Omega_\omega}`$, …), a
**copy of the base's last storey** takes the place of the first add unit: the trailing mark
is dropped, $`x`$ is moved to the anchor position, row-1 values are raised by $`1`$, and the
final leaf keeps the level being named. Ordinary units follow.

```
M(W_{W+1}) = M(W_W) ++ copy ++ [unit] ++ [+1 unit]
             |7 cols| |7 cols|
```

After a storey has been crossed, a leaf naming the region's own level takes **the row-1
value of its own unit's anchor** (before crossing, $`\mathrm{leaf\_y}(v)`$). The upgrade
mark likewise goes at the position of the copy, lifted by the storeys.

### Rule 9: $`\psi_{\Omega_u}(X)`$ is a collapse, so it raises no unit

A collapse whose subscript is written as the cardinal itself, $`\psi_{\Omega_u}(X)`$, sits
**just below** $`\Omega_u`$ (the opposite of $`\psi_u`$ with an ordinal subscript, which
sits just above $`\Omega_u`$). The matrix raises no new unit either: it **lowers the row-1
value of the last leaf of $`M(\Omega_u)`$ by one** — that is the mark of the collapse — and
spells the argument underneath:

```math
M(\psi_{\Omega_u}(X)) = M(\Omega_u)^{\downarrow} +\!\!+ \mathrm{write\_level}(\mathrm{lvl}(X),\ x,\ y_0{-}1)
```

with $`y_0`$ the original leaf's row-1 value. If the argument is the subscript itself, one
column $`(x,y_0,0)`$ suffices.

### Rule 10: ladder coverage is the deepest level column in the common prefix

The $`k`$ of rule 3 — how much of the head of $`M(v)`$ the context supplies — is counted as
follows. Take the **common prefix** of $`M(v)`$ with each candidate ladder matrix — the
anchor staircase $`M(d)`$, the matrix being written, and $`M(u)`$ when inside
$`\psi_{\Omega_u}`$ — and count coverage up to the **deepest level column** in it (row-1
value at most $`d`$). The maximum over the candidates is taken, capped at depth $`d`$.

The same $`M(\omega\cdot2)`$ therefore comes out differently: inside
$`\psi_{\Omega_{\omega+1}}`$ (ladder $`M(\omega{+}1)`$) it is covered down to one remaining
column, while inside $`\psi_1`$ (ladders: the staircase $`M(1)`$ and the matrix so far) it
is not covered and all of $`M(\omega\cdot2)[1:]`$ is written one storey up.

### Validation

Of the 812 pure $`\psi_0(\Omega_\alpha)`$ rows of the sheet, yaBMS `bms -s` rejects **27
rows whose own matrix is not a standard form**; the remaining 785 are the measured set:

| region | match | mismatch |
|---|---|---|
| $`\alpha \lt \Omega_1`$ | 128 | 0 |
| arithmetic on $`\Omega_1`$ | 101 | 0 |
| arithmetic on $`\Omega_v`$ ($`v \ge 2`$) | 525 | 31 |
| total | **754** | 31 |

The 31 mismatches break down as:

| verdict | rows | grounds |
|---|---|---|
| the sheet is right | 3 | our output is not a standard form |
| undecided | 28 | both are standard forms |

Nine sheet rows with an error (1947 / 2113 / 2131 / 2133 / 2532 / 2723 / 3439 / 3452 / 3453)
were fixed on the sheet's side (the old value and the grounds are in the sheet's column I).
Each was checked by a BM4 expansion ($`M(\beta)[n]`$ of a following row) or is a
parenthesis typo.

Two independent cross-checks run alongside.

- **Row order**: the 754 matching rows come out strictly increasing under the builder's own
  ordinal comparison, in the sheet's row order (0 violations).
  This check is what found the direction of rule 9: the matrices agreed but the order broke
  in 14 places, and setting $`\psi_{\Omega_u}(X) \lt \Omega_u`$ brought it to 0.
- **Standard form**: **782 of the 785** matrices the builder writes are standard forms
  (`bms -s`). This checker found 12 separate fixes and also flagged the non-standard
  sheet rows. Collisions, where two different $`\alpha`$ produce the same matrix, went from
  57 pairs down to 11.

### Open (the 31 mismatches)

What is left splits into small families; none of them exceeds 20 rows.

1. **One digit's row-1 value raised by $`1`$ (17 rows).** In the storey copies of the
   $`\Omega_{\Omega_2}`$ family the sheet writes the first sub-unit's digit as $`(4,4,1)`$
   where rule 8's copy gives $`(4,3,1)`$. Across the whole sheet this shape (a digit's row-1
   value above its root's) occurs in exactly these 17 of 2618 places.
2. **Nestings from $`\Omega_{\Omega_\Omega}`$ up (14 rows)**, the leaf depth after crossing
   a storey, an $`x`$ offset in the base — families of a few rows each.

Aiming for the "plain" form instead (no storeys, no lift corrections, the leaf always
$`\mathrm{leaf\_y}(v)`$) drops the match count to 681 and the standard-form count to 761.
Indeed the plain leaf $`(8,3,0)`$ for $`\Omega_\omega\cdot\Omega+\Omega_3`$ is non-standard
in BM4 and in BM3.3 alike: **no depth-3 address exists in that context**. Addresses are
emergent, so the plain form is not a matter of taste but of whether it exists at all.

**Summary**: what the three nesting levels carry never changes — **the number of add units
is addition**, **the number of multiply units is multiplication** (one factor each), and
**the nesting of $`\mathrm{B}`$ is exponentiation and collapse**. Row $`y`$ carries the
subscript of $`\Omega`$, and that subscript is again written in the same grammar. All the
arithmetic on $`\Omega`$ adds is two things: the values in row $`y`$ are **addresses, not
absolute numbers** (rules 3 and 4), and the ladder has to be relaid when the addresses run
out (rule 6).

## Extension to the gap rows (general $`\psi_0(X)`$)

The rules above are for the pure rows $`\psi_0(\Omega_\alpha)`$. For the other rows of the
sheet (the gap rows) the builder first lowers the label $`X`$ to the form the matrix writes
(`lower`), then lays the columns unit by unit (`block`). The sheet's labels are normal forms
(the largest form in each argument) while the matrices are terms, so a lowering convention is
needed between them. Measured by `tools/probe_gap.py`.

| | match | mismatch |
|---|---|---|
| pure rows | 754 | 58 (27 of them non-standard) |
| gap rows (the 3868 with a readable label) | **2149** | 1719 |

The main conventions (details in notes, entries 777 and 778):

1. **Finite lowering**: in the argument of $`\psi_v`$, the part $`H`$ above level $`v{+}1`$ is
   one column $`\psi_{v+1}(H)`$ ($`\psi_0(\Omega_2+\psi_1(\Omega_2)\cdot\omega) = D_0 D_1(D_2 0 + 1)`$).
2. **Storeys inside a collapse argument**: when the columns of $`H`$ write a level-$`(v{+}1)`$
   leaf under a marker of the same depth ($`\Omega_\omega\cdot\Omega = (1,1,1)(2,1,0)`$), a
   higher level after it would read that leaf as the marker's level. So $`H`$ is cut at that
   leaf into $`B`$ and written $`B+\psi_{v+1}(H)+R`$. The same happens at level $`\omega`$.
3. **The upgrade suffix**, and when the next unit absorbs it.
4. **Cardinal-index $`\psi_{\Omega_{u+1}}`$** is the column of a level-$`u`$ marker, and its
   argument is written with the column's own spelling as the ladder. It can absorb the
   summands before it.
5. **Shared ladders**: what sibling units wrote (all of it, or from their last top unit on) is
   also a ladder. When the part after the shared level column starts with a marker, a storey
   copy goes before each deeper column ($`\Omega_{\omega2}+\Omega_{\omega+2} = \ldots(3,2,0)(4,3,1)(4,3,0)`$).
6. **Where children hang**: when a spelt level ends in a marker pair of equal depth, its
   children hang from the first marker ($`\Omega_{\omega^2}\cdot\omega = (1,1,1)(2,1,1)(2,0,0)`$).

Fifteen sheet errors found along the way (6 labels, 9 matrices) were corrected in the sheet,
with notes in column I.

### Check by an independent evaluator

For the direction matrix → ordinal there is Ytosk's evaluator (an algorithm that turns a matrix
into an Extended Buchholz term below SRO,
[Googology Wiki](https://googology.fandom.com/wiki/User_blog:Ytosk/Algorithm_that_changes_BMS_matrices_into_ordinals_up_to_SRO)).
It is defined in Lean in [`lean/Ebocf.lean`](../../../lean/Ebocf.lean) (the functions v, o, SF).
The sheet's last row psi(I) is exactly SRO, the upper end of the evaluator's range.

- **The Lean version and the JavaScript one** (https://github.com/hemisemidemipresent/bms) give
  the same term on all 4767 matrices of the sheet (11 of them have no value, because v and o
  call each other in a cycle; SRO is one of them).
- **The value of the sheet's matrix equals its label** on **4428** of the 4680 labelled rows.
- **Round trip of the builder**: taking "standard under `bms -s` and eval(builder's matrix) =
  label" as correctness, without looking at the sheet, gives **2967 / 4680** rows. Of the 2903
  rows where the builder equals the sheet, 2899 pass it. 68 rows differ from the sheet but pass.
- Measured by `tools/probe_ebocf.py` (its `rt` mode needs only Lean).

This check found 17 sheet errors, now corrected with notes in column I:
- 9 labels: 1532, 2025, 2654, 2816, 3077, 3319, 3694, 3777, 4384. Each label is out of order
  with a neighbouring label, and the value of the matrix lies between them.
- 8 matrices: 1287, 1433, 1787, 1816, 2009, 2817–2819: the same matrix as a neighbour, out of
  order, or a missing parenthesis. Rows 2817–2819 have (4,1,0) where (4,2,0) belongs; the BM4
  expansion [1] of row 2820 has the label's value. The builder used to have a special rule to
  match these three rows; it is removed.

The 27 sheet matrices with broken parentheses (such as `(3,2,1(4,2,1)`) are now read by the
normalization (rule 4 of `tools/normalize_sheet.py`); before, the broken column was dropped.

27 rows remain where both the sheet's matrix and the builder's are standard and in order, but
the evaluator gives the sheet's matrix a value other than the label. The evaluator has no proof
either, so which one is wrong is left open.
