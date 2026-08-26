# From BMS 2-row standard forms to DBMS standard forms

[← Back](README-en.md) | [Japanese](algorithm.md) | [English](algorithm-en.md)

> **Two rows only.** This document covers the 2-row fragment of BMS, below
> `psi_0(Omega_omega)`.

## 1. Notation

A **column** is $`p = (p_0, p_1) \in \mathbb{N}^2`$; $`p_0`$ is its *depth* and $`p_1`$ its *level*. A **matrix** is a finite sequence of columns,

```math
\mathrm{Seq} := (\mathbb{N}^2)^{<\omega}.
```

Write $`\varepsilon`$ for the empty sequence, $`\frown`$ for concatenation, $`|M|`$ for the length, $`M_i`$ for the $`i`$-th entry and $`M[i,j) := (M_i, \dots, M_{j-1})`$ for a slice. $`M_{i,0}, M_{i,1}`$ are the two components of $`M_i`$.

For $`M \in \mathrm{Seq}`$ and a column $`p`$ put

```math
\mathrm{arg}_p(M) := M[0, k), \qquad \mathrm{sib}_p(M) := M[k, |M|), \qquad
k := \min \{\, i \le |M| \mid i = |M| \lor M_{i,0} \le p_0 \,\}.
```

Then $`M = \mathrm{arg}_p(M) \frown \mathrm{sib}_p(M)`$, and $`\mathrm{arg}_p(M)`$ is the longest prefix consisting only of columns strictly deeper than $`p`$. Shifting the depth is written

```math
\sigma^e(M) := \bigl((M_{0,0}+e,\ M_{0,1}),\ \dots,\ (M_{|M|-1,0}+e,\ M_{|M|-1,1})\bigr),
\qquad \sigma := \sigma^1 .
```

Truth values are $`\top, \bot`$.

## 2. Standard forms

BMS and DBMS share the same expansion rule; only the diagonal differs. For two rows,

```math
\mathrm{diag}_{\mathrm{B}}(x) = (x,\ x), \qquad
\mathrm{diag}_{\mathrm{D}}(x) = (x,\ \max(x-1,\ 0)).
```

Writing $`\mathrm{ST}_{\mathrm{B}}, \mathrm{ST}_{\mathrm{D}} \subseteq \mathrm{Seq}`$ for the two sets of standard forms,

```math
M \in \mathrm{ST}_{\mathrm{B}} \implies \forall i\ (M_{i,1} \le M_{i,0}),
\qquad
M \in \mathrm{ST}_{\mathrm{D}} \implies \forall i\ (M_{i,0} = 0 \lor M_{i,1} < M_{i,0}).
```

BMS admits $`(x,x)`$; DBMS does not. A column of level $`s \gt 0`$ must sit at depth $`s+1`$ or deeper in DBMS. That single fact is the whole content of the conversion.

## 3. Terms

```math
\mathcal{T} \ni t ::= Z \ \mid\ P(s;\ t_1,\ t_2) \qquad (s \in \mathbb{N})
```

$`P(s; t_1, t_2)`$ reads as "a node of level $`s`$, with argument $`t_1`$ and sibling $`t_2`$".

### 3.1 $`\mathrm{b2t} : \mathrm{Seq} \to \mathcal{T}`$

```math
\mathrm{b2t}(\varepsilon) := Z, \qquad
\mathrm{b2t}(p \frown r) := P\bigl(p_1;\ \mathrm{b2t}(\mathrm{arg}_p(r)),\ \mathrm{b2t}(\mathrm{sib}_p(r))\bigr)
```

### 3.2 $`\mathrm{t2b} : \mathcal{T} \times \mathbb{N} \to \mathrm{Seq}`$

```math
\mathrm{t2b}(Z, d) := \varepsilon, \qquad
\mathrm{t2b}\bigl(P(s; t_1, t_2),\ d\bigr) := \bigl((d, s)\bigr) \frown \mathrm{t2b}(t_1,\ d+1) \frown \mathrm{t2b}(t_2,\ d)
```

$`\mathrm{b2t}`$ throws the depth away; $`\mathrm{t2b}`$ recovers it from the nesting. The very same two functions apply to DBMS matrices as well ($`\mathrm{b2t}(N)`$ is what we call DBMSThree).

## 4. $`\mathrm{b2d} : \mathrm{Seq} \to \mathrm{Seq}`$

The work is done by $`\Gamma^{f,\varphi}_{d,\ell} : \mathrm{Seq} \to \mathrm{Seq}`$, where $`d`$ is the depth of the current block, $`\ell`$ the level of the parent, $`f`$ says whether we are at the head of a block, and $`\varphi`$ is the parent's instruction to "write it in shadow form".

```math
\mathrm{b2d}(M) := \Gamma^{\top,\bot}_{0,0}(M)
```

### 4.1 Units

```math
\mathrm{u}_p(\varepsilon) := 0, \qquad
\mathrm{u}_p(q \frown r) := \begin{cases}
  |\mathrm{arg}_p(r)| + 1 + \mathrm{u}_p(\mathrm{sib}_p(r)) & (q = p) \cr
  0 & (q \ne p)
\end{cases}
```

A **unit** is "one copy of $`p`$ together with its argument block", and $`\mathrm{u}_p(B)`$ counts how many columns of $`B`$ its leading units occupy.

### 4.2 Symbols

For $`M = p \frown r`$ we use the following. The nesting shows which symbols are meaningful only when the condition above them holds.

- Always:
  - $`s := p_1`$ — the level of the column being written
  - $`A := \mathrm{arg}_p(r)`$ — the argument block of $`p`$
  - $`B := \mathrm{sib}_p(r)`$ — the sibling block of $`p`$
  - $`\lambda := f \land (s = \ell + 1) \land (d \le s \lor \varphi)`$ — whether to lay a ladder
  - $`d' := \begin{cases} d + 1 & (\lambda) \cr s + 1 & (\lnot\lambda \land 0 \lt s \land d \le s) \cr d & (\text{otherwise}) \end{cases}`$ — the depth of the body
- Only when $`\lambda = \top`$:
  - $`U := B[0,\ \mathrm{u}_p(B))`$ — the leading units of $`B`$
  - $`B^{\ast} := B[\mathrm{u}_p(B),\ |B|)`$ — what is left
  - $`\pi := \bigl((p_0+1,\ p_1)\bigr) \frown \sigma(A) \frown \sigma(U)`$ — the prefix reused by the contraction
  - Only when $`B^{\ast} = q \frown r^{\ast}`$:
    - $`\alpha := \mathrm{arg}_q(r^{\ast})`$ — the argument block of $`q`$
    - $`\beta := \mathrm{sib}_q(r^{\ast})`$ — the sibling block of $`q`$
    - $`R := \alpha[\,|\pi|,\ |\alpha|)`$ — $`\alpha`$ with the prefix removed
    - $`\kappa := (q_1 + 1 = s) \land (q_0 = p_0) \land \bigl(\alpha[0, |\pi|) = \pi\bigr) \land (R \ne \varepsilon) \land (R_{0,0} = p_0 + 1) \land (R_{0,1} \lt s)`$ — whether to contract

When $`B^{\ast} = \varepsilon`$ we set $`\kappa := \bot`$.

### 4.3 Definition of $`\Gamma^{f,\varphi}_{d,\ell}`$

- If $`M = \varepsilon`$:

  $`\Gamma^{f,\varphi}_{d,\ell}(\varepsilon) = \varepsilon`$

- If $`M = p \frown r`$:
  - If $`\lambda = \top`$ (lay a ladder):
    - If $`\kappa = \top`$ (contract):

      $`\Gamma^{f,\varphi}_{d,\ell}(p \frown r) = \bigl((d,\ell),\ (d+1,s)\bigr) \frown \Gamma^{\top,\bot}_{d+2,\ s}(A) \frown \Gamma^{\bot,\bot}_{d+1,\ s}(U) \frown \Gamma^{\bot,\bot}_{d+1,\ s}(R) \frown \Gamma^{\bot,\bot}_{d,\ s}(\beta)`$

    - If $`\kappa = \bot`$ (do not contract):

      $`\Gamma^{f,\varphi}_{d,\ell}(p \frown r) = \bigl((d,\ell),\ (d+1,s)\bigr) \frown \Gamma^{\top,\bot}_{d+2,\ s}(A) \frown \Gamma^{\bot,\bot}_{d,\ s}(B)`$

  - If $`\lambda = \bot`$ (pass through, or jump to the level):

    $`\Gamma^{f,\varphi}_{d,\ell}(p \frown r) = \bigl((d',\ s)\bigr) \frown \Gamma^{\top,\ f \land (s = \ell)}_{d'+1,\ s}(A) \frown \Gamma^{\bot,\bot}_{d,\ s}(B)`$

The pair $`\bigl((d,\ell),(d+1,s)\bigr)`$ written when $`\lambda = \top`$ is the **ladder**. Its first column $`(d,\ell)`$ carries the parent's level, so it leaves no node in the term — it is a scaffold, a *shadow* — and $`(d+1,s)`$ is the body. When $`\kappa = \top`$, $`q`$ and its prefix $`\pi`$ are not written at all and only the contents follow. That is the **contraction**, and it corresponds to one DBMS column serving as two nodes[^1].

## 5. $`\mathrm{d2t} : \mathrm{Seq} \to \mathcal{T}`$

The work is done by $`\Delta^{f}_{\ell} : \mathrm{Seq} \times \mathcal{T} \to \mathcal{T}`$, whose second argument $`k`$ is "the term to place once the list runs out" (a continuation).

```math
\mathrm{d2t}(l) := \Delta^{\top}_{0}(l,\ Z)
```

### 5.1 Symbols

For $`l = p \frown \mathit{rest}`$:

- Always:
  - $`\mu := f \land (p_1 = \ell) \land (\mathit{rest} \ne \varepsilon) \land \bigl(\mathit{rest}_0 = (p_0 + 1,\ p_1 + 1)\bigr)`$ — whether $`p`$ is the shadow of a ladder
- Only when $`\mu = \top`$ (writing $`\mathit{rest} = t \frown \mathit{tail}`$):
  - $`t`$ — the body column of the ladder
  - $`a := \mathrm{arg}_t(\mathit{tail})`$ — the argument block of $`t`$
  - $`c := \mathrm{sib}_t(\mathit{tail})`$ — the sibling block of $`t`$
  - $`S := c[0,\ \mathrm{u}_t(c))`$ — the leading units of $`c`$
  - $`R := c[\mathrm{u}_t(c),\ |c|)`$ — what is left
  - $`\nu := (R \ne \varepsilon) \land (R_{0,0} = t_0) \land (R_{0,1} \lt t_1)`$ — whether $`t`$ has a double duty
  - Only when $`\nu = \top`$:
    - $`m := \min \{\, i \le |R| \mid i = |R| \lor R_{i,0} \lt t_0 \,\}`$
    - $`R^{-} := R[0, m)`$ — the part of $`R`$ that never gets shallower than $`t`$
    - $`R^{+} := R[m, |R|)`$ — the rest

### 5.2 Definition of $`\Delta^{f}_{\ell}`$

- If $`l = \varepsilon`$:

  $`\Delta^{f}_{\ell}(\varepsilon,\ k) = k`$

- If $`l = p \frown \mathit{rest}`$:
  - If $`\mu = \bot`$ (pass through):

    $`\Delta^{f}_{\ell}(p \frown \mathit{rest},\ k) = P\bigl(p_1;\ \Delta^{\top}_{p_1}(\mathrm{arg}_p(\mathit{rest}),\ Z),\ \Delta^{\bot}_{p_1}(\mathrm{sib}_p(\mathit{rest}),\ k)\bigr)`$

  - If $`\mu = \top`$ ($`p`$ is a shadow):
    - If $`\nu = \bot`$ (just drop the shadow):

      $`\Delta^{f}_{\ell}(p \frown t \frown \mathit{tail},\ k) = P\bigl(t_1;\ \Delta^{\top}_{t_1}(a,\ Z),\ \Delta^{\bot}_{t_1}(c,\ k)\bigr)`$

    - If $`\nu = \top`$ (undo the double duty):

      $`\Delta^{f}_{\ell}(p \frown t \frown \mathit{tail},\ k) = P\Bigl(t_1;\ \Delta^{\top}_{t_1}(a,\ Z),\ \Delta^{\bot}_{t_1}\bigl(S,\ P\bigl(p_1;\ \Delta^{\top}_{p_1}(t \frown a \frown S \frown R^{-},\ Z),\ \Delta^{\bot}_{\ell}(R^{+},\ k)\bigr)\bigr)\Bigr)`$

When $`\mu = \top`$ the shadow $`p`$ disappears. When $`\nu = \top`$, the single column $`t`$ serves both as a node of level $`t_1`$ and as a node of level $`p_1`$, so $`t \frown a \frown S \frown R^{-}`$ is reassembled and read again to split it back into two. The continuation $`k`$ is needed because siblings that sit next to each other in a DBMS matrix land in different places in the term.

## 6. Theorems

All proved in Lean 4 / Mathlib — no `sorry`, no extra axioms. $`A\langle n \rangle`$ is the $`n`$-th element of the fundamental sequence, $`\lt_o`$ the order on terms, $`\lt_{\mathrm{lex}}`$ the order on matrices.

**(T1) The reading is preserved.**

```math
M \in \mathrm{ST}_{\mathrm{B}} \implies \mathrm{d2t}(\mathrm{b2d}(M)) = \mathrm{b2t}(M)
```

**(T2) The image is a DBMS standard form.**

```math
M \in \mathrm{ST}_{\mathrm{B}} \implies \mathrm{b2d}(M) \in \mathrm{ST}_{\mathrm{D}}
```

**(T3) The order is preserved.**

```math
M, N \in \mathrm{ST}_{\mathrm{B}},\ M \ne N \implies
\bigl(\mathrm{d2t}(\mathrm{b2d}(M)) \lt_o \mathrm{d2t}(\mathrm{b2d}(N))
\iff M \lt_{\mathrm{lex}} N\bigr)
```

**(T4) The map is injective.**

```math
M, N \in \mathrm{ST}_{\mathrm{B}},\ \mathrm{b2d}(M) = \mathrm{b2d}(N) \implies M = N
```

**(R)** The crux of (T2) is the following lemma[^2]: the fundamental sequence of the image is covered by the image of the original fundamental sequence, after shifting the index.

```math
A \in \mathrm{ST}_{\mathrm{B}},\ |A| \gt 1,\ n \ge 1 \implies
\exists m \ge 1\ \exists n' \ge n\ \bigl(\mathrm{b2d}(A)\langle m \rangle = \mathrm{b2d}(A \langle n' \rangle)\bigr)
```

**(S)** Surjectivity is **not** proved.

```math
N \in \mathrm{ST}_{\mathrm{D}} \implies \exists M \in \mathrm{ST}_{\mathrm{B}}\ \bigl(\mathrm{b2d}(M) = N\bigr)
```

It has been checked for all 1740 elements of $`\mathrm{ST}_{\mathrm{D}}`$ with $`|N| \le 7`$, with no violation[^3].

## 7. Examples

### 7.1 A ladder

```math
M = \bigl((0,0),(1,1)\bigr), \qquad \mathrm{b2d}(M) = \bigl((0,0),(1,0),(2,1)\bigr)
```

```math
\begin{aligned}
\mathrm{b2t}(M) &= P(0;\ P(1; Z, Z),\ Z) \cr
\mathrm{b2t}(\mathrm{b2d}(M)) &= P(0;\ P(0;\ P(1;Z,Z),\ Z),\ Z) \cr
\mathrm{d2t}(\mathrm{b2d}(M)) &= P(0;\ P(1;Z,Z),\ Z)
\end{aligned}
```

$`(1,1)`$ cannot occur in $`\mathrm{ST}_{\mathrm{D}}`$, so level 1 is pushed down to depth 2 and the scaffold $`(1,0)`$ is inserted. The "$`\nu = \bot`$" case of $`\mathrm{d2t}`$ drops that scaffold again.

### 7.2 A contraction

```math
M = \bigl((0,0),(1,1),(1,0),(2,1),(2,0)\bigr), \qquad
\mathrm{b2d}(M) = \bigl((0,0),(1,0),(2,1),(2,0)\bigr)
```

```math
\begin{aligned}
\mathrm{b2t}(M) &= P\bigl(0; P(1; Z, P(0; P(1; Z, P(0;Z,Z)), Z)), Z\bigr) \cr
\mathrm{b2t}(\mathrm{b2d}(M)) &= P\bigl(0; P(0; P(1; Z, P(0;Z,Z)), Z), Z\bigr)
\end{aligned}
```

Five nodes become four columns. The "$`\nu = \top`$" case of $`\mathrm{d2t}`$ splits the one column back into two nodes and recovers $`\mathrm{b2t}(M)`$.

## 8. Correspondence with the implementations

| here | Lean (`lean/`) | Python (`rows2.py`) |
|---|---|---|
| $`\mathrm{arg}_p, \mathrm{sib}_p`$ | `takeWhile` / `dropWhile` | `split` |
| $`\sigma^e`$ | `shift1` / `shiftr0` | `shift1` |
| $`\mathrm{u}_p`$ | `unitsLen` | `units_split` |
| $`\pi`$ | `contrPre` | `contrPre` |
| $`\lambda`$ | `ladOf` | `lad` |
| $`d'`$ | `ddOf` | `dd` |
| $`\kappa`$ | `contrLen` | inline |
| $`\Gamma^{f,\varphi}_{d,\ell}`$ | `convC` | `convC` |
| $`\mathrm{b2d}`$ | `conC` | `convC M 0 0 True False` |
| $`\mathrm{b2t}`$ | `translate` (`Pair/Term.lean`) | `translate` |
| $`\mathrm{t2b}`$ | — | `untranslate` |
| $`\Delta^{f}_{\ell}`$ | `readK` | `readC` |
| $`\mathrm{d2t}`$ | `readCon` | `readC` |
| (T1) | `readC_conC_ST` | |
| (T2) | `ST_D_conC_final` | |
| (T3) | `conC_olt_iff_seqlex` | |
| (T4) | `conC_injective` | |
| (R) | `reindexD_holds` | |

The CLI is [`bms2dbms.py`](bms2dbms.py); usage is in [README-en.md](README-en.md).

## Notes

[^1]: Proving (R) unconditionally was by far the heaviest part of the whole
    development; `DbmsStd.lean` ended up at 15471 lines. Two branches resist a
    straightforward induction — the contraction branch, and the case where the
    parent of the last column is the node itself at a positive level (the
    "shifted copies"). The record is kept in
    [`lean/DBMS-STD-PLAN.md`](../../lean/DBMS-STD-PLAN.md).

[^2]: On naming. This document names every conversion in `src2dst` form. The
    Lean names `translate` / `conC` / `readCon` predate that convention, and do
    not say what maps to what.

[^3]: The plan is to obtain the bijection without building an inverse, using
    only cofinality on both sides — the route Naruyoko used for `Trans`. Its two
    conditions hold for all 7256 BMS 2-row standard forms of at most 7 columns
    (`cofinal_check.py`). Source: User blog:Naruyoko, "ペア数列システムの停止性
    証明に用いられた変換写像の全単射性".
