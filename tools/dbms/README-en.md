# bms2dbms / dbms2yseq / bms2yseq

[← Back](../../README.md) | [Japanese](README.md) | [English](README-en.md)

Three CLI tools that convert between BMS 2-row standard forms, DBMS standard
forms, and Y sequences.

```
BMS 2-row standard form  --conC-->  DBMS standard form  --rank counting-->  Y sequence
                         bms2dbms                        dbms2yseq
                         \______________________ bms2yseq _______________________/
```

The left half, `conC`, is proved correct in Lean 4 / Mathlib — no `sorry`, no
extra axioms. The right half is exactly the definition given in
[User blog:Koteitan/Dimensional BMS の定義とY数列との対応](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan)
on the Japanese Googology Wiki.

## Requirements

Python 3 only. No external libraries.

```
tools/dbms/bms2dbms.py    BMS 2-row standard form <-> DBMS standard form
tools/dbms/dbms2yseq.py   DBMS standard form <-> Y sequence
tools/dbms/bms2yseq.py    BMS 2-row standard form <-> Y sequence (composition)
tools/dbms/rows2.py       reference implementation (1:1 with the Lean definitions)
tools/dbms/core.py        expansion rule and standard-form test (shared by BMS / DBMS)
```

```
$ ./bms2yseq.py "(0,0)(1,1)(2,2)"
(0,0)(1,1)(2,2)  ->  Y(1,2,4,7)
```

---

# bms2dbms

Converts between BMS 2-row standard forms (below `psi_0(Omega_omega)`) and DBMS
standard forms.

The algorithm is described in [algorithm-en.md](algorithm-en.md); the formalisation
lives in [`lean/Dbms.lean`](../../lean/Dbms.lean) and
[`lean/DbmsStd.lean`](../../lean/DbmsStd.lean).

## Usage

```
bms2dbms.py [-r] [-c] [-t] [-q] [-f] [--no-verify] [MATRIX ...]
```

A matrix is written as `(0,0)(1,1)(2,2)`. **Always quote it — parentheses are
shell metacharacters.** With no argument the tool reads stdin, one matrix per
line (blank lines and lines starting with `#` are ignored).

| | |
|---|---|
| `-r`, `--reverse` | DBMS -> BMS (through the reading) |
| `-c`, `--check` | only report whether the input is a standard form |
| `-t`, `--tree` | also print the term (`Three`) of both sides |
| `-q`, `--quiet` | print only the resulting matrix |
| `-f`, `--force` | convert even when the input is not standard (no guarantee) |
| `--no-verify` | skip the post-conversion check |

## Examples

### Converting

```
$ ./bms2dbms.py "(0,0)(1,1)(2,2)"
(0,0)(1,1)(2,2)  ->  (0,0)(1,0)(2,1)(3,2)
```

BMS allows the level to catch up with the depth; DBMS does not. So each column
is pushed one step deeper and one shadow column appears.

### Where contraction happens

```
$ ./bms2dbms.py "(0,0)(1,1)(1,0)(2,1)(2,0)"
(0,0)(1,1)(1,0)(2,1)(2,0)  ->  (0,0)(1,0)(2,1)(2,0)
```

Five columns become four. In DBMS one column can **serve as two nodes**, so the
second ladder is never written (see "contraction" in algorithm.md).

### Expanding first

A trailing `[n]` expands by the fundamental sequence before converting — the
same notation as the `bms` CLI.

```
$ ./bms2dbms.py "(0,0)(1,1)(2,2)[3]"
(0,0)(1,1)(2,1)(3,1)  ->  (0,0)(1,0)(2,1)(3,1)(4,1)
```

`[3][1]` applies left to right.

### Seeing the term

Correctness means "both sides read to the same tree". `-t` shows that tree.

```
$ ./bms2dbms.py -t "(0,0)(1,1)(2,2)"
(0,0)(1,1)(2,2)  ->  (0,0)(1,0)(2,1)(3,2)
  BMS   P0(P1(P2(Z,Z),Z),Z)
  DBMS  P0(P1(P2(Z,Z),Z),Z)
```

`P<level>(argument, sibling)`, and `Z` is a leaf. Matching lines mean the
conversion preserved the reading.

### Reverse

```
$ ./bms2dbms.py -r "(0,0)(1,0)(2,1)(2,0)"
(0,0)(1,0)(2,1)(2,0)  ->  (0,0)(1,1)(1,0)(2,1)(2,0)
```

`conC` is proved injective in Lean, but **surjectivity is not proved yet**
(measured: all 1740 DBMS standard forms with `<=7` columns have a preimage, no
violation). So the reverse direction always checks the round trip
`conC (conC^{-1} D) = D` and reports exit code 2 when it fails.

Note: **do not compare at equal column counts.** A preimage can be longer than
its image, so matching them up within a fixed length makes the map look
non-surjective.

```
N  = (0,0)(1,0)(2,1)(2,1)(2,1)(2,0)                   6 columns
P* = (0,0)(1,1)(1,1)(1,1)(1,0)(2,1)(2,1)(2,1)(2,0)    9 columns,  conC(P*) = N
```

### Standard-form test only

```
$ ./bms2dbms.py -c "(0,0)(1,1)" "(1,1)"
standard	(0,0)(1,1)
non-standard	(1,1)
```

`-r -c` tests against the DBMS standard forms instead.

### Batch

```
$ printf '(0,0)(1,1)\n(0,0)(1,1)(2,2)\n' | ./bms2dbms.py -q
(0,0)(1,0)(2,1)
(0,0)(1,0)(2,1)(3,2)
```

## Verification

For a standard input, **the two proved properties are checked at run time**.

```
readCon (conC M) = translate M      the reading is preserved
ST_D (conC M)                       the image is a DBMS standard form
```

The reverse direction also checks the round trip. Since surjectivity is
unproved, that check is essential there. `--no-verify` skips it.

## Exit codes

| | |
|---|---|
| 0 | success |
| 1 | the input is not a standard form (`-c` verdict, or non-standard without `-f`) |
| 2 | a check failed (cannot happen if the proofs hold) |
| 3 | the input could not be parsed (3 or more rows, unbalanced parentheses, bad `[]`) |

With several inputs the largest code is returned.

## Notes

* **2 rows only.** Three or more rows (trio sequences) are out of scope and give
  exit code 3.
* Correctness is proved **only for standard forms**. A result produced through
  `-f` means nothing.
* Always quote the matrix. `bms2dbms.py (0,0)(1,1)` is mangled by the shell.

---

# dbms2yseq

Converts between DBMS standard forms and Y sequences.

## Definition

```
Y()  = DBMS(())
Y(1) = DBMS((0))
Y(Y ⌢ (y)) = DBMS(X ⌢ (x))     where Y(Y) = DBMS(X), and x is the y-th
                                smallest column that keeps X ⌢ (x) a DBMS
                                standard form
```

So **DBMS -> Y is nothing but "for each column, what is its rank among the
columns that may stand there"**. Columns are compared lexicographically after
padding with zeros (`(2)` = `(2,0)` < `(2,1)`).

## Usage

```
dbms2yseq.py [-r] [-s] [-q] [-f] [--rows N] [--no-verify] [ARG ...]
```

| | |
|---|---|
| `-r`, `--reverse` | Y sequence -> DBMS |
| `-s`, `--steps` | show the candidates and the rank for every column |
| `-q`, `--quiet` | print only the result |
| `-f`, `--force` | convert even when the input is not standard |
| `--rows N` | number of rows (default: max depth + 1) |
| `--no-verify` | skip the round-trip check |

## Examples

```
$ ./dbms2yseq.py "(0)(1)(2,1)(3,2,1)"
(0)(1)(2,1)(3,2,1)  ->  Y(1,2,4,8)

$ ./dbms2yseq.py -r "1,2,4,8,9,8"
Y(1,2,4,8,9,8)  ->  (0)(1)(2,1)(3,2,1)(4)(3,2,1)
```

`-s` shows how the counting goes.

```
$ ./dbms2yseq.py -s "(0)(1)(2,1)(3,2)"
(0)(1)(2,1)(3,2)  ->  Y(1,2,4,7)
   1: (0)          rank  1 of  1 candidates   (0)
   2: (1)          rank  2 of  2 candidates   (0) (1)
   3: (2,1)        rank  4 of  4 candidates   (0) (1) (2) (2,1)
   4: (3,2)        rank  7 of  8 candidates   (0) (1) (2) (2,1) (3) (3,1) (3,2) (3,2,1)
```

(The Japanese build prints the same table with Japanese labels.)

## Mind the row count

**Adding a row can insert candidates in between.** `(3,1,1)` sits between
`(3,1)` and `(3,2)`, so too few rows shifts the ranks. The default is
"max depth + 1" rows, which is enough: a column at depth `x` can carry at most
`x+1` non-zero entries, the diagonal `(x, x-1, ..., 1, 0)`. Use `--rows` to set
it explicitly.

## Verification

Every conversion checks the round trip `y2dbms (dbms2y X) = X`. `--no-verify`
skips it.

| | |
|---|---|
| 0 | success |
| 1 | the input is not a DBMS standard form |
| 2 | the round trip failed |
| 3 | the input could not be parsed |

## Measurements

| | |
|---|---|
| the 31 worked examples in the article | all match |
| 1740 DBMS standard forms with `<=7` columns | round trip 100%, no Y-sequence collision |

---

# bms2yseq

Converts between BMS 2-row standard forms and Y sequences — the composition of
`bms2dbms` and `dbms2yseq`.

## Usage

```
bms2yseq.py [-r] [-s] [-q] [-f] [--rows N] [--no-verify] [ARG ...]
```

| | |
|---|---|
| `-r`, `--reverse` | Y sequence -> BMS |
| `-s`, `--steps` | show the intermediate DBMS matrix and the rank of each column |
| `-q`, `--quiet` | print only the result |
| `-f`, `--force` | convert even when the input is not standard |
| `--rows N` | number of rows on the DBMS side |
| `--no-verify` | skip the checks |

## Examples

```
$ ./bms2yseq.py "(0,0)(1,1)(2,2)"
(0,0)(1,1)(2,2)  ->  Y(1,2,4,7)

$ ./bms2yseq.py -r "1,2,4,7"
Y(1,2,4,7)  ->  (0,0)(1,1)(2,2)

$ ./bms2yseq.py -s "(0,0)(1,1)(1,0)(2,1)(2,0)"
(0,0)(1,1)(1,0)(2,1)(2,0)  ->  Y(1,2,4,3)
  DBMS  (0)(1)(2,1)(2)
   1: (0)          rank  1 of  1 candidates
   2: (1)          rank  2 of  2 candidates
   3: (2,1)        rank  4 of  4 candidates
   4: (2)          rank  3 of  8 candidates
```

A trailing `[n]` expands first.

```
$ ./bms2yseq.py "(0,0)(1,1)(2,2)[3]"
(0,0)(1,1)(2,1)(3,1)  ->  Y(1,2,4,6,8)
```

## Outside the 2-row fragment

Y sequences reach further than 2-row BMS. A Y sequence that needs a third row
cannot be mapped back.

```
$ ./bms2yseq.py -r "1,2,4,8"
bms2yseq: (0)(1)(2,1)(3,2,1) is outside the 2-row fragment (row 3 is non-zero)
```

## Verification

Every conversion checks the two proved properties and the Y-side round trip.

```
readCon (conC M) = translate M      the reading is preserved
ST_D (conC M)                       the image is a DBMS standard form
y2dbms (dbms2y D) = D               the Y round trip
```

| | |
|---|---|
| 0 | success |
| 1 | the input is not a standard form |
| 2 | a check failed |
| 3 | the input could not be parsed |
| 4 | outside the 2-row fragment (`-r` only) |

## Measurements

| | |
|---|---|
| 7256 BMS standard forms with `<=7` columns | round trip 100%, no Y-sequence collision |
