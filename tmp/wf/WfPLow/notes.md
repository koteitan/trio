# WfPLow: WfSrcP.PLowRes (2026-10-31)

Result: not closed. No Lean change. Measurement of where the failing summand comes from.

## Measurement (probe_o.py -> o1.json; growP 79727 + expPt2)
For every PLowRes instance (shape P, not v(m) < tau.o c), every summand q >= w^2 of v(m):
- origin is unique: b = m, k = upg m, k < i (source_summand_origin gives q = bumpW(k));
  k has one bump child j0, j0 has one child d0, d0 < m. In the examples k, j0, d0 = k, k+1, k+2
  and i, j, c = m+1, m+2, m+3: (i, j, c) is a later copy of (k, j0, d0) (col d0 != col c).
- the window class of q is decided by o(d0) against o(c):
  | set / frame | q >= W_M | q < W_T | window (W_T <= q < W_M) |
  |---|---:|---:|---:|
  | growP b.B2 (Bad2) | 365 (o d0 >= o c) | 48 (o d0 < tau.o c) | 0 |
  | growP b.nB2 | 2130 (o d0 >= o c) | 314 (o d0 < tau.o c) | 140 (tau.o c <= o d0 < o c, all Lhd) |
  | growP a.nB2 | 5601 | 909 | 1 |
  | expPt2 a.nB2 | 12 | 0 | 0 |
- e1 d0 = e1 c, P1 d0 = P1 c, v(d0) = v(c) in all q < W_T and window cases.
- Without Bad2 the window is non-empty but every window summand is Lhd W_M (no DropFail):
  PLowRes holds on these sets also without the Bad2 premise.

## Why not closed
After source_failed_descends the claim is: o(d0) (grandchild of k = upg m through its bump
child) is not in [tau.o c, o c) unless bumpW(k) <| bumpW(i). This is a comparison of the
o-value of an earlier copy d0 with the cut value tau.o c of the later copy c. The library has no
lemma comparing o of a column with o of its copy (or with a cut of it); ArgDomCore / core_of_std
are about the syntactic sequence order, and no bridge from it to Valn o-values exists.
