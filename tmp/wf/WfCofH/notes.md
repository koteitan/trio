# WfCofH: surjectivity — the structural facts of WfCofL, and the engine reduction (2026-11-01)

Notation: A standard, A ≠ SRO, last column x = |A| − 1 nonzero, tA = val(A), r = bad root (`BRoot`),
Y_n = o_{A[n]}(x), Rt = last root (a (0,0,0) column after which every column is nonzero).

## Lean (all green, no sorry, axioms propext / Quot.sound / Classical.choice)

WfCofH1.lean (unconditional)
- `hRootD : HRootD` — `parLast_of` + `sInv_std` (`lastTy A = TRIO.srow A x` is `rfl`).
- `hNotSucc : HNotSucc` — the child Rt + 1 of the last root is counted (`R12` forbids the bump (1,0,1),
  `UAT` forbids "upgraded and topped" unless the upgrader is Rt, and `upg Rt = none`), so
  o(Rt) = sf(ψ_0(S)) with S ≠ 0. `NS t` := last summand of t is ψ_0(B) with B ≠ 0; `NS` survives `sp`, `sf`,
  `add _`, the sum of the roots (later columns are not roots), and `cof ψ_0(B) ∈ {ω, Ω_{μ+1}}`.

WfCofH2.lean
- `shift_step` (t = 1, any m ≥ 1): from a valuation ρP of A[m] whose copies read the good-part v of A,
  the true valuation σ of A[m+1] (Cons + Rk) satisfies σ.o x = ρP.o r, σ.v = ρ.v off DepX false,
  σ.o = ρ.o off DepX true. (`true_glue_eq` of WfQrL18 + `cons_copy`/`shiftV`.)
- `t1_core (hD : Desc3) (hG : HGood3)` : for t = 1 and n ≥ 1,
  o_{A[n+1]}(x) = o_{A[n]}(r)  and  o_{A[n+1]}(c) = o_A(c) for c < x, c ∉ DepX true.
  The read hypothesis `hagree` is carried by induction on the copies: m = 1 by `base_v_read` (needs Good3 A),
  m ≥ 2 by `shift_step` itself + `hnd_t1`. All structural hypotheses from `sInv_std`.
- `hShift1 : Desc3 → HGood3 → HShift1` (HShiftD for every t = 1 matrix, no diagonal point needed),
  `hShiftD_of : Desc3 → HGood3 → HDiagT1 → HShiftD`.

WfCofH3.lean
- `HEngPath` (the engine lemma, named hypothesis): diagonal type, n ≥ 2, true valuation σ of A[n]:
  for every row-0 ancestor c of x with c ≤ r:   fsD(o_A(c), Y_n) ≤ σ.o(c).
  Source in the engines: the lower half of (E3) of the q ≠ r engine (fsD(old, ζ) ≤ σ < old on the closure,
  WfQnE) and, for q = r, `DQ η false (o_A c) (σ.o c)` of `qr_engineDQ2` (DQ = fsD with summands ≥ lN inserted,
  hence ≥ fsD), both at ζ = η = Y_n. The path Rt → … → r lies in DepX A x true (`dep_anc_x`).
- `hPathRD_of : HEngPath → HPathRD` (c = r).
- `hEngD_of : Desc3 → HGood3 → HDiagT1 → HEngPath → HRootSP → HEngD` (c = Rt; earlier roots keep their values
  by `t1_core` + `depX_ge`; tA = app S o(Rt), fsD(app S o(Rt), Y) = app S fsD(o(Rt), Y) ≤ app S σ.o(Rt)).
- `evalFSNZ2_of_H : Desc3 → HGood3 → HDiagT1 → HEngPath → HRootSP → HCID → HCountS → EvalFSNZ 2`.

So the surjectivity residuals are now: Desc3 (order preservation), HGood3, HRootSP (value invariants of the
standard matrices, already in the Inv3 family), HDiagT1, HEngPath (engine lower bound), HCID, HCountS.

## Named hypotheses introduced, with measurements

- `HGood3` (Good3 of the valuation of every standard A ≠ SRO): audit field `good`, 0 / 708,797,194 (WfInvX).
- `HRootSP` (roots single and decreasing): audit fields `rootS` 0 / 25,807,885, `rootP` 0 / 23,201,224.
- `HDiagT1`: probeH T1 below.
- `HEngPath`: probeH P below.

probeH.py (all 73 files of WfCofL + graftG, CAP 3000, n = 2..4), RESULTS: see "Results" (appended).

## HCountS (t = 0, 2): locating the hole copies

probeC.py: for the successor-argument type, the node ψ_a(b) (b successor), the columns c with o_A(c) = ψ_a(b),
the path bound CP: fsD(o_A(h), k) ≤ o_{A[k+2]}(h) on the ancestors h of the node column, and the number of
columns of A[n] with value ψ_a(init b) (HOLE).
First sample (3 files, CAP 150):
- t = 0: when the node is a column value, it is o(r) with r = P_0(x) (= the bad root). 14 / 35 have no column
  with that value (the node only appears inside a sum / after sf).
- CP fails at the node itself (o_{A[n]}(r) = ψ_a(init b): in A[n] the hole copies r + jL are row-0 SIBLINGS of r,
  d = 0 for t = 0) and at the root when r is itself a root (the copies are new roots); it holds on every
  strict ancestor. So the counting happens at P_0(r) (or in the root sum when r is a root), not along the path.
- t = 2: the node is never a column value (o); see WHERE below.

## Results

probeH (out/, summaryH.txt; all 74 files = the 73 of WfCofL + graftG, CAP 3000):
- T1 (HDiagT1): diag ⇒ t = 1 on all 85,817 diagonal-type matrices; succ type: t = 0 39,780, t = 2 54,201.
  No t = 1 matrix is of succ type (so `P1` never fired).
- P (HEngPath), n = 2..4, every row-0 ancestor c of x with c ≤ r:
  c = r 195,105 / 195,105; c = Rt 257,451 / 257,451; c strictly between 1,664,295 / 1,664,295. 0 failures.

probeC (outC/, summaryC.txt; all 74 files, CAP 1000), successor-argument type:
- LOC t = 0: the node ψ_a(b) is o(r) (r = P_0(x)) in 10,589 + 699; in 2,833 no column has exactly that value
  (it appears only as a subterm after sf, deepest containing column: other 206, r 3).
- LOC t = 2: never o(r); the node is inside o(x) (in its subscript v(x) = v(P_1 x) + ω^(1 + bump terms): the "+1"
  of the bump term is the successor; 305 of the classified) or in o(q), q = P_0(x) (170).
- CP (path count bound fsD(o_A(h), k) ≤ o_{A[k+2]}(h)), t = 0: strict ancestors of the node column
  192,465 / 192,465; at the node column itself 10,291 failures (the hole copies are row-0 SIBLINGS of r in A[n],
  t = 0 has d = 0); at the root 997 failures, all with r = the root itself (the copies become new roots).
  t = 2: 9 failures on strict ancestors (example in summaryC.txt) — the t = 2 count does not run along the row-0
  path of the node column.
- HOLE: the number of columns of A[n] whose value is ψ_a(init b) is not n in general (n = 2: 1 / 2 / 3 occur),
  so "n copies of the hole" is not a per-column statement either.

## Next

1. HCountS, t = 0: Lean reduction like `hEngD_of`: HCountS ⇐ (count bound at P_0(r), the parent of the node
   column, measured 0 failures as part of CP-mid) + root sum; when r is a root, the root-sum count directly
   (new roots r + jL). Needs a t = 0 analog of `t1_core` (earlier roots keep values) — the t = 0 copies are
   siblings, `expand_eq_gexp_t0` (d0 = d1 = 0).
2. HCountS, t = 2: the hole is the ω-bump in v(x); the copies increase rows 0 and 1, so the count is carried by
   the subscripts. Formulate the bound on v (not o) along the row-1 path; CP on o fails (9).
3. HCID and HDiagT1 remain value-level (both measured 0 failures); HEngPath = lower half of (E3) / DQ, to be
   delivered by the engines (state it as their conclusion at ζ = Y_n).
