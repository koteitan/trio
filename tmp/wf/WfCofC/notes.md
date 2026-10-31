# WfCofC: surjectivity, the count part HCountS and HCID (2026-11-01)

## Lean

WfCofC1.lean (green; axioms propext / Classical.choice / Quot.sound)
- `t0_core (hG : HGood3)`: t = 0 (`lastTy A = 0`), bad root r = P_0(x), x = r + L, n ≥ 2, true valuation σ of A[n]
  (= gexp A r L 0 0 n, `expand_eq_gexp_t0`):
  σ.o c = o_A(c) for c < r off DepX true; σ.o(r + kL) = omid = ψ_{v(r)}(Y0) for k + 1 < n;
  σ.o(r + (n−1)L) = o_{A[1]}(r) (drop1); o_A(r) = ψ_{v(r)}(Y0 + 1); the copies r + kL are row-0 siblings of r.
  (From `t0_vals` (V3T0V), `o_r_omid`, `par0_gexp_root_t0`.)
- `hCountS0_of : HGood3 → HRootSP → HCntPath0 → HCountS0`.
  r a root: proved outright (roots of A[k+2] = roots before r ++ copy roots; fsD(tA,k) = S + omid·k ≤ S + omid·(k+1) + o_{A[1]}(r)).
  r not a root: last root Rt < r; residual `HCntPath0` = fsD(o_A(Rt), k) ≤ o_{A[k+2]}(Rt) (stated for roots c that are
  strict ancestors of r on the path to x).
- `hCountS_of : HCountS0 → HCountS12 → HCountS`, `evalFSNZ2_of_C`.

WfCofC2.lean (green)
- `diagAt_unique` (the diagonal point of a term is unique), `diagAt_app` (a diagonal point of t ≠ 0 is one of S + t),
  `anc0_child`.
- `hCID_of : HRootSP → HDiagLoc → HDiagStep → HCID`.
  - `HDiagLoc`: o_A(r) = ψ_ν(B), B ≠ 0, cof B = Ω_{ν+1} (o_A(r) is its own diagonal point).
  - `HDiagStep`: one edge c = P_0(d), d an ancestor of r: DiagAt(·, B, ν) in o_A(d) ⇒ DiagAt(·, B, ν) in o_A(c).
  Proof: up the path from r to the last root Rt (strong induction on r − c), then tA = S + o(Rt) (`diagAt_app`),
  then uniqueness against the diagonal point (a, b, μ) of tA gives B = b, ν = μ.
  Note: the literal point is NOT transmitted: the subscript changes (path(o_A(c)) ≠ path(tA) in 16,677 mid and
  10,280 r cases of the CAP-1000 run); only (B, ν) is kept.

WfCofC3.lean (green)
- `count_at_last_root` (generic: same roots, roots before Rt kept, bound at Rt ⇒ fsD(root A, η) ≤ root N).
- `hCountS12_of : HRootSP → HNoSucc1 → HRootKeep2 → HCntRoot2 → HCountS12`.
- `evalFSNZ2_of_C3`, `surj_of_C3`: EvalFSNZ 2 / surjectivity from
  Desc3, HGood3, HDiagT1, HEngPath, HRootSP (as before) and the new
  HDiagLoc, HDiagStep (for HCID), HCntPath0 (t = 0), HNoSucc1, HRootKeep2, HCntRoot2 (t = 1, 2).
- t = 2 design `HCntV2` (stated, measured, not used): along the row-1 path from x to Rt, every c ≠ x whose v_A(c)
  has the successor-argument type: fsD(v_A(c), k) ≤ v_{A[k+2]}(c). The naive "v at the last column of A[k+2]"
  (V2) is false; the node is not always in v(x) (VL false 5177 / 19642).

## Measurements (probeX.py; 77 files = WfCofH's 74 + graftH, graftQ1, graftQ2 (graftD/E/A3 already in); n = 2..4)

CAP 1000 per file (summary.txt), all 0 failures:
- HCntPath0 (P0): 13,344 × 3 n.  root case (proved): 950 × 3.  F0 (HCountS t = 0 itself) 14,294 × 3.
- HDiagLoc (DL) 32,790; CI (HCID itself) 32,790; HDiagStep (DB): Rt 24,714, mid 212,824, r 32,790.
- HRootKeep2 (R2roots, R2pre) 19,642 × 3 each; HCntRoot2 (C2) 19,642 × 3; F2 19,642 × 3.
- HCntV2 (VP) 22,543 × 3.  HNoSucc1: no t = 1 matrix of successor type.
- False forms: V2 (fsD(v_A(x), k) ≤ v at the last column of A[k+2]) 4678 / 5328 / 5940 failures (n = 2, 3, 4),
  smallest (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(4,1,0)(5,1,0)(3,2,1) at n = 2.
  DT (literal transmission of the diagonal point): false, smallest r-case
  (0,0,0)(1,1,1)(2,1,0)(3,1,0)(1,1,1)(1,1,1)(0,0,0)(1,1,0)(2,2,0).

WfCofC4.lean (green)
- `roots_N_d1` (t = 2, any d1: A[n] has the roots of A), `vals_before_root` (common prefix N.take K = A.take K,
  root column Rt < K ⇒ the values agree before Rt), `hRootKeep2 : HRootKeep2` (**proved**, no hypotheses).
- `evalFSNZ2_of_C4`, `surj_of_C4`: residuals now
  Desc3, HGood3, HDiagT1, HEngPath, HRootSP (earlier rounds) +
  HDiagLoc, HDiagStep (HCID), HCntPath0 (t = 0), HNoSucc1, HCntRoot2 (t = 2).

WfCofC5.lean (green)
- `hCntPath0_of : HCntAtG0 → HCntStep0 → HCntPath0` (up the path from g = P_0(r) to the last root).
  - `HCntAtG0`: t = 0, g = P_0(r): fsD(o_A(g), k) ≤ o_{A[k+2]}(g)  (the copies r + jL are children of g in A[k+2]).
  - `HCntStep0`: edge c = P_0(d), d a strict ancestor of r: bound at d ⇒ bound at c.
- `surj_of_C5`: residuals Desc3, HGood3, HDiagT1, HEngPath, HRootSP, HDiagLoc, HDiagStep, HCntAtG0, HCntStep0,
  HNoSucc1, HCntRoot2.

CAP 6000 per file (out2/, summary2.txt), all 0 failures:
- HCntPath0 (P0) 65,322 × 3 n; root case 5,845 × 3; F0 71,167 × 3.
- HDiagLoc (DL) 176,057; CI 176,057; HDiagStep (DB): Rt 134,418, mid 1,193,750, r 176,057.
- HRootKeep2 (now proved) R2roots / R2pre 93,335 × 3; HCntRoot2 (C2) 93,335 × 3; F2 93,335 × 3.
- HCntV2 (VP) 103,998 × 3. HNoSucc1: no t = 1 matrix of successor type among 176,057 t = 1 diagonal + others.
- False forms: V2 21,673 / 25,043 / 28,317; DT mid 91,932, r 56,062 (smallest
  (0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,3,0)(5,3,0)(6,3,0)(7,0,0)(5,3,0)).
