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
