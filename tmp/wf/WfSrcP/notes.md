# WfSrcP: lower-row case P shared by (a) shape (A) and (b) sub-case (P) (2026-10-31)

Shape P: c bump grandchild of i (j = last child of i in T, bump; c = last child of j), c changes,
c < x-1, c row-0 ancestor of x-1, e1 c < e1 m (m = P0 i = P1 i), every earlier child d of j has e1 d < e1 m.

## Lean (Ytosk/lean/Ytosk/WfSrcP1.lean, green, full build 1135 jobs, axioms propext/Classical.choice/Quot.sound)
- `PLow`: shared residual (no (a)/(b) frame condition; keeps Bad2, StepCtxT2, P2 x exists).
- `not_dropFail_of_lt_o`: v(P1 i) < tau.o c => no DropFail (window empty).
- `PLowRes` = PLow + premise `¬ rho.v m < tau.o c`; `pLow_of_res : PLowRes -> PLow`.
- `SrcARem3` = SrcARem2 with only shape (B); `srcARem2_of : PLow -> SrcARem3 -> SrcARem2`.
- `SrcBNonlost3` = SrcBNonlost2 with `¬ Anc0 c (x-1)` (only O'); `srcBNonlost2_of : PLow -> SrcBNonlost3 -> SrcBNonlost2`.
- `t2AbsNSrcW_of : PLowRes -> SrcARem3 -> SrcBNonlost3 -> SrcCRes -> WfT2Src.T2AbsNSrcW`.
Splice: T2BadRes first field := PLowRes ∧ SrcARem3 ∧ SrcBNonlost3 ∧ SrcCRes,
used as `WfSrcP.t2AbsNSrcW_of hP hA hB hC` in place of `WfSrcABC.t2AbsNSrcW_of hA hB hC`.

## Measurements (probe_p.py; p3..p7.json). B2 = exact Bad2 (UpgAbsX / BumpAbsC tests).
| set | (a) B2 P before K-filter | of which K has e1 d >= e1 m | (b) B2 P (exact premises) | V < tau.o c | PLowRes | window nonempty | DropFail |
|---|---:|---:|---:|---:|---:|---:|---:|
| b2grow1 | 432 | 432 | 0 | | | | 0 |
| b2grow2 | 1282 | 1282 | 0 | | | | 0 |
| wide grafts | 894 | 894 | 0 | | | | 0 |
| grow (404218) | 0 | | 1473 | 932 | 541 | 0 | 0 |
| growP (79727) | 0 | | 1494 | 1081 | 413 | 0 | 0 |
| paired400, real grafts, graftB, graftBb2St(_x2), cbadext, d3s, Cprime, deep2, t2ext, ext2, expPt2 | 0 | | 0 | | | | 0 |
- (a): under Bad2 shape P never reaches the residual: every instance has an earlier child d of j with
  e1 d >= e1 m (closed by failed_drop_earlier_row_lt). Non-Bad2 (a) P frames are many (grow 81939).
- The nonempty windows reported in WfSrcB/notes.md (94 grow, 140 growP) are ALL in non-Bad2 frames
  (probe_b3 did not test the Bad2 value condition). With Bad2 the P window is empty on every set.
  So the "gap claim is false" note does not apply to Bad2 frames, and the Lhd lead is not needed there.
- PLowRes instances (growP 413): always i has the single child j, j the single child c, v(m) is one
  psi term, and either v(m) >= W_M(i) (365) or v(m) < W_T(i) (48). e1 c in {0,1}, e1 m - e1 c in {1,2}.
  lev(v m) = v(c) in 207, lev(v m) > lev(W) in 206.
- Non-Bad2 only: expPt2 has 8 RES instances (all v(m) >= W).

## Next
PLowRes: show the gap `v(m) < W_T(i) ∨ W_M(i) <= v(m)` in the single-branch shape
(W_M(i) = omega(1 + omega(o c)), W_T(i) = same with tau.o c). Needs the relation of v(m) to o(c)
(copy of c at m's row-1 ancestor a with e1 a = e1 c, P1 c = P1 a by par1_deep_return).
Also: show nB = nK = 0 structurally in the residual (measured, not proved).
