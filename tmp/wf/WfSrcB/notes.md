# WfSrcB: part (b) of WfT2Src.T2AbsNSrcW (2026-10-31)

Case (b): P0 x = P1 x = x-1 (x = r+L last column).

## Lean (Ytosk/lean/Ytosk/WfSrcB1.lean)
- par2_prev / L_eq_one: Bad2 gives upg(x-1) != none, so e2(x-1) = 0 and P2 x = x-1. L = 1 always in (b).
- shape_b: lost c = x-1 gives i = P0(P0 r). c < x-1 closed when e1 c > e1 m (high) or
  e1 c = e1 m with x-1 below c (nonlost return, next column inside c's subtree automatically).
- Residual SrcBNonlost: c < x-1 with (x-1 below c, e1 c < e1 m) or (x-1 outside c's subtree, e1 c <= e1 m).
- Split bridge t2AbsNSrcW_of : SrcA -> SrcBNonlost -> SrcC -> WfT2Src.T2AbsNSrcW.

## Measurements (probe_b.py)
See probe_b_*.json. Tags: lost / high / earlier_return / nonlost_return / row1_desc / pending, x prevdesc|outside.
