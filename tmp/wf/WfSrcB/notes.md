# WfSrcB: part (b) of WfT2Src.T2AbsNSrcW (2026-10-31)

Case (b): P0 x = P1 x = x-1 (x = r+L last column). m = P0 i = P1 i, j the last changing bump child of i,
c the last changing child of j (T2SrcQuiet.failed_drop_branch).

## Lean
Ytosk/lean/Ytosk/WfSrcB1.lean
- par2_prev / L_eq_one: Bad2 gives upg(x-1) != none, so e2(x-1) = 0 and P2 x = x-1. L = 1 always in (b).
- shape_b: c = x-1 gives i = P0(P0 r). c < x-1 is closed when e1 c > e1 m (high grandchild) or
  e1 c = e1 m with x-1 below c (next column then stays in c's subtree, nonlost_return_value).
- SrcBNonlost (residual), SrcA ((a): no DropFail), SrcC ((c): the bound at the (b) shape).
- t2AbsNSrcW_of : SrcA -> SrcBNonlost -> SrcC -> WfT2Src.T2AbsNSrcW.
Ytosk/lean/Ytosk/WfSrcB2.lean
- outside_shape: c not above x-1. ICC (chg_struct) gives c' = next column after c's subtree,
  upg(c'-1) = c'. m' = P1(c'-1) is a strict ancestor of c, not i or j (row 2), so m' = m (then
  e1 m < e1 c, closed) or m' is a strict ancestor of m.
- SrcBNonlost2 (narrowed residual) and srcBNonlost_of_2 : SrcBNonlost2 -> SrcBNonlost.
Remaining inside SrcBNonlost2:
  (P) x-1 strictly below c and e1 c < e1 m;
  (O') x-1 outside c's subtree and the next-column upgrade c' has row-1 parent strictly above m.
Splice: T2BadRes first field := SrcA /\ SrcBNonlost2 /\ SrcC, used as
  WfSrcB.t2AbsNSrcW_of hA (WfSrcB.srcBNonlost_of_2 hB) hC.

## Measurements (probe_b.py, probe_b2.py; all case-(b) frames, every W-changing e12 column)
| set | (b) frames | W changes | DropFail | DropFail at i=g, c=x-1 | P (lower row) | P with nonempty window | O frames | O' (m' != m) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| grow (404218) | 14782 | 159907 | 1192 | 1192 | 31249 | 94 | 57717 | 0 |
| growP (79727, from the 94) | 4442 | 55538 | 661 | 661 | 12296 | 140 | 21280 | 0 |
| ext2 (1497986) | 980 | 4234 | 0 | 0 | 113 | 0 | 1494 | 0 |
| expPt2 (2460115) | 94 | 98 | 0 | 0 | 0 | 0 | 0 | 0 |
| t2ext (1207960) | 851 | 2288 | 0 | 0 | 92 | 0 | 331 | 0 |
| graftBb2St_x2 | 2673 | 5706 | 3 | 3 | 7 | 0 | 1390 | 0 |
| b2grow1 / b2grow2 / wide / cbadext | 31/27/12/26 | | 0 | | | | | 0 |
| paired grafts 400, graftBb2St_g0/g1 | 0 | | | | | | | |
r = x-1 in every (b) frame (proved). Every DropFail in (b) is at i = g with c = x-1 (proved by shape_b
given SrcBNonlost). O' never occurs. P with a nonempty window occurs (94, 140) and the window summand is
absorbed by Lhd: v(m) is one psi term with the same index as o(c) (example in probe_b3_grow.json).

growP = 2 expansion levels (n=1..4, len<=170) + bms-standard last-column grafts of the 94 P frames (gen_growP.py).

## False candidate (do not use)
- Gap claim for P: "for b on the row-1 chain of m, k = upg b < i, j0 bump child of k, d child of j0:
  o(d) < oT(c) or o(c) <= o(d)". 140 violations in growP (j0 < i in all), exactly the frames where the
  window is nonempty. So the P case needs the Lhd argument, not the window-emptiness argument
  used by T2SrcReturn.lost_branch_not_between. (probe_gap.py, probe_gap_1.json)
