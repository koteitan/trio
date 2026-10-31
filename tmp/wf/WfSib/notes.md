# WfSib notes (2026-10-31): H7WSib is false

## Result (Lean, green; full build 1149 jobs)
`Ytosk/lean/Ytosk/WfSibCex.lean`:
- `not_h7wSib : ¬ WfH7W.H7WSib` (axioms propext, Quot.sound)
- `not_sibMCol : ¬ WfH7W2.SibMCol`, `not_sibM : ¬ WfH7W2.SibM` (via h7wSib_of_col / h7wSib_of_sibM)
- `standard` (120-step trace from SRO), `cons`, `bad2` (first disjunct: g ancestor of x, UpgAbsX fails), `upg_ne`.

M (31 columns, bms -s = 1):
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)
(4,2,0)(5,3,1)(6,3,1)(7,3,0)(5,3,1)(6,3,1)(7,1,0)(6,3,0)(7,4,1)(8,4,1)(9,3,0)(10,4,1)(11,4,1)(12,3,0)(12,2,0)(12,0,0)
x = 30, r = 27 = (11,4,1) = bump g, g = 26 = (10,4,1), children(M.take 30) 27 = [28, 29], upg 29 = 12, m = P1 29 = 8
(row 1 = 1). c = 28 = (12,3,0) != (12,2,0) = col 29; upg 28 = 19 != 12.
Bad2: i = 29, k = 12, W = psi_{psi(1)}(0), summand q = psi(1) < W, not q <| W (u = 0, c = psi_1(0)).

## How it was found (hunt.py, hunt1.log)
Seeds: F3 frames (probe_sib frame) of graft_sib, graft2, graft3, graft4, graft5, b2grow1/2, graftBb2St, ext3s.
Grafts inside r's subtree: insert one column, replace one column (e0 in e0(r)+1..+4, row 1 <= e1(g)+1, row 2 0/1),
duplicate c's subtree with row-1/row-2 lifts, 400 random double inserts.
4.07M F3 frames, 922k structural failures with row 1 of m != 0, 10 bms-standard; all 10 are Bad2 (chk.py).
The earlier one-column +-1 grafts never produce them: c needs its own subtree (9,3,0)(10,4,1)(11,4,1) before
(12,3,0)... here the new sibling (12,3,0) is a child of r inserted before x-1.

## Consequence
The t0 lost-tail case (seed_sum_lhd -> lost_tail_dom) cannot use "c is a copy of x-1". The value form
WfH7W.H7WTail (Dom(v(P1(x-1)), v(c))) is not refuted here; it needs a separate check on these 10 matrices.
