# WfSrcO: the shared next-column case (B) of SrcARem2 / (O') of SrcBNonlost2 (2026-10-31)

## Result
The case is NOT structurally impossible. Only values exclude it.

- Standard 7-column matrix (bms -s = 1), outside any frame:
  (0,0,0)(1,1,1)(2,2,1)(3,2,1)(4,1,0)(1,1,1)(2,1,1)
  i=2, m=1, j=3, c=4 (changes: o_T(4) != o_M(4)), c'=5=upg(4), q=0 strict ancestor of m. x = 6 is a bump child of c' (snb).
- Standard 41-column matrix in the structural (b) frame (P0 x = P1 x = P2 x = x-1, upg(x-1)=7, P0(x-1)=38 bump child of 37):
  (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)(4,2,0)(5,3,1)(6,3,1)(7,2,0)(6,3,0)(7,4,1)(8,4,1)(9,2,0)(8,4,0)(9,5,1)(10,5,1)(11,2,0)(7,4,1)(8,4,0)(9,5,1)(10,5,1)(11,2,0)(10,5,0)(11,6,1)(12,6,1)(13,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)
  i=34, m=33, j=35, c=36 (changes), c'=37=g, q=8. Exact Bad2 is false (UpgAbsX trivially true: v(P1(x-1)) = v(0) = 0; BumpAbsC true).
- So the induction "chain to x-1 ends in a contradiction" cannot close the case: the terminal shape exists.

## Measurements (probe_B.py, B*.json)
- b2fam (2.4M): (B)-structure with c changing: 578 hits. Structural Bad2 part (upg(x-1), P0(x-1) bump child): 169 of them
  (a: 89, b: 80). Exact Bad2: 0. DropFail at i: 0 (all 578).
- Window at i (summands s of v(m) with psi(2) <= s, W_T <= s < W): empty in all 578; in 452 no summand in [psi(2), W) at all,
  in 126 two summands there but below W_T.
- v(m) <= tau.v(c) (certificate of not_dropFail_of_parent_le_child) holds only in 18 of 578.
- grow, growP, graftB, graft_b2, b2grow1/2, cbadext, graftBb2St_x2, wide grafts: 0 hits. std_a: 6 hits, no change of c.

## Lean (Ytosk/lean/Ytosk/WfSrcO1.lean, green, standard 3 axioms)
- chain_term: from (B) (c' < x, upg(c'-1)=c', ChgX false c', P0 c' = P1(c'-1) = q strict ancestor of m) by induction on
  x - c': supg/vupg impossible (e2 c' = 1), vpar impossible (TopC q), snb terminal, vbump: k = x or k above x-1 terminal,
  else ICC at k gives c2 > c' whose parent q2 is a strict ancestor of c' (not the bump child, not c': row 2).
- Term M x m c: an upgrade target cs > c, ChgX false cs, child of a strict ancestor qs = P1(cs-1) of m, with
  x a bump child of cs, or x / an ancestor of x-1 a child of a bump child of cs.
- term_of_outside: the start from a changing c (chg_off + chg_struct), no last-child hypotheses needed.
- termB_of_term: in (b) with Bad2 (e2(x-1) != 1) only the "ancestor of x-1" form: TermB.
- SrcARem3 (B replaced by not-Anc ∧ Term), SrcBNonlost3 (O' replaced by TermB), bridges srcARem2_of_3, srcBNonlost2_of_3,
  splice t2AbsNSrcW_of3 : SrcARem3 → SrcBNonlost3 → WfSrcC.SrcCRes → WfT2Src.T2AbsNSrcW.

## Next
The terminal case needs a value argument. Two routes, both value level:
1. Term ⇒ ¬DropFail at i (holds in all 578 measured, window empty).
2. Term ∧ c changes ⇒ ¬Bad2 (value part), i.e. UpgAbsX at x-1 and BumpAbsC hold.
