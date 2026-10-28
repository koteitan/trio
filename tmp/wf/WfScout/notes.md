# WfScout notes (2026-10-29): survey of the 13 top residuals, and hCl narrowed

## Survey (difficulty guess, one line each)
- HDropU: hard. The core drop lemma hypotheses (HardArg, VSmallNew, BumpWeakSrcB, ua, BumpAbsCB); value facts of every standard matrix.
- HFrameV2: hard. 10 frame fields (AbsDS, AbsUS, TPLoS, TPLoWs, AbsUWL, AbsUW0, AbsDWs, TrigS0, TPLoN, AbsDN), all fsD/hole value bounds.
- HLeafV2: hard. TP1LeafG/TP1WLeafG; antecedent (CPairG leaf with OHole) needs "s is a head partial sum of k", a combinatorial value reason (desc).
- HBumpExt: hard. Used only with K = M[n], k = x (T0BumpMono, T2BumpMonoV2); needs o_{M.take x}(c) <= o_{M[n]}(c), i.e. drop vs expansion values (fsD); circular with the M[n] invariant.
- T2CBadOut: very hard. A whole new t = 2 engine for the bad C shape (C_frame's hval is false there).
- hVU (T2VAncUse), hVCp (T2VRACopyEsc), hAG (T2VRAK KAG): hard. Statements about every G2 M r L n frame (copy levels, VDomF).
- hCl (T2SeedClV2B): partly cheap. Its standard-form, level-V and summand-bound fields follow from the invariant of M.take x. DONE (below).
- hPRE (T2SeedPResRCV2E): hard. qr (w1, dom), sv (T2SVStrict: X1 < sigma X1 needs the lost-upgrade psi_{V+1}(0) to survive all spArg/step steps; top summands are not moved, e.g. V + omega), C (decP, strict, lhd).
- hCan (HCanonV2): hard ("days" in desc). v(b) <= v(a) for adjacent siblings: compares bump grandchildren sums of two differently shaped subtrees.
- hDomQ (T2SeedDomV2Q): hard. Level-0 components of omega^S need the sibling state B (expPt2 has 16 cases where only B bounds them).
- T2QNDomBad2: hard. Vacuous on all sets (weak at q only in the simple shape), but the reason is a value fact: in the non-simple shapes an earlier sibling copy supplies the components.

## Re-measurement on graft / expansion families (qndom.py, qnshape.py, canon.py)
T2QNDomBad (the general Dom, superset of T2QNDomBad2's antecedent: Bad2 not required) on qn cases:
| set | matrices | qn | weak | non-simple weak |
|---|---:|---:|---:|---:|
| b2grow1 | 6,517 | 587 | 319 | 0 |
| b2grow2 | 10,081 | 821 | 485 | 0 |
| cbadext | 3,756 | 364 | 6 | 0 |
| ext2b2St | 2,133 | 30 | 0 | 0 |
| graftBb2 | 80,228 | 3,364 | 36 | 0 |
| graftB | 155,926 | 5,030 | 36 | 0 |
| grow (T2 grow family) | 404,218 | 66,636 | 0 | 0 |
| shape_d3s, kbump | 1,609 + 2,606 | 0 | 0 | 0 |
| ufam | 911,416 | 164,956 | 0 | 0 |
All weak cases: simple shape, form v_T(q) = V + omegaT, Dom true.

qnshape.py (exact Bad2 first disjunct, t = 2, qn): in all Bad2 qn cases g = q and k < x - 1;
non-simple shapes (q with 2-3 bump children before x, or p with 2-3 children) occur (b2grow1 268, b2grow2 292)
and are never weak.  Structurally (without the strong-absorption failure) g != q occurs (graftBb2 617, cbadext 8),
so g = q is a value fact, not structural.
k = x is impossible structurally (P1(x-1) would be q with e1 q < e1(x-1) = e1 q).

HCanonV2 (canon.py): graftBb2St 35, graftB 1,727, std_a 7,205, ufam 40,281 antecedents (shape_d3s, kbump, b2grow1/2: 0), conclusion true in all;
a's children are always all bump children of a; sb <= sa lexicographically always.

No residual was found false.

## Lean (green, Ytosk/lean/Ytosk/WfScoutSeedCl.lean, commits f77ad378, 095b4b1b, and the qn t1 bound)
New residual `Ytosk.WfScout.T2SeedClV2R`, bridge `Ytosk.WfScout.t2SeedClV2B_of_R : T2SeedClV2R → T2SeedClV2B`
(axioms propext, Classical.choice, Quot.sound).  Fields removed (now proved):
- qn: isOT (psi V (app B (psi t1 0))) — it is o_{M.take x}(r) (o_cl_eq; v_T(r) = v_M(r) by topP_C + v_take_of_untopped);
  Lc = [] → t1 <= qnS (in fact for every Lc: t1 = V + omegaT with omegaT <= omega^S, qn_take_t1L, add_le_add_left).
- sv: summands of X and X1 >= Omega_{V+1} (every child d of r has the column of x, P1 d = r, row 2 = 1, so
  V + 1 < v(d): sv_children_M / sv_children_ctx, then arg_summands_ge); isOT X1; level u = V of the last field
  (comps_V X1 < X1 from isOT psi_V(X1); comps_V V = [] by comps_self_nil).
- C: summands of X and X1 >= Omega_{V+1} (c_children_e1: q is the last child of r, earlier children have columns
  >= col q by sib_le, e1 q = e1 x > e1 r; so P1 d = r and V < v(d) by v_par1_lt); isOT X1; comps_V X1 < X1.
Left in T2SeedClV2R: qn: comps_V qnS < X1', path levels; sv: X = P + psi_b(x), X1 = P + T1,
T1 != 0, sigma P = P, path levels; C: the same shape fields, summands of sigma X1 >= Omega_{s'+1}, comps_V qnS < X1,
path levels.

Splice (V3TopT2B, lead): replace `(hCl : T2SeedClV2B)` by `(hClR : WfScout.T2SeedClV2R)` and add
`have hCl : T2SeedClV2B := WfScout.t2SeedClV2B_of_R hClR` at the start of the proof; import Ytosk.WfScoutSeedCl.
The count stays 14 (same residual slot, fewer fields).

## Not done: comps_V qnS (qn and C)
comps_V (V + omega^S): the V part is empty (summand subscripts < V), and omega^S has none when lev(omega^S) < V.
When lev(omega^S) = V (allowed by qn_omega_lev: a grandchild c of q with v(c) = V), omega^S = psi_V(Y) and Y need not be
below Omega_{V+1}; the bound by X1 needs values.
