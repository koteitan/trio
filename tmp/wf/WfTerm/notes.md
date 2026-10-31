# WfTerm: ATerm / BTerm (terminal shape of the next-column change chain), 2026-10-31

## Lean (Ytosk/lean/Ytosk/WfTermA.lean, green, full build 1146 jobs, axioms propext / Classical.choice / Quot.sound)
- Structural: `up1_of_hiR` (HiR a x -> Up1 a x), `hiR_of_par1`, `anc0_take`, `anc0_of_take`, `hiR_take`, `up1_take`.
- `not_dropFail_of_hi`: in the common frame of ATerm/BTerm (c bump grandchild of i, changes, off the path to x-1,
  e1 c <= e1 m), with the first chain step c' (NextC c c', upg(c'-1)=c', q = P0 c' = P1(c'-1) strict ancestor of m):
  1. q is on the row-1 chains of c and of m (HiR q c from par1_between).
  2. v(q) does not change in M.take x (ChgX false q gives TopC M x q, which forbids the row-1 child c'-1 of q).
  3. v(q) = tau.v(q) < tau.v(c) < tau.o(c) <= W_T(i) (v_chain_lt in the take, sub_lt_psi, child_sum_le_bumpW).
  4. The failing summand s = bumpW(k), upg b = k, b on the row-1 chain of m (source_summand_origin).
     b at or below q: s <= v(b) <= v(q) < W_T(i). b above q with lev s <= v(q): s < tau.o(c) (psi order: index first).
     Left: b strictly above q with v(q) < lev s  -> residual `TermHi`.
- Bridges: `aTerm_of : TermHi -> WfSrcR5.ATerm`, `bTerm_of : TermHi -> WfSrcR5.BTerm`.
  Splice: `WfSrcR5.t2AbsNSrcW_of hP (WfTerm.aTerm_of hH) (WfTerm.bTerm_of hH) hC` with hH : WfTerm.TermHi.

## Measurements (b2fam; frames_b2fam.pkl = the 560 matrices with a changing c, 578 frames; probe_v*.py)
- V1: v(q) < W_T(i) in 578/578 (now proved).
- Every summand of v(m) in [psi(2), W) is <= v(q) (252 of 252).
- P1(c) = q in 578/578 (not used).
- Chain origins (b on m's chain with an upgrade):
  - at or below q: 830, all < W_T (proved).
  - strictly above q: 1954; all have v(b) unchanged, e1 b >= e1 c, no bump child of k on the path to m.
    Index split: lev t <= v(q) (1164, all t < tau.o(c), proved) / lev t > v(q) (790, all t >= o(c) and t >= W(i)).
  So TermHi has 0 exceptions (the window premise never holds). Other sets: probe_B found the frame only in b2fam
  (std_a: 6 frames without a change of c; graft/expansion families: 0 frames).

## Next
TermHi: an upgrade term t = bumpW(k) on m's chain strictly above q with lev t > v(q) is >= W(i)
(measured: t >= o(c) always). Needs: lev t > v(q) = v(P1 c) forces lev t >= v(c) = v(q) + term(c),
i.e. no index of a chain upgrade term falls in (v(q), v(c)); in the equality case compare the psi arguments.
