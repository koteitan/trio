# WfQrE: the t = 1, q = r engine without TPLoWs / AbsDWs (2026-10-31)

Lean: Ytosk/lean/Ytosk/WfQrE1.lean (green). Scripts: cmp.py, cmpq.py, dq.py, runq.py, mfail.py, tpsrc.py, chain.sh.

## 1. What M[n] really is on M13
M13 = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(4,0,0)(2,1,0)(3,2,1)(4,2,1)(5,0,0)(6,1,0),
x = 12, r = 11, A = o(r) = psi(Omega_1), seed = 1, gamS 0..4 = 1, psi(1), psi(psi(1)), psi^3(1), psi^4(1).
D columns: o 0, 4, 8, 9, 10, 11 and v 9; d = 2 at 0, 4, 8, 9.
cmp.py / cmpq.py (true evaluator values of N = M[n]):
- n = 3, 4 (m = 1, 2): every D value is fsD(value_M, gamS(m + d)). The old engine is right there.
- n = 2 (m = 0): columns 10, 11 are fsD(., seed); columns 9, 8, 4, 0 are not:
  v_N(9) = q + q, q = v(8) = psi^3(1) = fsD(A, gamS 2) = W'.  (fsD(v 9, gamS 2) = W' only.)
  o_N(9) = psi_{q+q}(0), o_N(4) = o_N(8) = psi_q(psi_{q+q}(0)), o_N(0) likewise one level deeper.
  The summand q of v(P_1 9) = v(8) was absorbed by W = A in M and is not absorbed by W' in N.
mfail.py (levels): the failure of AbsDWs / TPLoWs at chain index k = m + d happens at m = 0 in most frames but also at
m = 1 (graftA1, graftA2: aw.maxm1 = 1, tp.maxm1 = 2). So "n = 2 only" is not a way out.

## 2. The general description: DQ
DQ eta t tN (Lean `DQ η k t tN`, Python dq.py): follow the hole path of t as fsD does; at every sum level on the path,
tN = (the same leading summands) ++ Q ++ (new last summand), every summand of Q in [new last, old last); at the end of
the path take the fsD step. Q = [] everywhere is exactly fsD on the path.
On M13 (n = 2) every D value of N is DQ(value_M, gamS(0 + d)) with one Q = [psi^3(1)] at the depth of v(9)
(depth 0 at v 9, 1 at o 9, 2 at o 8 / o 4, 3 at o 0). Also: fsD(t, g_k) < tN < fsD(t, g_{k+1}) (sandwich) there.
The source of Q is always a v frame:  v(i) = A + W = B ++ W,  v_N(i) = A + W' = B ++ Q ++ W'  (add_exchangeQ).

## 3. New engine invariants
- VLocQ (replaces VLocZ): VLocZ without its last (absorption) conjunct, in both frames. Conclusion at the v call:
  v_N(i) = B ++ Q ++ W' with Q in [W', W) (Lean v_upgQ, v_bumpQ: proved, no value field).
- OLocQ: OLocZ with D values DQ(value, Zf) instead of fsD(value, Zf). Subscript frame: DQ.om (proved).
  Last-child frame: needs (L') below.
- (L') = TPLoQ (replaces TPLoWs, field tplow): pattern of TPLoW at c (o(c) = psi_s(y), y != b_r, low part of y empty,
  last y = Omega_a, a not succ, OHole a, cof omega), a = v(i) = P + W at a D v call i (P = v(P_1 i)):
    not psi(P + fsD(W, gamS(m + d_i))) < Omega_{s+1}   for every m.
  Sufficient structural form PgeS: s <= P (then P + W' > P >= s for every W'; Lean tpLoQ_of_le, proved).
  TPLoW itself implies TPLoQ (P + W' >= W'), so TPLoQ  <=  TPLoW or PgeS.
- adw (AbsDWs) and the AbsDN0 seed case: no replacement needed. The absorption is no longer used: Q may be non-empty.
- ads / tplos (q != r engine t1_main_vlocSG): not addressed here; same mechanism (seed index m = 0, W = node), the same
  DQ form should apply to the q != r glue (not measured).

## 4. Measurements
(see section 6, filled in from tpsrc.jsonl / runq.jsonl)

## 5. What remains (Lean)
1. A glue with given D values (glueQ M x ρ ρN vq oq) and the path theorem qr_pathQ: the local equations
   oRhs(glueQ) i = oq i, vRhs(glueQ) i = vq i from OLocQ / VLocQ. Bookkeeping copy of qr_path (V3QRPath).
2. The omega exchange for DQ at bump frames above a DQ child (analog of omega_fsD_hole_Q / omega_lift1/2 with Q):
   omega(P ++ omega(G_N)) when o_N(k) = DQ(o(k)). Uses (L') in the place where qr_vloc used qr_lkeep.
3. The last-child o frame for DQ (analog of lo_keep_Q / the frame equation in qr_oloc) from TPLoQ.
4. Standard form (Good3 of M[n]) for DQ values: isOT of B ++ Q ++ W' is immediate (Q from a split of a standard
   tail); inside psi_s(...) the comps conditions need: comps of Q at the collapsing levels on the path are below the
   new argument. This is the analog of DV / hok_of_holeT and is the one place where a new value condition on Q may be
   needed (not yet formulated; Good3 of the true values holds on all data).
5. Root decrease: DQ.lt (proved, purely lexicographic) gives root_N < root_M once root_N = DQ(root_M).
6. qr_chain / qr_main with hLoc in DQ form (Zf r = gamS(n - 2) unchanged: r's own value has Q = []).
