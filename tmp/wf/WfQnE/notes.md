# WfQnE: the t = 1, q != r engine at the seed (2026-11-01)

## What really happens on the 26-column N (WfInvX1.N)
x = 25, r = 22, q = P0 x = 24, A = o(r) = psi(Omega_{Omega_1}) (mu = 0, b = Omega_{Omega_1}), seed = psi(Omega_{psi(2)}).
Bad column i = 20 = (3,2,1): P0 20 = P1 20 = 19, CL 20 = [] (its child 21 is the bump), CL 19 = [20], nothing upgrades to 20.
Bump term W = bumpW(20) = A (the node itself). V = v(19) = q0 = psi(Omega_{psi(Omega_{psi(X)})}), X = psi_{psi(2)}(...) + ...
- In N: v(20) = sf(add q0 A) = A (q0 < A is absorbed).
- In N[2] (m = 0, zeta = seed): v(20) = q0 + A[seed]  (A[seed] <= q0 < A: NOT absorbed); engine glue says A[seed].
- In N[3] (m = 1, zeta = gamS 1): v(20) = q0 + A[gamS 1]: still not absorbed.  From m = 2 on q0 < A[gamS m].
  So the failure is not "m = 0 only": hADzeta is false at m = 0 and m = 1 (WfQnE1.absDS_gam1_false).
- o(20) = Omega_{v(20)}, then o(19), o(4), o(0) carry Omega_{q0 + A[zeta]} instead of Omega_{A[zeta]}.
- TPLoS at c = 4, 19 (o(c) = psi_{q0}(Omega_A), s = q0): glue gives Omega_{A[seed]} < Omega_{q0+1} (low part appears),
  the true value Omega_{q0 + A[seed]} >= Omega_{q0+1}: the low part stays empty.  TPLoS fails only because of the glue.
Both failing fields are one phenomenon: the non-absorbed summand q0 of v(P1 i) at a bad-shape bump call with W = A.
Same mechanism as the q = r witness M13 (i = 9 = (3,2,1), P0 = P1 = 8, bad shape, W = A = psi(Omega_1)).

## Lean (green, build 1165 jobs)
- WfQnE1: true valuations tau2, tau3 of N[2], N[3] (Cons by decide), `expand_gexp` (expand N n = gexp N 22 3 3 0 n),
  `v20_2` / `v20_3` (tau.v 20 = app q0 (fsD (rho.v 20) zeta)), `not_cons_glue2` / `not_cons_glue3`:
  for every rhoP, glueZ N 25 rho rhoP (fun _ => zeta) is NOT a Cons valuation of gexp N 22 3 3 0 n (n = 2, 3).
  So the engine's output form (t1_main_vlocSG / vlocal_t1_at) is false here, not only its input fields.
- WfQnE2: BadShape1 (M-part of WfAbsW.BadAbsShape), AbsDSX / TPLoSX (old conclusion OR bad shape with W = o(r)),
  absDSX_of_absDS, tpLoSX_of_tpLoS, hADzetaX_of_absDSX (all zeta >= seed), bad_v_lt (sf(add V W') < A when V, W' < A),
  add_absorb (add V A = A when V < A).

## Measurements (analyze.py)
- fields(): ADS failure => BadShape1 at i and W = A (ADSX); TPLoS failure at c => exists bad i with AbsDS failing,
  c row-0 ancestor-or-self of P0 i, a = W_i (= A), s <= v(P1 i) (TPLX).
- primary(): a call deviating from the glue although all inputs of its equation equal the glue.  Claim: only
  bump calls with BadShape1, W = A and a summand of v(P1 i) in [A[zeta], A).
- scope(): with B = those calls, every deviation lies in the DepX-closure of B; at deviations glue <= true < old (M).
- The 6 failing family matrices (26, 34, 48, 49, 94, 111 columns), n = 2..5: all claims hold; deviations at n = 2, 3 only.
- Gen-1 grafts (graftQ1.pkl, 4540 standard t = 1 q != r grafts of the 56 seeds = 6 witnesses + their frame prefixes;
  ops: inserted children/larger siblings, row-1 +2/+3 (b >= 4), +-1 mutations, delete/duplicate, new last column, M[2]/M[3]
  prefixes): ADS fail 304 (all W = A, ADSX 304/304), TPL fail 608 (TPLX 608/608), primary deviations 397 all P.v.bad, 0 other.
- Gen-2 grafts (graftQ2.pkl, 29364 grafts of the 304 failing gen-1 grafts): ADS fail 15048 (all W = A, ADSX 15048/15048),
  TPL fail 30096 (TPLX 30096/30096), primary deviations 18496 all P.v.bad, 0 other.
- scope() on every failing graft (+2% sample of the rest), n = 2, 3: graftQ2 301980 deviating calls, graftQ1 5510:
  all inside DepXB(B), all with glue <= true < old (scopeQ1.json, scopeQ2.json).
- Sanity (fields hold there, so the glue must be exact): std_b 200k sample (27430 frames), graftM36x 100k (6285 frames),
  ext2 100k (40195 frames): 0 bad calls, 0 deviations in the scope sample.

## Proposal (the generalized t = 1, q != r engine)
Let A = o(r) = psi_mu(b), zeta = gamS mu b seed m (n = m + 2), and
  B_zeta = { i < x : DepX false i, e1 i, e2 i != 0, BadShape1 M i, bumpW i = A, exists q in summands v(P1 i), A[zeta] <= q < A }.
The true valuation sigma of gexp M r L d0 0 n satisfies
  (E1) sigma = glueZ M x rho (shiftV rhoP L) (fun _ => zeta) off DepXB M B_zeta (WfQnE3.AgreeOffB; congruence lemmas done);
  (E2) at i in B_zeta: sigma.v i = sf(add v(P1 i) A[zeta]) (< A by WfQnE2.bad_v_lt), sigma.o i = o-equation with CL i = [];
  (E3) on DepXB: fsD(old, zeta) <= sigma < old.
The fields used by the engine become AbsDSX / TPLoSX (WfQnE2): they are exactly the old ones with the bad case B allowed
(0 exceptions on all failures and grafts).  Proof plan: (1) generalize vlocal_t1_at to VLocal or bad (the bad case is the
bump frame with K = [] , k = r, W = A); (2) build sigma by cons_of_rk, prove (E1) by AgreeOffB induction on the rank;
(3) Good3 / Pn on DepXB from (E2), (E3) and the bad shape (o(m) = psi_{v(m)}(Lc + Omega_{v(i)}), the low part stays
empty because v(m) <= v(m) + A[zeta]); (4) root N < root M from (E3) at the root.
The q = r witness M13 (tplow / adw) has the same shape (i = 9, P0 = P1 = 8, BadShape1, W = A), so the q = r engine
(qr_vloc / qr_lkeep) should take the same generalization with zeta = gamS (m + d_i).
