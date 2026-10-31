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
