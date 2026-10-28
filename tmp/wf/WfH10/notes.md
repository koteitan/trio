# WfH10 notes (H10Big = T0H10Core.T0BadSeedsH10Big)

## 1. Structure forced by Bad2 in the H10 frame
x = r+L (last), P0 x = r, e1 x = 0.  Bad2 gives p = P0(x-1), b = P0 p, col p = bump b,
and (Anc0 b x or e2 x != 0).  e1 x = 0 gives e2 x = 0 (R12), so Anc0 b x.
p != r (Counted g r), so p is a strict descendant of r, b >= r, and b ancestor of x => b = r.
So: p = bump child of r (last child of r before x), x-1 = child of p, x = child of r.

The 68 codex U3 failures all have b != r (Bad2_ancestor = False): they are NOT antecedents
of H10Big.  Of the 2373 graft antecedent rows of codex's json, only 2 have the b = r shape,
both e1 g = 1.

## 2. Shape graft generator (gen_shape.py)
For M in a set, every r with e2 r = 1, upg(r-1) = r, every prefix end j in r's subtree,
every a in 1..e1 r: N = M[:j] + [bump(r), (e0r+2,a,0), (e0r+1,0,0)]  (+ variant with an
extra child (e0r+2,a2,0) of p).  Keep structural antecedents, then bms -s = 1 and < SRO.

d3s: 130,844 structural candidates, 1,609 standard (e1g: 1:802, 2:786, 3:21).

## 3. U3' (v(P1(x-1)) finite) is FALSE
151 + 6 + 2 standard antecedents with V = omega (p(1)) or omega+omega.  Smallest (24 cols):
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,0)(5,3,1)(6,3,1)(7,3,0)(5,3,1)(6,3,1)(7,2,0)(6,0,0)
r=20, g=16 (e1 g = 2), x=23, k=upg(22)=15, P1(22)=8, V = v(8) = omega, W = bumpW(15) = omega.
Strong absorption holds (V = W: nothing absorbed).  bms -s = 1, below SRO.

## 4. What the consumer needs, and what the data shows
UpgAbsX at x for every Cons sigma (sigma = rho by cons_unique with Inv3V2's Rk).
By upg_target_val + add_right_injective, W = bumpW k.  If W < E0, lhd_lt_small closes it.
On all 1609 d3s antecedents: k = upg(x-1) has exactly ONE child (never a bump child),
so W = omega.  Danger(V, W) false everywhere.

## 5. Lean (green)
Ytosk/lean/Ytosk/WfH10Bridge.lean:
- KNoBump (residual candidate): H10Big frame + e1 g >= 2 + upg(r-1)=r + upg(x-1)=k + Bad2 shape
  (P0(x-1)=p, P0 p=b, col p = bump b, Anc0 b x)  ->  no child of k is a bump child of k.
- h10Big_of_kNoBump : KNoBump -> T0H10Core.T0BadSeedsH10Big.  axioms [propext, Classical.choice, Quot.sound].

## 6. KNoBump is FALSE, and H10Big itself is FALSE (2026-10-29)
graft_kbump.py: insert a bump child (and small subtrees) under k in the 1,609 d3s antecedents.
11,457 structural candidates, 2,606 standard (bms -s = 1, below SRO): KNoBump false.
Among them 6 standard matrices where the strong absorption at x FAILS -> Bad2 holds -> H10 conclusion false.
Smallest (29 cols), all checks:
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(4,2,0)(5,3,1)(6,3,1)(7,3,0)(5,3,1)(6,3,1)(7,2,0)(6,0,0)
 r=25 (5,3,1), L=3, g=21 (4,2,0) e1 g = 2, x=28 (6,0,0), x-1=27 (7,2,0), p=26 = bump(25).
 upg(24)=25, upg(27)=18 (3,2,1); 18 has bump child 19 (4,2,1) with child 20 (5,1,0).
 V = v(P1 27) = v(11) = omega; v(18) = W = bumpW(18) = Omega_omega; omega not lhd Omega_omega
 (u = 0, c = Omega_1: comps_0(omega) = {1, 0} not dominated by comps_0(Omega_1) ++ [0] = {0}).
 Python Inv3V2 probes on the actual valuation: probe_inv3_prefix inv_fields (Good3, VSmallF, FrameOT,
 FrameClosed, TP1, TP1W, TrigOm, BumpKidsDec, BumpTermDec, AbsD/AbsDW/AbsDN, AbsU/AbsUW, TPLo/TPLoW/TPLoN,
 rootS, rootP): 0 failures; PH3cG, FC3 (codex checker): 0 failures; VSmallRAll (probe_inv2): 12 cases, 0 failures.
 The x-frame fields (AbsDS, AbsUS, TPLoS, TPLoWs, AbsUWL, AbsUW0, AbsDWs, TrigS0) are vacuous: P1 x = none.
 Only drop fields fail (BumpAbsC, BumpWeakSrc, UpgAbsX) -- expected on Bad2.
 reach.py: SRO -> M in 143 expansions (reach_cex29.json).
Other 5: same prefix with (7,2,0) doubled, or extra (5,1,0)/(6,1,0) under 19.

Consumer: T0BadSeedsH6's third field "Counted M g r -> Counted (gexp M r L 0 0 n) g r" fails on this M:
in M[n] (n=1,2,3) r=25 is isUpg (from 24) and topped (only child 26 = bump), so not counted at g.

## 7. Lean (green, build 1104 jobs)
Ytosk/lean/Ytosk/WfH10Cex.lean:
- standard : Std M (143-step trace, decide); frame : Frame M 25 3 21; big; preceding_upgrade; final_upgrade
- cons : Cons M ρ for an explicit table valuation; not_strong : ¬ UpgAbsX M 28 ρ; bad2 : Bad2 M
- h10_core_false : ¬ (∀ N, Std N → N ≠ SRO → Bad2 N → ∀ r L g, Frame N r L g → 2 ≤ e1 g → upg N (r-1) ≠ some r)   [propext]
- counted_M, not_counted_exp2, not_counted_gexp2,
  h6_counted_core_false : the structural core of H6 field 3 (without Inv3V2) is false.  [propext, Classical.choice, Quot.sound]
H10Big adds only the premise Inv3V2 M ρ rk; it is false unless some Inv3V2 field fails on this M,
and all probed fields hold.  So H10Big cannot be proved; the t=0 Bad2 engine must handle
"r uncounted at g in M[n]" (counted_first0G's hT is not available).

## 8. Where H10 is consumed, and what still holds (2026-10-29)
Chain: H10 -> H9 field 2 -> H8/H7 field 3 -> H6 field 3 via counted_first0G (hT = H10) giving
"Counted M g r -> Counted (gexp M r L 0 0 n) g r" -> passed unchanged through H5..H2 -> used ONLY in
t0_S1N_cnt (V3T0BadNode) as hcN, i.e. for S1 of T0SeedsN at g.
In t0_S1N_cnt, hcN is used only in two branches:
  (a) drop at r is lhd (po_lhd_or_weak left): hcN NOT used;
  (b) weak, v r <= v g: hcN used (t0_S1N_of Or.inr);
  (c) weak, v r > v g: hcN used (t0_S1AW_nodeHi).
s1_measure.py (H10 case = frame + upg(r-1)=r; shape_d3s + kbump_d3s, n = 2,3,4):
  S1 Lhd part  o_N(g) = psi_{v g}(X') lhd o(g)  holds 12,627/12,627 (not Bad2) and 18/18 (Bad2);
  r is uncounted at g in N in every case.
droplhd_measure.py: in the H10 case v r > v g always (4,215/4,215, branch (c) when weak);
  drop lhd at r: true on all non-Bad2, false on 3 of the 6 Bad2 (incl. the 29-col matrix).
So on the counterexample the engine goes to branch (c), t0_S1AW_nodeHi, which needs Counted N g r: false.
The seed fact S1 itself is numerically true there; only the route is missing.
RClaimU (the other conjunct of S1) was NOT measured.

Proposed replacement (not adopted, not in Lean): in t0_S1N_cnt split on the H10 case
(r-1 upgrades to r and r topped in M.take x).  Outside it, counted_first0G gives hcN with no residual.
Inside it, a new S1 node lemma for "r uncounted in N" is needed (o_N(g) loses o(r), keeps the copies).
