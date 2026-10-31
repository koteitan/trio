# WfExQ: the invariant step (ExpStepQ) of the new q = r engine, 2026-11-01

Lean (all green, no sorry, axioms = propext / Classical.choice / Quot.sound; roots in the lakefile):
Ytosk/lean/Ytosk/WfExQ1.lean ... WfExQ12.lean.  Scripts here: audit3.py (audit), run.sh, gen_auwl.py
(data of WfExQ12), graftU.py (graft family around the AbsUWL witnesses), axcheck*.lean.

## (1) The target bundle Inv3V3 (WfExQ1)
`Inv3V3 M ρ rk` = `Inv3V2` with
- `adn   : AbsDN`  -> `adn0   : AbsDN0` (WfInvA1),
- `tplow : TPLoWs` -> `tploq  : TPLoQ` (new, WfExQ1),
- `adw   : AbsDWs` dropped,
- `auwl  : AbsUWL` dropped (NEW this round: false, WfExQ12; the first version of Inv3V3, commit aad2270f, had it),
- `ads   : AbsDS`  -> `adsx   : AbsDSX` (WfQnE2),
- `tplos : TPLoS`  -> `tplosx : TPLoSX` (WfQnE2),
other 18 fields unchanged: cons good rank vs fc fo kd td ph fc3 vra aus tp1 tp1w auw0 trigs tplon rootS rootP.
`TPLoQ`: TPLoWAt pattern at the seed (q = r frame, D o call c, o(c) = ψ_s(y), y ≠ b_r, low part of y empty,
last y = Ω_a, a not succ, OHole a, cof a = ω); for every chain level m with m + d_c ≥ 1:
  ¬ ψ(a[g(m + d_c)]) < Ω_{s+1}   (old TPLoW)
  or  (a source exists and at every source i: ¬ ψ(P + W[g(max 1 (m + d_i))]) < Ω_{s+1})
a source = D v call i, e1 i ≠ 0, v(i) = a, W = bumpW i (e2 i ≠ 0) or last v(upg i) (e2 i = 0); P = v(P1 i);
g(k) = gamS μ b_r seed k (`TSrc`).
Bridges (proved): `tpLoQ_of_tpLoWs`, `Inv3V2A.toV3`, `Inv3V2.toV3` (Inv3V2 has more fields; each new form is weaker).

## NEW FALSE FIELD: AbsUWL (WfExQ12, Lean)
N = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)
(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(9,2,1)(10,2,1)(11,2,0)(9,2,1)(10,2,1)(11,1,0)(12,0,0)(13,1,1)(10,2,0)(11,3,1)
(12,3,1)(13,1,0)(14,2,1)(12,3,0)(11,3,1)(12,3,1)(13,1,0)(14,2,0)  (39 columns, Std by a 340-step trace, < SRO;
from graftE; 5 failing matrices of 39-42 columns there).
x = 38, r = P1 x = P0 x = 37 (q = r), A = o(r) = ψ_{ψ(1)}(Ω_{ψ(1)+1}).  i = 34 = (12,3,0) is a D v call upgrading
to k = 35, d_i = 2 (dOf proved: DepL path vupg 35, vbump (36, 37) weight 2, ochild 38 weight 0).
W = last v(35) = A itself; q0 = v(29) = ψ_{ψ(1)}(ψ_{ψ(1)}(ψ_{ψ(1)}(ψ(ψ_{ψ(1)}(0))))) < W, but
q0 ≥ W[gamS μ b_r 1 2] = ψ_{ψ(1)}(ψ_{ψ(1)}(ψ_{ψ(1)}(1))).
Same phenomenon as the bad bump call (W = A, a summand of v(P1 i) re-exposed), here at an UPGRADE call.
Theorems: not_absUWL, no_inv3V2, no_inv3V2A, main (Std N ∧ N ≠ SRO ∧ no Inv3V2 ∧ no Inv3V2A).
Consequence: the old HFrameV2 is false also through auwl (TakeFrameV2.auwl).  AbsUWL's only consumer was the old
absorption engine (qr_vloc); the DQ engine needs none (WfQrE1.v_upgDQ), so it is dropped like adw.

## (2) Measurements (audit3.py = WfInvX/audit.py + exact Lean forms of AbsDN0, TPLoQ, AbsDSX, TPLoSX)
Mode `new` (new fields only) on q = r frame sets: famframes (208,964 family-prefix frames), WfInvA/frames/std_b
(1,564,945), t2ext, graftM36x, g36_2:  adn0 0 / 117,803;  tploq 0 / 6,013,692 (old TPLoWs fails 98 on the same frames).
Mode `full` (all Inv3V2 fields + new ones) on the grafts not in the round-8 audit: see the table at the end.
Coverage of the old data (round-8 audit, 23.2M + 4.69M family prefixes): every new field is implied by an old field
(Lean bridges) and the old fields failed only on adn 474 / tplow 49 / ads, tplos 6 matrices, all re-measured here
(famframes, std_b frames) or in WfQnE (6 / 6) and graftQ1/Q2 (grafts of those 6).

## (3) The fields of Pn on M[n], q = r frame (proved unless listed under "remaining")
Carried property `PnV3f M ρ r L N σ := (∃ rk, Inv3V3 N σ rk) ∧ σ.o r < ρ.o r ∧ σ.v r ≤ ρ.v r ∧
  FrameMapT1 M ρ r L N σ ∧ VrDomQ M ρ r L N σ`; extra facts `Ex = ExDQX` (DQ at every D call, ρP.o r ≤ o(x)),
obtained from hLocH's C_strip conjuncts (`exDQX_of_loc`).
- cons, good: the ExpStepQ premises.  rank: rk_gexp_t1.  rootS: rootS_of_good.
- rootP: rootP_N_t1Q (DQ.lt at the root Rt ∈ D).                                                       [WfExQ2]
- fo: frameOT_N_t1Q -- frame heads only (frameHead_ltQ / frameHead_copyQ, copies for glueQ).          [WfExQ5]
- kd, td: copy of V3BumpN; uses only value ≤ old, value ≠ 0 (DQ.lt, o_ne_z_of_cons).                    [WfExQ6]
- ph, fc3, fc: the old carry used the D values only through trig_back_fsD; trig_back_DQ is the same for any DQ
  value.  The leaf residual (child Ω_{t+1} with v(i) ≤ t): c < x in D impossible (qr_holeD), c = x needs only
  ρP.o r < o(r) (no chain term gamS).                                                     [WfExQ4, 5, 8]
- vra: the frame map FrameMapT1 (copy of expStep_frameMapT1) is carried; vsmallRAll_of_mapT1.          [WfExQ11]
- vs: copy of expStep_vsmallFS; reduced to VSFResQ at the changed D children.                          [WfExQ10]
- tp1, tp1w: from ph and the two leaf conditions.
- σ.o r < o(r): DQ.lt at r ∈ D.  σ.v r ≤ v(r): r ∉ D_v.
Final statements: WfExQ11.expStepQ_V3f : ExpStepQ (PnV3f M ρ r L) (ExDQX M r L ρ) M r L d0 ρ;
WfExQ11.qr_chainV3f = WfQrH7.qr_chainH3 with Pn = PnV3f (its Ex conjunct of hLocH removed).

## Exact remaining list (q = r frame)
1. hVSF : VSFResQ M r L d0 ρ -- at a frame i < x whose counted child c is a D v call, the components of the new
   v_N(c) = B ++ Q ++ W' (relative to v(i)) are ≤ ψ_{v_N(c)}(0) or ≤ the state before c (the old VSFRes with Q).
2. hFr : FrameAtN M r L d0 -- the 8 last-column frame fields of M[n] (adsx aus tplosx tploq auw0 trigs tplon adn0)
   and the leaf conditions TP1LeafG / TP1WLeafG; frameAtN_of_glob: from the global HFrameV3 for a standard M.
   These are about the NEW last column of M[n]; the engine outputs do not give them.
3. base of the chain: Inv3V3 of M[1] = M.take x, ρ1.o r < o(r), FrameMapT1/VrDomQ of M[1] (the old
   frameMapT1_takeG), plus qr_chainH3's own hypotheses (hLocH without Ex, hv1, structural ones).

## Results table (summary.py; all runs finished)
new.jsonl (q = r frames: famframes, std_b, t2ext, graftM36x, g36_2; 2,139,163 matrices):
  adn0 0 / 124,564;  tploq 0 / 6,274,774;  (old TPLoWs 102 failures on the same frames).
full.jsonl (graftA1-3, D, E, F, G, H, Q1, Q2, w1, w2; 692,991 matrices < SRO): every Inv3V3 field 0 failures
  (structural 13 fields, cons good rank vs fc fo kd td ph fc3 vra aus tp1 tp1w auw0 trigs tplon rootS rootP,
  adsx 0/1,557,112, tplosx 0/2,041,262, tploq 0/3,160,295, adn0 0/579,956).
  Old fields: ads 15,352, tplos 30,704, tplow 1,066, adw 533, adn 57, auwl 5 (graftE; WfExQ12).
graftU.jsonl (graftU.pkl: 32,339 grafts of the 5 AbsUWL witnesses, gen 1 + 300-sample gen 2): every Inv3V3 field 0;
  old auwl 1,244, adw 88, tplow 26.
