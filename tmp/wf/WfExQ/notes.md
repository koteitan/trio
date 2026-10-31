# WfExQ: the invariant step (ExpStepQ) of the new q = r engine, 2026-11-01

Lean (all green, no sorry, axioms = propext / Classical.choice / Quot.sound; roots in the lakefile):
Ytosk/lean/Ytosk/WfExQ1.lean ... WfExQ9.lean.  Scripts here: audit3.py, run.sh, axcheck.lean.

## (1) The target bundle Inv3V3 (WfExQ1)
`Inv3V3 M ρ rk` = `Inv3V2` with
- `adn   : AbsDN`  -> `adn0  : AbsDN0` (WfInvA1),
- `tplow : TPLoWs` -> `tploq : TPLoQ` (new def, WfExQ1),
- `adw   : AbsDWs` dropped,
- `ads   : AbsDS`  -> `adsx  : AbsDSX` (WfQnE2),
- `tplos : TPLoS`  -> `tplosx : TPLoSX` (WfQnE2),
all other 19 fields unchanged (cons good rank vs fc fo kd td ph fc3 vra aus tp1 tp1w auwl auw0 trigs tplon rootS rootP).
`TPLoQ`: TPLoWAt pattern at the seed (q = r frame, D o call c, o(c) = ψ_s(y), y ≠ b_r, low part of y empty,
last y = Ω_a, a not succ, OHole a, cof a = ω); for every chain level m with m + d_c ≥ 1:
  ¬ ψ(a[g(m + d_c)]) < Ω_{s+1}   (old TPLoW)
  or  (a source exists and at every source i: ¬ ψ(P + W[g(max 1 (m + d_i))]) < Ω_{s+1})
where a source is a D v call i with e1 i ≠ 0, v(i) = a, W = bumpW i (e2 i ≠ 0) or last v(upg i) (e2 i = 0),
P = v(P1 i), g(k) = gamS μ b_r seed k (`TSrc`).
Bridges (proved): `tpLoQ_of_tpLoWs`, `Inv3V2A.toV3`, `Inv3V2.toV3`.

## (2) Measurements (audit3.py = WfInvX/audit.py + exact Lean forms of the 4 new fields)
Mode `new` (only the new fields) on the q = r frame sets not measured before:
famframes.pkl (208,964 family frames), WfInvA/frames/std_b, t2ext, graftM36x, g36_2:
  RESULTS: see the table at the end (filled when the run finished).
Mode `full` (all Inv3V2 fields + the new ones) on every graft not in the round-8 audit:
graftQ1, graftH, graftD, graftF, graftG, graftE, graftw1, graftw2, graftQ2, graftA1, graftA2, graftA3.
Coverage argument for the old data (round-8 audit, 23.2M matrices + 4.69M family prefixes): every new field is
implied by the old field (Lean bridges), and the old fields failed only on: adn 474 family matrices (AbsDN0 measured
0 / 203,672 there in WfInvA and again here on famframes), tplow 45 family + 4 std_b matrices (TPLoQ measured here on
famframes / std_b frames), ads / tplos 6 family matrices (AbsDSX / TPLoSX 6 / 6 in WfQnE, and graftQ1 / graftQ2 are
grafts of those 6).

## (3) Which fields of Pn on M[n] follow, q = r frame
Proved (Lean):
- cons, good: the ExpStepQ premises.
- rank: `rk_gexp_t1` (structure).            rootS: `rootS_of_good`.
- rootP: `rootP_N_t1Q` (only `oq Rt ≤ o(Rt)`, from DQ.lt at the root Rt ∈ D).            [WfExQ2]
- fo (FrameOT): `frameOT_N_t1Q` -- reads only v(i) and the earlier counted children of a frame, which the frame heads
  keep (`frameHead_ltQ`, `frameHead_copyQ` = copies of the glueZ lemmas for glueQ). No value fact.   [WfExQ5]
- kd, td (BumpKidsDec, BumpTermDec): copy of V3BumpN for glueQ; it uses the D values only through
  `value ≤ old` and `value ≠ 0` (DQ.lt, o_ne_z_of_cons).                                              [WfExQ6]
- ph, fc3, fc (PH3cG, FC3, FrameClosed): the old carry used the D values only through `trig_back_fsD`;
  `trig_back_DQ` is the same for any DQ value (base = fsD, sub = argument 0 never triggered, arg = same subscript and
  smaller argument).  `frameQR_N_t1Q`, `frameClosed_N_t1Q`.                                          [WfExQ4/5]
  Their leaf residual (child Ω_{t+1} of a frame before x with v(i) ≤ t) is proved for q = r (`omQ_qr`, `fcOm_qr`):
  c < x in D is impossible (`qr_holeD`: D values are holes, not successors); c = x needs only ρP.o r < o(r)
  (`ψ_μ(y) < ψ_μ(b + Ω_{μ+1})`, `between_app`), not the old chain term gamS.                          [WfExQ8]
- tp1, tp1w: from ph and the two leaf conditions (`tp1C_of_ph3cG`, `tp1WC_of_ph3cG`).
The chain bound ρP.o r < o(r) is carried in Pn (`PnV3r ρ r N σ = (∃ rk, Inv3V3 N σ rk) ∧ σ.o r < ρ.o r`); on M[n]
it is DQ.lt at r ∈ D.  `Ex = ExDQX` (DQ at every D call + ρP.o r ≤ o(x)) follows from hLocH's C_strip conjuncts
(`exDQX_of_loc`).

Final statements:
- `WfExQ8.expStepQ_V3Y`, `WfExQ9.expStepQ_V3r : ExpStepQ (PnV3r ρ r) (ExDQX M r L ρ) M r L d0 ρ`
- `WfExQ9.qr_chainV3`: WfQrH7.qr_chainH3 with Pn = PnV3r, the Ex conjunct of hLocH removed, base
  `hP1 : PnV3 (M[1]) ρ1`, `hs1 : ρ1.o r < ρ.o r`.

## Exact remaining list (for the q = r frame)
1. hVSF : ExpStepQR PnV3 VSmallF (ExDQY M r L ρ)   -- component condition of the new v values at counted children in
   D (v_N(c) = B ++ Q ++ W'); the glueZ version needed VSFRes2 / PassRootRes.  New argument (Q).
2. hVRA : ExpStepQR PnV3 VSmallRAll (ExDQY M r L ρ) -- same for VSmallRAll (glueZ: T1VSRAllStep).  New argument.
3. hFr : FrameAtN M r L d0 -- the nine last-column frame fields of M[n] (adsx aus tplosx tploq auwl auw0 trigs tplon
   adn0) and the two leaf conditions TP1LeafG / TP1WLeafG.  `frameAtN_of_glob`: implied by the global HFrameV3
   (= HFrameV2 ∧ HLeafV2 with the new forms) for a standard M.  These fields are about the NEW last-column frame of
   M[n], not about M's frame, so the DQ engine outputs do not give them.
4. base: hs1 (seed below o(r); from the drop lemma) and Inv3V3 of M[1] (the drop step, as before).
