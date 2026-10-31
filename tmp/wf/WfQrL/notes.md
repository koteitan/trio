# WfQrL: the q = r engine wired to DQ (2026-11-01)

Lean files (all green, no sorry, no axiom; roots added to the lakefile): Ytosk/lean/Ytosk/WfQrL1.lean ... WfQrL11.lean.
Scripts: compq.py (step 4, standard form of DQ values), frames.py (frame hypotheses of the DQ engine).

## Shared definition with the q != r agent
The bad bump call is `WfBad.BadCall M ρ r ζ i` (committed by WfQnL in Ytosk/lean/Ytosk/WfBad.lean):
BadShape1 M i, rows 1, 2 nonzero, bumpW M ρ i = o(r), a summand q of v(P1 i) with q < W, not q < W[ζ].
WfQrL1.absorbed_of_not_badCall uses it; WfQrL1.v_bumpQ_nil: a bump call with the absorption has Q = 0.
In the DQ form of the q = r engine no bad set is needed: DQ covers Q != 0 and Q = 0 alike.

## What is proved (Lean)
- WfQrL1: `glueQ M x ρ ρN oq vq` (given values on D), `glueZ_eq_glueQ`, `cons_glueQ_lt`, `OLocQ`/`VLocQ`
  (raw frame equations, no absorption), `qr_pathQ`, `bumpWQ`, `bumpW_glueQ`, `v_bumpDQ_glueQ`, `v_upgDQ_glueQ`,
  `add_exchangeQS` (Q is made of summands of v(P1 i)), `exchangeQ_nil`, `v_bumpQ_nil`.               [step 1]
- WfQrL2: omega exchange for DQ: `omega_DQ` (cases small / rest / subscript / argument / base), `DQ.true_inv`,
  `DQ.pre`, `DQ.snoc`, `lo_keep_DQ` (no low part appears if the new last summand is >= Omega_{s+1}),
  `lastQ_of_tpLoQ`, `lastQ_of_le` (TPLoQ / PgeS give that condition).                                   [step 2]
- WfQrL3: `hi_keep_DQ` (DQ keeps the high part and a low part; the side condition hHi of omega_DQ_arg).
- WfQrL4: last-child o frame: `frame_DQ_add` (no trigger: add_exchangeQ, Q from `pre`!), `frame_DQ_trig`
  (trigger, no low part), `o_frame_eq`, `o_frame_DQ`.                                                 [step 3]
- WfQrL5: `glueQ_eq_glueZ` (glueQ = glueZ of tildeV = oq + 1 on D, since fsD(X + 1, η) = X): the copy lemmas apply;
  `cons_N_t1Q`, `root_N_t1Q`.
- WfQrL6: `good3_N_t1Q`.
- WfQrL7: `qr_chainQ` (n-induction with given D values), `ExpStepQ` (carried property with extra facts Ex),
  `qr_mainQ` (hLoc from OLocQ / VLocQ + DQ.lt).                                                         [step 6]
- WfQrL8: `true_glue`: for the true valuation σ of M[n] (cons_of_rk + rk_N_t1), τ = glueQ(σ.o, σ.v) equals σ
  (rank induction `agree_of_eqs`), so Cons N τ and the local equations on D hold for free.
- WfQrL9: `qr_chainT`: the chain from facts about the true values on D only:
  σ.o r = γ(n-1), Single σ.o Rt, σ.o Rt < o(Rt), isOT on D, σ.o c <= o(c), σ.o c != 0, + Ex for Pn.
  No fsD, no absorption (adw), no TPLoW.
- WfQrL10: `qr_engineDQ`: by rank induction every D call of the true valuation is a DQ of the old value
  (o: DQ η false, v: DQ η true), composing DQ.sub / o_frame_DQ / v_upgDQ_glueQ / v_bumpDQ_glueQ, under the frame
  hypotheses hTrig, hUpgL, hBW, hPre, hSo, hSv, hX.  `engine_o_lt`: σ.o c < o(c) (the two bounds of hLocT).
- WfQrL11: `frame_DQ_node` (node case of the o frame, see below).

## Measurements
compq.py (step 4): at every argument level ψ_a(b) -> ψ_a(bN) above a non-empty Q of the true M[n] values (n = 2..4),
the new components g ∈ comps(a, bN) \ comps(a, strip(bN)) (strip = remove every Q):
  C_ot (g < bN): 0 failures; C_strip (g < strip(bN), the value with all Q removed): 0 failures;
  C_lN (g < new last summand of the Q level): FAILS (900 / 1475 on graftA1); C_Qq (comps(a, q) < q): FAILS (23).
  Sets: m13, g36_2, graftM36x, graftA1, graftA2 (+ graftA3, see compq.jsonl).  No DQ failure (DQFAIL 0).
  => the standard-form condition to carry is C_strip: "the new components brought by Q are below the old-engine
  value (Q removed) at that level".  Not formalized yet (needs a DQ with the stripped term carried along).
frames.py (frame hypotheses of qr_engineDQ, true values, n = 2, 3):
  hUpgL, hBW (some η in {Zf i, Zf k}), hPre, hSo, hSv: 0 failures on m13, g36_2.
  hTrig (same trigger in M and N) is FALSE; every failure still has o_N(i) = DQ(o(i)).  Shapes (g36_2, 200 frames):
    node: trigger in both, y = B + Ω_{s+1}, y_N gets a low part  -> proved: WfQrL11.frame_DQ_node;
    leaf parent (c = x): no trigger in M (o(x) = Ω_{μ+1}, y = 0), trigger in N  -> OPEN (needs the shape of the
      chain term γ(n-2) = o_N(x));
  frames.py now classifies add / trig / node / leafpar / other (frames.jsonl).

## Added after the first measurements (WfQrL12-18, all green)
- WfQrL12 `DQ.last` (hUpgL from the DQ of v(k) when the new last summand is single).
- WfQrL13 `omega_DQ_true` (DQ on a sum through ω), `OmSide`, `bumpW_DQ` (two ω layers).
- WfQrL14 `omega_DQ_E0` (ε0 crossing: Y = ε0, Y_N < ε0; the bad call of M13), `omega_DQ_node` (low part appears
  at an ω layer: DQ form of omega_lift), `frame_DQ_trig_lo` (trigger in both, low part in both).
- WfQrL15 `frame_DQ_leafpar` (parent of x: o(x) = Ω_{a+1}, trigger only in N, hi(y') = B + Q).
- WfQrL16 `qr_engineDQ2` (engine with per-frame steps), `OFrameOK`/`oframe_DQ` (5 o-frame shapes: add, trig,
  triglo, node, leafpar), `LayerOK`/`layer_DQ` (3 ω-layer shapes: OmSide, ε0 crossing, node), `bumpW_DQ2`.
- WfQrL17 `bumpW_eq_bumpWQ`, `bumpWQ_app`, `bump_step` (hBW2 from the two layer shapes + the VLocZ list conditions).
- WfQrL18 `true_glue_eq`, `qr_chainE`: the q = r chain for all n >= 2 where the root drop and o(c) bounds come from
  the DQ engine; hypotheses (hLocE): chain term at r, Single σ.o Rt, standard form on D, σ.o c != 0, hX, the
  o-frame step, hUpgL, the bump step (each supplied by the shape lemmas above), Pn via ExpStepQ.
frames.py now classifies every o-frame / ω-layer by shape; on m13 + g36_2 (n = 2, 3): 0 unclassified frames,
every leaf-parent frame satisfies the hypotheses of frame_DQ_leafpar, every ω layer is OmSide | ε0 | node.
Caveat: the Python hQ0 test checks "Y single → Y_N single" (slightly weaker than Lean's Q = 0); hB tested with
η = Zf(k) only.

## Measurement results (final, this round)
compq.jsonl: m13, g36_2, graftM36x, graftA1, graftA2, graftA3 (113k frames), n = 2..4: DQ failures 0, C_ot 0 fail,
  C_strip 0 fail (1475 levels with new components per graftA set), C_lN / C_Qq fail (not usable).
frames.jsonl: m13, g36_2, graftM36x, graftA1, graftA2 (n = 2, 3; graftA3 not run, ~45 min): 0 FAIL of any kind:
  hSo, hSv, hPre, hUpgL, hBW; every o-frame is add | trig | triglo | node | leafpar (leafpar lemma hypotheses hold on
  all 41,772 leaf-parent frames); every changed ω layer is OmSide | ε0 crossing (614) | node (8,124).
Not yet attacked by new grafts (graftA1-3 are the grafts of round 9).

## Next
1-3. Done as shape lemmas (WfQrL12-17).  Remaining: derive the shape predicates (OFrameOK, LayerOK) from invariant
   fields of M (TPLoQ / lo_keep_DQ / hi_keep_DQ / old omega_fsD_hole_Q / the chain term shape at x), i.e. state the
   fields on M, measure them on all sets + grafts, and prove field -> shape.
4. Standard form (hSo, hSv): formalize C_strip (DQ carrying the stripped term; isOT of B ++ Q ++ lN, and comps).
5. σ.o r = γ(n-1) (Q = [] at r) and hX (DQ.base at x: fsD(o(x), γ) = γ).
6. Then qr_chainT gives all n >= 2 with Pn = Inv3V2A via ExpStepQ (the invariant step for the DQ glue is the large
   remaining part; qr_final_inv3V2A without tplow / adw needs it).
