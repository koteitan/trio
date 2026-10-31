# WfQrH: discharging hLocE of WfQrL18.qr_chainE (q = r engine), 2026-11-01

Lean (all green, no sorry, axioms = propext / Classical.choice / Quot.sound; roots in the lakefile):
Ytosk/lean/Ytosk/WfQrH1.lean ... WfQrH7.lean.  Scripts here: mside.py, oframe.py, compq2.py, graftH.py,
famframes.py, show1.py, show2.py, axcheck.lean.

## Main statement: WfQrH7.qr_chainH
The q = r chain for all n >= 2 (Cons, Rk, Good3, Pn of M[n], ρN.o r < o(r), ρN.o r < o(x), root drop) from:
- (C_strip) at every D call, the change is a `DQC` (WfQrH6): `∃ η tS, DQC η false (o c) (σ.o c) tS`,
  `∃ η tS, DQC η true (v i) (σ.v i) tS`;
- `Ex n ρP σ.o σ.v` (the ExpStepQ side facts for Pn = Inv3V2A; unchanged from WfQrL18);
- (OFields) at every last-child o frame and every η with `DQ η false (o c) (σ.o c)`: `OFields v pre (o c) (σ.o c) η`;
- hUpgL (unchanged), the bump step hBW2 (unchanged; WfQrH4.bump_step3 supplies it from `LayerF` + list conditions);
- base: `ρ1.o r < o(x)`, `ρ1.o r ≠ 0` (ρ1 = value of M[1] = M.take x).
Gone compared with qr_chainE: the chain γ and `σ.o r = γ(n-1)`, hX, `Single (σ.o Rt)`, isOT on D (o and v),
`σ.o c ≠ 0`, `Single ∧ isOT (σ.o c)`, the o-frame step itself.

## WfQrH1: qr_chainF (no chain γ; hX proved)
- `σ.o r = γ(n-1)` was used only for the bound `ρP.o r ≤ o(x) ∧ ≠ 0` (good3_N_t1Q).  The carried invariant is now
  `ρP.o r < o(x) ∧ ρP.o r ≠ 0`, re-established from the engine (`σ.o r < o(r)`, r ∈ D) and `o(r) ≤ o(x)`.
- hX: `σ.o x = ρP.o r` (copy) and `o(x) = Ω_{a+1}` give `DQ.base` with η = ρP.o r (`hX_of_omsucc`).

## WfQrH5: o(x) = Ω_{v(r)+1} and o(r) < o(x) are theorems (qr_chainG); o_ne_z_of_cons
x last, row 1 ≠ 0, row 2 = 0, P1 x = r: no children and no upgrade, so v(x) = v(r) + 1 (`vx_eq`), o(x) = Ω_{v(r)+1}
(`ox_eq`), o(r) = ψ_{v(r)}(Y) < o(x) (`or_lt_ox`).  `σ.o c ≠ 0` for any Cons valuation (`o_ne_z_of_cons`).

## WfQrH2/H3: the o-frame step from fields (frame_step_reduce, frame_step_trigArg, frame_step_leaf, hOF_of_fields)
By the DQ constructor at o(c) = ψ_s(y):
- sub (y = 0): add shape, no hypothesis.   arg without trigger in M: add shape, no hypothesis (y_N < y).
- arg with trigger in M: from TrigN (trigger in M[n]), lNz (last(y_N) ≠ 0 for the single-last decomposition),
  Last (lo(y) = 0 -> last(y) = Ω_{s+1} ∨ last(y_N) and its summands ≥ Ω_{s+1}); node / trig / triglo decided inside.
- base: only the leaf parent o(c) = Ω_{a+1}; then (no trigger at o_N(c)) -> add, or LeafPar fields -> leafpar.
`OFields` = (base -> leaf-parent case split) ∧ (triggered arg -> TrigN ∧ lNz ∧ Last).
trigN_of_pre: TrigN from `pre ≤ init(y)` ∧ lNz — but PreB `pre ≤ init(y)` is FALSE (g36_2: 780 / 2484 triggered arg
frames: y single, pre ≠ 0, the DQ path goes through a subscript `Ω_A -> Ω_{A_N}`).  PreS `pre < init(y) + Ω_{sub last y}`
holds but does not give TrigN when the subscript changes.  TrigN itself: 0 failures.  An M-side form needs a lower
bound of the chain values η against the subscripts on the DQ path (Bachmann-type property of fsD / DQ).

## WfQrH4: the ω layer (LayerF, layer_step, bumpW_DQ3, bump_step3)
No shape needed when both sides < ε0 (omega_DQ_small) or both ≥ ε0 with ≥ 2 summands (omega_DQ_rest); OmSide asked
only at the η of the DQ.  Measured: almost every changed layer is single (g36_2: 5140 single, 36 multi, 4 ε0 crossing),
so the reduction is small; the single case is LayerOK's OmSide / ε0 / node.

## WfQrH6: C_strip formalized (DQC, DQC.toDQ, DQC.strip_le, DQC.ot, std_of_DQC)
`DQC η k t tN tS`: DQ with the stripped term tS (every Q removed) and, at each argument level ψ_a(b) -> ψ_a(b_N),
C_strip (new components of b_N not in comps(a, b_S) are < b_S) and isOT(ψ_a(b_S)); at mk: isOT Q; at base:
isOT(fsD l η).  DQC.ot: isOT t -> isOT tN.  std_of_DQC gives the standard-form conjuncts of hLocE.
New fields to measure: OT_S (isOT ψ_a(b_S)), OT_Q (isOT Q) — compq2.py.

## Lean defects found in the round-10 statements (proved)
- WfQrL13.OmSide is unsatisfiable on a single layer (WfQrH4.not_omSide_single: its hQ0 quantifies over every
  decomposition and `Y_N = 0 ++ (Y_N ++ 0)` forces `Y_N = 0`).  So WfQrL16.LayerOK holds on a single layer only via the
  ε0 / node shapes, while 97% of changed layers are single (369,262 single / 8,078 multi / 574 ε0 crossing).
  frames.py tested the weaker "Y single -> Y_N single".  Fix: OmSide1 (hQ0 only for the single-last decomposition of
  the DQ), omega_DQ_true1, LayerF, bumpW_DQ3, bump_step3.
- WfQrL3.hi_keep_DQ's side condition hlNz is unsatisfiable (WfQrH2.hi_keep_hlNz_false); frame_step_trigArg proves the
  kept high part for the single-last decomposition instead.
- All WfQrH fields are stated for the single-last decomposition (`∃ s0 y0, l = ψ_{s0}(y0)` and the DQ premise).

## WfQrH8: hUpgL from the single last summand (DQ.last1, upgL_of)

## Measurements (all 0 failures unless stated)
mside.py, every q = r frame (M < SRO) of the 71 sets in sets1.txt (WfInvA/frames/* = all handoff sets + the 15
families, frames_g/graftA1-3, graftE, graftF, graftG): 3,481,601 frames: OX, RX (now theorems), S1, V1
(`v_{M.take x}(r) ≤ v(r)`, hv1 of qr_chainH3) 0 failures (mside1.jsonl).
oframe.py (n = 2, 3; CAP = 2000 random frames per set; 72 sets incl. famframes.pkl = 208,964 q = r frames among all
prefixes of the family members and of their M[2], M[3]): 64,642 frames, 645,356 triggered-arg o frames:
  forms: only sub / arg / base at the leaf parent x (no other base form, no base at c ≠ x);
  OFields: TrigN, lNz, Last, Leaf (add 64,642 / leafpar 64,642, Leaf.lt) 0 failures; untriggered arg -> no trigger in
  M[n] 358,688 ok (this is the Lean lemma notTrig_arg).
  M-side candidates for TrigN are FALSE: PreB `pre ≤ init(y)` (100,700 failures; smallest witness 9 columns
  (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,0)(2,2,1)(3,2,1)(4,1,0)(5,2,0), n = 2, i = 0, c = 4), PreS (3,154), PreSeed / PreEta
  `pre < η` (153k), PreB ∨ PreEta (97k), lNgeEta `last(y_N) ≥ η` (67,948).  lastNotOne (last(y) ≠ 1) 0 failures.
  layers: single 369,262, multi 8,078, ε0 crossing 574, no other crossing.
compq2.py (n = 2, 3, same samples): DQ 1,801,736 ok; C_strip 8,648,670 ok; OT_S (isOT ψ_a(b_S)) 8,648,670 ok;
  OT_Q 200 ok (non-empty Q is rare).
graftH.py (new graft family around trigsub / leafpar / non-empty-Q frames; WfInvD graftD.gen): see graftH.log,
  mside_H.jsonl, of_H.jsonl, cq_H.jsonl.

## Remaining hypotheses of WfQrH7.qr_chainH3 (exact)
1. hLocH (per n ≥ 2, true valuation σ of M[n], given ρP.o r < o(x), ρP.o r ≠ 0):
   a. C_strip: `∃ η tS, DQC η false (o c) (σ.o c) tS` for c ≤ x in D, `∃ η tS, DQC η true (v i) (σ.v i) tS` for
      i < x in D (measured: C_strip, OT_S, OT_Q, DQ);
   b. Ex n ρP σ.o σ.v (ExpStepQ side facts for Pn; unchanged);
   c. OFields at every last-child o frame for every η with DQ η false (o c) (σ.o c): leaf / Ω_s / arg-decomposition at
      a base form; TrigN, lNz, Last at a triggered argument form (N-side; measured);
   d. hUpgL (WfQrH8.upgL_of: single last summand of v_N(k), standard v_N(k));
   e. hBW2 (WfQrH4.bump_step3: Single bumpW / bumpWQ, the VLocZ list conditions, LayerF at both layers).
2. hv1: v_{M[1]}(r) ≤ v(r) (measured, 3.48M frames).
3. The structural hypotheses of qr_chainE (hpath, hx2, hxnb, hz2, hiu, hiux, hnd, hOS, hOSD, hVS, hPre, Rt, hsM, hpM,
   h1x, hp1, base Cons/Rk/Good3/Pn of M[1], hPv1, ExpStepQ).
Not M-side: TrigN / Last / leaf decision need a lower bound of DQ values against the chain values η along the DQ path;
the naive M-side forms are false (above).
