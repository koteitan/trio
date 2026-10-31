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

## Measurements
mside.py (M < SRO, every q = r frame of 71 sets: WfInvA/frames/* (all sets incl. the 15 families), frames_g/graftA1-3,
graftE, graftF, graftG): OX, RX (now theorems), S1 (base ρ1.o r < o(x), ≠ 0): see mside0.jsonl.
oframe.py / compq2.py (n = 2, 3): see of_*.jsonl, cq_*.jsonl (results summarized below when finished).
