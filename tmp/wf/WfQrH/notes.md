# WfQrH: discharging hLocE of WfQrL18.qr_chainE (q = r engine), 2026-11-01

Lean (green, no sorry, no axiom): Ytosk/lean/Ytosk/WfQrH1.lean, WfQrH2.lean.
Scripts: mside.py (M-side facts of qr_chainF), oframe.py (fields of the o-frame reduction), show1.py (print one frame).

## WfQrH1: qr_chainF (chain without γ, hX proved)
- The chain term `σ.o r = γ(n-1)` was used only for the bound `ρP.o r ≤ o(x) ∧ ≠ 0` (good3_N_t1Q).  qr_chainF carries
  `ρP.o r < o(x) ∧ ρP.o r ≠ 0` instead; at each level it comes from the engine (`σ.o r < o(r)`, r ∈ D) and the M-side
  fact `o(r) ≤ o(x)` (hrx).  Conclusion adds `ρN.o r < o(r)`.
- hX is proved: `σ.o x = ρP.o r` (the copy, shiftV) and `o(x) = Ω_{a+1}` (hOx, M-side) give DQ.base with η = ρP.o r
  (`hX_of_omsucc`, fsD(Ω_{a+1}, η) = η).
- New M-side hypotheses: hOx `o(x) = ψ(succ a, 0, 0)`, hrx `o(r) ≤ o(x)`; base: `ρ1.o r < o(x)`, `ρ1.o r ≠ 0`
  (ρ1 = value of M.take x = M[1]).
- Measured (mside.py, M < SRO, every q = r frame): OX, RX, S1 0 failures (mside0.jsonl); copy sanity CHcopy/CHdrop 0
  failures on m13, g36_2 (n = 2, 3).

## WfQrH2: the o-frame step reduced (frame_step_reduce, trigN_of_pre, frame_step_trigArg)
- By the DQ constructor at o(c) = ψ_s(y): `sub` -> add shape (no trigger anywhere, pre < 0 false); `arg` without a
  trigger in M -> add shape (y_N < y kills the trigger); no hypothesis needed for these.
- `arg` with a trigger in M: frame_step_trigArg from (TrigN) the trigger in M[n], (lNz) last(y_N) ≠ 0, and (Last) the
  trichotomy `lo(y) = 0 -> last(y) = Ω_{s+1} ∨ last(y_N) ≥ Ω_{s+1}`; the node / trig / triglo shapes are decided inside
  (hi part kept is proved inline, no all-decomposition side conditions).
- `base`: left as hBase.  Measured: only the leaf parent c = x with o(x) = Ω_{a+1} (form.base.leaf.x).
- trigN_of_pre: TrigN from the M-side `pre ≤ init(y)` and lNz.  BUT PreB is FALSE (g36_2: 780 / 2484 triggered arg
  frames): there y is single (init y = 0), pre ≠ 0, and the subscript of last(y_N) differs from that of last(y).
  PreS `pre < init(y) + Ω_{subscript of last(y)}` holds (2484 / 2484) but does not imply TrigN when the subscript
  changes.  TrigN itself holds (0 failures).
