# WfQrO: q = r engine, o frames — Bachmann-type lower bound for DQ (2026-11-01)

`WfQrO3.preG_of_preB`: PreB is the special case of PreG.

Lean (green, no sorry, axioms propext / Classical.choice / Quot.sound; roots in the lakefile):
Ytosk/lean/Ytosk/WfQrO1.lean, WfQrO2.lean, WfQrO3.lean.  Scripts here: explore.py, trail.py, m1.py, ocut.py (first
tries), og.py (the OG fields, exact search), layer.py (OmSide1 single-layer fields), axcheck.lean.

## The formulation (WfQrO1)
`DQ η k t tN` changes `t` along one path (last summand -> argument / subscript -> ... -> one base node
`l -> fsD(l, η)`).  `DQG η k t tN tc` is `DQ` with a lower witness `tc`:
- mk   : `t = B + l`, `tN = B + Q + lN`, `tc = B + lc`;
- mkQ  : `tc = B + Q + lc` (the comparison passes the re-exposed summands `Q`);
- base : `tc = g` for any `g < fsD(l, η)` (`g = 0`: the base summand deleted, the "cut");
- sub  : `Ω_a -> Ω_{aN}`, `tc = ψ_{ac}(X) + R`;
- arg  : `ψ_a(b) -> ψ_a(bN)`, `tc = ψ_a(bc) + R`;
- low  : `ψ_a(b) -> ψ_a(bN)`, `tc = ψ_{a'}(X) + R`, `a' < a`.
Theorems: `DQG.lt : tc < tN`, `above : p ≤ tc -> p < tN` (the Bachmann-type bound), `DQG.toDQ`,
`DQ.toG` (every DQ has the cut witness when every base value is nonzero).
In words: `p < t` stays below `DQ_η(t)` when the first difference of `p` from `t` is off the DQ path (exit through the
initial part `B`, through `Q`, or at a smaller subscript), or reaches the base node below `fsD(l, η)`.
`pre ≤ init(y)` (the false PreB) is the special case "exit at the top level".

## OFields of WfQrH3 from it
- TrigN <- PreG: `∃ yc, DQG η true y yN yc ∧ pre ≤ yc` (`trigN_of_G`).
- lNz <- `η ≠ 0` and `last(y) ≠ 1` (`lNz_of`, `fsD_ne_z_of_ne_one`).
- Last <- LastG: every decomposition `yN = B + Q + lN` with `DQ η false l lN` and `lo(y) = 0` has `l = Ω_{s+1}` or a
  witness `lc ≥ Ω_{s+1}` of `DQG η false l lN lc` with `lN` single (`last_of_G`).
- `OG v pre s y yN η` = (Trig -> PreG ∧ last ≠ 1 ∧ LastG); `ofields_arg_of_G` (the triggered-argument conjunct),
  `WfQrO2.ofields_of_G` (OFields from the unchanged base part + OG + `η ≠ 0`).
- Leaf decision (c = x: no trigger at `e = ρP.o r` or LeafPar): NOT reduced here (it is about the chain value
  `e = o_{M[n-1]}(r)`; needs an induction over n on `ρP.o r`).  Still a field (measured 0 failures in WfQrH).

## OmSide1 single-layer components (WfQrO2, WfQrO3)
- hQ0 <- `Y_N` single, `η ≠ 0`, `Y ≠ 1` (`hQ0_of`).
- hLo <- `l_N ≠ 0` (kept high part, `lo(b) ≠ 0`, no other hypothesis) and, for `lo(b) = 0`, a DQG witness
  `lc ≥ Ω_{a+1}` with `l_N` single (`lo_keep`, `keep_of_G`).
- `omSide1_of`: OmSide1 from YN single, `η ≠ 0`, `Y ≠ 1`, hArg (`DQ η true b bN` at the arg form), LoG, hB.
- hB with `lo(b) = 0`: proved (`WfQrO3.hB_lo0`: `ω^Y = Y`, `ω^{Y_N} = Y_N`).  hB with `lo(b) ≠ 0`
  (`ω^Y = ψ_a(hi(b) + Y)`, fsD through the cofinality of the last summand) remains a field.
- Node layers (`last(b) = Ω_{a+1}`) are LayerF's node disjunct, not OmSide1: there LoG and hB are false (396/1964 in
  g36_2 CAP 300) and not needed.

## hv1 = v_{M[1]}(r) ≤ v(r) (WfQrO2)
`hv1_of_drop`: from the conclusion of the drop lemma `drop_all_hardW2` (`∀ i < x, PO ρ ρ' i ∧ PV2 M ρ ρ' i`, `ρ'` the
value of `M.take x = M[1]`) at `r`: `PV2` = `LhdE` (≤) or `WkVA` (<) (`v_le_of_PV2`).  So hv1 is no longer an
independent residual; it is a consequence of the drop lemma, whose own hypotheses are in the top statement.

## Measurements (0 failures unless stated)
og.py, CAP = 2000 per set, n = 2, 3, all 71 sets of WfQrH/sets1.txt + graftH + famframes (73 sets), triggered
argument o frames (c < x): og_all.jsonl, 71,710 matrices, 646,554 frames:
  PreG 646,554 / LastG 436,328 (all decompositions) / LastNot1 646,554 / EtaNz 646,554 / DQ 1,006,494: 0 failures.
  PreB.old 101,134 failures (as in WfQrH).
- PreB.old (`pre ≤ init y`) fails as before (about 1/6 of the frames) — PreG replaces it.
- CR.pre0 (`c = r -> pre = 0`) is FALSE (only an observation; not used).
- First try LastCut (witness `g = 0`, no Q) failed 4/946 (θ passes the base below η); LastG with base `g < fsD`
  failed once (θ passes the re-exposed Q: g36_2, 36 columns, n = 2, i = 24, c = 31); with `mkQ` 0 failures.
- trail.py: on g36_2 (CAP 300, 974 frames) the trail of `pre` never reaches the base (all exit through an initial part),
  i.e. even the cut form `pre ≤ y with the base summand deleted` holds there (ocut.py PreCut 1906/1906).
- M[1] forms: `Trig in M.take x` fails at c = r (M[1] changes v(r)) and twice at c ≠ r (36 columns, i = 20, c = 24;
  there PreB holds); `o_{M[1]}(c) ≤ o_{M[n]}(c)` 1935/1935 on g36_2 CAP 600; `y1 ≤ cut(y)` false (40/808).
layer.py (single layers ≥ ε₀, η ∈ gamS(…, k ≤ 4) with DQ; 72 sets = sets1 + graftH, CAP 2000): layer_all.jsonl,
  69,710 matrices, 349,734 single layers (56,018 node layers skipped): YNsingle 349,734, Arg 199,580, LoNot1 199,580,
  LoG 182,622, HB 293,308: 0 failures.
Not done (time): the second-generation graft graftO.py (seeds with PreB false from graftH / famframes) was written but
not run; run `nice -n 15 python3 graftO.py graftO.pkl 10 ../WfQrH/graftH.pkl ../WfQrH/famframes.pkl`, then og.py on it.

## Remaining (exact)
1. OG at every triggered-arg o frame: PreG and LastG (measured; they are restatements of TrigN / Last as "the first
   difference of pre (resp. Ω_{s+1}) from y is off the DQ path or passes the base below fsD", not consequences of
   M-side facts).  The strongest measured M-side form is the cut form (trail never reaches the base on g36_2).
   `last(y) ≠ 1`, `η ≠ 0` (measured; `η ≠ 0` follows from `ρP.o r ≠ 0` for the seed).
2. Leaf decision at c = x (unchanged).
3. OmSide1: YN single, hArg, LoG at non-node single layers, hB with lo(b) ≠ 0.
4. hv1 is discharged by the drop lemma (`hv1_of_drop`); qr_chainH3 itself was not restated.
