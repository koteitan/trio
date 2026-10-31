# WfQnL: wiring the t = 1, q != r engine to the bad set (2026-11-01)

Shared definition (for the q = r agent too): `Ytosk/lean/Ytosk/WfBad.lean`
- `BadCall M ρ r ζ i` = BadShape1 M i ∧ e1 i ≠ 0 ∧ e2 i ≠ 0 ∧ bumpW M ρ i = ρ.o r ∧ ∃ q ∈ summands v(P1 i), q < W ∧ ¬ q < fsD W ζ.
- `BadSet M x ρ r ζ i` = i < x ∧ DepX M x false i ∧ BadCall.  Its closure is `WfQnE3.DepXB M (BadSet ..)`.

## Lean (all green, no sorry, no axiom; build 1187+ jobs)
- WfQnL1 (step 1): `vlocal_t1_at_loc` (= vlocal_t1_at with the absorption asked only at the call),
  `vlocal_t1_atX`: under the AbsDSX-shaped field (output of `hADζX_of_absDSX`) every v call of D is
  `VLocal ∨ BadSet`; `vlocal_t1_atX_nobad`.
- WfQnL2: `agree_off_rk`, `agreeOffB_of_eqs`: a solution σ (Cons + Rk) equals any τ that satisfies the
  equations off `DepXB N B`, off that closure (rank induction); `cons_unique`.
- WfQnL3: `t1_pathB` = t1_path with OLocal / VLocal asked only off `DepXB M B` (hole + glue equation off the
  closure); `vlocal_offB` (VLocal ∨ BadSet gives VLocal off the closure).
- WfQnL4 (step 2, (E1) in N): `depX_rk`, `not_depX_vx` (¬ DepX M x false x from a ranking), `depXB_lt`
  (closure below x), `cons_glue_ltB`, `depXB_N_of_M` (closure in M ⊆ closure in N = M[n] below x),
  `E1_N`: σ = glue off `DepXB N B`.
- WfQnL5: `depXB_M_of_N` (closure in N lies below x and inside the closure in M, given `hndN`),
  `E1_M`: σ = glue at every call outside `{i < x ∧ DepXB M B b i}` (copy columns included).
- WfQnL6 ((E2)): `BumpNA` / `bump_na` (ζ-data of every bump call of D, no absorption field),
  `bumpW_glue_na` (bump term of the glue = W[ζ]), `vRhs_glue_na`: rhs of glue = sf(add v(P1 i) W[ζ]),
  `vRhs_glue_bad`: at a bad call (W = A = o(r)) the value is sf(add v(P1 i) A[ζ]) < A.
- WfQnL7 (step 4): `root_N_any` (root of M[n] drops for any valuation that keeps the earlier roots and
  puts a single term below o(Rt) at Rt), `root_N_E3`: root decrease from E1_M; (E3) is needed only when
  Rt ∈ DepXB M B (then: Single σ.o(Rt) ∧ σ.o(Rt) < ρ.o(Rt)).
- WfQnL8: `hndN_of_hnd`: hndN from the `hnd` of val_N_t1 (par1_copy / upg_copy / par1_root / upg_root);
  one residual `hu0`: upg (M[n-1]) r = some g → g ≤ r.

## Residual hypotheses introduced (with measurement status)
- `hndN` (WfQnL5) and `hu0` (WfQnL8): structural; measured by hu0.py (below).
- (E3) at Rt: covered by WfQnE scope() (every deviation has glue <= true < old, 307490 calls); Single is
  standard form of a true o value.
- `hO` of t1_pathB: OLocal off DepXB M B.  Not yet derived: the old route derives OLocal from TPLoS; TPLoSX
  fails only at c that are row-0 ancestors of P0 i (i bad) — claim to measure next: such (true, c) are in DepXB.

## Measurements (hu0.py; t = 1, q != r frames, n = 2..4)
(see results section, appended when the runs finish)

## Next
1. OLocal off DepXB from TPLoSX (measure "TPLoS failure c => (true,c) ∈ DepXB M B" first).
2. (E3) on DepXB in Lean: fsD(old, ζ) <= σ < old by rank induction inside the closure, using
   vRhs_glue_bad at the leaves (bad_v_lt: < A; >= A[ζ] = glue) and monotonicity of oRhs / vRhs.
3. Good3 / Pn on DepXB from (E2)/(E3); then assemble `t1_main_vlocSX` from t1_main_vlocSG with
   AbsDSX / TPLoSX: hV -> vlocal_t1_atX, val via E1_M + root_N_E3 instead of cons_N_t1 + root_N_t1.
