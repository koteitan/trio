# WfCof: goal 5 (surjectivity) — EvalCof from the fundamental sequences

## Statements (Lean: Ytosk/lean/Ytosk/WfCof.lean, green)

V3Surj: `surj : Desc3 → EvalCof → ...`, with

    EvalCof : ∀ A std, A ≠ SRO, A ≠ [], ∀ tA t, Val A tA → isOT t → t < tA → ∃ n tN, Val (A[n]) tN ∧ t ≤ tN

Proved here (no new axioms; `#print axioms` = propext, Quot.sound, Classical.choice):

- `fs_cof_omega` (terms only, unconditional): isOT s, cof s = ω, isOT t, t < s ⇒ ∃ k, t < s[k]
  (s[k] = `fs s (natT k)`, γ_0 = 0). Diagonal points via `cof_gam` (V3SeedTop), using
  comps μ b' ⊆ comps a b' (a ≤ μ) and the standardness of ψ_a(b').
- `le_fs_of_cof_succ`: cof s = succ, t < s ⇒ t ≤ s[η] (any η) (`fs_succ_eq`: s[η] + 1 = s).
- `cof_of_lt_Om1`: isOT s, 0 < s < Ω_1 ⇒ cof s ∈ {succ, ω}.
- `val_lt_Om1` (unconditional): Val M t ⇒ t < Ω_1 (all summands of the root have index 0: `I0`).
- `val_zero_last` (unconditional): last column (0,0,0), Val M tA, Val (M.take x) tN, isOT tN ⇒ tA = tN + 1.
- Reductions:
  - `evalCof_of_E : Desc3 → EvalFSE → EvalCof`
  - `evalCof_of_NZ : Desc3 → EvalFSNZ c → EvalCof`, `evalCof_of_evalFS : Desc3 → EvalFS c → EvalCof`
  - `surj_of_evalFSNZ`, `surj_of_evalFS`.

  where (A std, A ≠ SRO, A ≠ [], tA = val A)

      EvalFS c   : ∀ k tN, Val (A[k + c]) tN → tA[k] ≤ tN
      EvalFSNZ c : EvalFS c restricted to a nonzero last column
      EvalFSE    : nonzero last column, ∀ k, ∃ n tN, Val (A[n]) tN ∧ tA[k] ≤ tN   (weakest)

So goal 5 = Desc3 + EvalFSNZ 2 (or the weaker EvalFSE). The zero-last-column case is closed.

## Measurement (fsprobe.py, fsprobe2.py)

For A and n: L(n) = max k with tA[k] ≤ val(A[n]); deficit def(n) = n − L(n). EvalFS c ⇔ def(n) ≤ c for n ≥ c.

- Sample of 2000 from std_a (NMAX 6): cof(tA) ∈ {succ (exactly the zero-last-column matrices,
  val(A[1]) + 1 = tA in all 305), ω}. Never big (as `cof_of_lt_Om1` says).
  Per type of the last column, minimal uniform c: t = 0: c ∈ {0,1,2}; t = 1: {0,1,2}; t = 2: {1,2}. Never 3.
  val(A[n]) < val(A[n+1]) for all n ≥ 1 (strictly increasing), and val(A[n]) < tA always.
- c = 1 is false: e.g. A = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(2,1,0)(1,1,1)(2,1,0) (t = 1):
  tA = ψ_0(X + ψ_{Ω_ω}(ψ_1(0))) with X = ψ_{ψ_{ψ_0(1)}(0)}(0) + ψ_{Ω_ω}(Ω_ω + Ω_ω);
  val(A[n]) lies in [tA[n−2], tA[n−1]) for all n ≥ 2: the expansion's diagonal chain starts one step behind
  the γ_0 = 0 chain of `fs`, and one more step is lost to "n copies vs the n-th element".
- Why 2: index shift 1 (A[n] has n copies, A[1] is A minus its last column, which is ≤ tA[0] in general
  for t = 1, 2) + seed lag 1 (the last copy has no upgrader, so its diagonal seed is o_{A[1]}(r),
  the fsD chain c_n = fsD(c_∞, c_{n−1}) from c_1).

Results over all sets and families (2026-10-31):

- out/ (fsprobe.py, CAP 150000, NMAX 6; 13 family files: WfAbsW, WfB2L, WfB2S, WfH7W2, WfInvD, WfSib, ...):
  128,312 matrices; max def over n >= 1 is <= 2; val(A[n]) < tA in every case.
- out2/ (fsprobe2.py, CAP 20000 per file, NMAX 5; all 50 handoff sets incl. std_b, ext1, ext2, expP, expPt2, t2ext,
  the graftA1..3 / graftM36 / graftM36x families, the descent set desc1.pkl (271k random deep descents from
  SRO[2..5], len <= 40), and the new graft family graftF.pkl (48,754: 60 smallest deficit-2 seeds, their M[2]/M[3]
  and prefixes, gen_all + row-1 lift to 4..6 + larger sibling, 2 generations, bms -s = 1)):
  nonzero last column, minimal uniform c per type t of the last column:

      t   c=0      c=1      c=2      c>=3
      0   75,253   50,927   36,281   0
      1   17,142  209,357  153,941   0
      2    9,483   73,412   98,939   0

  zero last column: 10,172, all with val(A[1]) + 1 = tA. val(A[n]) strictly increasing in n >= 1: 724,735/724,735.
  Large n (graftF_b sample 1500, NMAX 9): c <= 2 still (out2/large_n.json).
  Not evaluated: 2 matrices of sets/cbadext.pkl (no value) and 1 A[n] there (no value); outside the claim.

## What remains for goal 5

1. Desc3 (goal 4; shared with goal 3).
2. EvalFSNZ 2 (or EvalFSE): a lower bound for val(A[n]), the converse direction of Desc3's upper bound.
   Natural route: the engines already describe val(A[n]) along the path as fsD(o_A(h), ζ_n)
   (FSD.lean, desc.md "経路上の節点での一様な関係"); fs t (natT k) = fsD at the γ_k chain.
   EvalFS then needs (a) fs t k ≤ fsD t ζ for γ_k ≤ ζ (`DiagAt.fsD_mono` / `fsD_mono_big`)
   and (b) the seed bound γ_k ≤ ζ_{k+2} (the chain of seeds in A[n] dominates the γ chain two steps behind).
   For t = 0 (copies of a ψ_0 summand) it is an additive count.
