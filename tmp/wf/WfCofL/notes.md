# WfCofL: EvalFSNZ 2 (goal 5) — term lemma and reduction to engine-side facts

Notation: A standard, A ≠ SRO, last column x = |A| − 1 nonzero, tA = val(A), tA[k] = fs tA (natT k),
r = bad root (`BRoot`), Y_n = o_{A[n]}(x) (in A[n], the root of the second copy), γ_0 = 0, γ_{k+1} = ψ_μ(b[γ_k]).

## Lean (all green, no sorry, axioms propext / Quot.sound / Classical.choice)

WfCofL1.lean (term side, unconditional)
- `DiagAt.fs_eq_fsD_gam` : DiagAt a b μ t ⇒ t[k] = fsD(t, γ_k)
- `DiagAt.fs_le_fsD`     : γ_k ≤ ζ ⇒ t[k] ≤ fsD(t, ζ)
- `SuccAt` (ω from ψ_a(b), b successor), `SuccAt.fs_eq_fsD` (t[η] = fsD(t, η)), `SuccAt.fsD_le` (count monotone)
- `fs_eq_fsD_of_cof_succ` : cof t = succ ⇒ t[η] = fsD(t, η′) (both the predecessor)
- `omega_path` : cof t = ω ⇒ (∃ DiagAt) ∨ (∃ SuccAt)
- `IdxLB t k ζ`, `fs_le_fsD_of_idxLB` (cof not big), `EngLB c`, `evalFSNZ_of_engLB`, `surj_of_engLB`

WfCofL2.lean
- `HEngD`  : DiagAt a b μ tA, n ≥ 2 ⇒ fsD(tA, Y_n) ≤ val(A[n])
- `HRecD`  : DiagAt a b μ tA, n ≥ 2 ⇒ ψ_μ(b[Y_n]) ≤ Y_{n+1}
- `HCount` : no diagonal point ⇒ tA[k] ≤ val(A[k+2])
- `gam_le_Y` : γ_k ≤ Y_{k+2} by induction (base γ_0 = 0: this is where the shift 2 is spent)
- `evalFSNZ2_of_parts : Desc3 → HEngD → HRecD → HCount → EvalFSNZ 2`, `surj_of_parts`

WfCofL3.lean
- `HRecD ⇐ HRootD ∧ HShiftD ∧ HPathRD ∧ HCID` (`hRecD_of`)
  - `HShiftD` : o_{A[n+1]}(x) = o_{A[n]}(r)                 (copy shift)
  - `HPathRD` : fsD(o_A(r), Y_n) ≤ o_{A[n]}(r)              (path relation at r, lower half)
  - `HCID`    : o_A(r) = ψ_μ(b)                             (the diagonal node of tA is the bad root's value)
  - `HRootD`  : the bad root exists
- `evalFSNZ2_of_path`

WfCofL4.lean
- `HCount ⇐ Desc3 ∧ HNotSucc ∧ HCountS` (`hCount_of`)
  - `HNotSucc` : nonzero last column ⇒ cof tA ≠ succ
  - `HCountS`  : SuccAt a b tA ⇒ fsD(tA, k) = frame(ψ_a(init b) · k) ≤ val(A[k+2])
- `evalFSNZ2_of_facts : Desc3 → HEngD → HRootD → HShiftD → HPathRD → HCID → HNotSucc → HCountS → EvalFSNZ 2`
- (first version had HCBase + HCRec "one more copy adds one summand"; HCRec is FALSE, see below; removed)

## Measurements

probe.py (std_a, 3000): the path kind of tA is determined by the type t of the last column:
t = 1 ⇔ DiagAt (μ = level of the diagonal node), t ∈ {0, 2} ⇔ SuccAt. No other kind (never `none`).
Python note: `Ev.o` is not normalized; Lean's ρ.o is `sf`'d, so compare `sf(o)` (raw o gave false failures).

probe2.py, all 73 files (handoff sets, the families of WfCof/files.txt, graftF, desc1, graftE; CAP 3000, n = 2..4):

    diagonal type (t = 1): 84,150 matrices, 252,450 pairs (A, n)
      E    fsD(tA, Y_n) ≤ val(A[n])            252,450 / 252,450   (HEngD)
      S    γ_{n−2} ≤ Y_n                        252,450 / 252,450
      R1   ψ_μ(b[Y_n]) ≤ Y_{n+1}                252,450 / 252,450   (HRecD), and it is an equality (R1eq)
      SH   Y_{n+1} = o_{A[n]}(r)                252,450 / 252,450   (HShiftD; also at n = 1)
      CH   Y_{n+1} = fsD(o_A(r), Y_n)           252,450 / 252,450   (HPathRD, as an equality)
      CI   o_A(r) = ψ_μ(b)                       84,150 /  84,150   (HCID)
      R1b  the recurrence at n = 1 is false in all 84,150 (seed lag: Y_2 = o_{A[1]}(r) has no upgrader),
           and γ_1 ≤ Y_2 fails in 47,540 — so the base of the induction must be at n = 2, γ_0 = 0.
    counting type (t = 0, 2): C0 = HCount 278,271 / 278,271.

probe3.py, all 73 files (counting type; m_n = max m ≤ 14 with fsD(tA, m) ≤ val(A[n]), n = 1..5):

    t = 0: 39,052 matrices, t = 2: 53,705; never a `none` path (so HNotSucc holds on all of them)
      C0   m_n ≥ n − 2 (= HCountS)           278,271 / 278,271
      BASE m_2 ≥ 0                             92,757 / 92,757
      REC  m_{n+1} ≥ m_n + 1 (n ≥ 2)          FALSE: t = 2, 70 pairs (WfAbsW graft36b/c, graftD, graftM36, g36_2);
           by n (NMAX 4 rerun of graft36b/c): n = 2: 39 + 21, n = 3: 5 + 1, n = 4: 0.
           Example (one of these families, n = 2): SuccAt at ψ_0(1) deep inside (index ψ(1) + ω); m_n = 2, 2, 2, 3, 4, 5 for n = 1..6:
           for small n the value is decided by a larger branch outside the hole, the hole count is n − 1 only later.
      REC1 (n = 1) false in 6,442.
    So the counting part is left as HCountS (direct), not as a per-copy recurrence.

## Graft attack (graftG.py → graftG.pkl, 56,699 matrices)

Seeds (30 each, smallest of std_a / ext1 / WfAbsW graft36c): diagonal type with γ_1 > Y_2 (tight seed), diagonal type
with fsD(tA, Y_2) < val(A[2]) (strict engine bound), counting type with m_2 = 0; their A[2], A[3], prefixes;
WfCof graftF generator (gen 1 + 300-sample gen 2, bms -s = 1, < SRO). Random 8,000 measured (n = 2..4):
diagonal type 2,217 matrices / 6,651 pairs: E, S, R1 (= equality), SH, CH, CI all 0 failures;
counting type 1,606 matrices: C0 (HCountS) 4,818 / 4,818 (here REC also holds; its failures are in WfAbsW graft36b/c).

## Next

- Engine side: HEngD and HPathRD are the lower halves of the uniform path relation o_{A[n]}(h) = fsD(o_A(h), Y)
  (desc.md) at h = root and h = r; (E3) of WfQnE gives the lower half off the q = r bad shape.
  HShiftD is structural (the columns from x on in A[n+1] are the columns from r on in A[n], shifted in row 0).
  HCID: the Ω_{μ+1} of tA is the hole of the last column.
- HCountS: needs the position of the hole copies (n − 1 copies of ψ_a(init b) appear only for larger n); a per-copy recurrence on the max count is false.
