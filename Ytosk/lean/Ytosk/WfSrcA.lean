/-
**Part (a) of `WfT2Src.T2AbsNSrcW` (2026-10-31, WfSrcA).**

Case (a): `P0 x ≠ x − 1 ∨ P1 x ≠ x − 1`. A failed drop absorption at `i` gives (proved,
`T2SrcQuiet.failed_drop_branch`) `m = P0 i = P1 i`, the last changing bump branch `j` and its last
child `c` with `τ.o c ≠ ρ.o c`. Proved cases:
- `c = x − 1` (lost grandchild): `T2SrcReturn.not_dropFail_of_lost_grandchild`.
- `e1 c > e1 m`: excluded by `failed_drop_grandchild_row_le`.
- an earlier child of `j` at or above `m`'s row: excluded by `failed_drop_earlier_row_lt`.
- `e1 c = e1 m` and the next column `c + 1` inside `m`'s subtree: `nonlost_return_value` gives
  `τ.v c = ρ.v m`, and `not_dropFail_of_parent_le_child` closes it.

Residual `SrcARem` (the two general subcases (i), (ii) of the codex handoff): in the remaining
shape (not `e1 c = e1 m ∧ e0 m < e0 (c + 1)`) the drop absorption does not fail. It follows from the
structural `SrcAShape` (the remaining shape does not occur), `srcARem_of_shape`.
Measured (tmp/wf/WfSrcA/notes.md): no exception; it is false without the Bad2 (a) frame
(non-frame counterexample in std_a), so the frame premises are necessary.

Narrowed (`SrcARem2`, `srcARem_of_rem2` via `caseB_next`): the remaining shape is
(A) `c` an ancestor of `x − 1` with `e1 c < e1 m`, or (B) the change enters through the next column
`c′` after `c`'s subtree (`upg(c′ − 1) = c′`) whose row-0 parent `q = P1(c′ − 1)` is a strict
ancestor of `m` (`q = m` is impossible: it would give `e1 c > e1 m`).

`t2AbsNSrcW_of_rem2 : SrcARem2 → T2AbsNSrcWBC → WfT2Src.T2AbsNSrcW`.
`t2AbsNSrcW_of`: `SrcARem → T2AbsNSrcWBC → WfT2Src.T2AbsNSrcW`, where `T2AbsNSrcWBC` is
`T2AbsNSrcW` restricted to `P0 x = P1 x = x − 1` (parts (b) and (c)).
-/
import Ytosk.V3T2SrcReturn

namespace Ytosk.WfSrcA

open T

set_option linter.unusedSectionVars false

/-- A row-2 parent exists only for a column with row 2 nonzero. -/
theorem par2_entry_lt {M : Mat} {x r : Nat} (hr : par M 2 x = some r) : entry M 2 r < entry M 2 x := by
  have hr' : climb (par M 1) (fun q => decide (entry M 2 q < entry M 2 x)) (x + 1) (par M 1 x) =
      some r := hr
  cases hq : par M 1 x with
  | none => rw [hq] at hr'; simp [climb_none] at hr'
  | some q0 =>
    rw [hq] at hr'
    have hq0 := par_lt M 1 x q0 hq
    have := (climb_chain_iff (par M 1) _ (par_lt M 1) r (x + 1) q0 (by omega)).mp hr'
    simpa using this.2.1

/-- **Residual (cases (i) and (ii))**: at a Bad2 (a) frame, the last child `c < x − 1` of the last
bump branch `j` of `i`, whose `o` changes, with every earlier child of `j` below `m`'s row and
`e1 c ≤ e1 m`, is a return at `m`'s row whose next column stays in `m`'s subtree. -/
def SrcAShape : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      (par M 0 (r + L) ≠ some (r + L - 1) ∨ par M 1 (r + L) ≠ some (r + L - 1)) →
      ∀ τ, Cons (M.take (r + L)) τ →
      ∀ i m j c (B K : List Nat), i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        par M 0 i = some m → par M 1 i = some m →
        j ∈ children M i → col M j = bump M i → children (M.take (r + L)) i = B ++ [j] →
        children M j = K ++ [c] → c < r + L - 1 → τ.o c ≠ ρ.o c →
        (∀ d ∈ K, entry M 1 d < entry M 1 m) → entry M 1 c ≤ entry M 1 m →
        entry M 1 c = entry M 1 m ∧ entry M 0 m < entry M 0 (c + 1)

/-- **Case (B)**: a changing bump grandchild `c` off the path to `x − 1`, at or below `m`'s row.
The change enters through the next column `c′` after the subtree of `c` (ICC), an upgrade target of
`c′ − 1`, whose row-0 parent `q = P1(c′ − 1)` is a strict ancestor of `m`. The case `q = m` would put
`c` above `m`'s row, and `q` cannot be `c`, a column below `c`, `j` or `i`. -/
theorem caseB_next {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ)
    (hG : Good3 M ρ) {x i m j c : Nat} (hx : x + 1 = M.length)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT)
    (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) {B K : List Nat} (hBj : children (M.take x) i = B ++ [j])
    (hK : children M j = K ++ [c]) (hcx : c < x) (hce : τ.o c ≠ ρ.o c)
    (hnA : ¬ Anc0 M c (x - 1)) (hrow : entry M 1 c ≤ entry M 1 m) :
    ∃ c' q, NextC M c c' ∧ c' < x ∧ upg M (c' - 1) = some c' ∧ ChgX M x false c' ∧
      par M 0 c' = some q ∧ par M 1 (c' - 1) = some q ∧ Anc0 M q m ∧ q ≠ m := by
  have hch : ChgX M x true c := by
    by_contra hn
    exact hce ((chg_off hx hC hG hT hRT c hcx).1 hn)
  obtain ⟨c', ⟨hcc', hall', hnot'⟩, hc'x, hup', hchg'⟩ :=
    (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hch).2 c hcx (Anc0.refl c) hnA
  have hc1 : Anc0 M c (c' - 1) := hall' (c' - 1) (by omega) (by omega)
  obtain ⟨q, hq1, hq2, hcol, _⟩ := upg_spec hup'
  have he0 : entry M 0 c' = entry M 0 q + 1 := by
    have : entry M 0 c' = (col M c').1 := rfl
    rw [this, hcol]
  have hqc := par_lt M 1 _ _ hq2
  obtain ⟨hh, hph⟩ := par0_some_of (M := M) hqc (by omega)
  have hR := S.r0p c' hh hph
  have hhc := par_lt M 0 c' hh hph
  have hAh : Anc0 M hh (c' - 1) :=
    anc_between (Anc0.step hph (Anc0.refl hh)) (c' - 1) (by omega) (by omega)
  have hAq : Anc0 M q (c' - 1) := anc0_of_par M 1 q (c' - 1) hq1
  have hhq : hh = q := anc0_eq_of_e0 hAh hAq (by omega)
  subst hhq
  have hc'N : c' < M.length := by omega
  have hjc : par M 0 c = some j := (mem_children_iff.mp (by rw [hK]; simp : c ∈ children M j)).2
  have hij : par M 0 j = some i := (mem_children_iff.mp hj).2
  have hjx : j < x := by have := par_lt M 0 c j hjc; omega
  rcases anc0_total hAh hc1 with hqc' | hcq
  · -- `q` is a strict ancestor of `c`
    have hqne : hh ≠ c := by
      intro he; subst he; exact hnot' (Anc0.step hph (Anc0.refl _))
    have hqj := anc0_par hqc' hqne hjc
    have hqnj : hh ≠ j := by
      intro he; subst he
      have hmem : c' ∈ children M hh := mem_children_iff.mpr ⟨hc'N, hph⟩
      rw [hK] at hmem
      rcases List.mem_append.mp hmem with hk | hk
      · have hs := children_sorted M hh
        rw [hK] at hs
        have := (List.pairwise_append.mp hs).2.2 c' hk c (by simp)
        omega
      · simp at hk; omega
    have hqi := anc0_par hqj hqnj hij
    have hqni : hh ≠ i := by
      intro he; subst he
      have hmem : c' ∈ children (M.take x) hh := mem_take_children (mem_children_iff.mpr ⟨hc'N, hph⟩) hc'x
      rw [hBj] at hmem
      rcases List.mem_append.mp hmem with hk | hk
      · have hs := children_sorted (M.take x) hh
        rw [hBj] at hs
        have h1 := (List.pairwise_append.mp hs).2.2 c' hk j (by simp)
        have h2 := par_lt M 0 c j hjc
        omega
      · simp at hk
        have h2 := par_lt M 0 c j hjc
        omega
    have hqm := anc0_par hqi hqni hmi
    refine ⟨c', hh, ⟨hcc', hall', hnot'⟩, hc'x, hup', hchg', hph, hq1, hqm, ?_⟩
    intro he; subst he
    -- `P1(c′ − 1) = m` puts `c` strictly above `m`'s row
    have hmc : hh < c := by
      have := par_lt M 0 c j hjc; have := par_lt M 0 j i hij; have := par_lt M 0 i hh hmi; omega
    have hb := par1_between hq1 c hc1 hmc
    have hl := par1_entry_lt hq1
    omega
  · exact absurd (Anc0.step hph hcq) hnot'

/-- **Residual, weaker form**: in the remaining shape (not a return at `m`'s row with the next column
inside `m`'s subtree) the drop absorption does not fail. Implied by `SrcAShape` (`srcARem_of_shape`). -/
def SrcARem : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      (par M 0 (r + L) ≠ some (r + L - 1) ∨ par M 1 (r + L) ≠ some (r + L - 1)) →
      ∀ τ, Cons (M.take (r + L)) τ →
      ∀ i m j c (B K : List Nat), i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        par M 0 i = some m → par M 1 i = some m →
        j ∈ children M i → col M j = bump M i → children (M.take (r + L)) i = B ++ [j] →
        children M j = K ++ [c] → c < r + L - 1 → τ.o c ≠ ρ.o c →
        (∀ d ∈ K, entry M 1 d < entry M 1 m) → entry M 1 c ≤ entry M 1 m →
        ¬ (entry M 1 c = entry M 1 m ∧ entry M 0 m < entry M 0 (c + 1)) →
        ¬ WfT2Abs.DropFail M ρ τ (r + L) i

theorem srcARem_of_shape (hS : SrcAShape) : SrcARem := by
  intro M ρ rk C hB2 hz hs r L hx hr ha τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcl hce
    hearly hrow hn
  exact absurd (hS M ρ rk C hB2 hz hs r L hx hr ha τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK
    hcl hce hearly hrow) hn

/-- **Residual, narrowed**: `SrcARem` with the two remaining shapes made explicit:
(A) `c` is an ancestor of `x − 1` strictly below `m`'s row, or
(B) the change enters through the next column `c′` after `c`'s subtree, an upgrade target whose
row-0 parent `q = P1(c′ − 1)` is a strict ancestor of `m`. -/
def SrcARem2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      (par M 0 (r + L) ≠ some (r + L - 1) ∨ par M 1 (r + L) ≠ some (r + L - 1)) →
      ∀ τ, Cons (M.take (r + L)) τ →
      ∀ i m j c (B K : List Nat), i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        par M 0 i = some m → par M 1 i = some m →
        j ∈ children M i → col M j = bump M i → children (M.take (r + L)) i = B ++ [j] →
        children M j = K ++ [c] → c < r + L - 1 → τ.o c ≠ ρ.o c →
        (∀ d ∈ K, entry M 1 d < entry M 1 m) → entry M 1 c ≤ entry M 1 m →
        ((Anc0 M c (r + L - 1) ∧ entry M 1 c < entry M 1 m) ∨
          ∃ c' q, NextC M c c' ∧ c' < r + L ∧ upg M (c' - 1) = some c' ∧ ChgX M (r + L) false c' ∧
            par M 0 c' = some q ∧ par M 1 (c' - 1) = some q ∧ Anc0 M q m ∧ q ≠ m) →
        ¬ WfT2Abs.DropFail M ρ τ (r + L) i

theorem srcARem_of_rem2 (h : SrcARem2) : SrcARem := by
  intro M ρ rk C hB2 hz hs r L hx hr ha τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcl hce
    hearly hrow hn
  apply h M ρ rk C hB2 hz hs r L hx hr ha τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcl hce
    hearly hrow
  have hRT : Rk (M.take (r + L)) rk := rk_take (by omega) C.I.rank
    (by have := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
        simpa only [show M.length - 1 = r + L from by omega] using this)
  by_cases hA : Anc0 M c (r + L - 1)
  · left
    refine ⟨hA, ?_⟩
    have hjc : par M 0 c = some j := (mem_children_iff.mp (by rw [hK]; simp : c ∈ children M j)).2
    have hij : par M 0 j = some i := (mem_children_iff.mp hj).2
    have hmc : Anc0 M m c := Anc0.step hjc (Anc0.step hij (Anc0.step hmi (Anc0.refl m)))
    have hmne : m ≠ c := by
      have := par_lt M 0 c j hjc; have := par_lt M 0 j i hij; have := par_lt M 0 i m hmi; omega
    have h0 := anc0_e0_lt hmc hmne
    have hc1 : Anc0 M c (c + 1) := anc_between hA (c + 1) (by omega) (by omega)
    have h0' := anc0_e0_lt hc1 (by omega)
    by_contra hge
    exact hn ⟨by omega, by omega⟩
  · right
    exact caseB_next C.S C.I.cons C.I.good (x := r + L) (by omega) hT hRT hmi hm1 hj hBj hK
      (by omega) hce hA hrow

/-- **Part (a)**: with `SrcARem`, the drop absorption does not fail in case (a). -/
theorem not_dropFail_of_case_a (hS : SrcARem) {M : Mat} {ρ τ : Valn}
    {rk : Bool → Nat → Nat} (C : StepCtxT2 M ρ rk) (hB2 : Bad2 M)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (hs : TRIO.srow M (M.length - 1) = 2)
    {r L i : Nat} (hx : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (ha : par M 0 (r + L) ≠ some (r + L - 1) ∨ par M 1 (r + L) ≠ some (r + L - 1))
    (hi : i < r + L) (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0)
    (hT : Cons (M.take (r + L)) τ) : ¬ WfT2Abs.DropFail M ρ τ (r + L) i := by
  intro hf
  have hx2 : entry M 2 (r + L) = 1 := by
    have := par2_entry_lt hr
    have := C.S.z2 (r + L)
    omega
  obtain ⟨m, j, c, K, B, hmi, hm1, hj, hb, hc, hcx, hce, hBj, _, hK, _, _⟩ :=
    T2SrcQuiet.failed_drop_branch C hx hr hi h1 h2 hT hf
  by_cases hcl : c = r + L - 1
  · subst hcl
    exact T2SrcReturn.not_dropFail_of_lost_grandchild C hB2 hx hr hx2 ha hi h1 h2 hT hj hb hc hf
  have hcl' : c < r + L - 1 := by omega
  obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
  have hGT : Good3 (M.take (r + L)) τ := by
    have he : M.length - 1 = r + L := by omega
    rw [← he] at hT ⊢
    exact good3_take_any (Inv3W.ofV2 C.S C.I) C.toW (by omega) hT
  have hRT : Rk (M.take (r + L)) rk := rk_take (by omega) C.I.rank
    (by have := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
        simpa only [show M.length - 1 = r + L from by omega] using this)
  have hrow := T2SrcQuiet.failed_drop_grandchild_row_le C.S C.I.cons C.I.good
    hx hT hRT hGT hmi hm1 hj hb hc hcx hf
  have hearly : ∀ d ∈ K, entry M 1 d < entry M 1 m := by
    intro d hd
    have hdj : d ∈ children M j := by rw [hK]; exact List.mem_append_left _ hd
    have hdc : d < c := by
      have hs := children_sorted M j
      rw [hK] at hs
      exact (List.pairwise_append.mp hs).2.2 d hd c (by simp)
    exact T2SrcQuiet.failed_drop_earlier_row_lt hX hJ C.I.cons C.I.good hx hT hRT hGT
      hmi hm1 hj hb hc hcx hdj hdc hf
  have hshape' : entry M 1 c = entry M 1 m ∧ entry M 0 m < entry M 0 (c + 1) := by
    by_contra hn
    exact hS M ρ rk C hB2 hz hs r L hx hr ha τ hT i m j c B K hi h1 h2 hmi hm1
      hj hb hBj hK hcl' hce hearly hrow hn hf
  obtain ⟨hc1, hnext⟩ := hshape'
  have hiN : i < M.length := by omega
  have hm2 : entry M 2 m = 0 := by
    by_contra hn
    exact no_par1_of_e2 C.S.z1c hiN (by have := C.S.z2 m; omega) hm1
  have hc2 := T2SrcQuiet.bump_grandchild_e2_zero hX hJ hj hb hc
  have hv := T2SrcPrefix.nonlost_return_value C.S C.I.cons C.I.good (x := r + L) (by omega) hT hRT
    hmi hm1 hj hb hc (by omega) hc1 hm2 hc2 hnext
  have hjx : j < r + L := Nat.lt_trans (mem_children hc).1 hcx
  have hjT : j ∈ children (M.take (r + L)) i := mem_take_children hj hjx
  have hbT : col (M.take (r + L)) j = bump (M.take (r + L)) i := by
    rw [col_take M hjx, bump_take M hi, hb]
  have hcT : c ∈ children (M.take (r + L)) j := mem_take_children hc hcx
  apply T2SrcPrefix.not_dropFail_of_parent_le_child C.I.good hi (by omega) hT hGT hjT hbT hcT _ hf
  rw [hm1, hv]
  exact le_refl _

/-- **Parts (b) and (c)**: `T2AbsNSrcW` restricted to `P0 x = P1 x = x − 1`. -/
def T2AbsNSrcWBC : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some (r + L - 1) → par M 1 (r + L) = some (r + L - 1) →
      ∀ τ, Cons (M.take (r + L)) τ →
      ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → WfT2Abs.DropFail M ρ τ (r + L) i →
        WfT2Src.SrcFacts M ρ τ (r + L) i →
        L = 1 ∧ (∃ p, par M 0 r = some p ∧ par M 0 p = some i) ∧
          ∀ s ∈ summands (vOpt ρ (par M 1 i)), ¬ s < psi z two z → s < bumpW M ρ i →
            ¬ Lhd z s (bumpW M ρ i) → s < WfT2Abs.Bnd (ρ.v r)

/-- **Bridge**: part (a) from `SrcARem`, parts (b), (c) from `T2AbsNSrcWBC`. -/
theorem t2AbsNSrcW_of (hS : SrcARem) (hBC : T2AbsNSrcWBC) : WfT2Src.T2AbsNSrcW := by
  intro M ρ rk C hB2 hz hs r L hlen hr τ hτ i hi h1 h2 hfail hfacts
  by_cases ha : par M 0 (r + L) ≠ some (r + L - 1) ∨ par M 1 (r + L) ≠ some (r + L - 1)
  · exact absurd hfail (not_dropFail_of_case_a hS C hB2 hz hs hlen hr ha hi h1 h2 hτ)
  · push Not at ha
    exact hBC M ρ rk C hB2 hz hs r L hlen hr ha.1 ha.2 τ hτ i hi h1 h2 hfail hfacts

/-- **Bridge with the narrowed residual** `SrcARem2`. -/
theorem t2AbsNSrcW_of_rem2 (hS : SrcARem2) (hBC : T2AbsNSrcWBC) : WfT2Src.T2AbsNSrcW :=
  t2AbsNSrcW_of (srcARem_of_rem2 hS) hBC

end Ytosk.WfSrcA
