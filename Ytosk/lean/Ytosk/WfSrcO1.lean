/-
**The shared next-column case of `WfSrcA.SrcARem2` (B) and `WfSrcB.SrcBNonlost2` (O′)** (2026-10-31, WfSrcO).

Setting: a changing bump grandchild `c` of `i` (`m = P0 i`), not above `x − 1`. The change of `c` enters through the
next column `c′` after the subtree of `c` (`ICC`): `upg(c′ − 1) = c′`, `ChgX M x false c′`, and its row-0 parent
`q = P1(c′ − 1)` is a strict ancestor of `m`.

This file follows the change of `c′` to the right (`chain_term`). `e2 c′ = 1`, so of the rules that make `v(c′)` change
only two are possible: `snb` (`x` is a bump child of `c′`) and `vbump` (a child `k` of a bump child of `c′` changes);
`supg`・`vupg` need `e2 c′ ≠ 1`, and `vpar` contradicts `TopC M x q` (`c′` is a row-1 child of `q`). In `vbump`, either
`k` reaches `x` (`k = x` or `k` above `x − 1`), or `ICC` at `k` gives the next upgrade target `c₂ > c′` whose row-0
parent is again a strict ancestor of `c′` (it cannot be the bump child or `c′`: row 2), so of `m`. Induction on
`x − c′` ends in the terminal shape `Term`: an upgrade target `c*` after `c`, child of a strict ancestor of `m`,
with `x` a bump child of `c*`, or `x` or an ancestor of `x − 1` a child of a bump child of `c*`.

In case (b) (`P0 x = x − 1`, `Bad2`) the first two terminal forms are impossible (row 2 of `x − 1`): `TermB`.

The case is **not** structurally impossible: the standard 7-column matrix
`(0,0,0)(1,1,1)(2,2,1)(3,2,1)(4,1,0)(1,1,1)(2,1,1)` has it (`i = 2`, `m = 1`, `c = 4`, `c′ = 5`, `q = 0`), and the
41-column standard matrix of tmp/wf/WfSrcO/notes.md has it in the structural (b) frame with `upg(x − 1)` and
`P0(x − 1)` a bump child (only the value part of `Bad2` fails). So the narrowed residuals still need values.

Bridges: `srcARem2_of_3 : SrcARem3 → WfSrcA.SrcARem2`, `srcBNonlost2_of_3 : SrcBNonlost3 → WfSrcB.SrcBNonlost2`,
and `t2AbsNSrcW_of3` (the splice of `WfSrcABC.t2AbsNSrcW_of`).
-/
import Ytosk.WfSrcABC

namespace Ytosk.WfSrcO

open T

set_option linter.unusedSectionVars false

/-- **The terminal shape** of the change chain: an upgrade target `cs > c0` whose `v` changes, a row-0 child of a
strict ancestor `qs` of `m` (`qs = P1(cs − 1)`), with `x` a bump child of `cs`, or `x` or an ancestor of `x − 1` a
child of a bump child of `cs`. -/
def Term (M : Mat) (x m c0 : Nat) : Prop :=
  ∃ cs qs, c0 < cs ∧ cs < x ∧ upg M (cs - 1) = some cs ∧ ChgX M x false cs ∧
    par M 0 cs = some qs ∧ par M 1 (cs - 1) = some qs ∧ Anc0 M qs m ∧ qs ≠ m ∧
    ((x ∈ children M cs ∧ col M x = bump M cs) ∨
      ∃ j k, j ∈ children M cs ∧ col M j = bump M cs ∧ k ∈ children M j ∧ (k = x ∨ Anc0 M k (x - 1)))

/-- **The terminal shape in case (b)**: only the ancestor-of-`x − 1` form. -/
def TermB (M : Mat) (x m c0 : Nat) : Prop :=
  ∃ cs qs, c0 < cs ∧ cs < x ∧ upg M (cs - 1) = some cs ∧ ChgX M x false cs ∧
    par M 0 cs = some qs ∧ par M 1 (cs - 1) = some qs ∧ Anc0 M qs m ∧ qs ≠ m ∧
    ∃ j k, j ∈ children M cs ∧ col M j = bump M cs ∧ k ∈ children M j ∧ Anc0 M k (x - 1)

/-- The row-0 parent of an upgrade target is the row-1 parent of the upgraded column. -/
theorem par0_of_upg_target {M : Mat} (S : SInv M) {c' q : Nat} (_hc'N : c' < M.length)
    (hq1 : par M 1 (c' - 1) = some q) (hq2 : par M 1 c' = some q)
    (hcol : col M c' = (entry M 0 q + 1, entry M 1 (c' - 1), entry M 2 q + 1)) :
    par M 0 c' = some q := by
  have he0 : entry M 0 c' = entry M 0 q + 1 := by
    have : entry M 0 c' = (col M c').1 := rfl
    rw [this, hcol]
  have hqc := par_lt M 1 _ _ hq2
  obtain ⟨hh, hph⟩ := par0_some_of (M := M) hqc (by omega)
  have hR := S.r0p c' hh hph
  have hhc := par_lt M 0 c' hh hph
  have hq1lt := par_lt M 1 _ _ hq1
  have hAh : Anc0 M hh (c' - 1) :=
    anc_between (Anc0.step hph (Anc0.refl hh)) (c' - 1) (by omega) (by omega)
  have hAq : Anc0 M q (c' - 1) := anc0_of_par M 1 q (c' - 1) hq1
  have hhq : hh = q := anc0_eq_of_e0 hAh hAq (by omega)
  rw [hph, hhq]

/-- Row 2 of an upgrade target is `1` and of the row-1 parent `0`. -/
theorem upg_target_rows {M : Mat} (S : SInv M) {c' q : Nat}
    (hcol : col M c' = (entry M 0 q + 1, entry M 1 (c' - 1), entry M 2 q + 1)) :
    entry M 2 c' = 1 ∧ entry M 2 q = 0 := by
  have h := e2_of_col hcol
  have := S.z2 c'
  omega

/-- **The change chain** (induction on `x − c′`). -/
theorem chain_term {M : Mat} (S : SInv M) {x : Nat} (hx : x + 1 = M.length) {m : Nat} :
    ∀ n c', x - c' ≤ n → c' < x → upg M (c' - 1) = some c' → ChgX M x false c' →
      ∀ q, par M 0 c' = some q → par M 1 (c' - 1) = some q → Anc0 M q m → q ≠ m →
      ∀ c0, c0 < c' → Term M x m c0 := by
  intro n
  induction n with
  | zero => intro c' hn hc'x; omega
  | succ n ih =>
    intro c' hn hc'x hup hchg q hq0 hq1 hqm hqne c0 hc0
    obtain ⟨q', hq'1, hq'2, hcol, _⟩ := upg_spec hup
    have hqq : q' = q := by rw [hq1] at hq'1; exact (Option.some.inj hq'1).symm
    subst hqq
    obtain ⟨he2c, he2q⟩ := upg_target_rows S hcol
    have hqlt := par_lt M 0 c' q' hq0
    have hqm' : q' < m := by have := hqm.le; omega
    cases hchg with
    | supg hne =>
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hne
      exact absurd he2c (upg_e12 hk).2
    | snb h1 h2 hxi hxb =>
      exact ⟨c', q', hc0, hc'x, hup, ChgX.snb h1 h2 hxi hxb, hq0, hq1, hqm, hqne, Or.inl ⟨hxi, hxb⟩⟩
    | vpar h1 hp hm2 =>
      rw [hq'2] at hp
      cases hp
      have hT := (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hm2).1 rfl (by omega)
      exact absurd hq'2 (hT.2.2 c' hc'x)
    | vupg h1 h2 hu hk => omega
    | @vbump _ j k h1 h2 hj hjb hk hck =>
      have hchg' : ChgX M x false c' := ChgX.vbump h1 h2 hj hjb hk hck
      have hkN := (mem_children hk).2
      have hjk := (mem_children hk).1
      have hc'j := (mem_children hj).1
      have hpk : par M 0 k = some j := (mem_children_iff.mp hk).2
      have hpj : par M 0 j = some c' := (mem_children_iff.mp hj).2
      by_cases hkx : k = x
      · exact ⟨c', q', hc0, hc'x, hup, hchg', hq0, hq1, hqm, hqne, Or.inr ⟨j, k, hj, hjb, hk, Or.inl hkx⟩⟩
      by_cases hA : Anc0 M k (x - 1)
      · exact ⟨c', q', hc0, hc'x, hup, hchg', hq0, hq1, hqm, hqne, Or.inr ⟨j, k, hj, hjb, hk, Or.inr hA⟩⟩
      have hkx' : k < x := by omega
      obtain ⟨c2, hN2, hc2x, hup2, hchg2⟩ :=
        (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hck).2 k hkx' (Anc0.refl k) hA
      obtain ⟨q2, h21, h22, hcol2, _⟩ := upg_spec hup2
      have hkc2 := hN2.1
      have hph := par0_of_upg_target S (by omega) h21 h22 hcol2
      obtain ⟨_, he2q2⟩ := upg_target_rows S hcol2
      have hq2c2 := par_lt M 0 c2 q2 hph
      have hAh : Anc0 M q2 (c2 - 1) := anc0_of_par M 1 q2 (c2 - 1) h21
      have hAk : Anc0 M k (c2 - 1) := hN2.2.1 (c2 - 1) (by omega) (by omega)
      have hq2k : Anc0 M q2 k ∧ q2 ≠ k := by
        rcases anc0_total hAh hAk with h | h
        · refine ⟨h, ?_⟩
          intro he
          subst he
          exact hN2.2.2 (Anc0.step hph (Anc0.refl _))
        · exact absurd (Anc0.step hph h) hN2.2.2
      have hq2j := anc0_par hq2k.1 hq2k.2 hpk
      have hje2 : entry M 2 j = 1 := e2_of_col hjb
      have hq2nj : q2 ≠ j := by intro he; rw [he] at he2q2; omega
      have hq2c' := anc0_par hq2j hq2nj hpj
      have hq2nc' : q2 ≠ c' := by intro he; rw [he] at he2q2; omega
      have hq2q := anc0_par hq2c' hq2nc' hq0
      have hq2m : Anc0 M q2 m := hq2q.trans hqm
      have hq2ne : q2 ≠ m := by have := hq2q.le; omega
      exact ih c2 (by omega) hc2x hup2 hchg2 q2 hph h21 hq2m hq2ne c0 (by omega)

/-- **The start of the chain**: a changing bump grandchild `c` off the path to `x − 1`, at or below `m`'s row,
gives the terminal shape. -/
theorem term_of_outside {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {x m i j c : Nat} (hx : x + 1 = M.length)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT)
    (hmi : par M 0 i = some m) (h2 : entry M 2 i ≠ 0)
    (hj : j ∈ children M i) (hb : col M j = bump M i) (hc : c ∈ children M j) (hcx : c < x)
    (hce : τ.o c ≠ ρ.o c) (hnA : ¬ Anc0 M c (x - 1)) (hrow : entry M 1 c ≤ entry M 1 m) :
    Term M x m c := by
  have hch : ChgX M x true c := by
    by_contra hn
    exact hce ((chg_off hx hC hG hT hRT c hcx).1 hn)
  obtain ⟨c', hN, hc'x, hup, hchg'⟩ :=
    (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hch).2 c hcx (Anc0.refl c) hnA
  obtain ⟨m', hm'1, hm'c, hcol, _⟩ := upg_spec hup
  have hcc' : c < c' := hN.1
  have hph := par0_of_upg_target S (by omega) hm'1 hm'c hcol
  obtain ⟨_, he2⟩ := upg_target_rows S hcol
  have hAc : Anc0 M c (c' - 1) := hN.2.1 (c' - 1) (by omega) (by omega)
  have hAm' : Anc0 M m' (c' - 1) := anc0_of_par M 1 m' (c' - 1) hm'1
  have hm'c : Anc0 M m' c ∧ m' ≠ c := by
    rcases anc0_total hAm' hAc with h | h
    · refine ⟨h, ?_⟩
      intro he
      subst he
      exact hN.2.2 (Anc0.step hph (Anc0.refl _))
    · exact absurd (Anc0.step hph h) hN.2.2
  have hpj : par M 0 j = some i := (mem_children_iff.mp hj).2
  have hpc : par M 0 c = some j := (mem_children_iff.mp hc).2
  have hAj : Anc0 M m' j := anc0_par hm'c.1 hm'c.2 hpc
  have hmj : m' ≠ j := by
    intro he
    rw [he, e2_of_col hb] at he2
    omega
  have hAi : Anc0 M m' i := anc0_par hAj hmj hpj
  have hmi' : m' ≠ i := by
    intro he
    rw [he] at he2
    exact h2 he2
  have hAm : Anc0 M m' m := anc0_par hAi hmi' hmi
  have hme : m' ≠ m := by
    intro hme
    subst hme
    have h1 := par1_entry_lt hm'1
    have h2' := par1_between hm'1 c hAc (by have := hm'c.1.le; have := hm'c.2; omega)
    omega
  exact chain_term S hx (x - c') c' (le_refl _) hc'x hup hchg' m' hph hm'1 hAm hme c hcc'

/-- In case (b) under `Bad2`, the terminal shape is `TermB`. -/
theorem termB_of_term {M : Mat} (S : SInv M) {x m c0 : Nat} (hx : x + 1 = M.length)
    (hB : Bad2 M) (hp0 : par M 0 x = some (x - 1)) (h : Term M x m c0) : TermB M x m c0 := by
  obtain ⟨cs, qs, h0, hcx, hup, hch, hq0, hq1, hqm, hqne, hcase⟩ := h
  obtain ⟨⟨kb, hkb⟩, _⟩ := hB
  have hxm : M.length - 2 = x - 1 := by omega
  rw [hxm] at hkb
  have hx2 := (upg_e12 hkb).2
  obtain ⟨q', _, _, hcol, _⟩ := upg_spec hup
  have hcs2 : entry M 2 cs = 1 := by
    have h := e2_of_col hcol
    have := upg_target_e2 hup
    have := S.z2 cs
    omega
  refine ⟨cs, qs, h0, hcx, hup, hch, hq0, hq1, hqm, hqne, ?_⟩
  rcases hcase with ⟨hxi, _⟩ | ⟨j, k, hj, hjb, hk, hkx | hA⟩
  · have hp := (mem_children_iff.mp hxi).2
    rw [hp0] at hp
    cases hp
    exact absurd hcs2 hx2
  · subst hkx
    have hp := (mem_children_iff.mp hk).2
    rw [hp0] at hp
    cases hp
    exact absurd (e2_of_col hjb) hx2
  · exact ⟨j, k, hj, hjb, hk, hA⟩

/-- **Residual (a), narrowed**: `WfSrcA.SrcARem2` with shape (B) replaced by the terminal shape of its change chain. -/
def SrcARem3 : Prop :=
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
          (¬ Anc0 M c (r + L - 1) ∧ Term M (r + L) m c)) →
        ¬ WfT2Abs.DropFail M ρ τ (r + L) i

/-- **Bridge (a)**. -/
theorem srcARem2_of_3 (h : SrcARem3) : WfSrcA.SrcARem2 := by
  intro M ρ rk C hB2 hz hs r L hx hr ha τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcl hce
    hearly hrow hcase
  apply h M ρ rk C hB2 hz hs r L hx hr ha τ hT i m j c B K hi h1 h2 hmi hm1 hj hb hBj hK hcl hce
    hearly hrow
  by_cases hA : Anc0 M c (r + L - 1)
  · rcases hcase with hA' | ⟨c', q, hN, hc'x, _, _, _, _, _, _⟩
    · exact Or.inl hA'
    · exact absurd (anc_between hA c' (by have := hN.1; omega) (by omega)) hN.2.2
  · right
    refine ⟨hA, ?_⟩
    rcases hcase with ⟨hA', _⟩ | ⟨c', q, hN, hc'x, hup, hchg, hq0, hq1, hqm, hqne⟩
    · exact absurd hA' hA
    · exact chain_term C.S (x := r + L) (by omega) (r + L - c') c' (le_refl _) hc'x hup hchg q hq0 hq1
        hqm hqne c hN.1

/-- **Residual (b, non-lost), narrowed**: `WfSrcB.SrcBNonlost2` with the outside sub-case (O′) replaced by the
terminal shape `TermB` of its change chain. -/
def SrcBNonlost3 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → ∀ x, x + 1 = M.length →
    par M 2 x = some (x - 1) → par M 0 x = some (x - 1) → par M 1 x = some (x - 1) →
    ∀ τ, Cons (M.take x) τ → ∀ i m j c, i < x → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      par M 0 i = some m → par M 1 i = some m → j ∈ children M i → col M j = bump M i →
      c ∈ children M j → c < x - 1 → τ.o c ≠ ρ.o c →
      (∃ B, children (M.take x) i = B ++ [j] ∧
        ∀ d ∈ B, bumpTerm (M.take x) τ i d = bumpTerm M ρ i d) →
      (∃ K, children M j = K ++ [c] ∧ ∀ d ∈ K, τ.o d = ρ.o d ∧ entry M 1 d < entry M 1 m) →
      entry M 1 c ≤ entry M 1 m → (Anc0 M c (x - 1) → entry M 1 c < entry M 1 m) →
      (¬ Anc0 M c (x - 1) → TermB M x m c) →
      ¬ WfT2Abs.DropFail M ρ τ x i

/-- **Bridge (b)**. -/
theorem srcBNonlost2_of_3 (h : SrcBNonlost3) : WfSrcB.SrcBNonlost2 := by
  intro M ρ rk C hB x hx hr hp0 hp1 τ hT i m j c hi h1 h2 hmi hm1 hj hb hc hcx hce hBr hK hrow hdesc _
  have hRT : Rk (M.take x) rk := rk_take (by omega) C.I.rank
    (by have := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
        simpa only [show M.length - 1 = x from by omega] using this)
  refine h M ρ rk C hB x hx hr hp0 hp1 τ hT i m j c hi h1 h2 hmi hm1 hj hb hc hcx hce hBr hK hrow hdesc ?_
  intro hnA
  exact termB_of_term C.S hx hB hp0
    (term_of_outside C.S C.I.cons C.I.good hx hT hRT hmi h2 hj hb hc (by omega) hce hnA hrow)

/-- **Splice**: `WfT2Src.T2AbsNSrcW` from the narrowed (a), (b) and `WfSrcC.SrcCRes`. -/
theorem t2AbsNSrcW_of3 (hA : SrcARem3) (hB : SrcBNonlost3) (hC : WfSrcC.SrcCRes) :
    WfT2Src.T2AbsNSrcW :=
  WfSrcABC.t2AbsNSrcW_of (srcARem2_of_3 hA) (srcBNonlost2_of_3 hB) hC

end Ytosk.WfSrcO
