/-
**`WfSrcR5.ATerm` and `WfSrcR5.BTerm` from the chain-above-`q` residual `TermHi` (2026-10-31, WfTerm).**

Setting (shared by `ATerm` and `BTerm`): `c` (a bump grandchild of `i`, `m = P0 i = P1 i`, off the path to `x − 1`)
changes in `M.take x`; its change enters through the next column `c′` after its subtree, `upg(c′ − 1) = c′`, and
`q = P1(c′ − 1) = P0 c′` is a strict ancestor of `m`.

Proved here (no new hypothesis):
- `q` lies on the row-1 chain of `m` and of `c` (`HiR`, `up1_of_hiR`).
- `v(q)` does not change in `M.take x` (`TopC` forbids the row-1 child `c′` of `q`).
- Hence every summand `s` of `v(m)` whose origin `b` (`s = bumpW(k)`, `upg b = k`, `b` on the row-1 chain of `m`)
  is at or below `q` satisfies `s ≤ v(b) ≤ v(q) = τ.v(q) ≤ τ.v(c) < τ.o(c) ≤ W_T(i)`: it is outside the window.

Residual `TermHi`: only the origins strictly above `q` on the chain.
Bridges: `aTerm_of : TermHi → WfSrcR5.ATerm`, `bTerm_of : TermHi → WfSrcR5.BTerm`.
-/
import Ytosk.WfSrcR5

namespace Ytosk.WfTerm

open T
open WfHUACDeep

set_option linter.unusedSectionVars false

/-- A row-1 chain from the row condition on the path. -/
theorem up1_of_hiR {M : Mat} {a : Nat} : ∀ x, Anc0 M a x → HiR M a x → Up1 M a x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hA hH
    by_cases hax : a = x
    · subst hax; exact Up1.refl _
    · have he : entry M 1 a < entry M 1 x := hH x hA (Anc0.refl x) (fun h => hax h.symm)
      obtain ⟨y, hy, hay, hAy⟩ := par1_near hA hax he
      have hyx := par_lt M 1 x y hy
      have hYX := anc0_of_par M 1 y x hy
      have hHy : HiR M a y := fun s h1 h2 hne => hH s h1 (h2.trans hYX) hne
      exact Up1.step hy (ih y hyx hAy hHy)

/-- The row-1 parent of a column below `c` is on the row-1 chain of `c`. -/
theorem hiR_of_par1 {M : Mat} {q e c : Nat} (hq : par M 1 e = some q) (hce : Anc0 M c e) :
    HiR M q c := by
  intro s h1 h2 hne
  have hse : Anc0 M s e := h2.trans hce
  have hqs : q < s := by have := h1.le; omega
  have h3 := par1_between hq s hse hqs
  have h4 := par1_entry_lt hq
  omega

theorem hiR_mono {M : Mat} {q m c : Nat} (h : HiR M q c) (hm : Anc0 M m c) : HiR M q m :=
  fun s h1 h2 hne => h s h1 (h2.trans hm) hne

theorem up1_take {M : Mat} {k a b : Nat} (h : Up1 M a b) (hb : b < k) : Up1 (M.take k) a b := by
  induction h with
  | refl => exact Up1.refl _
  | @step x y hp _ ih =>
    have hyx := par_lt M 1 x y hp
    exact Up1.step (by rw [par_take M 1 x hb]; exact hp) (ih (by omega))


theorem anc0_take {M : Mat} {k a b : Nat} (h : Anc0 M a b) (hb : b < k) : Anc0 (M.take k) a b := by
  induction h with
  | refl => exact Anc0.refl _
  | @step b c hp _ ih =>
    have hbc := par_lt M 0 c b hp
    exact Anc0.step (by rw [par_take M 0 c hb]; exact hp) (ih (by omega))

theorem anc0_of_take {M : Mat} {k a b : Nat} (h : Anc0 (M.take k) a b) (hb : b < k) : Anc0 M a b := by
  induction h with
  | refl => exact Anc0.refl _
  | @step b c hp _ ih =>
    have hbc := par_lt (M.take k) 0 c b hp
    rw [par_take M 0 c hb] at hp
    exact Anc0.step hp (ih (by omega))

theorem hiR_take {M : Mat} {k q c : Nat} (h : HiR M q c) (hc : c < k) : HiR (M.take k) q c := by
  intro s h1 h2 hne
  have hsc := h2.le
  have hqs := h1.le
  rw [entry_take M 1 (by omega), entry_take M 1 (by omega)]
  exact h s (anc0_of_take h1 (by omega)) (anc0_of_take h2 hc) hne

/-- **Residual**: the origins strictly above `q` on the row-1 chain of `m` whose index exceeds `v(q)` are not in the
failing window (origins with index `≤ v(q)` are below `τ.o(c)`, proved in `not_dropFail_of_hi`). -/
def TermHi : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → Bad2 M → ∀ x, x + 1 = M.length → (∃ r, par M 2 x = some r) →
    ∀ τ, Cons (M.take x) τ → ∀ i m j c, i < x → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      par M 0 i = some m → par M 1 i = some m → j ∈ children M i → col M j = bump M i →
      c ∈ children M j → c < x - 1 → τ.o c ≠ ρ.o c → entry M 1 c ≤ entry M 1 m →
      ¬ Anc0 M c (x - 1) → WfSrcO.Term M x m c →
      ∀ c' q, NextC M c c' → c' < x → upg M (c' - 1) = some c' → ChgX M x false c' →
        par M 0 c' = some q → par M 1 (c' - 1) = some q → Anc0 M q m → q ≠ m →
        ∀ b k, Up1 M q b → b ≠ q → Up1 M b m → upg M b = some k → ρ.v q < lev (bumpW M ρ k) →
          ¬ bumpW M ρ k < psi z two z → ¬ bumpW M ρ k < bumpW (M.take x) τ i →
          bumpW M ρ k < bumpW M ρ i → Lhd z (bumpW M ρ k) (bumpW M ρ i)

/-- **The common step**: no `DropFail` at `i` in the next-column frame, from `TermHi`. -/
theorem not_dropFail_of_hi (H : TermHi) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : Bad2 M) {x : Nat} (hx : x + 1 = M.length) (hr : ∃ r, par M 2 x = some r)
    {τ : Valn} (hT : Cons (M.take x) τ) {i m j c : Nat} (hi : i < x) (h1 : entry M 1 i ≠ 0)
    (h2 : entry M 2 i ≠ 0) (hmi : par M 0 i = some m) (hm1 : par M 1 i = some m)
    (hj : j ∈ children M i) (hb : col M j = bump M i) (hc : c ∈ children M j) (hcx : c < x - 1)
    (hce : τ.o c ≠ ρ.o c) (hrow : entry M 1 c ≤ entry M 1 m) (hnA : ¬ Anc0 M c (x - 1)) :
    ¬ WfT2Abs.DropFail M ρ τ x i := by
  classical
  have S := C.S
  have hRT : Rk (M.take x) rk := rk_take (by omega) C.I.rank
    (by have := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
        simpa only [show M.length - 1 = x from by omega] using this)
  have hGT : Good3 (M.take x) τ := by
    have he : M.length - 1 = x := by omega
    rw [← he] at hT ⊢
    exact good3_take_any (Inv3W.ofV2 C.S C.I) C.toW (by omega) hT
  have hTerm := WfSrcO.term_of_outside C.S C.I.cons C.I.good hx hT hRT hmi h2 hj hb hc (by omega) hce hnA hrow
  -- the first step of the change chain (as in `term_of_outside`)
  have hch : ChgX M x true c := by
    by_contra hn
    exact hce ((chg_off hx C.I.cons C.I.good hT hRT c (by omega)).1 hn)
  obtain ⟨c', hN, hc'x, hup, hchg'⟩ :=
    (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hch).2 c (by omega) (Anc0.refl c) hnA
  obtain ⟨q, hq1, hqc', hcol, _⟩ := upg_spec hup
  have hcc' : c < c' := hN.1
  have hph := WfSrcO.par0_of_upg_target S (by omega) hq1 hqc' hcol
  obtain ⟨_, he2⟩ := WfSrcO.upg_target_rows S hcol
  have hAc : Anc0 M c (c' - 1) := hN.2.1 (c' - 1) (by omega) (by omega)
  have hAq : Anc0 M q (c' - 1) := anc0_of_par M 1 q (c' - 1) hq1
  have hqc : Anc0 M q c ∧ q ≠ c := by
    rcases anc0_total hAq hAc with h | h
    · refine ⟨h, ?_⟩
      intro he
      subst he
      exact hN.2.2 (Anc0.step hph (Anc0.refl _))
    · exact absurd (Anc0.step hph h) hN.2.2
  have hpj : par M 0 j = some i := (mem_children_iff.mp hj).2
  have hpc : par M 0 c = some j := (mem_children_iff.mp hc).2
  have hAj : Anc0 M q j := anc0_par hqc.1 hqc.2 hpc
  have hqj : q ≠ j := by
    intro he
    rw [he, e2_of_col hb] at he2
    omega
  have hAi : Anc0 M q i := anc0_par hAj hqj hpj
  have hqi : q ≠ i := by
    intro he
    rw [he] at he2
    exact h2 he2
  have hAm : Anc0 M q m := anc0_par hAi hqi hmi
  have hme : q ≠ m := by
    intro hme
    subst hme
    have h1' := par1_entry_lt hq1
    have h2' := par1_between hq1 c hAc (by have := hqc.1.le; have := hqc.2; omega)
    omega
  -- `q` is on the row-1 chains of `c` and `m`
  have hHc : HiR M q c := hiR_of_par1 hq1 hAc
  have hmc : Anc0 M m c :=
    (anc0_of_par M 0 m i hmi).trans ((anc0_of_par M 0 i j hpj).trans (anc0_of_par M 0 j c hpc))
  have hUm : Up1 M q m := up1_of_hiR m hAm (hiR_mono hHc hmc)
  have hUc : Up1 M q c := up1_of_hiR c hqc.1 hHc
  -- `v(q)` does not change
  have hqx : q < x := by have := par_lt M 1 _ _ hq1; omega
  have hvq : τ.v q = ρ.v q := by
    apply (chg_off hx C.I.cons C.I.good hT hRT q hqx).2
    intro hq
    have hTop := (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hq).1 rfl hqx
    exact hTop.2.2 (c' - 1) (by omega) hq1
  -- `v(q) < W_T(i)`
  have hjx : j < x := by have := (mem_children hc).1; omega
  have hcT : c < x := by omega
  have hjT : j ∈ children (M.take x) i := mem_take_children hj hjx
  have hbT : col (M.take x) j = bump (M.take x) i := by rw [col_take M hjx, bump_take M hi, hb]
  have hcTc : c ∈ children (M.take x) j := mem_take_children hc hcT
  have hlenT : (M.take x).length = x := by rw [List.length_take]; omega
  have hvqc : τ.v q ≤ τ.v c :=
    T2SrcReturn.chain_value_le hT hGT (up1_take hUc hcT) (by rw [hlenT]; exact hcT)
  have hvqcs : τ.v q < τ.v c :=
    v_chain_lt hT hGT hRT c (by have := hqc.1.le; have := hqc.2; omega) (by rw [hlenT]; exact hcT)
      (anc0_take hqc.1 hcT) (hiR_take hHc hcT)
  have hvco : τ.v c < τ.o c := by
    obtain ⟨y, hy⟩ := o_psi_sub hT (show c < (M.take x).length by rw [hlenT]; exact hcT)
    rw [hy, sf_ot (hGT.ot_v c (by rw [hlenT]; exact hcT))]
    exact sub_lt_psi _ _ _
  have hGo : ∀ t ∈ (children (M.take x) j).map τ.o, isOT t = true := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact hGT.ot_o d (mem_children hd).2
  have hoW : τ.o c ≤ bumpW (M.take x) τ i :=
    le_trans (T2SrcLeaf.mem_le_sumN hGo (List.mem_map.mpr ⟨c, hcTc, rfl⟩))
      (T2SrcLeaf.child_sum_le_bumpW hGT hjT hbT)
  have hqW : ρ.v q < bumpW (M.take x) τ i := by
    rw [← hvq]
    exact lt_of_le_of_lt hvqc (lt_of_lt_of_le hvco hoW)
  -- the failing summand
  intro hf
  apply hf
  intro s hs hs2 hnT hsM
  have hiN : i < M.length := by omega
  obtain ⟨b, k, hbm, hu, he⟩ := T2SrcOrigins.source_summand_origin S C.I.cons C.I.good hiN hm1 hs hs2
  change s = bumpW M ρ k at he
  subst he
  rcases T2SrcReturn.chain_comparable hbm hUm with hbq | hqb
  · -- the origin is at or below `q`: below `W_T(i)`
    exfalso
    apply hnT
    have hbN : b < M.length := by have := up1_le hbm; have := par_lt M 1 i m hm1; omega
    have hkb : bumpW M ρ k ≤ ρ.v b := by
      rw [HUACSupport.value_at_target S C.I.cons C.I.good hbN hu]
      exact le_add_single _ (omega_single _)
    have hbq' : ρ.v b ≤ ρ.v q :=
      T2SrcReturn.chain_value_le C.I.cons C.I.good hbq (by omega)
    exact lt_of_le_of_lt (le_trans hkb hbq') hqW
  · by_cases hbq : b = q
    · subst hbq
      exfalso
      apply hnT
      have hbN : b < M.length := by omega
      have hkb : bumpW M ρ k ≤ ρ.v b := by
        rw [HUACSupport.value_at_target S C.I.cons C.I.good hbN hu]
        exact le_add_single _ (omega_single _)
      exact lt_of_le_of_lt hkb hqW
    · by_cases hlev : lev (bumpW M ρ k) ≤ ρ.v q
      · -- index at most `v(q)`: below `τ.o(c)`
        exfalso
        apply hnT
        obtain ⟨s0, y0, hW0⟩ := omega_psi_form (sumN (one :: (children M k).map (bumpTerm M ρ k)))
        change bumpW M ρ k = psi s0 y0 z at hW0
        obtain ⟨y, hy⟩ := o_psi_sub hT (show c < (M.take x).length by rw [hlenT]; exact hcT)
        rw [sf_ot (hGT.ot_v c (by rw [hlenT]; exact hcT))] at hy
        have hs0 : s0 < τ.v c := by
          rw [hW0] at hlev
          exact lt_of_le_of_lt (hvq ▸ hlev) hvqcs
        have hlt : bumpW M ρ k < τ.o c := by
          rw [hW0, hy, T.psi_lt_psi]; exact Or.inl hs0
        exact lt_of_lt_of_le hlt hoW
      · exact H M ρ rk C hB x hx hr τ hT i m j c hi h1 h2 hmi hm1 hj hb hc hcx hce hrow hnA hTerm
          c' q hN hc'x hup hchg' hph hq1 hAm hme b k hqb hbq hbm hu
          (by rcases lt_or_ge (ρ.v q) (lev (bumpW M ρ k)) with h | h
              · exact h
              · exact absurd h hlev) hs2 hnT hsM

/-- **Bridge (a)**. -/
theorem aTerm_of (H : TermHi) : WfSrcR5.ATerm := by
  intro M ρ rk C hB _ _ r L hx hr _ τ hT i m j c B K hi h1 h2 hmi hm1 hj hb _ hK hcl hce _ hrow hnA _
  have hc : c ∈ children M j := by rw [hK]; simp
  exact not_dropFail_of_hi H C hB hx ⟨r, hr⟩ hT hi h1 h2 hmi hm1 hj hb hc hcl hce hrow hnA

/-- **Bridge (b)**. -/
theorem bTerm_of (H : TermHi) : WfSrcR5.BTerm := by
  intro M ρ rk C hB x hx hr _ _ τ hT i m j c hi h1 h2 hmi hm1 hj hb hc hcx hce _ _ hrow hnA _
  exact not_dropFail_of_hi H C hB hx ⟨x - 1, hr⟩ hT hi h1 h2 hmi hm1 hj hb hc hcx hce hrow hnA

end Ytosk.WfTerm
