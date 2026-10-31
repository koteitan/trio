/-
**WfQrO1 (2026-11-01): a Bachmann-type lower bound for `DQ`, and the triggered-argument `o`-frame fields from it.**

`DQ η k t tN` changes `t` along one path (last summand -> argument or subscript -> ... -> one base node
`l -> fsD(l, η)`).  A term `p < t` stays below `tN` as soon as its comparison with `t` is decided off the path, or at the
base node below `fsD(l, η)`.  `DQG η k t tN tc` is `DQ` with a witness `tc < tN` (`DQG.lt`) that records this comparison:
- `mk`   : `t = B ++ l`, `tc = B ++ lc` (the comparison is decided inside `l`, or `p ≤ B`: then any `lc`);
- `mkQ`  : `tN = B ++ Q ++ lN`, `tc = B ++ Q ++ lc` (the comparison passes the re-exposed summands `Q`);
- `base` : `tc` is any `g < fsD(l, η)` (the comparison reaches the base; `g = 0` is the "cut": base summand deleted);
- `sub`  : `Ω_a -> Ω_{a_N}`, `tc = ψ_{a_c}(X) + R` (`a_c` from the subscript; any argument and tail);
- `arg`  : `ψ_a(b) -> ψ_a(b_N)`, `tc = ψ_a(b_c) + R`;
- `low`  : `ψ_a(b) -> ψ_a(b_N)`, `tc = ψ_{a'}(X) + R` with `a' < a` (decided at the subscript, off the path).
`above` : `p ≤ tc -> p < tN`.

Consumers (WfQrH3.OFields, triggered argument form `o(c) = ψ_s(y) -> ψ_s(y_N)`):
- TrigN from `PreG`: `∃ yc, DQG η true y y_N yc ∧ pre ≤ yc` (`trigN_of_G`).  Replaces the false `PreB` (`pre ≤ init y`
  is the special case `yc = init y ++ lc`).
- lNz from `η ≠ 0` and `last(y) ≠ 1` (`lNz_of`, via `fsD_ne_z_of_ne_one`).
- Last from `LastG`: `l = Ω_{s+1}` or `∃ lc, DQG η false l lN lc ∧ Ω_{s+1} ≤ lc ∧ lN single` (`last_of_G`).
`ofields_arg_of_G` assembles the triggered-argument conjunct of `OFields`.
-/
import Ytosk.WfQrH3
import Ytosk.WfQrH6

namespace Ytosk.WfQrO1
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL4 Ytosk.WfQrL11 Ytosk.WfQrL15 Ytosk.WfQrL16 Ytosk.WfQrH2 Ytosk.WfQrH3

/-- `DQ` with a lower witness `tc` (see the file header). -/
inductive DQG (η : T) : Bool → T → T → T → Prop
  | mk {B l lN lc Q s y : T} : l = psi s y z → DQG η false l lN lc →
      (∀ q ∈ summands Q, lN ≤ q ∧ q < l) → DQG η true (app B l) (app B (app Q lN)) (app B lc)
  | mkQ {B l lN lc Q s y : T} : l = psi s y z → DQG η false l lN lc →
      (∀ q ∈ summands Q, lN ≤ q ∧ q < l) → DQG η true (app B l) (app B (app Q lN)) (app B (app Q lc))
  | base {l g : T} : fsD l η < l → g < fsD l η → DQG η false l (fsD l η) g
  | sub {a aN ac X R : T} : DQG η true a aN ac → DQG η false (psi a z z) (psi aN z z) (psi ac X R)
  | arg {a b bN bc R : T} : DQG η true b bN bc → DQG η false (psi a b z) (psi a bN z) (psi a bc R)
  | low {a b bN bc a' X R : T} : DQG η true b bN bc → a' < a →
      DQG η false (psi a b z) (psi a bN z) (psi a' X R)

/-- `DQG` forgets to `DQ`. -/
theorem DQG.toDQ {η : T} : ∀ {k : Bool} {t tN tc : T}, DQG η k t tN tc → DQ η k t tN := by
  intro k t tN tc h
  induction h with
  | mk hl _ hQ ih => exact DQ.mk hl ih hQ
  | mkQ hl _ hQ ih => exact DQ.mk hl ih hQ
  | base h _ => exact DQ.base h
  | sub _ ih => exact DQ.sub ih
  | arg _ ih => exact DQ.arg ih
  | low _ _ ih => exact DQ.arg ih

/-- **The witness is below the new value.** -/
theorem DQG.lt {η : T} : ∀ {k : Bool} {t tN tc : T}, DQG η k t tN tc → tc < tN := by
  intro k t tN tc h
  induction h with
  | @mk B l lN lc Q s y _ _ hQ ih =>
    exact app_lt_app_left B (lt_of_lt_of_le ih (WfQrH6.le_app_Q (fun q hq => (hQ q hq).1)))
  | mkQ _ _ _ ih => exact app_lt_app_left _ (app_lt_app_left _ ih)
  | base _ hg => exact hg
  | sub _ ih => exact T.psi_lt_psi.mpr (Or.inl ih)
  | arg _ ih => exact T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, ih⟩))
  | low _ ha _ => exact T.psi_lt_psi.mpr (Or.inl ha)

/-- **Bachmann-type lower bound**: everything up to the witness stays below the new value. -/
theorem above {η : T} {k : Bool} {t tN tc p : T} (h : DQG η k t tN tc) (hp : p ≤ tc) : p < tN :=
  lt_of_le_of_lt hp h.lt

/-- The cut (base summand deleted, `g = 0`) exists whenever the base value is not `0`; any `DQ` derivation lifts. -/
theorem DQ.toG {η : T} : ∀ {k : Bool} {t tN : T}, DQ η k t tN →
    (∀ l, fsD l η < l → fsD l η ≠ z) → ∃ tc, DQG η k t tN tc := by
  intro k t tN h hnz
  induction h with
  | mk hl _ hQ ih =>
    obtain ⟨lc, hlc⟩ := ih
    exact ⟨_, DQG.mk hl hlc hQ⟩
  | @base l hlt =>
    refine ⟨z, DQG.base hlt ?_⟩
    cases hf : fsD l η with
    | z => exact absurd hf (hnz l hlt)
    | psi a b c => exact T.z_lt_psi a b c
  | sub _ ih =>
    obtain ⟨ac, hac⟩ := ih
    exact ⟨_, DQG.sub (X := z) (R := z) hac⟩
  | arg _ ih =>
    obtain ⟨bc, hbc⟩ := ih
    exact ⟨_, DQG.arg (R := z) hbc⟩

/-- `fsD` of a single summand `≠ 1` at a nonzero index is nonzero. -/
theorem fsD_ne_z_of_ne_one {η s y : T} (hη : η ≠ z) (h1 : psi s y z ≠ one) : fsD (psi s y z) η ≠ z := by
  unfold fsD
  by_cases hy : y = z
  · subst hy
    by_cases hs : s = z
    · subst hs; exact absurd rfl h1
    · simp only [if_neg hs]
      by_cases ha : isSucc s = true
      · rw [if_pos ha]; exact hη
      · rw [if_neg ha]; exact fun h => T.noConfusion h
  · simp only [if_neg hy]
    split
    · cases hc : η with
      | z => exact absurd hc hη
      | psi a b c =>
        simp only [count, mulT]
        intro h
        have := (app_eq_z h).1
        exact T.noConfusion this
    · split <;> exact fun h => T.noConfusion h

/-- **TrigN from the witness** (`PreG`). -/
theorem trigN_of_G {η v pre s y yN yc : T} (ht : Trig v pre s y) (hG : DQG η true y yN yc) (hp : pre ≤ yc) :
    Trig v pre s yN := by
  have hlt : yc < yN := hG.lt
  refine ⟨above hG hp, ?_⟩
  have h2 : psi v z z < psi s y z := ht.2
  show psi v z z < psi s yN z
  rw [psi_lt_psi_z_iff] at h2 ⊢
  rcases h2 with h | ⟨rfl, -⟩
  · exact Or.inl h
  · refine Or.inr ⟨rfl, ?_⟩
    cases hN : yN with
    | z => rw [hN] at hlt; exact absurd hlt (T.not_lt_z _)
    | psi a b c => exact T.z_lt_psi a b c

/-- **lNz** from `η ≠ 0` and `last(y) ≠ 1`. -/
theorem lNz_of {η y : T} (hη : η ≠ z)
    (h1 : ∀ B l, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → l ≠ one) :
    ∀ B l lN Q, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → ∀ (yN : T), yN = app B (app Q lN) →
      DQ η false l lN → lN ≠ z := by
  intro B l lN Q hy hl yN _ hd
  obtain ⟨s0, y0, rfl⟩ := hl
  cases hd with
  | base _ => exact fsD_ne_z_of_ne_one hη (h1 B _ hy ⟨s0, y0, rfl⟩)
  | sub _ => exact fun h => T.noConfusion h
  | arg _ => exact fun h => T.noConfusion h

/-- **Last from the witness** (`LastG`). -/
theorem last_of_G {η l lN θ : T}
    (h : l = θ ∨ ∃ lc, DQG η false l lN lc ∧ θ ≤ lc ∧ ∃ a b, lN = psi a b z) :
    l = θ ∨ (¬ lN < θ ∧ ∀ q ∈ summands lN, ¬ q < θ) := by
  rcases h with h | ⟨lc, hG, hθ, a, b, rfl⟩
  · exact Or.inl h
  · have hlt : θ < psi a b z := lt_of_le_of_lt hθ hG.lt
    have hn : ¬ psi a b z < θ := fun h' => lt_irrefl' _ (T.lt_trans' h' hlt)
    refine Or.inr ⟨hn, ?_⟩
    intro q hq
    simp only [summands, List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [hq]; exact hn

/-- The fields `OG` of a triggered argument frame, in the witness form. -/
def OG (v pre s y yN η : T) : Prop :=
  Trig v pre s y →
    (∃ yc, DQG η true y yN yc ∧ pre ≤ yc) ∧
    (∀ B l, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → l ≠ one) ∧
    (∀ B l lN Q, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → yN = app B (app Q lN) → DQ η false l lN →
      (split y (psi (succ s) z z)).2 = z →
      l = psi (succ s) z z ∨ ∃ lc, DQG η false l lN lc ∧ psi (succ s) z z ≤ lc ∧ ∃ a b, lN = psi a b z)

/-- **The triggered-argument conjunct of `OFields` from `OG` and `η ≠ 0`.** -/
theorem ofields_arg_of_G {v pre oc oN η : T} (hη : η ≠ z)
    (hG : ∀ s y yN, oc = psi s y z → oN = psi s yN z → DQ η true y yN → OG v pre s y yN η) :
    ∀ s y yN, oc = psi s y z → oN = psi s yN z → DQ η true y yN → Trig v pre s y →
    Trig v pre s yN ∧
    (∀ B l lN Q, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → yN = app B (app Q lN) → DQ η false l lN → lN ≠ z) ∧
    (∀ B l lN Q, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → yN = app B (app Q lN) → DQ η false l lN →
      (split y (psi (succ s) z z)).2 = z →
      l = psi (succ s) z z ∨ (¬ lN < psi (succ s) z z ∧ ∀ q ∈ summands lN, ¬ q < psi (succ s) z z)) := by
  intro s y yN hoc hoN hd ht
  obtain ⟨⟨yc, hyc, hp⟩, h1, hL⟩ := hG s y yN hoc hoN hd ht
  refine ⟨trigN_of_G ht hyc hp, ?_, ?_⟩
  · intro B l lN Q hy hl hyN hdl
    exact lNz_of hη h1 B l lN Q hy hl yN hyN hdl
  · intro B l lN Q hy hl hyN hdl hlo
    exact last_of_G (hL B l lN Q hy hl hyN hdl hlo)

end Ytosk.WfQrO1
