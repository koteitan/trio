/-
**WfQrH2 (2026-11-01): the last-child `o` frame step reduced to two cases.**
`o(c) = ψ_s(y)`, `o_N(c) = oN` with `DQ η false (ψ_s(y)) oN`.  By the three constructors of `DQ`:
- `sub` (`y = 0`): no trigger in `M` nor in `M[n]` (`pre < 0` is false) -> add shape, no hypothesis;
- `arg` (`oN = ψ_s(y_N)`, `y_N = DQ(y)`) without a trigger in `M`: no trigger in `M[n]` (`y_N < y`) -> add shape;
- `arg` with a trigger in `M`: `frame_step_trigArg` below, from the trigger in `M[n]` and the low-part trichotomy;
- `base` (`oN = fsD(ψ_s(y), η)`): left as the hypothesis `hBase` (measured: only the leaf parent `c = x`).
The trigger in `M[n]` follows from the `M`-side `pre ≤ init(y)` and `lN ≠ 0` (`trigN_of_pre`).
-/
import Ytosk.WfQrL16

namespace Ytosk.WfQrH2
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL2 Ytosk.WfQrL3 Ytosk.WfQrL4 Ytosk.WfQrL11 Ytosk.WfQrL14 Ytosk.WfQrL16

/-- The frame step of `qr_engineDQ2` (`hOF`'s conclusion) for given `o(c)`, `o_N(c)`. -/
def FStep (v pre oc oN : T) : Prop :=
  ∃ η', DQ η' false (psi v (spArg v pre oc) z) (psi v (spArg v pre oN) z)

theorem notTrig_z {v pre s : T} : ¬ Trig v pre s z := fun h => T.not_lt_z pre h.1

theorem notTrig_arg {v pre s y yN : T} (hlt : yN < y) (hnt : ¬ Trig v pre s y) : ¬ Trig v pre s yN := by
  rintro ⟨h1, h2⟩
  apply hnt
  refine ⟨T.lt_trans' (show pre < yN from h1) hlt, ?_⟩
  have : psi s yN z < psi s y z := by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hlt⟩
  exact T.lt_trans' (show psi v z z < psi s yN z from h2) this

/-- **The frame step reduced to the base form and the triggered argument form.** -/
theorem frame_step_reduce {η v pre s y oN : T} (hpre : isOT pre = true) (hd : DQ η false (psi s y z) oN)
    (hSN : Single oN)
    (hBase : fsD (psi s y z) η = oN → fsD (psi s y z) η < psi s y z → FStep v pre (psi s y z) oN)
    (hTA : ∀ yN, oN = psi s yN z → DQ η true y yN → Trig v pre s y → FStep v pre (psi s y z) oN) :
    FStep v pre (psi s y z) oN := by
  cases hd with
  | base hlt => exact hBase rfl hlt
  | @sub a aN h =>
    refine ⟨η, frame_DQ_add hpre hSN (DQ.sub h) notTrig_z ?_⟩
    intro s' y' he
    obtain ⟨-, rfl, -⟩ := T.psi.inj he
    exact notTrig_z
  | @arg a b bN h =>
    by_cases ht : Trig v pre s y
    · exact hTA bN rfl h ht
    · refine ⟨η, frame_DQ_add hpre hSN (DQ.arg h) ht ?_⟩
      intro s' y' he
      obtain ⟨rfl, rfl, -⟩ := T.psi.inj he
      exact notTrig_arg h.lt ht

theorem lt_app_psi : ∀ (B a b c : T), B < app B (psi a b c)
  | z, a, b, c => by simp [app]
  | psi a1 b1 B', a, b, c => by
    simp only [app_psi]
    rw [T.psi_lt_psi]
    exact Or.inr (Or.inr ⟨rfl, rfl, lt_app_psi B' a b c⟩)

/-- **The trigger in `M[n]` from `M`-side `pre ≤ init(y)`** (`y = B ++ l`, `y_N = B ++ Q ++ lN`, `lN ≠ 0`). -/
theorem trigN_of_pre {η v pre s y yN : T} (hd : DQ η true y yN) (ht : Trig v pre s y)
    (hpre : ∀ B l lN Q, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → yN = app B (app Q lN) → DQ η false l lN → pre ≤ B ∧ lN ≠ z) :
    Trig v pre s yN := by
  obtain ⟨B, l, lN, Q, s0, y0, ey, eyN, hl, hdl, _⟩ := DQ.true_inv hd
  obtain ⟨hpB, hlN⟩ := hpre B l lN Q ey ⟨s0, y0, hl⟩ eyN hdl
  have hYz : app Q lN ≠ z := fun he => hlN (app_eq_z he).2
  have hBlt : B < yN := by
    rw [eyN]
    cases hY : app Q lN with
    | z => exact absurd hY hYz
    | psi a1 b1 c1 => exact lt_app_psi B a1 b1 c1
  refine ⟨lt_of_le_of_lt hpB hBlt, ?_⟩
  have h2 : psi v z z < psi s y z := ht.2
  show psi v z z < psi s yN z
  rw [psi_lt_psi_z_iff] at h2 ⊢
  rcases h2 with h | ⟨rfl, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨rfl, ?_⟩
    rw [eyN]
    cases hB : app B (app Q lN) with
    | z => exact absurd (app_eq_z hB).2 hYz
    | psi => exact T.z_lt_psi _ _ _

/-- **The triggered argument form**: trigger in both; the low part of `y` decides the shape.  `hLast` is the
trichotomy at the last summand `l` of `y` (`θ = Ω_{s+1}`): `l = θ` (node) or `lN` and its summands stay `≥ θ`. -/
theorem frame_step_trigArg {η v pre s y yN : T} (hy : isOT (psi s y z) = true) (hyN : isOT (psi s yN z) = true)
    (hyot : isOT y = true)
    (hd : DQ η true y yN) (ht : Trig v pre s y) (htN : Trig v pre s yN)
    (hlNz : ∀ B l lN Q, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → yN = app B (app Q lN) → DQ η false l lN → lN ≠ z)
    (hLast : ∀ B l lN Q, y = app B l → (∃ s0 y0, l = psi s0 y0 z) → yN = app B (app Q lN) → DQ η false l lN →
      (split y (psi (succ s) z z)).2 = z →
      l = psi (succ s) z z ∨ (¬ lN < psi (succ s) z z ∧ ∀ q ∈ summands lN, ¬ q < psi (succ s) z z)) :
    FStep v pre (psi s y z) (psi s yN z) := by
  obtain ⟨B, l, lN, Q, s0, y0, ey, eyN, hl, hdl, hQ⟩ := DQ.true_inv hd
  have hlz := hlNz B l lN Q ey ⟨s0, y0, hl⟩ eyN hdl
  have hYz : app Q lN ≠ z := fun he => hlz (app_eq_z he).2
  by_cases hlo : (split y (psi (succ s) z z)).2 = z
  · -- no low part in `y`
    rcases hLast B l lN Q ey ⟨s0, y0, hl⟩ eyN hdl hlo with hθ | hkeep
    · -- node: `l = Ω_{s+1}`
      by_cases hloN : (split yN (psi (succ s) z z)).2 = z
      · exact ⟨η, frame_DQ_trig hy hyN hd ht htN hlo hloN⟩
      · refine frame_DQ_node hy hyN ht htN hlo hloN (B := B) (by rw [ey, hθ]) ?_ ?_
        · -- `hi(y_N) = B`
          have hlt : lN < psi (succ s) z z := by rw [← hθ]; exact hdl.lt
          have hY : head (app Q lN) < psi (succ s) z z := by
            cases hQc : Q with
            | z => simpa [app] using lt_of_le_of_lt (head_le_self lN) hlt
            | psi a1 b1 c1 =>
              have := (hQ (psi a1 b1 z) (by rw [hQc]; simp [summands])).2
              rw [hθ] at this
              simpa [app, head] using this
          have hBlo : (split B (psi (succ s) z z)).2 = z := by
            apply split_snd_z_of_ge
            intro q hq
            have e := split_app (psi (succ s) z z) y
            rw [hlo, app_z_right] at e
            have : q ∈ summands (split y (psi (succ s) z z)).1 := by
              rw [e, ey, summands_app]; exact List.mem_append_left _ hq
            exact split_fst_ge _ y q this
          rw [eyN, WfQrL3.split_app_low hY hYz]
          have e2 := split_app (psi (succ s) z z) B
          rw [hBlo, app_z_right] at e2
          exact e2
        · rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self s)
    · have hyall : ∀ q ∈ summands y, ¬ q < psi (succ s) z z := by
        intro q hq
        have e := split_app (psi (succ s) z z) y
        rw [hlo, app_z_right] at e
        rw [← e] at hq
        exact split_fst_ge _ y q hq
      have hloN : (split yN (psi (succ s) z z)).2 = z := by
        rw [eyN]
        apply split_snd_z_of_ge
        intro q hq
        rw [summands_app, summands_app] at hq
        rcases List.mem_append.mp hq with hq | hq
        · apply hyall; rw [ey, summands_app]; exact List.mem_append_left _ hq
        · rcases List.mem_append.mp hq with hq | hq
          · intro hqt
            exact hkeep.1 (lt_of_le_of_lt (hQ q hq).1 hqt)
          · exact hkeep.2 q hq
      exact ⟨η, frame_DQ_trig hy hyN hd ht htN hlo hloN⟩
  · -- low part in `y`: kept
    have hlt : l < psi (succ s) z z := by
      rw [ey, hl] at hyot hlo; rw [hl]; exact last_lt_of_lo hyot hlo
    have hYl : head (app Q lN) < psi (succ s) z z := by
      cases hQc : Q with
      | z => simpa [app] using lt_of_le_of_lt (head_le_self lN) (lt_trans hdl.lt hlt)
      | psi a1 b1 c1 =>
        have := (hQ (psi a1 b1 z) (by rw [hQc]; simp [summands])).2
        simpa [app, head] using lt_trans this hlt
    have hl0 : head l < psi (succ s) z z := by rw [hl]; simpa [head] using (show psi s0 y0 z < _ by rw [← hl]; exact hlt)
    have hlnz : l ≠ z := by rw [hl]; simp
    have e1 : split yN (psi (succ s) z z) = ((split B (psi (succ s) z z)).1, app (split B (psi (succ s) z z)).2 (app Q lN)) := by
      rw [eyN, WfQrL3.split_app_low hYl hYz]
    have e2 : split y (psi (succ s) z z) = ((split B (psi (succ s) z z)).1, app (split B (psi (succ s) z z)).2 l) := by
      rw [ey, WfQrL3.split_app_low hl0 hlnz]
    have hhi : (split yN (psi (succ s) z z)).1 = (split y (psi (succ s) z z)).1 := by rw [e1, e2]
    have hloN : (split yN (psi (succ s) z z)).2 ≠ z := by
      rw [e1]; exact fun he => hYz (app_eq_z he).2
    exact ⟨η, frame_DQ_trig_lo hy hyN hd ht htN hlo hloN hhi⟩

end Ytosk.WfQrH2
