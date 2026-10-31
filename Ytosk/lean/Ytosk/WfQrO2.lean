/-
**WfQrO2 (2026-11-01): `v_{M[1]}(r) ≤ v(r)` from the drop lemma, and the single-layer components of `OmSide1`.**
- `hv1` of `WfQrH7.qr_chainH3` is the `v` claim `PV2` of the drop lemma (`drop_all_hardW2`, `M -> M.take x`) at `r`:
  `LhdE` gives `≤`, the weak alternative `WkVA` gives `<` (`v_le_of_PV2`, `hv1_of_drop`).
- `hQ0` (single `Y`): the decomposition is `B = 0`, `l = Y`; `Q = 0` as soon as `Y_N` is a single summand and
  `l_N ≠ 0` (`η ≠ 0`, `Y ≠ 1`) (`hQ0_of`).
- `hLo`: the kept high part (`lo(b) ≠ 0`) needs only `l_N ≠ 0`; the empty low part (`lo(b) = 0`) needs `l_N` and its
  summands `≥ Ω_{a+1}`, which follows from a `DQG` witness `lc ≥ Ω_{a+1}` (`lo_keep`, `lo_keep_G`).
- `omSide1_of`: `OmSide1` from these and the base clause `hB`.
-/
import Ytosk.WfQrO1
import Ytosk.WfQrH4
import Ytosk.WfDrE1

namespace Ytosk.WfQrO2
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL2 Ytosk.WfQrL3 Ytosk.WfQrL4 Ytosk.WfQrL11 Ytosk.WfQrL13 Ytosk.WfQrL14
  Ytosk.WfQrL16 Ytosk.WfQrH2 Ytosk.WfQrH3 Ytosk.WfQrH4 Ytosk.WfQrO1

/-- The `v` claim of the drop lemma bounds the new value. -/
theorem v_le_of_PV2 {M : Mat} {ρ ρ' : Valn} {i : Nat} (h : PV2 M ρ ρ' i) : ρ'.v i ≤ ρ.v i := by
  rcases h.1 with h | h
  · rcases h with h | h
    · exact le_of_eq h
    · exact le_of_lt h.1
  · exact le_of_lt h.1.1

/-- **`hv1` (`v_{M[1]}(r) ≤ v(r)`) from the conclusion of the drop lemma** (`drop_all_hardW2`, `ρ'` = the value of
`M.take x = M[1]`). -/
theorem hv1_of_drop {M : Mat} {x r : Nat} {ρ ρ' : Valn} (h : ∀ i, i < x → PO ρ ρ' i ∧ PV2 M ρ ρ' i) (hr : r < x) :
    ρ'.v r ≤ ρ.v r :=
  v_le_of_PV2 (h r hr).2

/-- A single summand `Q ++ lN` with `lN ≠ 0` has `Q = 0`. -/
theorem q_z_of_single {Q lN a b : T} (h : app Q lN = psi a b z) (hl : lN ≠ z) : Q = z := by
  cases Q with
  | z => rfl
  | psi a1 b1 c1 =>
    simp only [app_psi] at h
    injection h with _ _ h3
    exact absurd (app_eq_z h3).2 hl

/-- A single `Y = B ++ l` (`l` single) has `B = 0`. -/
theorem b_z_of_single {s b B l s0 y0 : T} (h : psi s b z = app B l) (hl : l = psi s0 y0 z) : B = z := by
  cases B with
  | z => rfl
  | psi a1 b1 c1 =>
    simp only [app_psi] at h
    injection h with _ _ h3
    rw [hl] at h3
    exact absurd (app_eq_z h3.symm).2 (fun h => T.noConfusion h)

/-- **`hQ0` of `OmSide1`** from `Y_N` single, `η ≠ 0`, `Y ≠ 1`. -/
theorem hQ0_of {η Y YN : T} (hη : η ≠ z) (hS : ∃ a b, YN = psi a b z) (h1 : Y ≠ one) :
    ∀ s b, Y = psi s b z → ∀ B l lN Q, Y = app B l → (∃ s0 y0, l = psi s0 y0 z) → YN = app B (app Q lN) →
      DQ η false l lN → Q = z := by
  intro s b hY B l lN Q eY hl eYN hd
  obtain ⟨s0, y0, hl'⟩ := hl
  have hB : B = z := b_z_of_single (hY ▸ eY) hl'
  subst hB
  have hlY : l = Y := by simpa [app] using eY.symm
  have hlN : lN ≠ z := by
    subst hl'
    cases hd with
    | base _ => exact fsD_ne_z_of_ne_one hη (hlY ▸ h1)
    | sub _ => exact fun h => T.noConfusion h
    | arg _ => exact fun h => T.noConfusion h
  obtain ⟨a, b', hYN⟩ := hS
  simp only [app_z] at eYN
  exact q_z_of_single (eYN ▸ hYN) hlN

/-- **`hLo` of `OmSide1`** from `l_N ≠ 0` and, when `lo(b) = 0`, the kept last summand. -/
theorem lo_keep {η a b bN : T} (hbot : isOT b = true) (hd : DQ η true b bN)
    (hlNz : ∀ B l lN Q, b = app B l → (∃ s0 y0, l = psi s0 y0 z) → bN = app B (app Q lN) → DQ η false l lN →
      lN ≠ z)
    (hkeep : ∀ B l lN Q, b = app B l → (∃ s0 y0, l = psi s0 y0 z) → bN = app B (app Q lN) → DQ η false l lN →
      loOf a b = z → ¬ lN < psi (succ a) z z ∧ ∀ q ∈ summands lN, ¬ q < psi (succ a) z z) :
    (loOf a b = z → loOf a bN = z) ∧ (loOf a b ≠ z → hiOf a bN = hiOf a b ∧ loOf a bN ≠ z) := by
  obtain ⟨B, l, lN, Q, s0, y0, ey, eyN, hl, hdl, hQ⟩ := DQ.true_inv hd
  have hlz := hlNz B l lN Q ey ⟨s0, y0, hl⟩ eyN hdl
  have hYz : app Q lN ≠ z := fun he => hlz (app_eq_z he).2
  refine ⟨fun hlo => ?_, fun hlo => ?_⟩
  · have hk := hkeep B l lN Q ey ⟨s0, y0, hl⟩ eyN hdl hlo
    unfold loOf at hlo ⊢
    have hyall : ∀ q ∈ summands b, ¬ q < psi (succ a) z z := by
      intro q hq
      have e := split_app (psi (succ a) z z) b
      rw [hlo, app_z_right] at e
      rw [← e] at hq
      exact split_fst_ge _ b q hq
    rw [eyN]
    apply split_snd_z_of_ge
    intro q hq
    rw [summands_app, summands_app] at hq
    rcases List.mem_append.mp hq with hq | hq
    · apply hyall; rw [ey, summands_app]; exact List.mem_append_left _ hq
    · rcases List.mem_append.mp hq with hq | hq
      · intro hqt
        exact hk.1 (lt_of_le_of_lt (hQ q hq).1 hqt)
      · exact hk.2 q hq
  · unfold loOf hiOf at *
    have hlt : l < psi (succ a) z z := by
      have hb2 := hbot
      have hlo2 := hlo
      rw [ey, hl] at hb2 hlo2; rw [hl]; exact last_lt_of_lo hb2 hlo2
    have hYl : head (app Q lN) < psi (succ a) z z := by
      cases hQc : Q with
      | z => simpa [app] using lt_of_le_of_lt (head_le_self lN) (lt_trans hdl.lt hlt)
      | psi a1 b1 c1 =>
        have := (hQ (psi a1 b1 z) (by rw [hQc]; simp [summands])).2
        simpa [app, head] using lt_trans this hlt
    have hl0 : head l < psi (succ a) z z := by
      rw [hl]; simpa [head] using (show psi s0 y0 z < _ by rw [← hl]; exact hlt)
    have hlnz : l ≠ z := by rw [hl]; simp
    have e1 : split bN (psi (succ a) z z) =
        ((split B (psi (succ a) z z)).1, app (split B (psi (succ a) z z)).2 (app Q lN)) := by
      rw [eyN, WfQrL3.split_app_low hYl hYz]
    have e2 : split b (psi (succ a) z z) =
        ((split B (psi (succ a) z z)).1, app (split B (psi (succ a) z z)).2 l) := by
      rw [ey, WfQrL3.split_app_low hl0 hlnz]
    refine ⟨by rw [e1, e2], ?_⟩
    rw [e1]; exact fun he => hYz (app_eq_z he).2

/-- The kept last summand of `lo_keep` from a `DQG` witness `lc ≥ Ω_{a+1}` (single `l_N`). -/
theorem keep_of_G {η a l lN : T}
    (h : ∃ lc, DQG η false l lN lc ∧ psi (succ a) z z ≤ lc ∧ ∃ a' b', lN = psi a' b' z) :
    ¬ lN < psi (succ a) z z ∧ ∀ q ∈ summands lN, ¬ q < psi (succ a) z z := by
  rcases last_of_G (l := l) (Or.inr h) with h' | h'
  · obtain ⟨lc, hG, hθ, a', b', rfl⟩ := h
    exfalso
    have := lt_of_le_of_lt hθ hG.lt
    exact (lt_irrefl' _) (h' ▸ (lt_trans' this hG.toDQ.lt))
  · exact h'

/-- **`OmSide1` from its single-layer fields**: `Y_N` single, `η ≠ 0`, `Y ≠ 1`, the `DQG` witness of the empty low part
(`LoG`), and the base clause `hB`. -/
theorem omSide1_of {η Y YN : T} (hY : isOT Y = true) (hYN : isOT YN = true)
    (hsm : (Y < E0 ∧ YN < E0) ∨ (¬ Y < E0 ∧ ¬ YN < E0))
    (hη : η ≠ z) (hS : ∃ a b, YN = psi a b z) (h1 : Y ≠ one)
    (hLoG : ∀ a b bN, Y = psi a b z → YN = psi a bN z → b ≠ z → DQ η true b bN →
      (∀ B l, b = app B l → (∃ s0 y0, l = psi s0 y0 z) → l ≠ one) ∧
      ∀ B l lN Q, b = app B l → (∃ s0 y0, l = psi s0 y0 z) → bN = app B (app Q lN) → DQ η false l lN →
        loOf a b = z → ∃ lc, DQG η false l lN lc ∧ psi (succ a) z z ≤ lc ∧ ∃ a' b', lN = psi a' b' z)
    (hArg : ∀ a b bN, Y = psi a b z → YN = psi a bN z → b ≠ z → DQ η true b bN)
    (hB : YN = fsD Y η → fsD (omega Y) η = omega (fsD Y η) ∧ fsD (omega Y) η < omega Y) :
    OmSide1 η Y YN := by
  refine ⟨hY, hYN, hsm, fun s b hYs => hQ0_of hη hS h1 s b hYs, ?_, hB⟩
  intro a b bN hYa hYNa hb
  have hd := hArg a b bN hYa hYNa hb
  obtain ⟨hne1, hL⟩ := hLoG a b bN hYa hYNa hb hd
  have hbot : isOT b = true := by rw [hYa] at hY; exact isOT_arg hY
  refine lo_keep hbot hd ?_ ?_
  · intro B l lN Q hy hl hyN hdl
    exact lNz_of hη hne1 B l lN Q hy hl bN hyN hdl
  · intro B l lN Q hy hl hyN hdl hlo
    exact keep_of_G (hL B l lN Q hy hl hyN hdl hlo)

/-- **`OFields` with the triggered-argument part from `OG`** (the base / leaf-parent part unchanged). -/
theorem ofields_of_G {v pre oc oN η : T} (hη : η ≠ z)
    (hBase : fsD oc η = oN → fsD oc η < oc →
      (∃ a, oc = psi (succ a) z z ∧
        ((∀ s' y', oN = psi s' y' z → ¬ Trig v pre s' y') ∨ (∃ s' y', oN = psi s' y' z ∧ LeafPar v pre a s' y'))) ∨
      (∃ s s', oc = psi s z z ∧ oN = psi s' z z) ∨
      (∃ s y yN, oc = psi s y z ∧ oN = psi s yN z ∧ DQ η true y yN))
    (hG : ∀ s y yN, oc = psi s y z → oN = psi s yN z → DQ η true y yN → OG v pre s y yN η) :
    OFields v pre oc oN η :=
  ⟨hBase, ofields_arg_of_G hη hG⟩

end Ytosk.WfQrO2
