/-
**3 行・t = 0: g の o の枠（種 S1）。**

r が g で数えられるとき、N での g の子の値は M の子の値 Lc のあとに ψ_v(Y0)（中間のコピーの根）が m 個、
最後に ρ′.o(r)（M.take x での r の値）が並ぶ。M では Lc のあとに ψ_v(Y0 + 1)（= o_M(r)）。
- m ≥ 1: 最初の ψ_v(Y0) のあとは書き換えが起きない（`no_rw_after`）ので、最後の子 ρ′.o(r) ⊴ ψ_v(Y0)
  の枠（`node_lhd`）で ψ_v(Y0) を m + 1 個並べた値以下。それは o_M(g) の基本列の項 o_M(g)[k]
  （2 行の `t0_frame_notrig`・`t0_frame_trig`・`t0_frame_swallow`）で、Buchholz 氏の ◁ で o_M(g) より下。
- m = 0: 最後の子 ρ′.o(r) ◁ o_M(r) の 1 枠。
-/
import Ytosk.V3T0D

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem app_assoc' : ∀ (x y w : T), app (app x y) w = app x (app y w)
  | z, _, _ => rfl
  | psi a b c, y, w => by simp only [app_psi]; rw [app_assoc' c y w]

theorem mulT_succ' (t : T) : ∀ n, mulT t (n + 1) = app (mulT t n) t
  | 0 => by simp [mulT]
  | n + 1 => by
    show app t (mulT t (n + 1)) = app (app t (mulT t n)) t
    rw [mulT_succ' t n, app_assoc']

/-- `cof` is `0` only at `0`, and a successor only for a successor. -/
theorem cof_props : ∀ t : T, (cof t = .zero → t = z) ∧ (cof t = .succ → isSucc t = true)
  | z => ⟨fun _ => rfl, fun h => by simp [cof] at h⟩
  | psi a b (psi c d e) => by
    have ih := cof_props (psi c d e)
    refine ⟨fun h => absurd (ih.1 (by simpa [cof] using h)) (by simp), fun h => ?_⟩
    have := ih.2 (by simpa [cof] using h)
    simpa [isSucc, last] using this
  | psi a b z => by
    have iha := cof_props a
    have ihb := cof_props b
    by_cases hb : b = z
    · subst hb
      by_cases ha : a = z
      · subst ha
        refine ⟨fun h => by simp [cof] at h, fun _ => ?_⟩
        simp [isSucc, last, one]
      · by_cases hs : isSucc a = true
        · refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp [cof, ha, hs] at h
        · refine ⟨fun h => ?_, fun h => ?_⟩
          · simp only [cof, if_pos, if_neg ha, if_neg hs] at h
            exact absurd (iha.1 h) ha
          · simp only [cof, if_pos, if_neg ha, if_neg hs] at h
            exact absurd (iha.2 h) hs
    · by_cases hs : isSucc b = true
      · refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp [cof, hb, hs] at h
      · refine ⟨fun h => ?_, fun h => ?_⟩
        · cases hc : cof b with
          | zero => exact absurd (ihb.1 hc) hb
          | big μ =>
            simp only [cof, if_neg hb, if_neg hs, hc] at h
            split at h <;> cases h
          | succ => simp [cof, hb, hs, hc] at h
          | omega => simp [cof, hb, hs, hc] at h
        · cases hc : cof b with
          | succ => exact absurd (ihb.2 hc) hs
          | big μ =>
            simp only [cof, if_neg hb, if_neg hs, hc] at h
            split at h <;> cases h
          | zero => simp [cof, hb, hs, hc] at h
          | omega => simp [cof, hb, hs, hc] at h

theorem natT_lt_om (μ : T) : ∀ k, natT k < psi (succ μ) z z
  | 0 => T.z_lt_psi _ _ _
  | k + 1 => by
    show psi z z (natT k) < psi (succ μ) z z
    rw [psi_lt_psi]
    exact Or.inl (lt_of_le_of_ne (z_le _) (Ne.symm (succ_ne_z μ)))

/-- **Every natural index is valid** for a `ψ` with a nonzero argument. -/
theorem validLt_natT {a b : T} (hb : b ≠ z) (k : Nat) : ValidLt (psi a b z) (natT k) := by
  have h := cof_props (psi a b z)
  unfold ValidLt
  cases hc : cof (psi a b z) with
  | zero => exact absurd (h.1 hc) (by simp)
  | succ =>
    exfalso
    have := h.2 hc
    simp only [isSucc, last, beq_iff_eq, one, psi.injEq] at this
    exact hb this.2.1
  | omega => trivial
  | big μ => exact natT_lt_om μ k

/-- `◁` with a natural index is `◁` with index `0`. -/
theorem lhd_natT_z {k : Nat} {b a : T} (h : Lhd (natT k) b a) : Lhd z b a := by
  refine ⟨h.1, fun u c h1 h2 x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := h.2 u c h1 h2 x hx
  rcases List.mem_append.mp hy with hy | hy
  · exact ⟨y, List.mem_append_left _ hy, hxy⟩
  · have hyz : y = z := by
      simp only [Gc, List.mem_cons] at hy
      rcases hy with hy | hy
      · exact hy
      · exact comps_natT k y hy
    exact ⟨y, List.mem_append_right _ (by simp [Gc, hyz]), hxy⟩

theorem lt_app_one (Y : T) : Y < app Y one := by
  have := app_lt_app_left Y (show z < one from T.z_lt_psi _ _ _)
  rwa [app_z_right] at this

/-- **No rewrite after the first copy**: once `ψ_v(Y0)` has been appended, `Y0` is at most the state. -/
theorem no_rw_after {a B v Y0 : T} (hO : isOT (psi v Y0 z) = true) {m : Nat} (hm : 1 ≤ m) :
    ¬ (lt (spArg a B (mulT (psi v Y0 z) m)) Y0 = true ∧ lt (psi a z z) (psi v Y0 z) = true) := by
  rintro ⟨h1, h2⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have e : spArg a B (mulT (psi v Y0 z) (m' + 1)) =
      spArg a (step a B v Y0 z) (mulT (psi v Y0 z) m') := by
    show spArg a B (app (psi v Y0 z) (mulT (psi v Y0 z) m')) = _
    rw [app_psi, app_z, spArg_cons, step_rest a B v Y0 _ z]
  rw [e] at h1
  have hle1 : Y0 ≤ step a B v Y0 z := by
    unfold step
    split_ifs with ht
    · exact le_H hO
    · have hB : ¬ lt B Y0 = true := fun h => ht ⟨h, h2⟩
      have hBY : Y0 ≤ B := by
        rcases lt_or_ge B Y0 with h | h
        · exact absurd h hB
        · exact h
      exact le_trans hBY (le_of_lt (by
        have := add_lt_add_left B (T.z_lt_psi v Y0 z); rwa [add_z_right] at this))
  have hle2 := le_spArg a (mulT (psi v Y0 z) m') (step a B v Y0 z) (isOT_mulT hO ⟨_, _, rfl⟩ m')
  exact absurd (lt_of_lt_of_le (show _ < Y0 from h1) (le_trans hle1 hle2)) (lt_irrefl' _)

/-- **The core of the `g` frame** (`t = 0`): the children `ψ_v(Y0)` × m and then `X′ ◁ ψ_v(Y0 + 1)`
against the single child `ψ_v(Y0 + 1)`. -/
theorem s1_core {a B v Y0 X' : T} {m : Nat}
    (hOld : isOT (psi a (spArg a B (psi v (app Y0 one) z)) z) = true)
    (hX : isOT (psi v (app Y0 one) z) = true) (hO : isOT (psi v Y0 z) = true)
    (hBX : ∀ q ∈ summands B, psi v (app Y0 one) z ≤ q)
    (hX' : Single X') (hl : Lhd z X' (psi v (app Y0 one) z))
    (hX'O : 1 ≤ m → X' ≤ psi v Y0 z)
    (hy' : ∀ s' y', X' = psi s' y' z → s' ≠ v → y' = z)
    (hsub : lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true → SubSmall a v)
    (hsub0 : ∀ s' y', X' = psi s' y' z → s' ≠ v →
      lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true → SubSmall a s')
    (hcl : lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true → Closed a B) :
    Lhd z (psi a (spArg a (spArg a B (mulT (psi v Y0 z) m)) X') z)
      (psi a (spArg a B (psi v (app Y0 one) z)) z) := by
  obtain ⟨s', y', rfl⟩ := hX'.2
  have hc' := hX'.1
  have hOX : psi v Y0 z < psi v (app Y0 one) z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one Y0⟩)
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    simp only [mulT]
    show Lhd z (psi a (spArg a B (psi s' y' z)) z) (psi a (spArg a B (psi v (app Y0 one) z)) z)
    rw [spArg_single, spArg_single]
    have hsub' : (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) ∨
        (lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true) → SubSmall a s' := by
      intro hrw
      by_cases hs : s' = v
      · subst hs
        apply hsub
        rcases hrw with hn | ho
        · have hle : psi s' y' z ≤ psi s' (app Y0 one) z := le_of_lt hl.1
          have hyy : y' ≤ app Y0 one := by
            rcases (le_iff _ _).mp hle with h | h
            · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
              · exact absurd h (lt_irrefl' _)
              · exact le_of_lt h
            · simp only [psi.injEq] at h; rw [h.2.1]
          exact ⟨lt_of_lt_of_le hn.1 hyy, lt_of_lt_of_le hn.2 hle⟩
        · exact ho
      · have hyz := hy' s' y' rfl hs
        rcases hrw with hn | ho
        · exfalso; have := hn.1; rw [hyz] at this; exact T.not_lt_z _ this
        · exact hsub0 s' y' rfl hs ho
    have hE := node_lhd hX hc' (Or.inr hl) hBX hsub hsub' (fun _ hr => hcl hr)
    apply lhd_of_lhdE_lt hE
    apply psi_lt_psi_z_iff.mpr; right; refine ⟨rfl, ?_⟩
    apply step_lt hX hc' (Or.inl hl) hBX
    · intro ht' hss
      exfalso
      have hyz := hy' s' y' rfl (ne_of_lt hss)
      have := ht'.1; rw [hyz] at this; exact T.not_lt_z _ this
    · intro h; exfalso; have := lt_app_one Y0; rw [h] at this; exact T.not_lt_z _ this
  · -- `m ≥ 1`
    set O := psi v Y0 z with hOdef
    set B' := spArg a B (mulT O m) with hB'
    have hnr := no_rw_after (a := a) (B := B) hO hm
    rw [← hOdef, ← hB'] at hnr
    have hB'O : ∀ q ∈ summands B', O ≤ q :=
      spArg_summands_ge ⟨v, Y0, rfl⟩ (mulT O m) B (isOT_mulT hO ⟨_, _, rfl⟩ m)
        (fun q hq => by rw [summands_mulT ⟨_, _, rfl⟩ m q hq])
        (fun q hq => le_trans (le_of_lt hOX) (hBX q hq))
    -- the middle value: `m + 1` copies
    have hMid : spArg a B (mulT O (m + 1)) = step a B' v Y0 z := by
      rw [mulT_succ', spArg_app, hOdef, spArg_single]
    -- (i) the last child against `ψ_v(Y0)`
    have hNM : LhdE (psi a (step a B' s' y' z) z) (psi a (step a B' v Y0 z) z) := by
      by_cases heq : psi s' y' z = O
      · rw [hOdef] at heq; simp only [psi.injEq] at heq; rw [heq.1, heq.2.1]; exact Or.inl rfl
      · have hlt' : psi s' y' z < O := lt_of_le_of_ne (hX'O hm) heq
        have hlO : Lhd z (psi s' y' z) O := lhd_restrict hl hlt' (le_of_lt hOX)
        have hnew : ¬ (lt B' y' = true ∧ lt (psi a z z) (psi s' y' z) = true) := by
          rintro ⟨h1, h2⟩
          by_cases hs : s' = v
          · subst hs
            have hyy : y' ≤ Y0 := by
              rcases psi_lt_psi_z_iff.mp hlt' with h | ⟨_, h⟩
              · exact absurd h (lt_irrefl' _)
              · exact le_of_lt h
            exact hnr ⟨lt_of_lt_of_le h1 hyy, lt_trans h2 hlt'⟩
          · have := hy' s' y' rfl hs
            rw [this] at h1; exact T.not_lt_z _ h1
        exact node_lhd hO hc' (Or.inr hlO) hB'O (fun h => absurd h hnr)
          (fun h => by rcases h with h | h
                       · exact absurd h hnew
                       · exact absurd h hnr)
          (fun _ h => absurd h hnr)
    -- (ii) the middle value is a term of the fundamental sequence of the old value
    have hArg : spArg a B (psi v (app Y0 one) z) ≠ z := by
      intro h
      have := lt_spArg a (b := B) hX (by simp)
      rw [h] at this; exact T.not_lt_z _ this
    have hfsM : ∃ k, psi a (spArg a B (mulT O (m + 1))) z =
        fs (psi a (spArg a B (psi v (app Y0 one) z)) z) (natT k) := by
      by_cases htr : lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true
      · by_cases hbad : lt B Y0 = true ∧ (split Y0 (psi (succ v) z z)).2 = z
        · refine ⟨m, ?_⟩
          have := t0_frame_swallow (n := m + 1) (by omega) hX hO htr hbad.1 hbad.2
          rw [show m + 1 - 1 = m by omega] at this
          exact this.symm
        · exact ⟨m + 1, (t0_frame_trig (n := m + 1) (by omega) hOld hX hO htr hbad).symm⟩
      · have hXapp : isOT (app B (psi v (app Y0 one) z)) = true := by
          have h1 := isOT_arg hOld
          rw [spArg_single] at h1; unfold step at h1
          rw [if_neg htr, add_eq_app_of_ge ⟨_, _, rfl⟩ _ hBX] at h1
          exact h1
        exact ⟨m + 1, (t0_frame_notrig (m + 1) hXapp htr hBX).symm⟩
    obtain ⟨k, hk⟩ := hfsM
    have hlM : Lhd z (psi a (spArg a B (mulT O (m + 1))) z)
        (psi a (spArg a B (psi v (app Y0 one) z)) z) := by
      rw [hk]; exact lhd_natT_z (lhd_fs hOld (validLt_natT hArg k))
    rw [hMid] at hlM
    have hnew : spArg a B' (psi s' y' z) = step a B' s' y' z := spArg_single _ _ _ _
    rw [hnew]
    exact lhd_of_lhdE_lt (LhdE.trans hNM (Or.inr hlM)) (lt_of_le_of_lt hNM.le hlM.1)

end Ytosk
