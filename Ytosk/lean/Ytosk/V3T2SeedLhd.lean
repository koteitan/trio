/-
**3 行・t = 2: 種の枠の ◁ の純粋な順序数の補題（`seed_frame_lhd`）。**

種の枠では、最後の数える子が「書き換えない葉 Ω_s」から「ψ_{s′}(y′)（s′ < s）」に替わる。子の段の ◁ は偽
（C = Ω_{s′+1} が y′ を押さえない）だが、ψ_a の段では区間のどの C も引数 C″ = B + C′（C′ ∈ [Ω_{s′}, Ω_s]）を
成分に持つので、新しい引数 X の成分は「X 以下」か「B・a・s′ の成分以下」なら押さえられる
（s′ の成分は s′ ◁ s で C′ の頭の添字 t ∈ [s′, s] の成分に移す）。
実測（C′ 2 万行列、n = 2..4、q = r・sv・q ≠ r の 6 万枠）: 仮定 hdom・s′ ◁ s・B + Ω_{s′} ≤ X < B + Ω_s は全件成立。
-/
import Ytosk.FS
import Ytosk.OTLemmas

namespace Ytosk

open T

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- **A term between `B` and `B + W` extends `B`** (the order is lexicographic). -/
theorem app_prefix_of_between : ∀ {B C W : T}, B ≤ C → C ≤ app B W → ∃ C', C = app B C'
  | z, C, _, _, _ => ⟨C, rfl⟩
  | psi b1 b2 Br, C, W, h1, h2 => by
    cases C with
    | z =>
      exfalso
      rcases (le_iff _ _).mp h1 with h | h
      · exact T.not_lt_z _ h
      · cases h
    | psi c1 c2 Cr =>
      have h2' : psi c1 c2 Cr ≤ psi b1 b2 (app Br W) := h2
      have hcb : c1 = b1 ∧ c2 = b2 := by
        rcases (le_iff _ _).mp h1 with h | h
        · rcases (le_iff _ _).mp h2' with h' | h'
          · rw [T.psi_lt_psi] at h h'
            rcases h with h | ⟨e1, h⟩ | ⟨e1, e2, _⟩
            · rcases h' with h' | ⟨e1', _⟩ | ⟨e1', _, _⟩
              · exact absurd (lt_trans h h') (lt_irrefl' _)
              · rw [e1'] at h; exact absurd h (lt_irrefl' _)
              · rw [e1'] at h; exact absurd h (lt_irrefl' _)
            · rcases h' with h' | ⟨e1', h'⟩ | ⟨e1', e2', _⟩
              · rw [e1] at h'; exact absurd h' (lt_irrefl' _)
              · exact absurd (lt_trans h h') (lt_irrefl' _)
              · rw [e2'] at h; exact absurd h (lt_irrefl' _)
            · exact ⟨e1.symm, e2.symm⟩
          · simp only [psi.injEq] at h'; exact ⟨h'.1, h'.2.1⟩
        · simp only [psi.injEq] at h; exact ⟨h.1.symm, h.2.1.symm⟩
      obtain ⟨rfl, rfl⟩ := hcb
      have hl : Br ≤ Cr := by
        rcases (le_iff _ _).mp h1 with h | h
        · rw [T.psi_lt_psi] at h
          rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact absurd h (lt_irrefl' _)
          · exact le_of_lt h
        · simp only [psi.injEq] at h; rw [h.2.2]
      have hr : Cr ≤ app Br W := by
        rcases (le_iff _ _).mp h2' with h | h
        · rw [T.psi_lt_psi] at h
          rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact absurd h (lt_irrefl' _)
          · exact le_of_lt h
        · simp only [psi.injEq] at h; rw [h.2.2]
      obtain ⟨C', hC'⟩ := app_prefix_of_between hl hr
      exact ⟨C', by rw [hC']; rfl⟩

theorem app_left_cancel : ∀ {p y y' : T}, app p y = app p y' → y = y'
  | z, _, _, h => h
  | psi a b c, y, y', h => by
    simp only [app_psi, psi.injEq] at h
    exact app_left_cancel h.2.2

theorem app_le_app_left_iff (p : T) {y y' : T} : app p y ≤ app p y' ↔ y ≤ y' := by
  constructor
  · intro h
    rcases (le_iff _ _).mp h with h | h
    · exact le_of_lt ((app_lt_app_left_iff p).mp h)
    · rw [app_left_cancel h]
  · exact app_le_app_left p

/-- **The ◁ of a seed frame.** The old last child is the leaf `Ω_s` (it does not rewrite), the new state is `X`
with `B + Ω_{s′} ≤ X < B + Ω_s`, `a < s′`, `s′ ◁ s`, and the components of `X` at the levels `≤ a` are at most
`X` or at most a component of `B`, `a` or `s′`. -/
theorem seed_frame_lhd {a B s s' X : T} (has : a < s') (hXs : app B (psi s' z z) ≤ X)
    (hXlt : X < app B (psi s z z)) (hs : s' = s ∨ Lhd z s' s)
    (hdom : ∀ u, ¬ lt a u = true → ∀ g ∈ comps u X,
      g ≤ X ∨ ∃ d ∈ comps u B ++ comps u a ++ comps u s', g ≤ d) :
    Lhd z (psi a X z) (psi a (app B (psi s z z)) z) := by
  refine ⟨psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hXlt⟩), fun u C hC1 hC2 => ?_⟩
  by_cases hau : lt a u = true
  · intro e he
    simp only [comps, if_pos hau, List.nil_append] at he
    simp [comps] at he
  -- the head of `C` is `ψ_a(C″)` with `X ≤ C″ ≤ B + Ω_s`
  cases C with
  | z => exact absurd hC1 (T.not_lt_z _)
  | psi c1 C'' Cr =>
    have hc1 : c1 = a ∧ X ≤ C'' ∧ C'' ≤ app B (psi s z z) := by
      have h1 : psi a X z < psi c1 C'' Cr := hC1
      rcases (le_iff _ _).mp hC2 with h2 | h2
      · rw [T.psi_lt_psi] at h1 h2
        rcases h1 with h1 | ⟨e1, h1⟩ | ⟨e1, e2, _⟩
        · rcases h2 with h2 | ⟨e1', _⟩ | ⟨e1', _, _⟩
          · exact absurd (lt_trans h1 h2) (lt_irrefl' _)
          · rw [e1'] at h1; exact absurd h1 (lt_irrefl' _)
          · rw [e1'] at h1; exact absurd h1 (lt_irrefl' _)
        · rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, e2', _⟩
          · rw [e1] at h2; exact absurd h2 (lt_irrefl' _)
          · exact ⟨e1.symm, le_of_lt h1, le_of_lt h2⟩
          · exact ⟨e1.symm, le_of_lt h1, by rw [e2']⟩
        · rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, e2', _⟩
          · rw [e1] at h2; exact absurd h2 (lt_irrefl' _)
          · exact ⟨e1.symm, by rw [e2], le_of_lt h2⟩
          · exact ⟨e1.symm, by rw [e2], by rw [e2']⟩
      · simp only [psi.injEq] at h2
        exact ⟨h2.1, by rw [h2.2.1]; exact le_of_lt hXlt, by rw [h2.2.1]⟩
    obtain ⟨hca, hXC, hCB⟩ := hc1
    subst c1
    have hBX : B ≤ X := le_trans (le_app_self B _) hXs
    obtain ⟨C', rfl⟩ := app_prefix_of_between (le_trans hBX hXC) hCB
    have hC's : C' ≤ psi s z z := (app_le_app_left_iff B).mp hCB
    have hs'C : psi s' z z ≤ C' := (app_le_app_left_iff B).mp (le_trans hXs hXC)
    -- the head subscript `t` of `C′` lies in `[s′, s]`
    cases C' with
    | z => exact absurd (lt_of_lt_of_le (T.z_lt_psi _ _ _) hs'C) (lt_irrefl' _)
    | psi t w rr =>
      have hts' : s' ≤ t := by
        rcases (le_iff _ _).mp hs'C with h | h
        · rw [T.psi_lt_psi] at h
          rcases h with h | ⟨e, _⟩ | ⟨e, _, _⟩
          · exact le_of_lt h
          · rw [e]
          · rw [e]
        · simp only [psi.injEq] at h; rw [h.1]
      have hts : t ≤ s := by
        rcases (le_iff _ _).mp hC's with h | h
        · rw [T.psi_lt_psi] at h
          rcases h with h | ⟨e, _⟩ | ⟨e, _, _⟩
          · exact le_of_lt h
          · rw [e]
          · rw [e]
        · simp only [psi.injEq] at h; rw [h.1]
      have htu : ¬ lt t u = true := by
        intro htu
        have hat : a < t := lt_of_lt_of_le has hts'
        have : a < u := lt_trans hat htu
        exact hau this
      -- the components of `C`
      have hmemC : ∀ d, d ∈ comps u (app B (psi t w rr)) → d ∈ comps u (psi a (app B (psi t w rr)) Cr) := by
        intro d hd
        simp only [comps, if_neg hau, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr (Or.inl hd))
      have hCC : app B (psi t w rr) ∈ comps u (psi a (app B (psi t w rr)) Cr) := by
        simp only [comps, if_neg hau, List.mem_append, List.mem_cons, true_or]
      have haC : ∀ d ∈ comps u a, d ∈ comps u (psi a (app B (psi t w rr)) Cr) := by
        intro d hd
        simp only [comps, if_neg hau, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr (Or.inr hd))
      have hBC : ∀ d ∈ comps u B, d ∈ comps u (psi a (app B (psi t w rr)) Cr) := by
        intro d hd; apply hmemC; rw [comps_app]; exact List.mem_append_left _ hd
      have htC : ∀ d ∈ comps u t, d ∈ comps u (psi a (app B (psi t w rr)) Cr) := by
        intro d hd; apply hmemC; rw [comps_app]
        apply List.mem_append_right
        simp only [comps, if_neg htu, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr (Or.inr hd))
      have hs'dom : ∀ d ∈ comps u s', ∃ f ∈ comps u (psi a (app B (psi t w rr)) Cr) ++ Gc u z, d ≤ f := by
        intro d hd
        rcases (le_iff _ _).mp hts' with hlt | heq
        · rcases hs with heq' | hl
          · exfalso; rw [heq'] at hlt; exact absurd (lt_of_lt_of_le hlt hts) (lt_irrefl' _)
          · obtain ⟨f, hf, hdf⟩ := hl.2 u t hlt hts d hd
            rcases List.mem_append.mp hf with hf | hf
            · exact ⟨f, List.mem_append_left _ (htC f hf), hdf⟩
            · exact ⟨f, List.mem_append_right _ hf, hdf⟩
        · rw [heq] at hd
          exact ⟨d, List.mem_append_left _ (htC d hd), le_refl _⟩
      intro e he
      simp only [comps, if_neg hau, List.mem_append, List.mem_cons, comps, List.not_mem_nil,
        or_false] at he
      rcases he with (rfl | he | he)
      · exact ⟨_, List.mem_append_left _ hCC, hXC⟩
      · rcases hdom u hau e he with h | ⟨d, hd, hed⟩
        · exact ⟨_, List.mem_append_left _ hCC, le_trans h hXC⟩
        · rcases List.mem_append.mp hd with hd | hd
          · rcases List.mem_append.mp hd with hd | hd
            · exact ⟨d, List.mem_append_left _ (hBC d hd), hed⟩
            · exact ⟨d, List.mem_append_left _ (haC d hd), hed⟩
          · obtain ⟨f, hf, hdf⟩ := hs'dom d hd
            exact ⟨f, hf, le_trans hed hdf⟩
      · exact ⟨e, List.mem_append_left _ (haC e he), le_refl _⟩

end Ytosk
