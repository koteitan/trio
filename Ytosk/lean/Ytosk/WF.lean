/-
**拡張 Buchholz の標準形の整礎性。**

`wf_OT`: 標準形の項の上の辞書式順序 `<` は整礎。順序数への評価は使わない。
設計は `Ytosk/wf.md`（補題 10〜13 と定理）。
-/
import Ytosk.Dist

namespace Ytosk

open T

/-- `γ ≺ η`: the target of the collapse `γ = ψ_ν(b)` (`b ≠ 0`) is `η = Ω_{ν+1}`. -/
def Prec (γ η : T) : Prop := ∃ ν b, b ≠ z ∧ γ = psi ν b z ∧ η = Om (succ ν)

theorem HW : ∀ γ, W γ → C γ W γ := fun _ h => D_C_self D_W h

theorem one_eq_om : one = Om z := rfl

/-- Lemma 10 (the key lemma). -/
theorem key {η : T} (hG : G W η) (hprec : ∀ γ, Prec γ η → G W γ → W γ) : W η := by
  have h14 : cond14 W η := by
    intro β _ hWb hpl
    have hpη : plus β ≤ η := plus_le_of_plus_lt hpl
    have main : ∀ t, Acc (R (C β W)) t → C β W t → t < plus β → W t := by
      intro t hacc
      induction hacc with
      | intro t _ ih =>
        intro hC htp
        have IH : ∀ s, C β W s → s < t → W s :=
          fun s hs hst => ih s ⟨hs, hst⟩ hs (lt_trans hst htp)
        by_cases hle : ∃ δ, W δ ∧ δ < plus η ∧ t ≤ δ
        · obtain ⟨δ, hδ, hδη, htδ⟩ := hle
          have hδβ : δ < β := hWb δ hδ hδη
          have hCδ : C δ W t := C_down HW (le_of_lt hδβ) hC
          have hwp : WP (C δ W) t := WP_le (D_WP_self D_W hδ) hCδ htδ
          exact (D_W.2 δ (D_W.1 δ hδ) ⟨δ, hδ, le_refl δ⟩ t
            (lt_of_le_of_lt htδ (lt_plus_self δ))).mp hwp
        · have h18 : ∀ δ, W δ → δ < plus η → δ < t := by
            intro δ hδ hδη
            rcases lt_or_ge δ t with h | h
            · exact h
            · exact absurd ⟨δ, hδ, hδη, h⟩ hle
          have htη : t < η := lt_of_lt_of_le htp hpη
          have key2 : ∀ t', C β W t' → t' = t → W t := by
            intro t' hC' he
            cases hC' with
            | zero => subst he; exact zero_W
            | base hb _ _ => exact he ▸ hb
            | sum h1 h2 hx hy hot =>
              subst he
              exact D_sum D_W (IH _ h1 (lt_app_left hx hy)) (IH _ h2 (lt_app_right hot hx)) hx hy
                hot
            | @om ν hν =>
              subst he
              have hWν : W ν := IH ν hν (sub_lt_om ν)
              exact hG.2.2 _ (C.om (D_C D_W hWν η)) htη
            | @col ν b hν hb hbz hl hot =>
              subst he
              have hνle : ν ≤ lev β := by simpa using lt_plus_iff.mp htp
              have hνeq : ν = lev β := le_antisymm hνle hl
              have hl1 : lev β = lev (psi ν b z) := by simp [hνeq]
              have hGt : G W (psi ν b z) := by
                refine ⟨hot, C_level_eq HW hl1 (C.col hν hb hbz hl hot), ?_⟩
                intro s hs hst
                exact IH s (C_level_eq HW hl1.symm hs) hst
              have hpβ : plus β = Om (succ ν) := by simp [plus, hνeq]
              rcases (le_iff _ _).mp hpη with hlt | heq
              · exfalso
                have hWν : W ν := IH ν hν (sub_lt ν b z)
                have hsucc : C η W (succ ν) := by
                  by_cases hν0 : ν = z
                  · subst hν0; exact (C.om C.zero : C η W (Om z))
                  · exact C.sum (D_C D_W hWν η) (C.om C.zero : C η W (Om z)) hν0 (by simp [one])
                      (isOT_succ (D_W.1 ν hWν))
                have hWo : W (Om (succ ν)) := hG.2.2 _ (C.om hsucc) (hpβ ▸ hlt)
                have h1 : Om (succ ν) < psi ν b z := h18 _ hWo (hpβ ▸ hpl)
                have h2 : psi ν b z < Om (succ ν) := by
                  rw [Om, T.psi_lt_psi]; exact Or.inl (lt_succ_self ν)
                exact lt_irrefl _ (lt_trans h1 h2)
              · exact hprec _ ⟨ν, b, hbz, rfl, by rw [← heq, hpβ]⟩ hGt
          exact key2 t hC rfl
    intro t hwp htp
    exact main t hwp.2 hwp.1 htp
  obtain ⟨h1, h2⟩ := L315 D_W hG h14
  exact ⟨_, h2, h1⟩

/-- Lemma 11: `G(W) ⊆ W`. -/
theorem G_W {η : T} (hG : G W η) : W η := by
  apply key hG
  rintro γ ⟨ν, b, hb, rfl, _⟩ hGγ
  apply key hGγ
  rintro δ ⟨ν', b', _, _, h⟩ _
  simp only [Om, psi.injEq] at h
  exact absurd h.2.1 hb

/-- Lemma 12: `W` is closed under `σ ↦ Ω_σ`. -/
theorem om_W : ∀ σ, W σ → W (Om σ) := by
  have : ∀ σ, Acc (R W) σ → W σ → W (Om σ) := by
    intro σ hacc
    induction hacc with
    | intro σ _ ih =>
      intro hσ
      apply G_W
      refine ⟨isOT_om.mpr (D_W.1 σ hσ), C.om (D_C D_W hσ _), ?_⟩
      have sz : ∀ n s, size s < n → C (Om σ) W s → s < Om σ → W s := by
        intro n
        induction n with
        | zero => intro s h; exact absurd h (Nat.not_lt_zero _)
        | succ n ihn =>
          intro s hs hC hlt
          have key2 : ∀ s', C (Om σ) W s' → s' = s → W s := by
            intro s' hC' he
            cases hC' with
            | zero => subst he; exact zero_W
            | base hb _ _ => exact he ▸ hb
            | @sum x y h1 h2 hx hy hot =>
              subst he
              have hxl : x < app x y := lt_app_left hx hy
              have hyl : y < app x y := lt_app_right hot hx
              exact D_sum D_W
                (ihn x (by have := size_lt_app_left (x := x) hy; omega) h1 (lt_trans hxl hlt))
                (ihn y (by have := size_lt_app_right (y := y) hx; omega) h2 (lt_trans hyl hlt))
                hx hy hot
            | @om μ hμ =>
              subst he
              have hμσ : μ < σ := om_lt_om.mp hlt
              have hWμ : W μ := ihn μ (by have := size_sub_lt μ z z; simp only [Om] at hs; omega)
                hμ (lt_trans (sub_lt_om μ) hlt)
              exact ih μ ⟨hWμ, hμσ⟩ hWμ
            | @col ν b _ _ hbz hl _ =>
              subst he
              exfalso
              rw [Om, T.psi_lt_psi] at hlt
              simp only [lev, Om] at hl
              rcases hlt with h | ⟨_, h⟩ | ⟨_, h, _⟩
              · exact absurd h (not_lt_of_ge hl)
              · exact absurd h (T.not_lt_z _)
              · exact hbz h
          exact key2 s hC rfl
      exact fun s hs hlt => sz (size s + 1) s (Nat.lt_succ_self _) hs hlt
  exact fun σ hσ => this σ (W_wf hσ) hσ

/-- Lemma 13: `W` is closed under the collapses. -/
theorem psi_W : ∀ a, W a → ∀ σ, W σ → isOT (psi σ a z) = true → W (psi σ a z) := by
  have : ∀ a, Acc (R W) a → W a → ∀ σ, W σ → isOT (psi σ a z) = true → W (psi σ a z) := by
    intro a hacc
    induction hacc with
    | intro a _ ih =>
      intro ha σ hσ hot
      have MIH : ∀ b, W b → b < a → ∀ τ, W τ → isOT (psi τ b z) = true → W (psi τ b z) :=
        fun b hb hba τ hτ hot' => ih b ⟨hb, hba⟩ hb τ hτ hot'
      by_cases ha0 : a = z
      · subst ha0; exact om_W σ hσ
      have hza : z < a := by
        cases a with
        | z => exact absurd rfl ha0
        | psi => exact T.z_lt_psi _ _ _
      have omW : ∀ μ, W μ → W (Om μ) :=
        fun μ hμ => MIH z zero_W hza μ hμ (isOT_om.mpr (D_W.1 μ hμ))
      apply G_W
      refine ⟨hot, C.col (D_C D_W hσ _) (D_C D_W ha _) ha0 (by simp) hot, ?_⟩
      have sz : ∀ n s, size s < n → C (psi σ a z) W s → s < psi σ a z → W s := by
        intro n
        induction n with
        | zero => intro s h; exact absurd h (Nat.not_lt_zero _)
        | succ n ihn =>
          intro s hs hC hlt
          have key2 : ∀ s', C (psi σ a z) W s' → s' = s → W s := by
            intro s' hC' he
            cases hC' with
            | zero => subst he; exact zero_W
            | base hb _ _ => exact he ▸ hb
            | @sum x y h1 h2 hx hy hot' =>
              subst he
              have hxl : x < app x y := lt_app_left hx hy
              have hyl : y < app x y := lt_app_right hot' hx
              exact D_sum D_W
                (ihn x (by have := size_lt_app_left (x := x) hy; omega) h1 (lt_trans hxl hlt))
                (ihn y (by have := size_lt_app_right (y := y) hx; omega) h2 (lt_trans hyl hlt))
                hx hy hot'
            | @om μ hμ =>
              subst he
              have hWμ : W μ := ihn μ (by have := size_sub_lt μ z z; simp only [Om] at hs; omega)
                hμ (lt_trans (sub_lt_om μ) hlt)
              exact omW μ hWμ
            | @col π b hπ hb hbz hl hot' =>
              subst he
              simp only [lev] at hl
              have hπσ : π = σ ∧ b < a := by
                rw [psi_lt_psi_z_iff] at hlt
                rcases hlt with h | h
                · exact absurd h (not_lt_of_ge hl)
                · exact h
              obtain ⟨rfl, hba⟩ := hπσ
              -- the parts of `b` reached through levels `≥ π` are in `W`
              have inner : ∀ m b', size b' < m → size b' < size (psi π b z) →
                  C (psi π a z) W b' → (∀ g ∈ comps π b', g < a) → W b' := by
                intro m
                induction m with
                | zero => intro b' h; exact absurd h (Nat.not_lt_zero _)
                | succ m ihm =>
                  intro b' hbm hbs hCb hcomp
                  rcases lt_or_ge b' (psi π a z) with hlt' | hge
                  · exact ihn b' (by omega) hCb hlt'
                  · have key3 : ∀ u, C (psi π a z) W u → u = b' → W b' := by
                      intro u hu hue
                      cases hu with
                      | zero => subst hue; exact zero_W
                      | base _ hlt'' _ => subst hue; exact absurd hlt'' (not_lt_of_ge hge)
                      | @sum x y h1 h2 hx hy hot'' =>
                        subst hue
                        rw [comps_app] at hcomp
                        have sx := size_lt_app_left (x := x) hy
                        have sy := size_lt_app_right (y := y) hx
                        exact D_sum D_W
                          (ihm x (by omega) (by omega) h1
                            (fun g hg => hcomp g (List.mem_append_left _ hg)))
                          (ihm y (by omega) (by omega) h2
                            (fun g hg => hcomp g (List.mem_append_right _ hg)))
                          hx hy hot''
                      | @om μ hμ =>
                        subst hue
                        have hnμ : ¬ μ < π := by
                          intro h
                          apply not_lt_of_ge hge
                          rw [Om, psi_lt_psi_z_iff]; exact Or.inl h
                        have hc : ∀ g ∈ comps π μ, g < a := by
                          intro g hg
                          apply hcomp g
                          rw [Om, comps_psi_z_of_ge hnμ]
                          exact List.mem_cons_of_mem _ (List.mem_append_right _ hg)
                        have sμ := size_sub_lt μ z z
                        simp only [Om] at hbm hbs
                        exact omW μ (ihm μ (by omega) (by omega) hμ hc)
                      | @col τ c hτ hc hcz hl' hot'' =>
                        subst hue
                        simp only [lev] at hl'
                        have hnτ : ¬ τ < π := not_lt_of_ge hl'
                        rw [comps_psi_z_of_ge hnτ] at hcomp
                        have hca : c < a := hcomp c List.mem_cons_self
                        have st := size_sub_lt τ c z
                        have sc := size_arg_lt τ c z
                        have hWτ : W τ := ihm τ (by omega) (by omega) hτ
                          (fun g hg => hcomp g (List.mem_cons_of_mem _
                            (List.mem_append_right _ hg)))
                        have hWc : W c := ihm c (by omega) (by omega) hc
                          (fun g hg => hcomp g (List.mem_cons_of_mem _
                            (List.mem_append_left _ hg)))
                        exact MIH c hWc hca τ hWτ hot''
                    exact key3 b' hCb rfl
              have hWb : W b := inner (size b + 1) b (Nat.lt_succ_self _) (size_arg_lt _ _ _) hb
                (fun g hg => lt_trans (comps_lt hot' g hg) hba)
              exact MIH b hWb hba π hσ hot'
          exact key2 s hC rfl
      exact fun s hs hlt => sz (size s + 1) s (Nat.lt_succ_self _) hs hlt
  exact fun a ha => this a (W_wf ha) ha

/-- Every standard term is in `W`. -/
theorem OT_W : ∀ t, isOT t = true → W t
  | z, _ => zero_W
  | psi a b c, h => by
    have ha := OT_W a (isOT_sub h)
    have hb := OT_W b (isOT_arg h)
    have hc := OT_W c (isOT_rest h)
    have hhead : W (psi a b z) := psi_W b hb a ha (isOT_head h)
    by_cases hc0 : c = z
    · subst hc0; exact hhead
    · exact D_sum D_W hhead hc (by simp) hc0 (by simpa using h)

/-- **Theorem.** The lexicographic order on the standard extended Buchholz terms is well-founded. -/
theorem wf_OT : WellFounded (fun s t : T => isOT s = true ∧ isOT t = true ∧ s < t) := by
  constructor
  intro t
  by_cases ht : isOT t = true
  · exact Subrelation.accessible (fun {s _} h => ⟨OT_W s h.1, h.2.2⟩) (W_wf (OT_W t ht))
  · constructor
    rintro s ⟨_, hto, _⟩
    exact absurd hto ht

end Ytosk
