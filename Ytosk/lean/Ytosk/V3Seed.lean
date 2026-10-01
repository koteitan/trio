/-
**始点の条件の一般化**: σ ≤ b[0] の代わりに、種 0 の鎖 γ_k = gamS μ b 0 k で σ ≤ b[γ_k] かつ γ_k < ψ_μ(σ)
（3 行では Ω_{Ω_1}[0] = 1 のように添字がつぶれて σ ≤ b[0] が崩れる。実測で k ≤ 2）。
-/
import Ytosk.V3MainT1

namespace Ytosk

open T

theorem seedOK_of_lhd_gam {a b μ σ : T} (hot : isOT (psi a b z) = true) (hcb : cof b = .big μ)
    (hμ : ¬ lt μ a = true) (hsot : isOT (psi μ σ z) = true) (k : Nat) (hσ : σ ≤ fs b (gamS μ b z k)) (hγ : gamS μ b z k < psi μ σ z)
    (hl : Lhd z σ b) :
    SeedOK a b μ (psi μ σ z) := by
  have hbot : isOT b = true := isOT_arg hot
  have hcomp := comps_lt hot
  have hS0 := seedOK_z a b μ
  have hmono : fs b (gamS μ b z k) < fs b (psi μ σ z) := fs_mono hcb hγ
  have hσlt : σ < fs b (psi μ σ z) := lt_of_le_of_lt hσ hmono
  have hslt : psi μ σ z < psi (succ μ) z z := by
    rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ)
  have hval : ValidLt b (psi μ σ z) := by unfold ValidLt; rw [hcb]; exact hslt
  have hfsle : fs b (psi μ σ z) ≤ b := le_of_lt (fs_lt hval)
  have hge : psi μ z z ≤ psi μ σ z := by
    rw [le_iff]
    rcases (le_iff _ _).mp (z_le σ) with h4 | h4
    · left; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h4⟩
    · right; rw [← h4]
  -- the Denis node `ψ_a(b[0])` is standard
  have hd0 : isOT (psi a (fs b (gamS μ b z k)) z) = true := isOT_diag_seed hot hcb hμ hS0 k
  have hcd0 := comps_lt hd0
  refine ⟨hsot, hslt, ?_, ?_, ?_⟩
  · rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hσlt⟩
  · intro g hg
    simp only [comps, hμ, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    rcases hg with (rfl | hg | hg) | hg
    · exact hσlt
    · -- a component of `σ`: dominated by components of `b[0]`
      rcases (le_iff _ _).mp hσ with hlt | heq
      · obtain ⟨y, hy, hgy⟩ := hl.2 a (fs b (gamS μ b z k)) hlt (le_of_lt (fs_lt (by
          unfold ValidLt; rw [hcb]; exact gamS_lt_om hot hcb hμ hS0 k))) g hg
        rcases List.mem_append.mp hy with hy | hy
        · exact lt_of_le_of_lt hgy (lt_trans (hcd0 y hy) hmono)
        · simp [Gc, comps] at hy; subst hy
          exact lt_of_le_of_lt hgy (lt_of_le_of_lt (z_le _) hmono)
      · rw [heq] at hg; exact lt_trans (hcd0 g hg) hmono
    · have hgb : g ∈ comps a b := comps_mu hbot hcb hge hslt hfsle (le_refl b) hμ g hg
      have hgb' := hcomp g hgb
      by_contra hcon
      have hgy : g ∈ comps a g := comps_mu hbot hcb hge hslt (le_of_not_gt hcon) (le_of_lt hgb') hμ g hg
      exact Nat.lt_irrefl _ (size_comps hgy)
    · simp at hg
  · intro u c0 c1 h1 h2 hau g hg
    have hμu : ¬ lt μ u = true := fun h => hau (show a < u from lt_of_le_of_lt (le_of_not_gt hμ) h)
    have hin : ∀ w ∈ comps u c0, w ∈ comps u (psi a c0 c1) := fun w hw => mem_comps_psi_arg hau hw
    have hc0in : c0 ∈ comps u (psi a c0 c1) := by simp [comps, hau]
    simp only [comps, hμu, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons] at hg
    rcases hg with (rfl | hg | hg) | hg
    · exact ⟨c0, List.mem_append_left _ hc0in, le_of_lt (lt_trans hσlt h1)⟩
    · obtain ⟨y, hy, hgy⟩ := hl.2 u c0 (lt_trans hσlt h1) h2 g hg
      rcases List.mem_append.mp hy with hy | hy
      · exact ⟨y, List.mem_append_left _ (hin y hy), hgy⟩
      · exact ⟨y, List.mem_append_right _ (by simpa [Gc, comps] using hy), hgy⟩
    · have := comps_mu hbot hcb hge hslt (le_of_lt h1) h2 hμu g hg
      exact ⟨g, List.mem_append_left _ (hin g this), le_refl _⟩
    · simp at hg


/-- **The seed condition from the components** (3 行で実測で常に成立する形): every component of the seed at
a level `u ≤ a` is below `b[seed]` or at most a component of `b[0]`. The `dom` field goes through
`b[0] ◁ b` (`lhd_fs` with index `0`). -/
theorem seedOK_of_c2 {a b μ seed : T} (hot : isOT (psi a b z) = true) (hcb : cof b = .big μ)
    (hμ : ¬ lt μ a = true) (hsot : isOT seed = true) (hslt : seed < psi (succ μ) z z)
    (hnext : seed < psi μ (fs b seed) z)
    (hC2 : ∀ u, ¬ lt a u = true → ∀ g ∈ comps u seed, g < fs b seed ∨ ∃ y ∈ comps u (fs b z), g ≤ y) :
    SeedOK a b μ seed := by
  have hbot : isOT b = true := isOT_arg hot
  have hS0 := seedOK_z a b μ
  have hd0 : isOT (psi a (fs b z) z) = true := isOT_diag_seed hot hcb hμ hS0 0
  have hcd0 := comps_lt hd0
  have hV0 : ValidLt b z := by unfold ValidLt; rw [hcb]; exact T.z_lt_psi _ _ _
  have hl0 : Lhd z (fs b z) b := lhd_fs hbot hV0
  -- `b[0] ≤ b[seed]`
  have hle : fs b z ≤ fs b seed := by
    rcases (le_iff _ _).mp (z_le seed) with h | h
    · exact le_of_lt (fs_mono hcb h)
    · rw [← h]
  refine ⟨hsot, hslt, hnext, ?_, ?_⟩
  · intro g hg
    rcases hC2 a (lt_irrefl' a) g hg with h | ⟨y, hy, hgy⟩
    · exact h
    · exact lt_of_le_of_lt hgy (lt_of_lt_of_le (hcd0 y hy) hle)
  · intro u c0 c1 h1 h2 hau g hg
    have hc0in : c0 ∈ comps u (psi a c0 c1) := by simp [comps, hau]
    rcases hC2 u hau g hg with h | ⟨y0, hy0, hgy⟩
    · exact ⟨c0, List.mem_append_left _ hc0in, le_of_lt (lt_trans h h1)⟩
    · obtain ⟨y, hy, hy0y⟩ := hl0.2 u c0 (lt_of_le_of_lt hle h1) h2 y0 hy0
      rcases List.mem_append.mp hy with hy | hy
      · exact ⟨y, List.mem_append_left _ (mem_comps_psi_arg hau hy), le_trans hgy hy0y⟩
      · exact ⟨y, List.mem_append_right _ hy, le_trans hgy hy0y⟩

theorem comps_nil_of_lt : ∀ {c u : T}, isOT c = true → c < u → comps u c = []
  | z, _, _, _ => rfl
  | psi v x c, u, hot, h => by
    have hv : lt v u = true := lt_trans (sub_lt v x c) h
    have hc : c < u := lt_trans (rest_lt hot) h
    simp only [comps, hv, if_true, List.nil_append]
    exact comps_nil_of_lt (isOT_rest hot) hc

theorem comps_self : ∀ {t : T}, isOT t = true → comps t t = []
  | z, _ => rfl
  | psi v x c, hot => by
    have hv : lt v (psi v x c) = true := sub_lt v x c
    simp only [comps, hv, if_true, List.nil_append]
    exact comps_nil_of_lt (isOT_rest hot) (rest_lt hot)

/-- A term of cofinality `Ω_{μ+1}` is above `μ`. -/
theorem lt_of_cof_big : ∀ {t μ : T}, isOT t = true → cof t = .big μ → μ < t
  | z, _, _, h => by simp [cof] at h
  | psi a b (psi c d e), μ, hot, h => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    exact lt_trans (lt_of_cof_big (isOT_rest hot) h') (rest_lt hot)
  | psi a b z, μ, hot, h => by
    unfold cof at h
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h
      by_cases ha : a = z
      · rw [if_pos ha] at h; cases h
      · rw [if_neg ha] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs] at h
          have hμ : init a = μ := by cases h; rfl
          have hsa : succ μ = a := by rw [← hμ]; unfold succ; exact init_app_one hs
          rw [← hsa]; exact lt_trans (lt_succ_self μ) (sub_lt _ _ _)
        · rw [if_neg hs] at h
          exact lt_trans (lt_of_cof_big (isOT_sub hot) h) (sub_lt _ _ _)
    · rw [if_neg hb] at h
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h
        cases hcb : cof b with
        | big ν =>
          rw [hcb] at h; simp only at h
          by_cases hν : lt ν a = true
          · rw [if_pos hν] at h
            have : ν = μ := by cases h; rfl
            subst this
            exact lt_trans hν (sub_lt _ _ _)
          · rw [if_neg hν] at h; cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- **Below the diagonal**: if `σ < b` and every component of `σ` at level `μ` is below `ρ`, then
`σ < b[ψ_μ(ρ)]`. With `ρ = σ` and `ψ_μ(σ)` standard this is `SeedOK.lt_next`. -/
theorem lt_fs_psi {μ ρ : T} : ∀ {b : T}, isOT b = true → cof b = .big μ → ∀ {σ : T}, σ < b →
    (∀ g ∈ comps μ σ, g < ρ) → σ < fs b (psi μ ρ z)
  | z, _, h, _, _, _ => by simp [cof] at h
  | psi a b (psi c d e), hot, h, σ, hσ, hc => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    show σ < psi a b (fs (psi c d e) (psi μ ρ z))
    cases σ with
    | z => exact T.z_lt_psi _ _ _
    | psi s τ c' =>
      rw [T.psi_lt_psi] at hσ ⊢
      rcases hσ with h1 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · refine Or.inr (Or.inr ⟨h1, h2, lt_fs_psi (isOT_rest hot) h' h3 ?_⟩)
        intro g hg; apply hc; simp only [comps, List.mem_append]; exact Or.inr hg
  | psi a b z, hot, h, σ, hσ, hc => by
    unfold fs
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl]
      by_cases ha : a = z
      · subst ha; simp [cof] at h
      · rw [if_neg ha]
        have hcf : cof (psi a z z) = (if isSucc a then Cof.big (init a) else cof a) := by
          simp [cof, ha]
        rw [hcf] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs]
          rw [if_pos hs] at h
          have hμ : init a = μ := by cases h; rfl
          have hsa : succ μ = a := by rw [← hμ]; unfold succ; exact init_app_one hs
          cases σ with
          | z => exact T.z_lt_psi _ _ _
          | psi s τ c' =>
            rw [T.psi_lt_psi] at hσ
            have hsl : s < a := by
              rcases hσ with h1 | ⟨_, h2⟩ | ⟨_, h2, _⟩
              · exact h1
              · exact absurd h2 (T.not_lt_z _)
              · exact absurd h2 (by simp [lt] at *)
            rw [← hsa] at hsl
            rcases (le_iff _ _).mp (lt_succ_iff.mp hsl) with h1 | h1
            · rw [psi_lt_psi_z_iff]; exact Or.inl h1
            · subst h1
              rw [psi_lt_psi_z_iff]
              refine Or.inr ⟨rfl, hc τ ?_⟩
              simp only [comps, List.mem_append]
              left; rw [if_neg (show ¬ lt s s = true from lt_irrefl' s)]; exact List.mem_cons_self
        · rw [if_neg hs]
          rw [if_neg hs] at h
          cases σ with
          | z => exact T.z_lt_psi _ _ _
          | psi s τ c' =>
            rw [T.psi_lt_psi] at hσ
            have hsl : s < a := by
              rcases hσ with h1 | ⟨_, h2⟩ | ⟨_, h2, _⟩
              · exact h1
              · exact absurd h2 (T.not_lt_z _)
              · exact absurd h2 (by simp [lt] at *)
            rw [psi_lt_psi_z_iff]; left
            by_cases hsμ : lt s μ = true
            · -- `s < μ < a[ψ_μ(ρ)]`
              exact lt_trans hsμ (lt_fs_psi (isOT_sub hot) h (lt_of_cof_big (isOT_sub hot) h)
                (by rw [comps_self (isOT_cof_mu (isOT_sub hot) h)]; simp))
            · apply lt_fs_psi (isOT_sub hot) h hsl
              intro g hg; apply hc
              simp only [comps, hsμ, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons]
              exact Or.inl (Or.inr (Or.inr hg))
    · rw [if_neg hb]
      unfold cof at h
      rw [if_neg hb] at h
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h
        rw [if_neg hs]
        cases hcb : cof b with
        | big ν =>
          rw [hcb] at h; simp only at h ⊢
          by_cases hν : lt ν a = true
          · rw [if_pos hν] at h ⊢
            have hνμ : ν = μ := by cases h; rfl
            subst hνμ
            cases σ with
            | z => exact T.z_lt_psi _ _ _
            | psi s τ c' =>
              rw [T.psi_lt_psi] at hσ
              rw [psi_lt_psi_z_iff]
              rcases hσ with h1 | ⟨h1, h2⟩ | ⟨_, _, h3⟩
              · exact Or.inl h1
              · subst h1
                refine Or.inr ⟨rfl, lt_fs_psi (isOT_arg hot) hcb h2 ?_⟩
                intro g hg; apply hc
                have : ¬ lt s ν = true := by
                  intro h'; exact lt_irrefl' _ (lt_trans h' hν)
                simp only [comps, this, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons]
                exact Or.inl (Or.inr (Or.inl hg))
              · exact absurd h3 (T.not_lt_z _)
          · rw [if_neg hν] at h; cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- **The seed condition** for `ψ_μ(σ)` with `σ < b`: only C2 (the components) is left. -/
theorem seedOK_of_lt_c2 {a b μ σ : T} (hot : isOT (psi a b z) = true) (hcb : cof b = .big μ)
    (hμ : ¬ lt μ a = true) (hsot : isOT (psi μ σ z) = true) (hσb : σ < b)
    (hC2 : ∀ u, ¬ lt a u = true → ∀ g ∈ comps u (psi μ σ z),
      g < fs b (psi μ σ z) ∨ ∃ y ∈ comps u (fs b z), g ≤ y) :
    SeedOK a b μ (psi μ σ z) := by
  have hbot : isOT b = true := isOT_arg hot
  refine seedOK_of_c2 hot hcb hμ hsot ?_ ?_ hC2
  · rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ)
  · rw [psi_lt_psi_z_iff]
    exact Or.inr ⟨rfl, lt_fs_psi hbot hcb hσb (comps_lt hsot)⟩

end Ytosk
