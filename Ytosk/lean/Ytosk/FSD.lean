/-
**対角化の点に値を直接入れる基本列 fsD。**

fsD(t, ζ) は Ω 型の基本列を一番深い位置で取り、対角化の点（ψ_a(b)、cof b = Ω_{μ+1}、μ ≥ a）でも
γ 列を作らずに ψ_a(b[ζ]) とする。展開 M[n] の経路上の列の値は fsD(o_M(h), ζ) の形になる
（ζ は最初のコピーの根の値、`desc.md` の「経路上の節点での一様な関係」）。
ζ の条件 `DV` のもとで、fsD は標準形を保ち小さくなる（`fsD_ot_lt`）。
-/
import Ytosk.FS

namespace Ytosk

open T

/-- `t⟨ζ⟩`: the `Ω`-type fundamental sequence, with `ζ` plugged in at the diagonal point too. -/
def fsD : T → T → T
  | z, _ => z
  | psi a b (psi c d e), η => psi a b (fsD (psi c d e) η)
  | psi a b z, η =>
    if b = z then
      (if a = z then z else if isSucc a then η else psi (fsD a η) z z)
    else if isSucc b then mulT (psi a (init b) z) (count η)
    else match cof b with
      | .big _ => psi a (fs b η) z
      | _ => psi a (fsD b η) z

/-- The index `ζ` fits `t`: below the `Ω` it replaces, and its components above each collapsing
level on the way are below the new argument. -/
def DV : T → T → Prop
  | z, _ => False
  | psi _ _ (psi c d e), η => DV (psi c d e) η
  | psi a b z, η =>
    if b = z then (a ≠ z ∧ (if isSucc a then η < psi a z z else DV a η))
    else if isSucc b then False
    else match cof b with
      | .big μ => η < psi (succ μ) z z ∧ (fs b η ≠ z → ∀ g ∈ comps a η, g < fs b η)
      | _ => DV b η ∧ (fsD b η ≠ z → ∀ g ∈ comps a η, g < fsD b η)

theorem fsD_lt : ∀ {t η : T}, DV t η → fsD t η < t
  | z, η, h => by simp [DV] at h
  | psi a b (psi c d e), η, h => by
    have h' : DV (psi c d e) η := by simpa [DV] using h
    show psi a b (fsD (psi c d e) η) < psi a b (psi c d e)
    rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, fsD_lt h'⟩)
  | psi a b z, η, h => by
    unfold DV at h
    unfold fsD
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h ⊢
      obtain ⟨ha, h⟩ := h
      rw [if_neg ha]
      by_cases hs : isSucc a = true
      · rw [if_pos hs] at h ⊢; exact h
      · rw [if_neg hs] at h ⊢
        rw [psi_lt_psi_z_iff]; exact Or.inl (fsD_lt (t := a) h)
    · rw [if_neg hb] at h ⊢
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; exact absurd h id
      · rw [if_neg hs] at h ⊢
        cases hcb : cof b with
        | big μ =>
          rw [hcb] at h; simp only at h ⊢
          have h' : ValidLt b η := by unfold ValidLt; rw [hcb]; exact h.1
          rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, fs_lt h'⟩
        | zero =>
          rw [hcb] at h; simp only at h ⊢
          rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, fsD_lt h.1⟩
        | succ =>
          rw [hcb] at h; simp only at h ⊢
          rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, fsD_lt h.1⟩
        | omega =>
          rw [hcb] at h; simp only at h ⊢
          rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, fsD_lt h.1⟩

theorem lhd_fsD : ∀ {t η : T}, isOT t = true → DV t η → Lhd η (fsD t η) t
  | z, η, _, h => by simp [DV] at h
  | psi a b (psi c d e), η, hot, h => by
    have h' : DV (psi c d e) η := by simpa [DV] using h
    have := lhd_app (psi a b z) (lhd_fsD (isOT_rest hot) h')
    simpa using this
  | psi a b z, η, hot, h => by
    unfold DV at h
    unfold fsD
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h ⊢
      obtain ⟨ha, h⟩ := h
      rw [if_neg ha]
      by_cases hs : isSucc a = true
      · rw [if_pos hs] at h ⊢
        refine ⟨h, fun u c _ _ x hx => ⟨x, List.mem_append_right _ (List.mem_cons_of_mem _ hx), le_refl _⟩⟩
      · rw [if_neg hs] at h ⊢
        have ih := lhd_fsD (t := a) (isOT_sub hot) h
        refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inl ih.1, fun u c h1 h2 => ?_⟩
        obtain ⟨v, c0, c1, rfl, hv1, hv2⟩ := between_sub h1 h2
        intro x hx
        simp only [comps, List.mem_append] at hx
        rcases hx with hx | hx
        · split at hx
          · simp at hx
          · rename_i hau
            have hvu : ¬ lt v u = true := fun h => hau (lt_of_le_of_lt hv1 h)
            simp only [List.mem_cons, List.mem_append] at hx
            rcases hx with rfl | hx | hx
            · exact ⟨z, List.mem_append_right _ (List.mem_cons_self), le_refl _⟩
            · simp at hx
            · rcases (le_iff _ _).mp hv1 with hv1 | rfl
              · obtain ⟨y, hy, hxy⟩ := ih.2 u v hv1 hv2 x hx
                refine ⟨y, ?_, hxy⟩
                rcases List.mem_append.mp hy with hy | hy
                · exact List.mem_append_left _ (by simp [comps, hvu, hy])
                · exact List.mem_append_right _ hy
              · exact ⟨x, List.mem_append_left _ (by simp [comps, hvu, hx]), le_refl _⟩
        · simp at hx
    · rw [if_neg hb] at h ⊢
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; exact absurd h id
      · rw [if_neg hs] at h ⊢
        cases hcb : cof b with
        | big μ =>
          rw [hcb] at h; simp only at h ⊢
          have h' : ValidLt b η := by unfold ValidLt; rw [hcb]; exact h.1
          exact lhd_psi a (lhd_fs (isOT_arg hot) h')
        | zero =>
          rw [hcb] at h; simp only at h ⊢
          exact lhd_psi a (lhd_fsD (isOT_arg hot) h.1)
        | succ =>
          rw [hcb] at h; simp only at h ⊢
          exact lhd_psi a (lhd_fsD (isOT_arg hot) h.1)
        | omega =>
          rw [hcb] at h; simp only at h ⊢
          exact lhd_psi a (lhd_fsD (isOT_arg hot) h.1)

theorem isOT_fsD : ∀ {t η : T}, isOT t = true → isOT η = true → DV t η → isOT (fsD t η) = true
  | z, η, _, _, h => by simp [DV] at h
  | psi a b (psi c d e), η, hot, hηot, h => by
    have h' : DV (psi c d e) η := by simpa [DV] using h
    have ih := isOT_fsD (isOT_rest hot) hηot h'
    show isOT (psi a b (fsD (psi c d e) η)) = true
    obtain ⟨h1, h2, _, h4, h5⟩ := isOT_psi_iff.mp hot
    rw [isOT_psi_iff]
    exact ⟨h1, h2, ih, le_trans (head_le_of_lt (fsD_lt h')) h4, h5⟩
  | psi a b z, η, hot, hηot, h => by
    have hcomp := comps_lt hot
    unfold DV at h
    unfold fsD
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h ⊢
      obtain ⟨ha, h⟩ := h
      rw [if_neg ha]
      by_cases hs : isSucc a = true
      · rw [if_pos hs]; exact hηot
      · rw [if_neg hs] at h ⊢
        have ih := isOT_fsD (isOT_sub hot) hηot h
        rw [isOT_psi_iff]; exact ⟨ih, rfl, rfl, z_le _, by simp [comps]⟩
    · rw [if_neg hb] at h ⊢
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; exact absurd h id
      · rw [if_neg hs] at h ⊢
        have hbot := isOT_arg hot
        cases hcb : cof b with
        | big μ =>
          rw [hcb] at h; simp only at h ⊢
          have hv : Valid b η := ⟨hηot, by rw [hcb]; exact h.1⟩
          exact psi_ot_of_lhd (isOT_sub hot) (isOT_fs hbot hv) (lhd_fs hbot hv.lt) hcomp h.2
        | zero =>
          rw [hcb] at h; simp only at h ⊢
          exact psi_ot_of_lhd (isOT_sub hot) (isOT_fsD hbot hηot h.1) (lhd_fsD hbot h.1) hcomp h.2
        | succ =>
          rw [hcb] at h; simp only at h ⊢
          exact psi_ot_of_lhd (isOT_sub hot) (isOT_fsD hbot hηot h.1) (lhd_fsD hbot h.1) hcomp h.2
        | omega =>
          rw [hcb] at h; simp only at h ⊢
          exact psi_ot_of_lhd (isOT_sub hot) (isOT_fsD hbot hηot h.1) (lhd_fsD hbot h.1) hcomp h.2

/-- **`t⟨ζ⟩` is standard and smaller.** -/
theorem fsD_ot_lt {t η : T} (hot : isOT t = true) (hηot : isOT η = true) (hv : DV t η) :
    isOT (fsD t η) = true ∧ fsD t η < t := ⟨isOT_fsD hot hηot hv, fsD_lt hv⟩

end Ytosk
