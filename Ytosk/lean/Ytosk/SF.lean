/-
**標準形化 `sf` は標準形の上で恒等（`sf_ot`）。**

鍵は `sp` の書き換えの段: 標準形の引数 b = P + ψ_s(y) + … で P < y なら、P はちょうど y の Ω_{s+1} 以上の部分になる。
そうでないと P のある加数 p = ψ_s(y″) について y″ = P + d″ となり、p が自分を真の部分項として含んでしまう（大きさで矛盾）。
-/
import Ytosk.Arith

namespace Ytosk

open T

/-! ## 連結としての和 -/

theorem head_le_of_app : ∀ {P x : T}, isOT (app P x) = true → P ≠ z → head x ≤ head P
  | z, _, _, hP => absurd rfl hP
  | psi a b c, x, h, _ => by
    rw [app_psi, isOT_psi_iff] at h
    obtain ⟨_, _, h3, h4, _⟩ := h
    by_cases hc : c = z
    · subst hc; simpa [head] using h4
    · have ih := head_le_of_app h3 hc
      rw [head_app_of_ne x hc] at h4
      exact le_trans ih h4

/-- A standard concatenation is the sum. -/
theorem add_eq_app : ∀ {P x : T}, isOT (app P x) = true → add P x = app P x
  | z, x, _ => by simp
  | psi a b c, x, h => by
    cases x with
    | z => simp
    | psi d e f =>
      have hx : head (psi d e f) ≤ head (psi a b c) := head_le_of_app h (by simp)
      simp only [head] at hx
      rw [add_psi_psi, if_neg (not_lt_of_ge hx), app_psi]
      rw [app_psi] at h
      rw [add_eq_app (isOT_rest h)]

theorem add_one_eq_succ {s : T} (hs : isOT s = true) : add s one = succ s :=
  add_eq_app (isOT_succ hs)

/-! ## 切り取り `cut` -/

/-- Every summand is at least `Ω_w`. -/
def AllGe (w : T) : T → Prop
  | z => True
  | psi s b c => ¬ (psi s b z < Om w) ∧ AllGe w c

/-- Every summand is below `Ω_w`. -/
def AllLt (w : T) : T → Prop
  | z => True
  | psi s b c => psi s b z < Om w ∧ AllLt w c

theorem cut_allLt {w : T} : ∀ {d : T}, AllLt w d → cut w d = z
  | z, _ => rfl
  | psi s b c, ⟨h1, h2⟩ => by
    have ih := cut_allLt h2
    simp only [cut, ih, true_and]
    exact if_pos h1

theorem cut_app {w d : T} (hd : AllLt w d) : ∀ {P : T}, AllGe w P → cut w (app P d) = P
  | z, _ => by simpa using cut_allLt hd
  | psi s b c, ⟨h1, h2⟩ => by
    have ih := cut_app hd h2
    simp only [app_psi, cut, ih]
    have : ¬ (c = z ∧ lt (psi s b z) (psi w z z) = true) := fun h => h1 h.2
    rw [if_neg this]

theorem allLt_of_head {w : T} : ∀ {d : T}, isOT d = true → head d < Om w → AllLt w d
  | z, _, _ => trivial
  | psi s b c, h, hh => by
    refine ⟨by simpa [head] using hh, ?_⟩
    by_cases hc : c = z
    · subst hc; trivial
    · have h4 := (isOT_psi_iff.mp h).2.2.2.1
      exact allLt_of_head (isOT_rest h) (lt_of_le_of_lt h4 (by simpa [head] using hh))

/-! ## 加数 -/

/-- The principal summands. -/
def summands : T → List T
  | z => []
  | psi s b c => psi s b z :: summands c

theorem summand_ge_of_app : ∀ {P x p : T}, isOT (app P x) = true → p ∈ summands P → head x ≤ p
  | z, _, _, _, h => by simp [summands] at h
  | psi a b c, x, p, h, hp => by
    simp only [summands, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simpa [head] using head_le_of_app h (by simp)
    · rw [app_psi] at h
      exact summand_ge_of_app (isOT_rest h) hp

theorem size_summand_le : ∀ {P p : T}, p ∈ summands P → size p ≤ size P
  | z, _, h => by simp [summands] at h
  | psi a b c, p, hp => by
    simp only [summands, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp [size]
    · have := size_summand_le hp; simp [size]; omega

theorem comps_of_summand {a : T} : ∀ {P s y : T}, psi s y z ∈ summands P → ¬ s < a →
    y ∈ comps a P
  | z, _, _, h, _ => by simp [summands] at h
  | psi s' b' c, s, y, hp, hs => by
    simp only [summands, List.mem_cons] at hp
    simp only [comps]
    rcases hp with h | hp
    · simp only [psi.injEq, and_true] at h
      obtain ⟨rfl, rfl⟩ := h
      have : lt s a = false := by simpa [lt_iff_lt] using hs
      simp [this]
    · exact List.mem_append_right _ (comps_of_summand hp hs)

theorem mem_summands : ∀ {P p : T}, p ∈ summands P → ∃ s y, p = psi s y z
  | z, _, h => by simp [summands] at h
  | psi a b c, p, hp => by
    simp only [summands, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨a, b, rfl⟩
    · exact mem_summands hp

theorem allGe_of_summands {w : T} : ∀ {P : T}, (∀ p ∈ summands P, ¬ p < Om w) → AllGe w P
  | z, _ => trivial
  | psi a b c, h => ⟨h _ (by simp [summands]),
      allGe_of_summands (fun p hp => h p (by simp [summands, hp]))⟩

/-! ## `sp` の折りたたみ -/

/-- In a standard argument `P + ψ_s(y) + c'` with `P < y`, every summand of `P` is `≥ Ω_{s+1}`. -/
theorem allGe_prefix {a P s y c' : T} (hb : isOT (psi a (app P (psi s y c')) z) = true)
    (hP : P ≠ z) (hs : ¬ s < a) (hPy : P < y) : AllGe (succ s) P := by
  have hot := isOT_arg hb
  have hcomp := comps_lt hb
  apply allGe_of_summands
  intro p hp hlt
  obtain ⟨s', y'', rfl⟩ := mem_summands hp
  have hge : psi s y z ≤ psi s' y'' z := by simpa [head] using summand_ge_of_app hot hp
  have hs'le : s' ≤ s := by
    have : s' < succ s := by
      rw [Om, T.psi_lt_psi] at hlt
      rcases hlt with h | ⟨_, h⟩ | ⟨_, _, h⟩
      · exact h
      · exact absurd h (T.not_lt_z _)
      · exact absurd h (T.not_lt_z _)
    exact lt_succ_iff.mp this
  have hyy : s' = s ∧ y ≤ y'' := by
    rcases (le_iff _ _).mp hge with h | h
    · rw [psi_lt_psi_z_iff] at h
      rcases h with h | ⟨rfl, h⟩
      · exact absurd h (not_lt_of_ge hs'le)
      · exact ⟨rfl, le_of_lt h⟩
    · simp only [psi.injEq, and_true] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, le_refl _⟩
  obtain ⟨rfl, hyy⟩ := hyy
  have hin : y'' ∈ comps a (app P (psi s' y c')) := by
    rw [comps_app]; exact List.mem_append_left _ (comps_of_summand hp hs)
  have hlt2 : y'' < app P (psi s' y c') := hcomp y'' hin
  obtain ⟨d, hd, _⟩ := decomp hP (lt_of_lt_of_le hPy hyy) hlt2
  have h1 := size_summand_le hp
  have h2 : size y'' = size P + size d := by rw [hd, size_app]
  simp only [size] at h1
  omega

/-- The fold of `sp` over a standard argument `P + c` reproduces it. -/
theorem sp_fold {a : T} : ∀ (c P : T), isOT (psi a (app P c) z) = true → sp a P c = psi a (app P c) z
  | z, P, _ => by simp [sp]
  | psi s y c', P, hb => by
    have hot := isOT_arg hb
    have hpre : isOT (app P (psi s y z)) = true := by
      have : app P (psi s y c') = app (app P (psi s y z)) c' := by rw [app_assoc]; simp
      rw [this] at hot; exact isOT_app_left hot
    have hnext : isOT (psi a (app (app P (psi s y z)) c') z) = true := by
      have : app (app P (psi s y z)) c' = app P (psi s y c') := by rw [app_assoc]; simp
      rw [this]; exact hb
    have ih := sp_fold c' (app P (psi s y z)) hnext
    have happ : app (app P (psi s y z)) c' = app P (psi s y c') := by rw [app_assoc]; simp
    simp only [sp]
    split
    · rename_i htrig
      obtain ⟨hPy, hΩ⟩ := htrig
      have hPy' : P < y := hPy
      have hs : ¬ s < a := by
        intro hsa
        have : psi a z z < psi s y c' := hΩ
        rw [T.psi_lt_psi] at this
        rcases this with h | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
        · exact lt_asymm h hsa
        · exact lt_irrefl _ hsa
        · exact lt_irrefl _ hsa
      have hsot : isOT s = true := by
        have := isOT_head (isOT_app_right hot); exact isOT_sub this
      have hyot : isOT y = true := by
        have := isOT_head (isOT_app_right hot); exact isOT_arg this
      have hcomp := comps_lt hb
      have hyb : y < app P (psi s y c') := by
        apply hcomp y; rw [comps_app]
        apply List.mem_append_right
        rw [comps, if_neg (by simpa [lt_iff_lt] using hs)]
        simp
      -- the low part of `y` is below `Ω_{s+1}`
      have hlow : ∀ d, y = app P d → d < psi s y c' → cut (add s one) y = P := by
        intro d hd hdlt
        rw [add_one_eq_succ hsot]
        by_cases hP : P = z
        · subst hP
          simp only [app_z] at hd; subst hd
          apply cut_allLt
          apply allLt_of_head hyot
          have h1 : head y ≤ psi s y z := by
            have := head_le_of_lt hdlt; simpa [head] using this
          exact lt_of_le_of_lt h1 (by rw [Om, psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self s))
        · rw [hd]
          apply cut_app _ (allGe_prefix hb hP hs hPy')
          have hdot : isOT d = true := by rw [hd] at hyot; exact isOT_app_right hyot
          apply allLt_of_head hdot
          have h1 : head d ≤ psi s y z := by
            have := head_le_of_lt hdlt; simpa [head] using this
          exact lt_of_le_of_lt h1 (by rw [Om, psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self s))
      obtain ⟨d, hd, hdlt⟩ : ∃ d, y = app P d ∧ d < psi s y c' := by
        by_cases hP : P = z
        · subst hP; exact ⟨y, by simp, by simpa using hyb⟩
        · exact decomp hP hPy' hyb
      rw [hlow d hd hdlt]
      have hsub : sub (psi s y z) (psi s P z) = psi s y z := by
        simp only [sub]
        have : lt (psi s P z) (psi s y z) = true := by
          show psi s P z < psi s y z
          rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hPy'⟩
        rw [if_pos this]
      rw [hsub, add_eq_app hpre, ih, happ]
    · rw [add_eq_app hpre, ih, happ]

/-- **`sf` is the identity on standard terms.** -/
theorem sf_ot : ∀ {x : T}, isOT x = true → sf x = x
  | z, _ => rfl
  | psi a b c, h => by
    simp only [sf]
    rw [sf_ot (isOT_sub h), sf_ot (isOT_arg h), sf_ot (isOT_rest h)]
    have h1 : sp a z b = psi a b z := by
      have := sp_fold (a := a) b z (by simpa using isOT_head h); simpa using this
    rw [h1]
    have : app (psi a b z) c = psi a b c := by simp
    rw [← this]; exact add_eq_app (by rw [this]; exact h)

end Ytosk
