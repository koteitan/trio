/-
**落とす補題: 枠 1 段（経路の仮定なし）。**

子の値が ◁ で下がる（c′ ◁ c）とき、親の値 ψ_a(step a B c′) ◁ ψ_a(step a B c)（`node_lhd`）。
`node_val` の経路の仮定を、次の 2 つの自然な仮定に置き換える。
- `SubSmall a s`: 添字 s の成分（段 ≤ a）は Ω_s 以下。
- M だけ書き換える枠（c は書き換え、c′ はしない）では B が段 ≤ a で閉じている（成分 ≤ B）。
どちらも外すと偽（`V3NodeLhd` の報告の反例: a = ω, B = ψ_{ω+1}(ψ_ω(Ω_{ω·2})), c = ψ_ω(Ω_{ω·2}),
c′ = ψ_ω(1) では ψ_a(B + c′) が標準形でない）。

場合分け:
- 書き換えなし同士: 引数どうしの ◁（`lhdE_step_nn'`）。
- 添字が下がる（s′ < s）: 子の ◁ を Ω_{s′+1} で使うと c′ の成分は Ω_{s′} 以下（`comps_le_of_lhd_om`）。
  c′ だけ書き換えは起きず、両方書き換えなら X′ = c′ で小さい道。
- 書き換えあり同士・添字が同じ: 高い部分が同じなら引数どうしの ◁。違えば X′ と X の間の C を
  ψ_s(C) か ψ_s(hi(y)) にして子の ◁ で押さえる（`PRel`、`lhdE_tt_same`）。
- c だけ書き換え: X′ = B + c′ の成分は B か c′ 以下（小さい道、`closed_tn`）。
-/
import Ytosk.V3DropV

namespace Ytosk

open T

/-- The components of the subscript `s` at the levels `≤ a` are at most `Ω_s`. -/
def SubSmall (a s : T) : Prop := ∀ u, ¬ lt a u = true → ∀ g ∈ comps u s, g ≤ psi s z z

/-- `X` is closed at the levels `≤ a`: its components there are at most `X`. -/
def Closed (a X : T) : Prop := ∀ u, ¬ lt a u = true → ∀ g ∈ comps u X, g ≤ X

/-- The relation of the arguments under `ψ_a`: the components of `X'` at the levels `≤ a` are dominated
in every `C ∈ (X', X]`. -/
def PRel (a X' X : T) : Prop :=
  X' ≤ X ∧ ∀ u, ¬ lt a u = true → ∀ C, X' < C → C ≤ X →
    ∀ g ∈ comps u X', ∃ d ∈ C :: comps u C, g ≤ d

/-- **The parent relation gives `◁` of the parents.** -/
theorem lhdE_psi_of_prel {a X' X : T} (h : PRel a X' X) : LhdE (psi a X' z) (psi a X z) := by
  rcases (le_iff _ _).mp h.1 with hlt | heq
  · right
    refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hlt⟩, fun u c h1 h2 => ?_⟩
    obtain ⟨c0, c1, rfl, hc1, hc2⟩ := between_psi h1 h2
    intro x hx
    simp only [comps, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · simp at hx
      · rename_i hau
        have hc0 : c0 ∈ comps u (psi a c0 c1) := by simp [comps, hau]
        simp only [List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · exact ⟨c0, List.mem_append_left _ hc0, hc1⟩
        · rcases (le_iff _ _).mp hc1 with hc1 | rfl
          · obtain ⟨d, hd, hxd⟩ := h.2 u hau c0 hc1 hc2 x hx
            refine ⟨d, List.mem_append_left _ ?_, hxd⟩
            simp only [List.mem_cons] at hd
            rcases hd with rfl | hd
            · exact hc0
            · simp [comps, hau, hd]
          · exact ⟨x, List.mem_append_left _ (by simp [comps, hau, hx]), le_refl _⟩
        · exact ⟨x, List.mem_append_left _ (by simp [comps, hau, hx]), le_refl _⟩
    · simp at hx
  · left; rw [heq]

theorem prel_small {a X' X : T} (hle : X' ≤ X) (hsm : Closed a X') : PRel a X' X :=
  ⟨hle, fun u hu C h1 _ g hg =>
    ⟨C, List.mem_cons_self .., le_of_lt (lt_of_le_of_lt (hsm u hu g hg) h1)⟩⟩

theorem lhdE_psi_closed {a X' X : T} (hle : X' ≤ X) (hsm : Closed a X') :
    LhdE (psi a X' z) (psi a X z) :=
  lhdE_psi_of_prel (prel_small hle hsm)

/-! ## 順序の小道具 -/

theorem psi_le_psi_z {x s y : T} (h : x ≤ s) : psi x z z ≤ psi s y z := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h))
  · rcases (le_iff _ _).mp (z_le y) with h | h
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h⟩))
    · rw [h]

theorem psi_le_psi_arg {s y' y : T} (h : y' ≤ y) : psi s y' z ≤ psi s y z := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h⟩))
  · exact le_refl _

theorem le_of_trig {a s y : T} (h : lt (psi a z z) (psi s y z) = true) : a ≤ s := by
  have h' : psi a z z < psi s y z := h
  rcases psi_lt_psi_z_iff.mp h' with h | ⟨rfl, _⟩
  · exact le_of_lt h
  · exact le_refl _

theorem not_lt_of_le_lev {a s u : T} (has : a ≤ s) (hu : ¬ lt a u = true) : ¬ lt s u = true := by
  intro h
  exact hu (lt_of_le_of_lt has h)

theorem ne_z_of_lt {B y : T} (h : lt B y = true) : y ≠ z := by
  rintro rfl; exact T.not_lt_z B h

/-- `P ++ L < Q` when `P < Q`, the summands of `Q` are `≥ θ` and `L` is below `θ`. -/
theorem app_lt_of_lt_hi {θ : T} : ∀ {P Q L : T}, P < Q → (∀ q ∈ summands Q, ¬ q < θ) →
    (L = z ∨ head L < θ) → app P L < Q
  | z, Q, L, hPQ, hQ, hL => by
    simp only [app_z]
    cases Q with
    | z => exact absurd hPQ (T.not_lt_z _)
    | psi d e f =>
      rcases hL with rfl | hL
      · exact T.z_lt_psi _ _ _
      · apply lt_of_head_lt
        have := hQ (psi d e z) (by simp [summands])
        exact lt_of_lt_of_le hL (not_lt.mp this)
  | psi a b c, z, L, hPQ, _, _ => absurd hPQ (T.not_lt_z _)
  | psi a b c, psi d e f, L, hPQ, hQ, hL => by
    simp only [app_psi]
    rw [T.psi_lt_psi] at hPQ ⊢
    rcases hPQ with h | ⟨h1, h⟩ | ⟨h1, h2, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h⟩)
    · exact Or.inr (Or.inr ⟨h1, h2,
        app_lt_of_lt_hi h (fun q hq => hQ q (by simp [summands, hq])) hL⟩)

/-- A principal term is at most `B ++ itself` when the summands of `B` are at least it. -/
theorem le_app_psi {s y : T} : ∀ {B : T}, (∀ q ∈ summands B, psi s y z ≤ q) →
    psi s y z ≤ app B (psi s y z)
  | z, _ => le_refl _
  | psi a b c, hB => by
    have h := hB (psi a b z) (by simp [summands])
    simp only [app_psi]
    rcases (le_iff _ _).mp h with h | h
    · rcases psi_lt_psi_z_iff.mp h with h | ⟨h1, h⟩
      · exact le_of_lt (T.psi_lt_psi.mpr (Or.inl h))
      · exact le_of_lt (T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨h1, h⟩)))
    · simp only [psi.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      refine le_of_lt (T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)))
      cases c with
      | z => exact T.z_lt_psi _ _ _
      | psi => exact T.z_lt_psi _ _ _

/-- The high part is at least `θ` when nonzero. -/
theorem le_hi {θ y : T} (h : (split y θ).1 ≠ z) : θ ≤ (split y θ).1 :=
  le_trans (not_lt.mp (split_fst_ge θ y _ (head_mem_summands h))) (head_le_self _)

/-- **`Ω_s ≤ H(s, y)`** for `y ≠ 0`. -/
theorem om_le_H {s y : T} (hc : isOT (psi s y z) = true) (hy : y ≠ z) : psi s z z ≤ H s y := by
  rw [H_eq hc]
  have hθ : psi s z z < psi (succ s) z z := psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s))
  by_cases hhi : (split y (psi (succ s) z z)).1 = z
  · have e := split_app (psi (succ s) z z) y
    rw [hhi, app_z] at e
    have hlo : (split y (psi (succ s) z z)).2 ≠ z := by rw [e]; exact hy
    rw [hhi, if_neg hlo, app_z]
    exact psi_le_psi_z (le_refl s)
  · exact le_trans (le_of_lt hθ) (le_trans (le_hi hhi) (le_app_self _ _))

/-- **`B ≤ hi(y)`** when `B < y` and the summands of `B` are at least `ψ_s(y)`. -/
theorem B_le_hi {B s y : T} (hc : isOT (psi s y z) = true) (hlt : B < y)
    (hB : ∀ q ∈ summands B, psi s y z ≤ q) : B ≤ (split y (psi (succ s) z z)).1 := by
  set hi := (split y (psi (succ s) z z)).1
  set lo := (split y (psi (succ s) z z)).2
  have e : app hi lo = y := split_app _ y
  rcases le_or_gt B hi with h | h
  · exact h
  · exfalso
    obtain ⟨w, hw, hwz, hwlo⟩ := between_app (A := hi) (x := z) (y := lo) (by rw [app_z_right]; exact h)
      (by rw [e]; exact le_of_lt hlt)
    have hwz' : w ≠ z := by rintro rfl; exact T.not_lt_z _ hwz
    have hlo : lo ≠ z := by rintro hl; rw [hl] at hwlo; exact hwz' (le_antisymm hwlo (z_le _))
    have hwc : w < psi s y z := lt_of_le_of_lt hwlo (split_lo_lt hc hlo)
    rcases head_lt_of_lt_principal hwc with h1 | h1
    · exact hwz' h1
    · have hmem : head w ∈ summands B := by
        rw [hw, summands_app]; exact List.mem_append_right _ (head_mem_summands hwz')
      exact absurd (hB _ hmem) (not_le.mpr h1)

/-! ## 添字が下がる場合 -/

/-- **Dropping the subscript**: if `ψ_{s'}(y') ◁ c` and `Ω_{s'+1} ≤ c`, the components of `ψ_{s'}(y')`
(at the levels `≤ a`) are at most `Ω_{s'}`. -/
theorem comps_le_of_lhd_om {a s' y' c : T} (hl : Lhd z (psi s' y' z) c)
    (hle : psi (succ s') z z ≤ c) (hsub : SubSmall a s') :
    ∀ u, ¬ lt a u = true → ∀ g ∈ comps u (psi s' y' z), g ≤ psi s' z z := by
  intro u hu g hg
  have h1 : psi s' y' z < psi (succ s') z z := psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s'))
  obtain ⟨w, hw, hgw⟩ := hl.2 u _ h1 hle g hg
  have hw' : w = z ∨ w ∈ comps u s' := by
    rcases List.mem_append.mp hw with hw | hw
    · simp only [comps, List.append_nil] at hw
      split at hw
      · simp at hw
      · simp only [List.mem_cons, List.nil_append] at hw
        rcases hw with rfl | hw
        · exact Or.inl rfl
        · rw [succ, comps_app] at hw
          rcases List.mem_append.mp hw with hw | hw
          · exact Or.inr hw
          · left
            simp only [one, comps, List.append_nil] at hw
            split at hw <;> simp_all
    · left; simpa [Gc, comps] using hw
  rcases hw' with rfl | hw'
  · exact le_trans hgw (z_le _)
  · exact le_trans hgw (hsub u hu w hw')

/-- With `s' < s`, the components of `c' ◁ ψ_s(y)` are at most `Ω_{s'}`, and `y' ≤ Ω_{s'}`. -/
theorem comps_le_of_sub_lt {a s' y' s y : T} (hl : Lhd z (psi s' y' z) (psi s y z)) (hss : s' < s)
    (hsub : SubSmall a s') :
    (∀ u, ¬ lt a u = true → ∀ g ∈ comps u (psi s' y' z), g ≤ psi s' z z) ∧ y' ≤ psi s' z z := by
  have h := comps_le_of_lhd_om hl (psi_le_psi_z (succ_le_of_lt hss)) hsub
  refine ⟨h, h z (T.not_lt_z a) y' ?_⟩
  rw [comps_psi_z_of_ge (T.not_lt_z s')]; exact List.mem_cons_self ..

/-- The child value is closed when its components are at most `Ω_{s'}`. -/
theorem closed_of_le_om {a s' y' : T}
    (h : ∀ u, ¬ lt a u = true → ∀ g ∈ comps u (psi s' y' z), g ≤ psi s' z z) :
    Closed a (psi s' y' z) :=
  fun u hu g hg => le_trans (h u hu g hg) (psi_le_psi_z (le_refl _))

/-- An argument below `Ω_{s'}` has no high part: `H(s', y') = ψ_{s'}(y')`. -/
theorem H_of_le_om {s' y' : T} (hc : isOT (psi s' y' z) = true) (hy : y' ≠ z)
    (hle : y' ≤ psi s' z z) : H s' y' = psi s' y' z := by
  rw [H_eq hc]
  have hhd : head y' < psi (succ s') z z :=
    lt_of_le_of_lt (le_trans (head_le_self y') hle) (psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s')))
  have h1 : (split y' (psi (succ s') z z)).1 = z := split_fst_of_head_lt hhd
  have e := split_app (psi (succ s') z z) y'
  rw [h1, app_z] at e
  rw [h1, e, if_neg hy, app_z]

/-! ## M だけ書き換える枠 -/

/-- **`c` rewrites, `c'` does not**: `X' = B + c'` is closed when `B` is. -/
theorem closed_tn {a B s' y' s y : T} (hl : Lhd z (psi s' y' z) (psi s y z))
    (hn' : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true))
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hB : ∀ q ∈ summands B, psi s y z ≤ q) (hBcl : Closed a B)
    (hsub : SubSmall a s) (hsub' : SubSmall a s') :
    Closed a (app B (psi s' y' z)) := by
  have has := le_of_trig ht.2
  have hcB : psi s' y' z ≤ app B (psi s' y' z) :=
    le_app_psi (fun q hq => le_trans (le_of_lt hl.1) (hB q hq))
  have hBX : B ≤ app B (psi s' y' z) := le_app_self _ _
  -- every component of `c'` is at most `B` or `c'`
  have hc' : ∀ u, ¬ lt a u = true → ∀ g ∈ comps u (psi s' y' z), g ≤ B ∨ g ≤ psi s' y' z := by
    intro u hu g hg
    rcases psi_lt_psi_z_iff.mp hl.1 with hss | ⟨rfl, hyy⟩
    · exact Or.inr (closed_of_le_om (comps_le_of_sub_lt hl hss hsub').1 u hu g hg)
    · have hsu : ¬ s' < u := not_lt_of_le_lev has hu
      rw [comps_psi_z_of_ge hsu] at hg
      simp only [List.mem_cons, List.mem_append] at hg
      have hom : psi s' z z ≤ psi s' y' z := psi_le_psi_arg (z_le _)
      rcases hg with rfl | hg | hg
      · -- `g = y'`
        by_cases hyz : g = z
        · subst hyz; exact Or.inl (z_le _)
        · have htr : lt (psi a z z) (psi s' g z) = true := by
            show psi a z z < psi s' g z
            rcases (le_iff _ _).mp has with h | rfl
            · exact psi_lt_psi_z_iff.mpr (Or.inl h)
            · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hyz)⟩)
          exact Or.inl (not_lt.mp (fun h => hn' ⟨h, htr⟩))
      · -- `g ∈ comps y'`
        by_cases hyz : y' = z
        · subst hyz; simp [comps] at hg
        · have htr : lt (psi a z z) (psi s' y' z) = true := by
            show psi a z z < psi s' y' z
            rcases (le_iff _ _).mp has with h | rfl
            · exact psi_lt_psi_z_iff.mpr (Or.inl h)
            · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hyz)⟩)
          have hyB : y' ≤ B := not_lt.mp (fun h => hn' ⟨h, htr⟩)
          rcases (le_iff _ _).mp hyB with hyB | rfl
          · have h1 : psi s' y' z < psi s' B z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hyB⟩)
            have h2 : psi s' B z ≤ psi s' y z := psi_le_psi_arg (le_of_lt ht.1)
            have hgc : g ∈ comps u (psi s' y' z) := by
              rw [comps_psi_z_of_ge hsu]; simp [hg]
            obtain ⟨w, hw, hgw⟩ := hl.2 u _ h1 h2 g hgc
            rw [List.mem_append, comps_psi_z_of_ge hsu] at hw
            simp only [Gc, comps, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
              at hw
            rcases hw with (rfl | hw | hw) | rfl
            · exact Or.inl hgw
            · exact Or.inl (le_trans hgw (hBcl u hu w hw))
            · exact Or.inr (le_trans hgw (le_trans (hsub' u hu w hw) hom))
            · exact Or.inl (le_trans hgw (z_le _))
          · exact Or.inl (hBcl u hu g hg)
      · exact Or.inr (le_trans (hsub' u hu g hg) hom)
  intro u hu g hg
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact le_trans (hBcl u hu g hg) hBX
  · rcases hc' u hu g hg with h | h
    · exact le_trans h hBX
    · exact le_trans h hcB

/-- In the frame where only `c` rewrites, `B + c' ≤ H(s, y)`. -/
theorem le_tn {a B s' y' s y : T} (hc : isOT (psi s y z) = true)
    (hl : psi s' y' z < psi s y z)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hB : ∀ q ∈ summands B, psi s y z ≤ q) :
    app B (psi s' y' z) ≤ H s y := by
  rw [H_eq hc]
  have hBhi := B_le_hi hc ht.1 hB
  have hss : s' ≤ s := by
    rcases psi_lt_psi_z_iff.mp hl with h | ⟨rfl, _⟩
    · exact le_of_lt h
    · exact le_refl _
  have hcθ : psi s' y' z < psi (succ s) z z :=
    psi_lt_psi_z_iff.mpr (Or.inl (lt_of_le_of_lt hss (lt_succ_self s)))
  rcases (le_iff _ _).mp hBhi with h | h
  · exact le_trans (le_of_lt (app_lt_of_lt_hi h (split_fst_ge _ y) (Or.inr (by simpa [head] using hcθ))))
      (le_app_self _ _)
  · have hlo : (split y (psi (succ s) z z)).2 ≠ z := by
      intro hlo
      have e := split_app (psi (succ s) z z) y
      rw [hlo, app_z_right, ← h] at e
      have := ht.1; rw [← e] at this; exact lt_irrefl' _ this
    rw [if_neg hlo, ← h]
    exact le_of_lt (app_lt_app_left B hl)

/-! ## 書き換えあり同士・添字が同じ -/

/-- **Both rewrite, same subscript.** -/
theorem lhdE_tt_same {a B s y' y : T} (hc' : isOT (psi s y' z) = true) (hc : isOT (psi s y z) = true)
    (hl : Lhd z (psi s y' z) (psi s y z))
    (ht' : lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hsub : SubSmall a s) :
    LhdE (psi a (step a B s y' z) z) (psi a (step a B s y z) z) := by
  have hOm := om_le_H hc' (ne_z_of_lt ht'.1)
  unfold step
  rw [if_pos ht', if_pos ht]
  rw [H_eq hc'] at hOm
  rw [H_eq hc', H_eq hc]
  have has := le_of_trig ht.2
  have hyy : y' < y := by
    rcases psi_lt_psi_z_iff.mp hl.1 with h | ⟨_, h⟩
    · exact absurd h (lt_irrefl' _)
    · exact h
  set θ := psi (succ s) z z with hθ
  have ey := split_app θ y
  have ey' := split_app θ y'
  set hi := (split y θ).1
  set lo := (split y θ).2
  set hi' := (split y' θ).1
  set lo' := (split y' θ).2
  have hcθ : head (psi s y' z) < θ := psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s))
  rcases split_mono θ hyy with hhi | ⟨hhi, hlo⟩
  · change hi' < hi at hhi
    apply lhdE_psi_of_prel
    set X' := app hi' (if lo' = z then z else psi s y' z)
    set X := app hi (if lo = z then z else psi s y z)
    have hy'X' : y' ≤ X' := by
      by_cases hl' : lo' = z
      · simp only [X', if_pos hl']; rw [← ey', hl']
      · simp only [X', if_neg hl']
        exact le_of_lt (lt_of_eq_of_lt ey'.symm (app_lt_app_left hi' (split_lo_lt hc' hl')))
    have hX'hi : X' < hi := by
      apply app_lt_of_lt_hi hhi (split_fst_ge θ y)
      split
      · exact Or.inl rfl
      · exact Or.inr hcθ
    have hy'hi : y' < hi := by
      rw [← ey']; exact app_lt_of_lt_hi hhi (split_fst_ge θ y) (split_snd_head θ y')
    have hhiy : hi ≤ y := by rw [← ey]; exact le_app_self _ _
    refine ⟨le_of_lt (lt_of_lt_of_le hX'hi (le_app_self _ _)), fun u hu C h1 h2 g hg => ?_⟩
    have hsu : ¬ s < u := not_lt_of_le_lev has hu
    have hCs : ∀ w ∈ comps u s, ∃ d ∈ C :: comps u C, w ≤ d := fun w hw =>
      ⟨C, List.mem_cons_self .., le_trans (hsub u hu w hw) (le_trans hOm (le_of_lt h1))⟩
    have key : ∀ g ∈ comps u y', ∃ d ∈ C :: comps u C, g ≤ d := by
      intro g hg
      have hgc : g ∈ comps u (psi s y' z) := by rw [comps_psi_z_of_ge hsu]; simp [hg]
      by_cases hChi : C ≤ hi
      · have h1' : psi s y' z < psi s C z :=
          psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt hy'X' h1⟩)
        obtain ⟨w, hw, hgw⟩ := hl.2 u _ h1' (psi_le_psi_arg (le_trans hChi hhiy)) g hgc
        rw [List.mem_append, comps_psi_z_of_ge hsu] at hw
        simp only [Gc, comps, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | hw | hw) | rfl
        · exact ⟨_, List.mem_cons_self .., hgw⟩
        · exact ⟨w, List.mem_cons_of_mem _ hw, hgw⟩
        · obtain ⟨d, hd, hwd⟩ := hCs w hw; exact ⟨d, hd, le_trans hgw hwd⟩
        · exact ⟨C, List.mem_cons_self .., le_trans hgw (z_le _)⟩
      · have hChi' : hi < C := lt_of_not_ge hChi
        have hlo : lo ≠ z := by
          intro hlo
          have : X = hi := by simp only [X, if_pos hlo, app_z_right]
          exact hChi (this ▸ h2)
        have h2' : C ≤ app hi (psi s y z) := by
          have : X = app hi (psi s y z) := by simp only [X, if_neg hlo]
          exact this ▸ h2
        obtain ⟨c0, hC, _, _⟩ := between_app (A := hi) (x := z) (by rw [app_z_right]; exact hChi') h2'
        have h1' : psi s y' z < psi s hi z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hy'hi⟩)
        obtain ⟨w, hw, hgw⟩ := hl.2 u _ h1' (psi_le_psi_arg hhiy) g hgc
        rw [List.mem_append, comps_psi_z_of_ge hsu] at hw
        simp only [Gc, comps, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | hw | hw) | rfl
        · exact ⟨C, List.mem_cons_self .., le_trans hgw (le_of_lt hChi')⟩
        · refine ⟨w, List.mem_cons_of_mem _ ?_, hgw⟩
          rw [hC, comps_app]; exact List.mem_append_left _ hw
        · obtain ⟨d, hd, hwd⟩ := hCs w hw; exact ⟨d, hd, le_trans hgw hwd⟩
        · exact ⟨C, List.mem_cons_self .., le_trans hgw (z_le _)⟩
    simp only [X'] at hg
    rw [comps_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · apply key
      rw [← ey', comps_app]; exact List.mem_append_left _ hg
    · split at hg
      · simp [comps] at hg
      · rw [comps_psi_z_of_ge hsu] at hg
        simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · exact ⟨C, List.mem_cons_self .., le_of_lt (lt_of_le_of_lt hy'X' h1)⟩
        · exact key g hg
        · exact hCs g hg
  · change hi' = hi at hhi
    change lo' < lo at hlo
    have hlo0 : lo ≠ z := by
      intro h; rw [h] at hlo; exact T.not_lt_z _ hlo
    rw [if_neg hlo0, ← hhi]
    by_cases hl' : lo' = z
    · rw [if_pos hl', app_z_right]
      exact lhdE_psi a (lhdE_prefix _ _)
    · rw [if_neg hl']
      exact lhdE_psi a (lhdE_app _ (Or.inr hl))

/-! ## 枠 1 段 -/

/-- **One frame of the drop, without a route hypothesis**: if the appended child value drops by `◁`,
the parent value `ψ_a(step …)` drops by `◁` (or stays). Hypotheses beyond `node_val`'s: the subscripts
are small (`SubSmall`), and in the frame where only the old child rewrites, the state `B` is closed
at the levels `≤ a`. -/
theorem node_lhd {a B s' y' s y : T}
    (hc : isOT (psi s y z) = true) (hc' : isOT (psi s' y' z) = true)
    (hrel : LhdE (psi s' y' z) (psi s y z))
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hsub : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → SubSmall a s)
    (hsub' : (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) ∨
      (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → SubSmall a s')
    (hBcl : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) →
      (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → Closed a B) :
    LhdE (psi a (step a B s' y' z) z) (psi a (step a B s y z) z) := by
  rcases hrel with h | hl
  · simp only [psi.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h; exact Or.inl rfl
  by_cases ht' : lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true
  · by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
    · -- both rewrite
      rcases psi_lt_psi_z_iff.mp hl.1 with hss | ⟨rfl, _⟩
      · obtain ⟨hcomp, hyle⟩ := comps_le_of_sub_lt hl hss (hsub' (Or.inl ht'))
        unfold step
        rw [if_pos ht', if_pos ht, H_of_le_om hc' (ne_z_of_lt ht'.1) hyle]
        apply lhdE_psi_closed _ (closed_of_le_om hcomp)
        have h1 : psi s' y' z < psi (succ s') z z := psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s'))
        exact le_trans (le_of_lt (lt_of_lt_of_le h1 (psi_le_psi_z (succ_le_of_lt hss))))
          (om_le_H hc (ne_z_of_lt ht.1))
      · exact lhdE_tt_same hc' hc hl ht' ht (hsub ht)
    · -- only the new child rewrites: `B = 0` and `c = Ω_s`, or impossible
      have hac : psi a z z < psi s y z := lt_trans (show psi a z z < psi s' y' z from ht'.2) hl.1
      have hyB : ¬ B < y := fun h => ht ⟨h, hac⟩
      rcases psi_lt_psi_z_iff.mp hl.1 with hss | ⟨rfl, hyy⟩
      · obtain ⟨_, hyle⟩ := comps_le_of_sub_lt hl hss (hsub' (Or.inl ht'))
        by_cases hBz : B = z
        · subst hBz
          have hy : y = z := by
            by_contra h; exact hyB (lt_of_le_of_ne (z_le _) (Ne.symm h))
          subst hy
          unfold step
          rw [if_pos ht', if_neg ht, H_of_le_om hc' (ne_z_of_lt ht'.1) hyle]
          exact lhdE_psi a (Or.inr hl)
        · exfalso
          have hcB : psi s y z ≤ B := le_trans (hBc _ (head_mem_summands hBz)) (head_le_self B)
          have hy'c : y' ≤ psi s y z :=
            le_trans hyle (le_trans (psi_le_psi_arg (z_le y')) (le_of_lt hl.1))
          exact lt_irrefl' B (lt_of_lt_of_le (show B < y' from ht'.1) (le_trans hy'c hcB))
      · exact absurd (lt_trans (show B < y' from ht'.1) hyy) hyB
  · by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
    · -- only the old child rewrites: the small route
      unfold step
      rw [if_neg ht', if_pos ht]
      have hadd : add B (psi s' y' z) = app B (psi s' y' z) := by
        have := add_app_drop (lo := z) (B := B) (s := s') (y := y')
          (fun q hq hlt => lt_irrefl' _ (lt_of_lt_of_le (lt_trans hlt hl.1) (hBc q hq))) (Or.inl rfl)
        rwa [app_z_right] at this
      rw [hadd]
      exact lhdE_psi_closed (le_tn hc hl.1 ht hBc) (closed_tn hl ht' ht hBc (hBcl ht' ht) (hsub ht) (hsub' (Or.inr ht)))
    · -- no rewrite
      exact lhdE_psi a (lhdE_step_nn' (Or.inr hl) ht' ht hBc)

/-! ## 閉性の仮定は外せない -/

/-- **Counterexample without the closedness of `B`** (a real frame of the 3-row data):
`a = ω`, `B = ψ_{ω+1}(ψ_ω(Ω_{ω·2}))`, `c = ψ_ω(Ω_{ω·2})`, `c' = Ω_ω ◁ c`. Only `c` rewrites, and
`ψ_ω(B + c')` is not below `ψ_ω(Ω_{ω·2})` by `◁`: its component `Ω_{ω·2}` (inside `B`) is not dominated
in `ψ_ω(Ω_{ω+2})`, which lies between; indeed `ψ_ω(B + c')` is not standard. -/
theorem node_lhd_needs_closed :
    let ω : T := psi z one z
    let y : T := psi (psi z one (psi z one z)) z z
    let B : T := psi (psi z one one) (psi ω y z) z
    isOT B = true ∧ isOT (psi ω y z) = true ∧ isOT (psi ω z z) = true ∧
    LhdE (psi ω z z) (psi ω y z) ∧ (∀ q ∈ summands B, psi ω y z ≤ q) ∧
    isOT (psi ω (step ω B ω y z) z) = true ∧ SubSmall ω ω ∧
    isOT (psi ω (step ω B ω z z) z) = false ∧ ¬ LhdE (psi ω (step ω B ω z z) z) (psi ω (step ω B ω y z) z) := by
  intro ω y B
  have hsub : SubSmall ω ω := by
    intro u hu g hg
    by_cases huz : u = z
    · subst huz; revert g; decide
    · have hzu : lt z u = true := lt_of_le_of_ne (z_le u) (Ne.symm huz)
      simp [ω, comps, hzu] at hg
  refine ⟨by decide, by decide, by decide, Or.inr (lhd_psi ω (lhd_zero (by decide))),
    by decide, by decide, hsub, by decide, ?_⟩
  rintro (h | h)
  · revert h; decide
  · -- the witness `ψ_ω(Ω_{ω+2})` between the parents
    have := h.2 z (psi ω (psi (psi z one (psi z z one)) z z) z) (by decide) (by decide)
    unfold Dom at this
    revert this; decide

/-! ## 最後の子を落とす -/

/-- **Dropping the last appended child**: `ψ_a(B) ◁ ψ_a(step a B c)`. In a rewriting frame `B` must be
closed at the levels `≤ a` (`drop_child_needs_closed`). -/
theorem drop_child_lhd {a B s y : T} (hc : isOT (psi s y z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hBcl : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → Closed a B) :
    LhdE (psi a B z) (psi a (step a B s y z) z) := by
  unfold step
  split_ifs with ht
  · have hle : B ≤ H s y := by
      rw [H_eq hc]; exact le_trans (B_le_hi hc ht.1 hBc) (le_app_self _ _)
    exact lhdE_psi_closed hle (hBcl ht)
  · have hadd : add B (psi s y z) = app B (psi s y z) := by
      have := add_app_drop (lo := z) (B := B) (s := s) (y := y)
        (fun q hq hlt => lt_irrefl' _ (lt_of_lt_of_le hlt (hBc q hq))) (Or.inl rfl)
      rwa [app_z_right] at this
    rw [hadd]
    exact lhdE_psi a (lhdE_prefix _ _)

/-- **Counterexample without the closedness of `B`** (the same real frame as `node_lhd_needs_closed`):
`ψ_ω(B)` is not below `ψ_ω(step ω B c) = ψ_ω(Ω_{ω·2})` by `◁`. -/
theorem drop_child_needs_closed :
    let ω : T := psi z one z
    let y : T := psi (psi z one (psi z one z)) z z
    let B : T := psi (psi z one one) (psi ω y z) z
    isOT B = true ∧ isOT (psi ω y z) = true ∧ (∀ q ∈ summands B, psi ω y z ≤ q) ∧
    isOT (psi ω (step ω B ω y z) z) = true ∧
    ¬ LhdE (psi ω B z) (psi ω (step ω B ω y z) z) := by
  intro ω y B
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rintro (h | h)
  · revert h; decide
  · have := h.2 z (psi ω (psi (psi z one (psi z z one)) z z) z) (by decide) (by decide)
    unfold Dom at this
    revert this; decide

/-! ## 弱い仮定の版（標準形で偽にならない形、2026-10-02）

`SubSmall a s`（添字の成分 ≤ Ω_s）と `Closed a B` は、SRO から届く標準形で偽になる
（添字 s = ψ_0(Ω_{Ω_1} + …) の成分 Ω_{Ω_1}、状態 B = ψ_2(X)·2 の成分 Ω_ω）。
そこで成分の押さえを 3 通りに広げる: Ω_s 以下、状態 B 以下、親の添字 a の同じ段の成分以下。
親の側 ψ_a(C) の成分には a の成分も入るので、3 つ目は ◁ の受け手で使える（`PRelA`）。
閉性の仮定は「B = hi(y)（このとき X = B + c で引数どうしの ◁）か `ClosedA`」に弱める。
-/

/-- The components of the subscript `s` at the levels `≤ a` are at most `Ω_s`, at most the state `B`,
or at most a component of the parent subscript `a` at the same level. -/
def SubSmallA (a B s : T) : Prop :=
  ∀ u, ¬ lt a u = true → ∀ g ∈ comps u s, g ≤ psi s z z ∨ g ≤ B ∨ ∃ d ∈ comps u a, g ≤ d

/-- `X` is closed at the levels `≤ a` up to the components of `a`. -/
def ClosedA (a X : T) : Prop :=
  ∀ u, ¬ lt a u = true → ∀ g ∈ comps u X, g ≤ X ∨ ∃ d ∈ comps u a, g ≤ d

theorem SubSmall.toA {a s : T} (h : SubSmall a s) (B : T) : SubSmallA a B s :=
  fun u hu g hg => Or.inl (h u hu g hg)

theorem Closed.toA {a X : T} (h : Closed a X) : ClosedA a X :=
  fun u hu g hg => Or.inl (h u hu g hg)

/-- The relation of the arguments under `ψ_a`, where the components of `a` may also dominate. -/
def PRelA (a X' X : T) : Prop :=
  X' ≤ X ∧ ∀ u, ¬ lt a u = true → ∀ C, X' < C → C ≤ X →
    ∀ g ∈ comps u X', ∃ d ∈ C :: (comps u C ++ comps u a), g ≤ d

/-- **The parent relation gives `◁` of the parents** (the components of `a` included). -/
theorem lhdE_psi_of_prelA {a X' X : T} (h : PRelA a X' X) : LhdE (psi a X' z) (psi a X z) := by
  rcases (le_iff _ _).mp h.1 with hlt | heq
  · right
    refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hlt⟩, fun u c h1 h2 => ?_⟩
    obtain ⟨c0, c1, rfl, hc1, hc2⟩ := between_psi h1 h2
    intro x hx
    simp only [comps, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · simp at hx
      · rename_i hau
        have hmem : ∀ w ∈ c0 :: (comps u c0 ++ comps u a), w ∈ comps u (psi a c0 c1) ++ Gc u z := by
          intro w hw
          apply List.mem_append_left
          simp only [comps]
          rw [if_neg hau]
          exact List.mem_append_left _ hw
        simp only [List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · exact ⟨c0, hmem _ List.mem_cons_self, hc1⟩
        · rcases (le_iff _ _).mp hc1 with hc1 | rfl
          · obtain ⟨d, hd, hxd⟩ := h.2 u hau c0 hc1 hc2 x hx
            exact ⟨d, hmem d hd, hxd⟩
          · exact ⟨x, hmem x (List.mem_cons_of_mem _ (List.mem_append_left _ hx)), le_refl _⟩
        · exact ⟨x, hmem x (List.mem_cons_of_mem _ (List.mem_append_right _ hx)), le_refl _⟩
    · simp at hx
  · left; rw [heq]

theorem prel_smallA {a X' X : T} (hle : X' ≤ X) (hsm : ClosedA a X') : PRelA a X' X :=
  ⟨hle, fun u hu C h1 _ g hg => by
    rcases hsm u hu g hg with h | ⟨d, hd, hgd⟩
    · exact ⟨C, List.mem_cons_self .., le_of_lt (lt_of_le_of_lt h h1)⟩
    · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_right _ hd), hgd⟩⟩

theorem lhdE_psi_closedA {a X' X : T} (hle : X' ≤ X) (hsm : ClosedA a X') :
    LhdE (psi a X' z) (psi a X z) :=
  lhdE_psi_of_prelA (prel_smallA hle hsm)

/-- **Both rewrite, same subscript**: the components of the subscript are dominated in every `C` above
the state and `Ω_s` up to the new value (`hCsX`). -/
theorem lhdE_tt_sameS {a B s y' y : T} (hc' : isOT (psi s y' z) = true) (hc : isOT (psi s y z) = true)
    (hl : Lhd z (psi s y' z) (psi s y z))
    (ht' : lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hCsX : ∀ u, ¬ lt a u = true → ∀ C, B < C → psi s z z < C → C ≤ H s y →
      ∀ w ∈ comps u s, ∃ d ∈ C :: (comps u C ++ comps u a), w ≤ d)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q) :
    LhdE (psi a (step a B s y' z) z) (psi a (step a B s y z) z) := by
  have hOm := om_le_H hc' (ne_z_of_lt ht'.1)
  have hBc' : ∀ q ∈ summands B, psi s y' z ≤ q := fun q hq => le_trans (le_of_lt hl.1) (hBc q hq)
  have hBhi' := B_le_hi hc' ht'.1 hBc'
  unfold step
  rw [if_pos ht', if_pos ht]
  rw [H_eq hc'] at hOm
  rw [H_eq hc', H_eq hc]
  have has := le_of_trig ht.2
  have hyy : y' < y := by
    rcases psi_lt_psi_z_iff.mp hl.1 with h | ⟨_, h⟩
    · exact absurd h (lt_irrefl' _)
    · exact h
  set θ := psi (succ s) z z with hθ
  have ey := split_app θ y
  have ey' := split_app θ y'
  set hi := (split y θ).1
  set lo := (split y θ).2
  set hi' := (split y' θ).1
  set lo' := (split y' θ).2
  have hcθ : head (psi s y' z) < θ := psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s))
  rcases split_mono θ hyy with hhi | ⟨hhi, hlo⟩
  · change hi' < hi at hhi
    apply lhdE_psi_of_prelA
    set X' := app hi' (if lo' = z then z else psi s y' z)
    set X := app hi (if lo = z then z else psi s y z)
    have hy'X' : y' ≤ X' := by
      by_cases hl' : lo' = z
      · simp only [X', if_pos hl']; rw [← ey', hl']
      · simp only [X', if_neg hl']
        exact le_of_lt (lt_of_eq_of_lt ey'.symm (app_lt_app_left hi' (split_lo_lt hc' hl')))
    have hX'hi : X' < hi := by
      apply app_lt_of_lt_hi hhi (split_fst_ge θ y)
      split
      · exact Or.inl rfl
      · exact Or.inr hcθ
    have hy'hi : y' < hi := by
      rw [← ey']; exact app_lt_of_lt_hi hhi (split_fst_ge θ y) (split_snd_head θ y')
    have hhiy : hi ≤ y := by rw [← ey]; exact le_app_self _ _
    have hBX' : B ≤ X' := le_trans hBhi' (le_app_self _ _)
    refine ⟨le_of_lt (lt_of_lt_of_le hX'hi (le_app_self _ _)), fun u hu C h1 h2 g hg => ?_⟩
    have hsu : ¬ s < u := not_lt_of_le_lev has hu
    have hCs : ∀ w ∈ comps u s, ∃ d ∈ C :: (comps u C ++ comps u a), w ≤ d :=
      hCsX u hu C (lt_of_le_of_lt hBX' h1) (lt_of_le_of_lt hOm h1) (by rw [H_eq hc]; exact h2)
    have key : ∀ g ∈ comps u y', ∃ d ∈ C :: (comps u C ++ comps u a), g ≤ d := by
      intro g hg
      have hgc : g ∈ comps u (psi s y' z) := by rw [comps_psi_z_of_ge hsu]; simp [hg]
      by_cases hChi : C ≤ hi
      · have h1' : psi s y' z < psi s C z :=
          psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt hy'X' h1⟩)
        obtain ⟨w, hw, hgw⟩ := hl.2 u _ h1' (psi_le_psi_arg (le_trans hChi hhiy)) g hgc
        rw [List.mem_append, comps_psi_z_of_ge hsu] at hw
        simp only [Gc, comps, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | hw | hw) | rfl
        · exact ⟨_, List.mem_cons_self .., hgw⟩
        · exact ⟨w, List.mem_cons_of_mem _ (List.mem_append_left _ hw), hgw⟩
        · obtain ⟨d, hd, hwd⟩ := hCs w hw; exact ⟨d, hd, le_trans hgw hwd⟩
        · exact ⟨C, List.mem_cons_self .., le_trans hgw (z_le _)⟩
      · have hChi' : hi < C := lt_of_not_ge hChi
        have hlo : lo ≠ z := by
          intro hlo
          have : X = hi := by simp only [X, if_pos hlo, app_z_right]
          exact hChi (this ▸ h2)
        have h2' : C ≤ app hi (psi s y z) := by
          have : X = app hi (psi s y z) := by simp only [X, if_neg hlo]
          exact this ▸ h2
        obtain ⟨c0, hC, _, _⟩ := between_app (A := hi) (x := z) (by rw [app_z_right]; exact hChi') h2'
        have h1' : psi s y' z < psi s hi z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hy'hi⟩)
        obtain ⟨w, hw, hgw⟩ := hl.2 u _ h1' (psi_le_psi_arg hhiy) g hgc
        rw [List.mem_append, comps_psi_z_of_ge hsu] at hw
        simp only [Gc, comps, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | hw | hw) | rfl
        · exact ⟨C, List.mem_cons_self .., le_trans hgw (le_of_lt hChi')⟩
        · refine ⟨w, List.mem_cons_of_mem _ (List.mem_append_left _ ?_), hgw⟩
          rw [hC, comps_app]; exact List.mem_append_left _ hw
        · obtain ⟨d, hd, hwd⟩ := hCs w hw; exact ⟨d, hd, le_trans hgw hwd⟩
        · exact ⟨C, List.mem_cons_self .., le_trans hgw (z_le _)⟩
    simp only [X'] at hg
    rw [comps_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · apply key
      rw [← ey', comps_app]; exact List.mem_append_left _ hg
    · split at hg
      · simp [comps] at hg
      · rw [comps_psi_z_of_ge hsu] at hg
        simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · exact ⟨C, List.mem_cons_self .., le_of_lt (lt_of_le_of_lt hy'X' h1)⟩
        · exact key g hg
        · exact hCs g hg
  · change hi' = hi at hhi
    change lo' < lo at hlo
    have hlo0 : lo ≠ z := by
      intro h; rw [h] at hlo; exact T.not_lt_z _ hlo
    rw [if_neg hlo0, ← hhi]
    by_cases hl' : lo' = z
    · rw [if_pos hl', app_z_right]
      exact lhdE_psi a (lhdE_prefix _ _)
    · rw [if_neg hl']
      exact lhdE_psi a (lhdE_app _ (Or.inr hl))

/-- **Both rewrite, same subscript** (weak hypothesis on the subscript). -/
theorem lhdE_tt_sameA {a B s y' y : T} (hc' : isOT (psi s y' z) = true) (hc : isOT (psi s y z) = true)
    (hl : Lhd z (psi s y' z) (psi s y z))
    (ht' : lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hsub : SubSmallA a B s) (hBc : ∀ q ∈ summands B, psi s y z ≤ q) :
    LhdE (psi a (step a B s y' z) z) (psi a (step a B s y z) z) :=
  lhdE_tt_sameS hc' hc hl ht' ht (fun u hu C hBC hOC _ w hw => by
    rcases hsub u hu w hw with h | h | ⟨d, hd, hwd⟩
    · exact ⟨C, List.mem_cons_self .., le_trans h (le_of_lt hOC)⟩
    · exact ⟨C, List.mem_cons_self .., le_trans h (le_of_lt hBC)⟩
    · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_right _ hd), hwd⟩) hBc

/-- **`c` rewrites, `c'` does not** (weak hypotheses): `X' = B + c'` is closed up to the components of `a`.
The subscript changes only for a leaf child (`hss`). -/
theorem closed_tnA {a B s' y' s y : T} (hl : Lhd z (psi s' y' z) (psi s y z))
    (hn' : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true))
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hB : ∀ q ∈ summands B, psi s y z ≤ q) (hBcl : ClosedA a B)
    (hsub' : SubSmallA a B s') (hss : y' ≠ z → s' = s) :
    ClosedA a (app B (psi s' y' z)) := by
  have has := le_of_trig ht.2
  have hcB : psi s' y' z ≤ app B (psi s' y' z) :=
    le_app_psi (fun q hq => le_trans (le_of_lt hl.1) (hB q hq))
  have hBX : B ≤ app B (psi s' y' z) := le_app_self _ _
  have hom : psi s' z z ≤ psi s' y' z := psi_le_psi_arg (z_le _)
  -- every component of `c'` is at most `B`, at most `c'`, or at most a component of `a`
  have hc' : ∀ u, ¬ lt a u = true → ∀ g ∈ comps u (psi s' y' z),
      g ≤ B ∨ g ≤ psi s' y' z ∨ ∃ d ∈ comps u a, g ≤ d := by
    intro u hu g hg
    have hsubg : ∀ w ∈ comps u s', g ≤ w → g ≤ B ∨ g ≤ psi s' y' z ∨ ∃ d ∈ comps u a, g ≤ d := by
      intro w hw hgw
      rcases hsub' u hu w hw with h | h | ⟨d, hd, hwd⟩
      · exact Or.inr (Or.inl (le_trans hgw (le_trans h hom)))
      · exact Or.inl (le_trans hgw h)
      · exact Or.inr (Or.inr ⟨d, hd, le_trans hgw hwd⟩)
    by_cases hyz : y' = z
    · subst hyz
      simp only [comps, List.append_nil] at hg
      split at hg
      · simp at hg
      · simp only [List.mem_cons, List.nil_append] at hg
        rcases hg with rfl | hg
        · exact Or.inl (z_le _)
        · exact hsubg g hg (le_refl _)
    · obtain rfl := hss hyz
      have hsu : ¬ s' < u := not_lt_of_le_lev has hu
      rw [comps_psi_z_of_ge hsu] at hg
      simp only [List.mem_cons, List.mem_append] at hg
      have htr : lt (psi a z z) (psi s' y' z) = true := by
        show psi a z z < psi s' y' z
        rcases (le_iff _ _).mp has with h | rfl
        · exact psi_lt_psi_z_iff.mpr (Or.inl h)
        · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hyz)⟩)
      have hyB : y' ≤ B := not_lt.mp (fun h => hn' ⟨h, htr⟩)
      rcases hg with rfl | hg | hg
      · exact Or.inl hyB
      · rcases (le_iff _ _).mp hyB with hyB | rfl
        · have h1 : psi s' y' z < psi s' B z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hyB⟩)
          have h2 : psi s' B z ≤ psi s' y z := psi_le_psi_arg (le_of_lt ht.1)
          have hgc : g ∈ comps u (psi s' y' z) := by
            rw [comps_psi_z_of_ge hsu]; simp [hg]
          obtain ⟨w, hw, hgw⟩ := hl.2 u _ h1 h2 g hgc
          rw [List.mem_append, comps_psi_z_of_ge hsu] at hw
          simp only [Gc, comps, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
          rcases hw with (rfl | hw | hw) | rfl
          · exact Or.inl hgw
          · rcases hBcl u hu w hw with h | ⟨d, hd, hwd⟩
            · exact Or.inl (le_trans hgw h)
            · exact Or.inr (Or.inr ⟨d, hd, le_trans hgw hwd⟩)
          · exact hsubg w hw hgw
          · exact Or.inl (le_trans hgw (z_le _))
        · rcases hBcl u hu g hg with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      · exact hsubg g hg (le_refl _)
  intro u hu g hg
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases hBcl u hu g hg with h | h
    · exact Or.inl (le_trans h hBX)
    · exact Or.inr h
  · rcases hc' u hu g hg with h | h | h
    · exact Or.inl (le_trans h hBX)
    · exact Or.inl (le_trans h hcB)
    · exact Or.inr h

/-- `B = hi(y)` and `B < y` force a low part. -/
theorem lo_ne_of_B_hi {B s y : T} (hlt : B < y) (hhi : B = (split y (psi (succ s) z z)).1) :
    (split y (psi (succ s) z z)).2 ≠ z := by
  intro hlo
  have e := split_app (psi (succ s) z z) y
  rw [hlo, app_z_right, ← hhi] at e
  rw [e] at hlt; exact lt_irrefl' _ hlt

/-- **One frame of the drop, weak hypotheses**: the subscript of the child changes only when the new child
is a leaf (`hss`); in the frame where only the old child rewrites, the components of the new subscript are
dominated (`SubSmallA`), and the state is the high part of `y` or closed up to `a`. -/
theorem node_lhdA {a B s' y' s y : T}
    (hc : isOT (psi s y z) = true) (hc' : isOT (psi s' y' z) = true)
    (hrel : LhdE (psi s' y' z) (psi s y z))
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hss : y' ≠ z → s' = s)
    (hsub' : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → SubSmallA a B s')
    (hBcl : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) →
      (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) →
      B = (split y (psi (succ s) z z)).1 ∨ ClosedA a B) :
    LhdE (psi a (step a B s' y' z) z) (psi a (step a B s y z) z) := by
  rcases hrel with h | hl
  · simp only [psi.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h; exact Or.inl rfl
  by_cases ht' : lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true
  · obtain rfl := hss (ne_z_of_lt ht'.1)
    have hyy : y' < y := by
      rcases psi_lt_psi_z_iff.mp hl.1 with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact h
    have ht : lt B y = true ∧ lt (psi a z z) (psi s' y z) = true :=
      ⟨lt_trans (show B < y' from ht'.1) hyy, lt_trans (show psi a z z < psi s' y' z from ht'.2) hl.1⟩
    exact lhdE_tt_sameA hc' hc hl ht' ht (hsub' ht) hBc
  · by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
    · rcases hBcl ht' ht with hhi | hcl
      · exact lhdE_psi a (lhdE_step_tn hc (Or.inr hl) ht' ht (lo_ne_of_B_hi ht.1 hhi) hhi hBc)
      · unfold step
        rw [if_neg ht', if_pos ht]
        have hadd : add B (psi s' y' z) = app B (psi s' y' z) := by
          have := add_app_drop (lo := z) (B := B) (s := s') (y := y')
            (fun q hq hlt => lt_irrefl' _ (lt_of_lt_of_le (lt_trans hlt hl.1) (hBc q hq))) (Or.inl rfl)
          rwa [app_z_right] at this
        rw [hadd]
        exact lhdE_psi_closedA (le_tn hc hl.1 ht hBc) (closed_tnA hl ht' ht hBc hcl (hsub' ht) hss)
    · exact lhdE_psi a (lhdE_step_nn' (Or.inr hl) ht' ht hBc)

/-- **Dropping the last appended child, weak hypothesis**: in a rewriting frame the state is the high
part of `y` (then the new state is `B + c`) or closed up to the components of `a`. -/
theorem drop_child_lhdA {a B s y : T} (hc : isOT (psi s y z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hBcl : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) →
      B = (split y (psi (succ s) z z)).1 ∨ ClosedA a B) :
    LhdE (psi a B z) (psi a (step a B s y z) z) := by
  unfold step
  split_ifs with ht
  · rcases hBcl ht with hhi | hcl
    · rw [H_eq hc, if_neg (lo_ne_of_B_hi ht.1 hhi), ← hhi]
      exact lhdE_psi a (lhdE_prefix _ _)
    · have hle : B ≤ H s y := by
        rw [H_eq hc]; exact le_trans (B_le_hi hc ht.1 hBc) (le_app_self _ _)
      exact lhdE_psi_closedA hle hcl
  · have hadd : add B (psi s y z) = app B (psi s y z) := by
      have := add_app_drop (lo := z) (B := B) (s := s) (y := y)
        (fun q hq hlt => lt_irrefl' _ (lt_of_lt_of_le hlt (hBc q hq))) (Or.inl rfl)
      rwa [app_z_right] at this
    rw [hadd]
    exact lhdE_psi a (lhdE_prefix _ _)

/-! ## 枠の支配 `FrameDom`（書き換える枠の仮定を 1 つにまとめた形）

書き換える枠（状態 B、子 c = ψ_s(y)、新しい状態 X = H(s, y)）で、B と Ω_s より上で X 以下のどの C でも、
B の成分と添字 s の成分が C・C の成分・親の添字 a の成分のどれかで押さえられる。
`Closed a B`・`SubSmall a s` から出るが、それより真に弱い（B = hi(y) の接頭辞、X = Ω_{s ++ δ} の形でも成り立つ）。
-/

/-- **The domination of a rewriting frame.** -/
def FrameDom (a B s X : T) : Prop :=
  ∀ u, ¬ lt a u = true → ∀ C, B < C → psi s z z < C → C ≤ X →
    ∀ g, (g ∈ comps u B ∨ g ∈ comps u s) → ∃ d ∈ C :: (comps u C ++ comps u a), g ≤ d

theorem frameDom_of_closed {a B s X : T} (hB : ClosedA a B) (hs : SubSmallA a B s) : FrameDom a B s X := by
  intro u hu C hBC hOC _ g hg
  rcases hg with hg | hg
  · rcases hB u hu g hg with h | ⟨d, hd, hgd⟩
    · exact ⟨C, List.mem_cons_self .., le_trans h (le_of_lt hBC)⟩
    · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_right _ hd), hgd⟩
  · rcases hs u hu g hg with h | h | ⟨d, hd, hgd⟩
    · exact ⟨C, List.mem_cons_self .., le_trans h (le_of_lt hOC)⟩
    · exact ⟨C, List.mem_cons_self .., le_trans h (le_of_lt hBC)⟩
    · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_right _ hd), hgd⟩

/-- A nonzero state is above `Ω_s` when its summands are at least the rewriting child `ψ_s(y)`, `y ≠ 0`. -/
theorem om_lt_B {B s y : T} (hBz : B ≠ z) (hy : y ≠ z) (hB : ∀ q ∈ summands B, psi s y z ≤ q) :
    psi s z z < B := by
  have h1 : psi s z z < psi s y z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hy)⟩)
  exact lt_of_lt_of_le h1 (le_trans (hB _ (head_mem_summands hBz)) (head_le_self B))

/-- **Dropping the last appended child, with `FrameDom`.** -/
theorem drop_child_lhdD {a B s y : T} (hc : isOT (psi s y z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hdom : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → FrameDom a B s (H s y)) :
    LhdE (psi a B z) (psi a (step a B s y z) z) := by
  unfold step
  split_ifs with ht
  · have hle : B ≤ H s y := by
      rw [H_eq hc]; exact le_trans (B_le_hi hc ht.1 hBc) (le_app_self _ _)
    apply lhdE_psi_of_prelA
    refine ⟨hle, fun u hu C h1 h2 g hg => ?_⟩
    have hBz : B ≠ z := by rintro rfl; simp [comps] at hg
    exact hdom ht u hu C h1 (lt_trans (om_lt_B hBz (ne_z_of_lt ht.1) hBc) h1) h2 g (Or.inl hg)
  · have hadd : add B (psi s y z) = app B (psi s y z) := by
      have := add_app_drop (lo := z) (B := B) (s := s) (y := y)
        (fun q hq hlt => lt_irrefl' _ (lt_of_lt_of_le hlt (hBc q hq))) (Or.inl rfl)
      rwa [app_z_right] at this
    rw [hadd]
    exact lhdE_psi a (lhdE_prefix _ _)

/-- **Only the old child rewrites, with `FrameDom`**: `B + c' ◁ H(s, y)` under `ψ_a`. -/
theorem prel_tn_dom {a B s' y' s y : T} (hc : isOT (psi s y z) = true)
    (hl : Lhd z (psi s' y' z) (psi s y z))
    (hn' : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true))
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hB : ∀ q ∈ summands B, psi s y z ≤ q) (hdom : FrameDom a B s (H s y))
    (hss : y' ≠ z → s' = s) :
    PRelA a (app B (psi s' y' z)) (H s y) := by
  have has := le_of_trig ht.2
  have hyz : y ≠ z := ne_z_of_lt ht.1
  have hcB : psi s' y' z ≤ app B (psi s' y' z) :=
    le_app_psi (fun q hq => le_trans (le_of_lt hl.1) (hB q hq))
  have hOc : psi s z z ≤ psi s y z := psi_le_psi_arg (z_le _)
  refine ⟨le_tn hc hl.1 ht hB, fun u hu C h1 h2 g hg => ?_⟩
  have hBC : B < C := lt_of_le_of_lt (le_app_self _ _) h1
  have hcC : psi s' y' z < C := lt_of_le_of_lt hcB h1
  have hd : ∀ w, (w ∈ comps u B ∨ w ∈ comps u s) → psi s z z < C → g ≤ w →
      ∃ d ∈ C :: (comps u C ++ comps u a), g ≤ d := by
    intro w hw hOC hgw
    obtain ⟨d, hd, hwd⟩ := hdom u hu C hBC hOC h2 w hw
    exact ⟨d, hd, le_trans hgw hwd⟩
  have hz : g ≤ z → ∃ d ∈ C :: (comps u C ++ comps u a), g ≤ d :=
    fun h => ⟨C, List.mem_cons_self .., le_trans h (z_le _)⟩
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · have hBz : B ≠ z := by rintro rfl; simp [comps] at hg
    exact hd g (Or.inl hg) (lt_trans (om_lt_B hBz hyz hB) hBC) (le_refl _)
  -- a component of `c'`
  by_cases hCc : C ≤ psi s y z
  · obtain ⟨w, hw, hgw⟩ := hl.2 u C hcC hCc g hg
    rcases List.mem_append.mp hw with hw | hw
    · exact ⟨w, List.mem_cons_of_mem _ (List.mem_append_left _ hw), hgw⟩
    · simp only [Gc, comps, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw; exact hz hgw
  have hcC' : psi s y z < C := lt_of_not_ge hCc
  have hOC : psi s z z < C := lt_of_le_of_lt hOc hcC'
  have hsu : ¬ s < u := not_lt_of_le_lev has hu
  by_cases hy' : y' = z
  · subst hy'
    rcases (le_iff _ _).mp (le_of_lt hl.1) with hlt | heq
    · rcases psi_lt_psi_z_iff.mp hlt with hss' | ⟨rfl, _⟩
      · -- `s' < s`: through `Ω_s`
        have hlt' : psi s' z z < psi s z z := psi_lt_psi_z_iff.mpr (Or.inl hss')
        obtain ⟨w, hw, hgw⟩ := hl.2 u (psi s z z) hlt' hOc g hg
        rw [List.mem_append, comps_psi_z_of_ge hsu] at hw
        simp only [Gc, comps, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | hw | hw) | rfl
        · exact hz hgw
        · simp at hw
        · exact hd w (Or.inr hw) hOC hgw
        · exact hz hgw
      · rw [comps_psi_z_of_ge hsu] at hg
        simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · exact hz (le_refl _)
        · simp [comps] at hg
        · exact hd g (Or.inr hg) hOC (le_refl _)
    · exact absurd heq (ne_of_lt hl.1)
  · obtain rfl := hss hy'
    rw [comps_psi_z_of_ge hsu] at hg
    simp only [List.mem_cons, List.mem_append] at hg
    have htr : lt (psi a z z) (psi s' y' z) = true := by
      show psi a z z < psi s' y' z
      rcases (le_iff _ _).mp has with h | rfl
      · exact psi_lt_psi_z_iff.mpr (Or.inl h)
      · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hy')⟩)
    have hyB : y' ≤ B := not_lt.mp (fun h => hn' ⟨h, htr⟩)
    rcases hg with rfl | hgy | hgs
    · exact ⟨C, List.mem_cons_self .., le_trans hyB (le_of_lt hBC)⟩
    · rcases (le_iff _ _).mp hyB with hyB | hyB
      · have h1' : psi s' y' z < psi s' B z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hyB⟩)
        have h2' : psi s' B z ≤ psi s' y z := psi_le_psi_arg (le_of_lt ht.1)
        have hgc : g ∈ comps u (psi s' y' z) := by rw [comps_psi_z_of_ge hsu]; simp [hgy]
        obtain ⟨w, hw, hgw⟩ := hl.2 u _ h1' h2' g hgc
        rw [List.mem_append, comps_psi_z_of_ge hsu] at hw
        simp only [Gc, comps, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | hw | hw) | rfl
        · exact ⟨C, List.mem_cons_self .., le_trans hgw (le_of_lt hBC)⟩
        · exact hd w (Or.inl hw) hOC hgw
        · exact hd w (Or.inr hw) hOC hgw
        · exact hz hgw
      · rw [hyB] at hgy; exact hd g (Or.inl hgy) hOC (le_refl _)
    · exact hd g (Or.inr hgs) hOC (le_refl _)

/-- **One frame of the drop, with `FrameDom`**: the subscript of the child changes only when the new
child is a leaf (`hss`); in the rewriting frame of the old child, `FrameDom` holds. -/
theorem node_lhdD {a B s' y' s y : T}
    (hc : isOT (psi s y z) = true) (hc' : isOT (psi s' y' z) = true)
    (hrel : LhdE (psi s' y' z) (psi s y z))
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hss : y' ≠ z → s' = s)
    (hdom : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → FrameDom a B s (H s y)) :
    LhdE (psi a (step a B s' y' z) z) (psi a (step a B s y z) z) := by
  rcases hrel with h | hl
  · simp only [psi.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h; exact Or.inl rfl
  by_cases ht' : lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true
  · obtain rfl := hss (ne_z_of_lt ht'.1)
    have hyy : y' < y := by
      rcases psi_lt_psi_z_iff.mp hl.1 with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact h
    have ht : lt B y = true ∧ lt (psi a z z) (psi s' y z) = true :=
      ⟨lt_trans (show B < y' from ht'.1) hyy, lt_trans (show psi a z z < psi s' y' z from ht'.2) hl.1⟩
    exact lhdE_tt_sameS hc' hc hl ht' ht
      (fun u hu C hBC hOC h2 w hw => hdom ht u hu C hBC hOC h2 w (Or.inr hw)) hBc
  · by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
    · unfold step
      rw [if_neg ht', if_pos ht]
      have hadd : add B (psi s' y' z) = app B (psi s' y' z) := by
        have := add_app_drop (lo := z) (B := B) (s := s') (y := y')
          (fun q hq hlt => lt_irrefl' _ (lt_of_lt_of_le (lt_trans hlt hl.1) (hBc q hq))) (Or.inl rfl)
        rwa [app_z_right] at this
      rw [hadd]
      exact lhdE_psi_of_prelA (prel_tn_dom hc hl ht' ht hBc (hdom ht) hss)
    · exact lhdE_psi a (lhdE_step_nn' (Or.inr hl) ht' ht hBc)

theorem FrameDom.mono {a B s X X' : T} (h : FrameDom a B s X) (hle : X' ≤ X) : FrameDom a B s X' :=
  fun u hu C h1 h2 h3 => h u hu C h1 h2 (le_trans h3 hle)

/-- **`H` is monotone in the argument.** -/
theorem H_mono {s y' y : T} (hc' : isOT (psi s y' z) = true) (hc : isOT (psi s y z) = true)
    (hyy : y' ≤ y) : H s y' ≤ H s y := by
  rcases (le_iff _ _).mp hyy with hlt | rfl
  · rw [H_eq hc', H_eq hc]
    have hcθ : head (psi s y' z) < psi (succ s) z z := psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s))
    rcases split_mono (psi (succ s) z z) hlt with hhi | ⟨hhi, hlo⟩
    · apply le_of_lt
      apply lt_of_lt_of_le _ (le_app_self _ _)
      apply app_lt_of_lt_hi hhi (split_fst_ge _ y)
      split
      · exact Or.inl rfl
      · exact Or.inr hcθ
    · rw [hhi]
      have hlo0 : (split y (psi (succ s) z z)).2 ≠ z := by
        intro h; rw [h] at hlo; exact T.not_lt_z _ hlo
      rw [if_neg hlo0]
      split
      · rw [app_z_right]; exact le_app_self _ _
      · exact le_of_lt (app_lt_app_left _ (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hlt⟩)))
  · exact le_refl _

end Ytosk
