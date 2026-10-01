/-
**区別された集合（Buchholz の distinguished sets）。**

設計は `Ytosk/wf.md`。Arai の 2 つの論文
（https://arxiv.org/abs/2211.08619, https://arxiv.org/abs/2304.00246 の 3 節）の組み立てを、
拡張 Buchholz に合わせて作り直したもの。
-/
import Ytosk.OTLemmas

namespace Ytosk

open T

/-! ## 集合 C^α(X) -/

/-- `C α X`: the closure of `X ∩ α` (and `0`) under sums, `ν ↦ Ω_ν`, and the collapses
`ψ_ν(b)` (`b ≠ 0`) whose target `Ω_{ν+1}` lies above `α`, i.e. `lev α ≤ ν`. -/
inductive C (α : T) (X : T → Prop) : T → Prop
  | zero : C α X z
  | base {δ : T} : X δ → δ < α → isOT δ = true → C α X δ
  | sum {x y : T} : C α X x → C α X y → x ≠ z → y ≠ z → isOT (app x y) = true →
      C α X (app x y)
  | om {ν : T} : C α X ν → C α X (Om ν)
  | col {ν b : T} : C α X ν → C α X b → b ≠ z → lev α ≤ ν → isOT (psi ν b z) = true →
      C α X (psi ν b z)

theorem C_ot {α : T} {X : T → Prop} {t : T} (h : C α X t) : isOT t = true := by
  induction h with
  | zero => rfl
  | base _ _ h => exact h
  | sum _ _ _ _ h => exact h
  | om _ ih => exact isOT_om.mpr ih
  | col _ _ _ _ h => exact h

/-- `C α X` depends only on `X ∩ α`. -/
theorem C_mono_X {α : T} {X Y : T → Prop} (hXY : ∀ t, t < α → X t → Y t) {t : T}
    (h : C α X t) : C α Y t := by
  induction h with
  | zero => exact C.zero
  | base hx hlt hot => exact C.base (hXY _ hlt hx) hlt hot
  | sum _ _ hx hy hot ihx ihy => exact C.sum ihx ihy hx hy hot
  | om _ ih => exact C.om ih
  | col _ _ hb hl hot ih1 ih2 => exact C.col ih1 ih2 hb hl hot

theorem C_ext {α : T} {X Y : T → Prop} (hXY : ∀ t, t < α → (X t ↔ Y t)) (t : T) :
    C α X t ↔ C α Y t :=
  ⟨C_mono_X (fun t h hx => (hXY t h).mp hx), C_mono_X (fun t h hy => (hXY t h).mpr hy)⟩

/-- A larger `α` of the same or a lower level gives a larger `C`. -/
theorem C_mono_alpha {α β : T} {X : T → Prop} (hab : α ≤ β) (hl : lev β ≤ lev α) {t : T}
    (h : C α X t) : C β X t := by
  induction h with
  | zero => exact C.zero
  | base hx hlt hot => exact C.base hx (lt_of_lt_of_le hlt hab) hot
  | sum _ _ hx hy hot ihx ihy => exact C.sum ihx ihy hx hy hot
  | om _ ih => exact C.om ih
  | col _ _ hb hl' hot ih1 ih2 => exact C.col ih1 ih2 hb (le_trans hl hl') hot

/-- Lemma 1 (1), the core (Arai (11)): under `∀ γ ∈ X, γ ∈ C^γ(X)`, an element of `C^β(X)` with
`β ≥ α` is in `C^α(X)` or in `X ∩ β`. By induction on the size. -/
theorem C_down_aux {X : T → Prop} (H : ∀ γ, X γ → C γ X γ) {α : T} :
    ∀ n, ∀ γ, size γ < n → ∀ β, α ≤ β → C β X γ → C α X γ ∨ (X γ ∧ γ < β) := by
  intro n
  induction n with
  | zero => intro γ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro γ hs β hab h
    -- a part `x` of `γ` that is in `C^β(X)` is in `C^α(X)`
    have part : ∀ x, size x < size γ → C β X x → C α X x := by
      intro x hx hxC
      rcases ih x (by omega) β hab hxC with h1 | ⟨h1, h2⟩
      · exact h1
      · rcases lt_or_ge x α with h3 | h3
        · exact C.base h1 h3 (C_ot hxC)
        · rcases ih x (by omega) x h3 (H x h1) with h4 | ⟨_, h5⟩
          · exact h4
          · exact absurd h5 (lt_irrefl _)
    cases h with
    | zero => exact Or.inl C.zero
    | base hx hlt _ => exact Or.inr ⟨hx, hlt⟩
    | sum hxC hyC hx hy hot =>
      exact Or.inl (C.sum (part _ (size_lt_app_left hy) hxC) (part _ (size_lt_app_right hx) hyC)
        hx hy hot)
    | om hν => exact Or.inl (C.om (part _ (size_sub_lt _ _ _) hν))
    | col hν hb hbz hl hot =>
      exact Or.inl (C.col (part _ (size_sub_lt _ _ _) hν) (part _ (size_arg_lt _ _ _) hb) hbz
        (le_trans (lev_le_of_le hab) hl) hot)

/-- Lemma 1 (1). -/
theorem C_down {X : T → Prop} (H : ∀ γ, X γ → C γ X γ) {α β : T} (hab : α ≤ β) {t : T}
    (h : C β X t) : C α X t := by
  rcases C_down_aux H (size t + 1) t (Nat.lt_succ_self _) β hab h with h1 | ⟨h1, _⟩
  · exact h1
  · rcases lt_or_ge t α with h3 | h3
    · exact C.base h1 h3 (C_ot h)
    · rcases C_down_aux H (size t + 1) t (Nat.lt_succ_self _) t h3 (H t h1) with h4 | ⟨_, h5⟩
      · exact h4
      · exact absurd h5 (lt_irrefl _)

/-- Lemma 1 (2): the same level gives the same `C`. -/
theorem C_level_eq {X : T → Prop} (H : ∀ γ, X γ → C γ X γ) {α β : T} (hl : lev α = lev β)
    {t : T} (h : C α X t) : C β X t := by
  rcases le_total α β with hab | hba
  · exact C_mono_alpha hab (le_of_eq hl.symm) h
  · exact C_down H hba h

/-! ## 整礎部分と区別された集合 -/

/-- The predecessor relation inside `Y`. -/
def R (Y : T → Prop) (s u : T) : Prop := Y s ∧ s < u

/-- The well-founded part `W(Y)` of `Y`. -/
def WP (Y : T → Prop) (t : T) : Prop := Y t ∧ Acc (R Y) t

/-- Accessibility depends only on the part of `Y` below the point. -/
theorem acc_transfer {Y Y' : T → Prop} {t : T} (h : Acc (R Y) t)
    (hsub : ∀ s, s < t → Y' s → Y s) : Acc (R Y') t := by
  induction h with
  | intro t _ ih =>
    constructor
    rintro s ⟨hs, hst⟩
    exact ih s ⟨hsub s hst hs, hst⟩ (fun s' hs' hy => hsub s' (lt_trans hs' hst) hy)

theorem WP_down {Y : T → Prop} {t s : T} (h : WP Y t) (hs : Y s) (hst : s < t) : WP Y s :=
  ⟨hs, h.2.inv ⟨hs, hst⟩⟩

theorem WP_le {Y : T → Prop} {t s : T} (h : WP Y t) (hs : Y s) (hst : s ≤ t) : WP Y s := by
  rcases (le_iff _ _).mp hst with h1 | rfl
  · exact WP_down h hs h1
  · exact h

theorem WP_ext {Y Y' : T → Prop} (h : ∀ t, Y t ↔ Y' t) (t : T) : WP Y t ↔ WP Y' t := by
  have : Y = Y' := funext fun t => propext (h t)
  subst this; exact Iff.rfl

/-- `α ≤ X`: `α` is at most some element of `X`. -/
def LeSet (α : T) (X : T → Prop) : Prop := ∃ δ, X δ ∧ α ≤ δ

/-- `X` is distinguished: below `α⁺`, `X` is the well-founded part of `C^α(X)` whenever `α ≤ X`. -/
def D (X : T → Prop) : Prop :=
  (∀ t, X t → isOT t = true) ∧
  ∀ α, isOT α = true → LeSet α X → ∀ t, t < plus α → (WP (C α X) t ↔ X t)

/-- The union of all distinguished sets. -/
def W (t : T) : Prop := ∃ X, D X ∧ X t

/-- `G(X)`: `α ∈ C^α(X)` and everything of `C^α(X)` below `α` is in `X`. -/
def G (X : T → Prop) (α : T) : Prop :=
  isOT α = true ∧ C α X α ∧ ∀ t, C α X t → t < α → X t

section
variable {X Y : T → Prop}

theorem D_WP_self (hX : D X) {γ : T} (hγ : X γ) : WP (C γ X) γ :=
  (hX.2 γ (hX.1 γ hγ) ⟨γ, hγ, le_refl γ⟩ γ (lt_plus_self γ)).mpr hγ

theorem D_C_self (hX : D X) {γ : T} (hγ : X γ) : C γ X γ := (D_WP_self hX hγ).1

/-- Lemma 2: an element of a distinguished `X` is in every `C^β(X)`. -/
theorem D_C (hX : D X) {γ : T} (hγ : X γ) (β : T) : C β X γ := by
  rcases le_or_gt β γ with h | h
  · exact C_down (fun _ h' => D_C_self hX h') h (D_C_self hX hγ)
  · exact C.base hγ h (hX.1 γ hγ)

/-- A distinguished set is well-founded. -/
theorem D_wf (hX : D X) {γ : T} (hγ : X γ) : Acc (R X) γ :=
  acc_transfer (D_WP_self hX hγ).2 (fun s hs hxs => C.base hxs hs (hX.1 s hxs))

end

/-- A minimal element, from accessibility. -/
theorem exists_min_acc {r : T → T → Prop} {P : T → Prop} (hacc : ∀ t, P t → Acc r t)
    (hne : ∃ t, P t) : ∃ t, P t ∧ ∀ s, P s → ¬ r s t := by
  apply Classical.byContradiction
  intro hno
  have key : ∀ t, Acc r t → ¬ P t := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro hp
      exact hno ⟨t, hp, fun s hs hrs => ih s hrs hs⟩
  obtain ⟨t, ht⟩ := hne
  exact key t (hacc t ht) ht

section
variable {X Y : T → Prop}

theorem D_agree_point (hX : D X) (hY : D Y) {ε α : T} (hε : ε < α) (hLY : LeSet α Y)
    (hagree : ∀ s, s < ε → (X s ↔ Y s)) (hxε : X ε) : Y ε := by
  have h1 : WP (C ε X) ε := D_WP_self hX hxε
  have h2 : WP (C ε Y) ε := (WP_ext (C_ext hagree) ε).mp h1
  obtain ⟨δ, hδ, hαδ⟩ := hLY
  exact (hY.2 ε (hX.1 ε hxε) ⟨δ, hδ, le_of_lt (lt_of_lt_of_le hε hαδ)⟩ ε
    (lt_plus_self ε)).mp h2

/-- Lemma 3, first half: two distinguished sets agree below a common point. -/
theorem D_agree_below (hX : D X) (hY : D Y) {α : T} (hLX : LeSet α X) (hLY : LeSet α Y) :
    ∀ t, t < α → (X t ↔ Y t) := by
  apply Classical.byContradiction
  intro hno
  have hex : ∃ t, t < α ∧ ((X t ∧ ¬ Y t) ∨ (Y t ∧ ¬ X t)) := by
    apply Classical.byContradiction; intro h; apply hno; intro t ht
    constructor
    · intro hx; apply Classical.byContradiction; intro hy; exact h ⟨t, ht, Or.inl ⟨hx, hy⟩⟩
    · intro hy; apply Classical.byContradiction; intro hx; exact h ⟨t, ht, Or.inr ⟨hy, hx⟩⟩
  by_cases hPX : ∃ t, X t ∧ t < α ∧ ¬ Y t
  · obtain ⟨εX, ⟨hxX, hεXα, hnyX⟩, hminX⟩ :=
      exists_min_acc (r := R X) (fun t h => D_wf hX h.1) hPX
    by_cases hPY : ∃ t, (Y t ∧ t < α ∧ ¬ X t) ∧ t < εX
    · obtain ⟨εY, ⟨⟨hyY, hεYα, hnxY⟩, hεYX⟩, hminY⟩ :=
        exists_min_acc (r := R Y) (fun t h => D_wf hY h.1.1) hPY
      have hag : ∀ s, s < εY → (Y s ↔ X s) := by
        intro s hs
        constructor
        · intro hy; apply Classical.byContradiction; intro hx
          exact hminY s ⟨⟨hy, lt_trans hs hεYα, hx⟩, lt_trans hs hεYX⟩ ⟨hy, hs⟩
        · intro hx; apply Classical.byContradiction; intro hy
          exact hminX s ⟨hx, lt_trans (lt_trans hs hεYX) hεXα, hy⟩ ⟨hx, lt_trans hs hεYX⟩
      exact hnxY (D_agree_point hY hX hεYα hLX hag hyY)
    · have hag : ∀ s, s < εX → (X s ↔ Y s) := by
        intro s hs
        constructor
        · intro hx; apply Classical.byContradiction; intro hy
          exact hminX s ⟨hx, lt_trans hs hεXα, hy⟩ ⟨hx, hs⟩
        · intro hy; apply Classical.byContradiction; intro hx
          exact hPY ⟨s, ⟨hy, lt_trans hs hεXα, hx⟩, hs⟩
      exact hnyX (D_agree_point hX hY hεXα hLY hag hxX)
  · have hPY : ∃ t, Y t ∧ t < α ∧ ¬ X t := by
      obtain ⟨t, ht, h1 | h1⟩ := hex
      · exact absurd ⟨t, h1.1, ht, h1.2⟩ hPX
      · exact ⟨t, h1.1, ht, h1.2⟩
    obtain ⟨εY, ⟨hyY, hεYα, hnxY⟩, hminY⟩ :=
      exists_min_acc (r := R Y) (fun t h => D_wf hY h.1) hPY
    have hag : ∀ s, s < εY → (Y s ↔ X s) := by
      intro s hs
      constructor
      · intro hy; apply Classical.byContradiction; intro hx
        exact hminY s ⟨hy, lt_trans hs hεYα, hx⟩ ⟨hy, hs⟩
      · intro hx; apply Classical.byContradiction; intro hy
        exact hPX ⟨s, hx, lt_trans hs hεYα, hy⟩
    exact hnxY (D_agree_point hY hX hεYα hLX hag hyY)

/-- Lemma 3: two distinguished sets agree below `α⁺` when both reach `α`. -/
theorem D_agree (hX : D X) (hY : D Y) {α : T} (hα : isOT α = true) (hLX : LeSet α X)
    (hLY : LeSet α Y) : ∀ t, t < plus α → (X t ↔ Y t) := by
  intro t ht
  have hb := D_agree_below hX hY hLX hLY
  rw [← hX.2 α hα hLX t ht, ← hY.2 α hα hLY t ht]
  exact WP_ext (C_ext hb) t

end

/-- Lemma 4: `W` is distinguished. -/
theorem D_W : D W := by
  refine ⟨fun t ⟨X, hX, ht⟩ => hX.1 t ht, ?_⟩
  intro α hα ⟨δ, ⟨X0, hX0, hδ⟩, hαδ⟩ t ht
  have hL0 : LeSet α X0 := ⟨δ, hδ, hαδ⟩
  have hWX : ∀ s, s < plus α → (W s ↔ X0 s) := by
    intro s hs
    constructor
    · rintro ⟨Y, hY, hys⟩
      rcases le_or_gt s α with h | h
      · exact (D_agree hY hX0 (hY.1 s hys) ⟨s, hys, le_refl s⟩ ⟨δ, hδ, le_trans h hαδ⟩ s
          (lt_plus_self s)).mp hys
      · exact (D_agree hX0 hY hα hL0 ⟨s, hys, le_of_lt h⟩ s hs).mpr hys
    · intro h; exact ⟨X0, hX0, h⟩
  rw [hWX t ht, ← hX0.2 α hα hL0 t ht]
  exact WP_ext (C_ext (fun s hs => hWX s (lt_trans hs (lt_plus_self α)))) t

/-- `W` is well-founded. -/
theorem W_wf {t : T} (h : W t) : Acc (R W) t := D_wf D_W h

/-- Lemma 5. -/
theorem D_G {X : T → Prop} (hX : D X) {γ : T} (hγ : X γ) : G X γ := by
  refine ⟨hX.1 γ hγ, D_C_self hX hγ, ?_⟩
  intro t ht htγ
  have hwp : WP (C γ X) t := WP_down (D_WP_self hX hγ) ht htγ
  exact (hX.2 γ (hX.1 γ hγ) ⟨γ, hγ, le_refl γ⟩ t (lt_trans htγ (lt_plus_self γ))).mp hwp

/-! ## 部分の閉包と和（補題 6） -/

section
variable {X : T → Prop}

/-- Combine: if `x1 + y1 = x + y` and the parts `x1`, `y1` are closed under cutting, then `x`,
`y` are in `C`. -/
theorem C_split_combine {α : T} {x1 y1 x y : T}
    (h1 : C α X x1) (h2 : C α X y1)
    (cl1 : ∀ u v, x1 = app u v → u ≠ z → v ≠ z → C α X u ∧ C α X v)
    (cl2 : ∀ u v, y1 = app u v → u ≠ z → v ≠ z → C α X u ∧ C α X v)
    (he : app x1 y1 = app x y) (hx1 : x1 ≠ z) (hy1 : y1 ≠ z) (hx : x ≠ z) (hy : y ≠ z)
    (hot : isOT (app x y) = true) : C α X x ∧ C α X y := by
  rcases app_split he with ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩
  · by_cases hm : m = z
    · subst hm; simp only [app_z_right, app_z] at *; exact ⟨h1, h2⟩
    · obtain ⟨hcx, hcm⟩ := cl1 x m rfl hx hm
      exact ⟨hcx, C.sum hcm h2 hm hy1 (isOT_app_right hot)⟩
  · by_cases hm : m = z
    · subst hm; simp only [app_z_right, app_z] at *; exact ⟨h1, h2⟩
    · obtain ⟨hcm, hcy⟩ := cl2 m y rfl hm hy
      exact ⟨C.sum h1 hcm hx1 hm (isOT_app_left hot), hcy⟩

/-- The parts of an element of a distinguished `X`, or of `C^α(X)`, are again there. -/
theorem split_closed (hX : D X) : ∀ n t, size t ≤ n →
    (X t → ∀ x y, t = app x y → x ≠ z → y ≠ z → X x ∧ X y) ∧
    (∀ α, C α X t → ∀ x y, t = app x y → x ≠ z → y ≠ z → C α X x ∧ C α X y) := by
  intro n
  induction n with
  | zero =>
    intro t ht
    have : t = z := by cases t with | z => rfl | psi => simp [size] at ht
    subst this
    exact ⟨fun _ x y he hx _ => absurd (app_eq_z he.symm).1 hx,
      fun _ _ x y he hx _ => absurd (app_eq_z he.symm).1 hx⟩
  | succ n ih =>
    intro t ht
    have sumcase : ∀ α x1 y1, C α X x1 → C α X y1 → x1 ≠ z → y1 ≠ z → t = app x1 y1 →
        isOT t = true → ∀ x y, t = app x y → x ≠ z → y ≠ z → C α X x ∧ C α X y := by
      intro α x1 y1 h1 h2 hx1 hy1 he hot x y he' hx hy
      have hs1 : size x1 ≤ n := by
        have := size_lt_app_left (x := x1) hy1; rw [← he] at this; omega
      have hs2 : size y1 ≤ n := by
        have := size_lt_app_right (y := y1) hx1; rw [← he] at this; omega
      exact C_split_combine h1 h2 (fun u v e hu hv => (ih x1 hs1).2 α h1 u v e hu hv)
        (fun u v e hu hv => (ih y1 hs2).2 α h2 u v e hu hv) (he.symm.trans he') hx1 hy1 hx hy
        (he' ▸ hot)
    have xpart : X t → ∀ x y, t = app x y → x ≠ z → y ≠ z → X x ∧ X y := by
      intro hxt x y he hx hy
      have hG := D_G hX hxt
      have hot := hX.1 t hxt
      have hlt_x : x < t := he ▸ lt_app_left hx hy
      have hlt_y : y < t := he ▸ lt_app_right (he ▸ hot) hx
      have key : ∀ t', C t X t' → t' = t → C t X x ∧ C t X y := by
        intro t' hC' he''
        cases hC' with
        | zero => exact absurd (app_eq_z (he.symm.trans he''.symm)).1 hx
        | base _ hlt _ => exact absurd (he'' ▸ hlt) (lt_irrefl t)
        | sum h1 h2 hx1 hy1 _ => exact sumcase t _ _ h1 h2 hx1 hy1 he''.symm hot x y he hx hy
        | om _ => exact absurd (he.symm.trans he''.symm) (app_ne_principal hx hy _ _)
        | col _ _ _ _ _ => exact absurd (he.symm.trans he''.symm) (app_ne_principal hx hy _ _)
      have hcc := key t hG.2.1 rfl
      exact ⟨hG.2.2 x hcc.1 hlt_x, hG.2.2 y hcc.2 hlt_y⟩
    refine ⟨xpart, ?_⟩
    intro α hC x y he hx hy
    have key : ∀ t', C α X t' → t' = t → C α X x ∧ C α X y := by
      intro t' hC' he''
      cases hC' with
      | zero => exact absurd (app_eq_z (he.symm.trans he''.symm)).1 hx
      | base hb hlt hot =>
        have hb' : X t := he'' ▸ hb
        have hot' : isOT t = true := he'' ▸ hot
        have hlt' : t < α := he'' ▸ hlt
        obtain ⟨hxx, hxy⟩ := xpart hb' x y he hx hy
        exact ⟨C.base hxx (lt_trans (he ▸ lt_app_left hx hy) hlt') (isOT_app_left (he ▸ hot')),
          C.base hxy (lt_trans (he ▸ lt_app_right (he ▸ hot') hx) hlt') (isOT_app_right (he ▸ hot'))⟩
      | sum h1 h2 hx1 hy1 hot =>
        exact sumcase α _ _ h1 h2 hx1 hy1 he''.symm (he'' ▸ hot) x y he hx hy
      | om _ => exact absurd (he.symm.trans he''.symm) (app_ne_principal hx hy _ _)
      | col _ _ _ _ _ => exact absurd (he.symm.trans he''.symm) (app_ne_principal hx hy _ _)
    exact key t hC rfl

theorem C_split (hX : D X) {α t x y : T} (h : C α X t) (he : t = app x y) (hx : x ≠ z)
    (hy : y ≠ z) : C α X x ∧ C α X y :=
  (split_closed hX (size t) t (Nat.le_refl _)).2 α h x y he hx hy

/-- Lemma 6: a distinguished set is closed under (standard) sums. -/
theorem D_sum (hX : D X) {x y : T} (hx : X x) (hy : X y) (hx0 : x ≠ z) (hy0 : y ≠ z)
    (hot : isOT (app x y) = true) : X (app x y) := by
  have Hx := D_WP_self hX hx
  have hLx : LeSet x X := ⟨x, hx, le_refl x⟩
  have key : ∀ y', Acc (R (C x X)) y' → C x X y' → y' ≠ z → isOT (app x y') = true →
      Acc (R (C x X)) (app x y') := by
    intro y' hacc
    induction hacc with
    | intro y' _ ih =>
      intro hC hne hot'
      constructor
      rintro s ⟨hs, hslt⟩
      rcases le_or_gt s x with h | h
      · exact (WP_le Hx hs h).2
      · obtain ⟨d', rfl, hd'⟩ := decomp hx0 h hslt
        have hd'0 : d' ≠ z := by
          rintro rfl; simp only [app_z_right] at h; exact lt_irrefl _ h
        have hCd' : C x X d' := (C_split hX hs rfl hx0 hd'0).2
        exact ih d' ⟨hCd', hd'⟩ hCd' hd'0 (C_ot hs)
  have hylt : y < plus x := by
    have h1 : y < app x y := lt_app_right hot hx0
    rw [lt_plus_iff, ← lev_app y hx0]
    exact lev_le_of_le (le_of_lt h1)
  have hyW : WP (C x X) y := (hX.2 x (hX.1 x hx) hLx y hylt).mpr hy
  have hC : C x X (app x y) := C.sum (D_C hX hx x) (D_C hX hy x) hx0 hy0 hot
  have hlt : app x y < plus x := lt_plus_iff.mpr (by rw [lev_app y hx0])
  exact (hX.2 x (hX.1 x hx) hLx (app x y) hlt).mp ⟨hC, key y hyW.2 hyW.1 hy0 hot⟩

end

/-! ## G から区別された集合へ（補題 8）と 0 ∈ W（補題 9） -/

/-- The candidate distinguished set `W(C^α(Y)) ∩ α⁺`. -/
def XL (Y : T → Prop) (α : T) (t : T) : Prop := WP (C α Y) t ∧ t < plus α

/-- Condition (14). -/
def cond14 (Y : T → Prop) (α : T) : Prop :=
  ∀ β, isOT β = true → (∀ s, Y s → s < plus α → s < β) → plus β < plus α →
    ∀ t, WP (C β Y) t → t < plus β → Y t

theorem plus_lt_plus_of_lev_lt {β α : T} (h : lev β < lev α) : plus β < plus α :=
  om_lt_om.mpr (lt_of_le_of_lt (succ_le_of_lt h) (lt_succ_self _))

/-- Lemma 8. -/
theorem L315 {Y : T → Prop} (hY : D Y) {α : T} (hG : G Y α) (h14 : cond14 Y α) :
    XL Y α α ∧ D (XL Y α) := by
  have HY : ∀ γ, Y γ → C γ Y γ := fun γ h => D_C_self hY h
  -- (15)
  have h15 : ∀ t, t < α → (XL Y α t ↔ Y t) := by
    intro t ht
    constructor
    · rintro ⟨⟨hC, _⟩, _⟩; exact hG.2.2 t hC ht
    · intro hy
      refine ⟨⟨C.base hy ht (hY.1 t hy), ?_⟩, lt_trans ht (lt_plus_self α)⟩
      exact acc_transfer (D_wf hY hy) (fun s hs hcs => hG.2.2 s hcs (lt_trans hs ht))
  have hα : XL Y α α := by
    refine ⟨⟨hG.2.1, ?_⟩, lt_plus_self α⟩
    constructor
    rintro s ⟨hcs, hs⟩
    exact ((h15 s hs).mpr (hG.2.2 s hcs hs)).1.2
  -- Claim 3.16
  have claim : ∀ γ, lev γ = lev α → XL Y α γ → C γ (XL Y α) γ := by
    intro γ hl hγ
    have h1 : C γ Y γ := C_level_eq HY hl.symm hγ.1.1
    refine C_mono_X ?_ h1
    intro s hs hys
    have hcs : C α Y s := C_level_eq HY hl (C.base hys hs (hY.1 s hys))
    exact ⟨WP_down hγ.1 hcs hs, lt_trans hs hγ.2⟩
  have HX : ∀ γ, XL Y α γ → C γ (XL Y α) γ := by
    intro γ hγ
    rcases lt_or_ge γ α with h | h
    · have hy := (h15 γ h).mp hγ
      exact C_mono_X (fun s hs hys => (h15 s (lt_trans hs h)).mpr hys) (HY γ hy)
    · have hl : lev γ = lev α :=
        le_antisymm (lt_plus_iff.mp hγ.2) (lev_le_of_le h)
      exact claim γ hl hγ
  refine ⟨hα, fun t ht => C_ot ht.1.1, ?_⟩
  intro β hβ ⟨δ, hXδ, hβδ⟩ t ht
  have hβα : lev β ≤ lev α := lt_plus_iff.mp (lt_of_le_of_lt hβδ hXδ.2)
  rcases (le_iff _ _).mp hβα with hlt | heq
  · have hpl : plus β < plus α := plus_lt_plus_of_lev_lt hlt
    have hpa : plus β ≤ α := plus_le_of_plus_lt hpl
    have htα : t < α := lt_of_lt_of_le ht hpa
    have hβα' : β < α := lt_of_lt_of_le (lt_plus_self β) hpa
    have hCeq : ∀ s, C β (XL Y α) s ↔ C β Y s := C_ext (fun s hs => h15 s (lt_trans hs hβα'))
    rw [WP_ext hCeq t, h15 t htα]
    by_cases hsub : ∀ s, Y s → s < plus α → s < β
    · constructor
      · intro hw; exact h14 β hβ hsub hpl t hw ht
      · intro hy
        have htβ : t < β := hsub t hy (lt_trans htα (lt_plus_self α))
        refine ⟨C.base hy htβ (hY.1 t hy), ?_⟩
        exact acc_transfer (D_WP_self hY hy).2
          (fun s _ hcs => C_down HY (le_of_lt htβ) hcs)
    · have hL : LeSet β Y := by
        apply Classical.byContradiction; intro hn; apply hsub; intro s hs hsa
        rcases lt_or_ge s β with h | h
        · exact h
        · exact absurd ⟨s, hs, h⟩ hn
      exact hY.2 β hβ hL t ht
  · have hCeq : ∀ s, C β (XL Y α) s ↔ C α Y s := by
      intro s
      rw [← C_ext (fun u hu => h15 u hu) s]
      exact ⟨C_level_eq HX heq, C_level_eq HX heq.symm⟩
    have hpl : plus β = plus α := by simp [plus, heq]
    rw [WP_ext hCeq t]
    exact ⟨fun h => ⟨h, hpl ▸ ht⟩, fun h => h.1⟩

theorem succ_ne_z (x : T) : succ x ≠ z := by
  cases x with
  | z => simp [succ, one]
  | psi => simp [succ]

/-- Lemma 9: `0 ∈ W`. -/
theorem zero_W : W z := by
  have hD0 : D (fun _ => False) := ⟨fun _ h => h.elim, fun _ _ ⟨_, h, _⟩ _ _ => h.elim⟩
  have hG0 : G (fun _ => False) z := ⟨rfl, C.zero, fun t _ h => absurd h (T.not_lt_z t)⟩
  have h14 : cond14 (fun _ => False) z := by
    intro β _ _ hpl
    exfalso
    simp only [plus, lev_z, om_lt_om] at hpl
    have : succ (lev β) = z := lt_one_iff.mp (by simpa [succ] using hpl)
    exact succ_ne_z _ this
  obtain ⟨h1, h2⟩ := L315 hD0 hG0 h14
  exact ⟨_, h2, h1⟩

end Ytosk
