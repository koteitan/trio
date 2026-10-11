/-
**PH3c の種類と FC3 の結論は、引数を下から挟むと保たれる（closure、2026-10-11）。**

1 列落としでは、B ≠ 0 の書き換えの枠で v(i)・B・s は変わらず、最後の数える子の引数だけが y から y′ ≤ y に下がる
（実測、deepA の全行列）。ここでは行列によらない順序数の補題を示す: B < y′ ≤ y なら
`PH3cKind B hi lo s` から `PH3cKind B hi′ lo′ s` が出る（hi・lo、hi′・lo′ は y・y′ を Ω_{s+1} で分けたもの）。
FC3 の結論も同様。使うのは辞書式の順序の性質だけで、標準形の仮定は要らない。
-/
import Ytosk.V3PDef

namespace Ytosk

open T

/-! ## 辞書式の挟み込み -/

/-- Squeezed between two terms with the same head summand, the head is the same. -/
theorem squeeze_head {a b c d a' b' c' : T} (h1 : psi a b c < psi a' b' c')
    (h2 : psi a' b' c' ≤ psi a b d) : a' = a ∧ b' = b ∧ c < c' ∧ c' ≤ d := by
  rw [T.psi_lt_psi] at h1
  rcases (le_iff _ _).mp h2 with h2 | h2
  · rw [T.psi_lt_psi] at h2
    rcases h1 with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, h1⟩
    · rcases h2 with h2 | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact absurd (T.lt_trans' h1 h2) (lt_irrefl' _)
      · exact absurd h1 (lt_irrefl' _)
      · exact absurd h1 (lt_irrefl' _)
    · rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, rfl, _⟩
      · exact absurd h2 (lt_irrefl' _)
      · exact absurd (T.lt_trans' h1 h2) (lt_irrefl' _)
      · exact absurd h1 (lt_irrefl' _)
    · rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, _, h2⟩
      · exact absurd h2 (lt_irrefl' _)
      · exact absurd h2 (lt_irrefl' _)
      · exact ⟨rfl, rfl, h1, le_of_lt h2⟩
  · obtain ⟨rfl, rfl, rfl⟩ := T.psi.inj h2
    rcases h1 with h1 | ⟨_, h1⟩ | ⟨_, _, h1⟩
    · exact absurd h1 (lt_irrefl' _)
    · exact absurd h1 (lt_irrefl' _)
    · exact ⟨rfl, rfl, h1, le_refl _⟩

/-- Below `psi a b d` and above a term with head subscript `t`: the subscript is between. -/
theorem sub_le_of_le {a b d a' b' c' : T} (h : psi a' b' c' ≤ psi a b d) : a' ≤ a := by
  rcases (le_iff _ _).mp h with h | h
  · rw [T.psi_lt_psi] at h
    rcases h with h | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact le_of_lt h
    · exact le_refl _
    · exact le_refl _
  · obtain ⟨rfl, _, _⟩ := T.psi.inj h; exact le_refl _

/-- **Prefix squeeze**: strictly above `B` and at most `B + R`, a term is `B + r` with `r ≠ 0`. -/
theorem app_squeeze : ∀ (B : T) {y R : T}, B < y → y ≤ app B R → ∃ r, r ≠ z ∧ y = app B r
  | z, y, _, h1, _ => ⟨y, fun h => by subst h; exact T.not_lt_z _ h1, rfl⟩
  | psi a b c, y, R, h1, h2 => by
    cases y with
    | z => exact absurd h1 (T.not_lt_z _)
    | psi a' b' c' =>
      obtain ⟨rfl, rfl, h1', h2'⟩ := squeeze_head h1 (by simpa [app] using h2)
      obtain ⟨r, hr, rfl⟩ := app_squeeze c h1' h2'
      exact ⟨r, hr, rfl⟩

theorem app_eq_self : ∀ {B X : T}, app B X = B → X = z
  | z, X, h => h
  | psi _ _ c, _, h => app_eq_self (T.psi.inj h).2.2

/-- Splitting `B + r` when every summand of `B` is at least `θ`. -/
theorem split_app_ge {θ : T} : ∀ {B : T} (r : T), (∀ q ∈ summands B, ¬ q < θ) →
    split (app B r) θ = (app B (split r θ).1, (split r θ).2)
  | z, r, _ => rfl
  | psi a b c, r, h => by
    simp only [app, split]
    rw [if_neg (show ¬ lt (psi a b z) θ = true from h _ (by simp [summands]))]
    rw [split_app_ge r (fun q hq => h q (by simp [summands, hq]))]

theorem summands_app_left : ∀ {B R q : T}, q ∈ summands B → q ∈ summands (app B R)
  | z, _, _, h => by simp [summands] at h
  | psi a b c, R, q, h => by
    simp only [summands, List.mem_cons, app] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (summands_app_left h)

/-! ## 切り口の挟み込み -/

/-- Membership in `cutsH` at a summand. -/
theorem mem_cutsH_psi {s a x c t : T} : t ∈ cutsH s (psi a x c) ↔
    (le s a = true ∧ t = psi s z z) ∨ (∃ u ∈ cutsH s a, t = psi u z z) ∨
      (le s a = true ∧ ∃ u ∈ cutsH s x, t = psi a u z) ∨ (∃ u ∈ cutsH s c, t = psi a x u) := by
  show t ∈ (if le s a then [psi s z z] else []) ++ (cutsH s a).map (fun t => psi t z z) ++
    (if le s a then (cutsH s x).map (fun t => psi a t z) else []) ++ (cutsH s c).map (fun t => psi a x t) ↔ _
  by_cases h : le s a = true
  · simp only [h, if_true, List.mem_append, List.mem_singleton, List.mem_map, true_and]
    constructor
    · rintro (((rfl | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨u, hu, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨u, hu, rfl⟩))
    · rintro (rfl | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · exact Or.inl (Or.inl (Or.inl rfl))
      · exact Or.inl (Or.inl (Or.inr ⟨u, hu, rfl⟩))
      · exact Or.inl (Or.inr ⟨u, hu, rfl⟩)
      · exact Or.inr ⟨u, hu, rfl⟩
  · have h' : le s a = false := by simpa using h
    rw [h']
    simp only [Bool.false_eq_true, if_false, List.mem_append, List.mem_map, List.not_mem_nil, false_or,
      or_false, false_and]
    constructor
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · exact Or.inl ⟨u, hu, rfl⟩
      · exact Or.inr ⟨u, hu, rfl⟩
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · exact Or.inl ⟨u, hu, rfl⟩
      · exact Or.inr ⟨u, hu, rfl⟩

/-- A cut is a cut of itself. -/
theorem cutsH_self {s : T} : ∀ {h t : T}, t ∈ cutsH s h → t ∈ cutsH s t
  | z, _, ht => by simp [cutsH] at ht
  | psi a x c, t, ht => by
    rcases mem_cutsH_psi.mp ht with ⟨_, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hs, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact mem_cutsH_psi.mpr (Or.inl ⟨by simp [le], rfl⟩)
    · exact mem_cutsH_psi.mpr (Or.inr (Or.inl ⟨u, cutsH_self hu, rfl⟩))
    · exact mem_cutsH_psi.mpr (Or.inr (Or.inr (Or.inl ⟨hs, u, cutsH_self hu, rfl⟩)))
    · exact mem_cutsH_psi.mpr (Or.inr (Or.inr (Or.inr ⟨u, cutsH_self hu, rfl⟩)))

theorem scuts_self {s : T} : ∀ {h t : T}, t ∈ scuts s h → t ∈ scuts s t
  | z, _, ht => by simp [scuts] at ht
  | psi a x c, t, ht => by
    simp only [scuts, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨u, hu, rfl⟩
    · split at ht
      · simp only [List.mem_singleton] at ht; subst ht; simp [scuts, le]
      · simp at ht
    · simp only [scuts, List.mem_append, List.mem_map]
      exact Or.inr ⟨u, scuts_self hu, rfl⟩

/-- **Cut squeeze**: a cut of `h` stays a cut of every `w` between it and `h`. -/
theorem mem_cutsH_squeeze {s : T} : ∀ {h t w : T}, t ∈ cutsH s h → t ≤ w → w ≤ h → t ∈ cutsH s w
  | z, _, _, ht, _, _ => by simp [cutsH] at ht
  | psi a x c, t, w, ht, h1, h2 => by
    rcases (le_iff _ _).mp h1 with h1 | rfl
    swap
    · exact cutsH_self ht
    cases w with
    | z => exact absurd h1 (T.not_lt_z _)
    | psi a' x' c' =>
      have ha : a' ≤ a := sub_le_of_le h2
      rcases mem_cutsH_psi.mp ht with ⟨_, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hs, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · -- top: `t = Ω_s` with `s ≤ a`
        refine mem_cutsH_psi.mpr (Or.inl ⟨?_, rfl⟩)
        rw [T.psi_lt_psi] at h1
        rcases h1 with h1 | ⟨rfl, _⟩ | ⟨rfl, _⟩
        · simp [le, show lt s a' = true from h1]
        · simp [le]
        · simp [le]
      · -- subscript
        refine mem_cutsH_psi.mpr (Or.inr (Or.inl ⟨u, mem_cutsH_squeeze hu ?_ ha, rfl⟩))
        rw [T.psi_lt_psi] at h1
        rcases h1 with h1 | ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact le_of_lt h1
        · exact le_refl _
        · exact le_refl _
      · -- argument
        rw [T.psi_lt_psi] at h1
        have ha' : a = a' := by
          rcases h1 with h1 | ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd (lt_of_lt_of_le h1 ha) (lt_irrefl' _)
          · exact h
          · exact h
        subst ha'
        have hx : x' ≤ x := by
          rcases (le_iff _ _).mp h2 with h2 | h2
          · rw [T.psi_lt_psi] at h2
            rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, rfl, _⟩
            · exact absurd h2 (lt_irrefl' _)
            · exact le_of_lt h2
            · exact le_refl _
          · rw [(T.psi.inj h2).2.1]
        have hu' : u ≤ x' := by
          rcases h1 with h1 | ⟨_, h1⟩ | ⟨_, rfl, _⟩
          · exact absurd h1 (lt_irrefl' _)
          · exact le_of_lt h1
          · exact le_refl _
        exact mem_cutsH_psi.mpr (Or.inr (Or.inr (Or.inl ⟨hs, u, mem_cutsH_squeeze hu hu' hx, rfl⟩)))
      · -- rest
        obtain ⟨rfl, rfl, h1', h2'⟩ := squeeze_head h1 h2
        exact mem_cutsH_psi.mpr (Or.inr (Or.inr (Or.inr ⟨u, mem_cutsH_squeeze hu (le_of_lt h1') h2', rfl⟩)))

/-- The same for the subscript chain. -/
theorem mem_scuts_squeeze {s : T} : ∀ {h t w : T}, t ∈ scuts s h → t ≤ w → w ≤ h → t ∈ scuts s w
  | z, _, _, ht, _, _ => by simp [scuts] at ht
  | psi a x c, t, w, ht, h1, h2 => by
    rcases (le_iff _ _).mp h1 with h1 | rfl
    swap
    · exact scuts_self ht
    cases w with
    | z => exact absurd h1 (T.not_lt_z _)
    | psi a' x' c' =>
      have ha : a' ≤ a := sub_le_of_le h2
      simp only [scuts, List.mem_append, List.mem_map] at ht ⊢
      rcases ht with ht | ⟨u, hu, rfl⟩
      · split at ht
        · simp only [List.mem_singleton] at ht; subst ht
          left
          rw [T.psi_lt_psi] at h1
          have : le s a' = true := by
            rcases h1 with h1 | ⟨rfl, _⟩ | ⟨rfl, _⟩
            · simp [le, show lt s a' = true from h1]
            · simp [le]
            · simp [le]
          simp [this]
        · simp at ht
      · right
        refine ⟨u, mem_scuts_squeeze hu ?_ ha, rfl⟩
        rw [T.psi_lt_psi] at h1
        rcases h1 with h1 | ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact le_of_lt h1
        · exact le_refl _
        · exact le_refl _

/-- Every element of the subscript chain is at least `Ω_s`. -/
theorem scuts_ge {s : T} : ∀ {h t : T}, t ∈ scuts s h → psi s z z ≤ t
  | z, _, ht => by simp [scuts] at ht
  | psi a x c, t, ht => by
    simp only [scuts, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨u, hu, rfl⟩
    · split at ht
      · simp only [List.mem_singleton] at ht; subst ht; exact le_refl _
      · simp at ht
    · have h1 := scuts_ge hu
      have hs : s < u := lt_of_lt_of_le (lt_Om_self s) h1
      exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inl hs)

/-! ## PH3c の種類 -/

/-- A summand at least `Ω_{s+1}` whose subscript is above `s`. -/
theorem not_lt_om_succ {s a x : T} (h : s < a) : ¬ psi a x z < psi (succ s) z z := by
  intro h'
  rw [psi_lt_psi_z_iff] at h'
  rcases h' with h' | ⟨rfl, h'⟩
  · exact absurd (lt_of_lt_of_le h (lt_succ_iff.mp h')) (lt_irrefl' _)
  · exact absurd h' (T.not_lt_z _)

/-- **The cut positions survive**: `B ∈ cutsNS s hi` and `B < y′ ≤ hi + lo` give `B ∈ cutsNS s hi′`. -/
theorem cutsNS_squeeze {s : T} : ∀ {hi B y' lo : T}, (∀ q ∈ summands hi, ¬ q < psi (succ s) z z) →
    B ∈ cutsNS s hi → B < y' → y' ≤ app hi lo → B ∈ cutsNS s (split y' (psi (succ s) z z)).1
  | z, _, _, _, _, hB, _, _ => by simp [cutsNS] at hB
  | psi a x c, B, y', lo, hge, hB, h1, h2 => by
    cases y' with
    | z => exact absurd h1 (T.not_lt_z _)
    | psi a' x' c' =>
      have h2' : psi a' x' c' ≤ psi a x (app c lo) := by simpa [app] using h2
      have ha : a' ≤ a := sub_le_of_le h2'
      have hgeA : ¬ psi a x z < psi (succ s) z z := hge _ (by simp [summands])
      simp only [cutsNS, List.mem_append, List.mem_map] at hB
      rcases hB with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩
      · -- subscript chain
        have hua : u ≤ a' := by
          rw [T.psi_lt_psi] at h1
          rcases h1 with h1 | ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact le_of_lt h1
          · exact le_refl _
          · exact le_refl _
        have hsa : s < a' := lt_of_lt_of_le (lt_of_lt_of_le (lt_Om_self s) (scuts_ge hu)) hua
        simp only [split]
        rw [if_neg (show ¬ lt (psi a' x' z) (psi (succ s) z z) = true from not_lt_om_succ hsa)]
        simp only [cutsNS, List.mem_append, List.mem_map]
        exact Or.inl (Or.inl ⟨u, mem_scuts_squeeze hu hua ha, rfl⟩)
      · -- argument
        rw [T.psi_lt_psi] at h1
        have ha' : a = a' := by
          rcases h1 with h1 | ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd (lt_of_lt_of_le h1 ha) (lt_irrefl' _)
          · exact h
          · exact h
        subst ha'
        have hx : x' ≤ x := by
          rcases (le_iff _ _).mp h2' with h2 | h2
          · rw [T.psi_lt_psi] at h2
            rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, rfl, _⟩
            · exact absurd h2 (lt_irrefl' _)
            · exact le_of_lt h2
            · exact le_refl _
          · rw [(T.psi.inj h2).2.1]
        have hu' : u ≤ x' := by
          rcases h1 with h1 | ⟨_, h1⟩ | ⟨_, rfl, _⟩
          · exact absurd h1 (lt_irrefl' _)
          · exact le_of_lt h1
          · exact le_refl _
        have hge' : ¬ psi a x' z < psi (succ s) z z := by
          intro h; apply hgeA
          rw [psi_lt_psi_z_iff] at h ⊢
          rcases h with h | ⟨h, h'⟩
          · exact Or.inl h
          · exact absurd h' (T.not_lt_z _)
        simp only [split]
        rw [if_neg (show ¬ lt (psi a x' z) (psi (succ s) z z) = true from hge')]
        simp only [cutsNS, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨u, mem_cutsH_squeeze hu hu' hx, rfl⟩)
      · -- a later summand
        obtain ⟨rfl, rfl, h1', h2''⟩ := squeeze_head h1 h2'
        simp only [split]
        rw [if_neg (show ¬ (lt _ _ = true) from hgeA)]
        simp only [cutsNS, List.mem_append, List.mem_map]
        exact Or.inr ⟨u, cutsNS_squeeze (fun q hq => hge q (by simp [summands, hq])) hu h1' h2'', rfl⟩

/-- **The kind is kept** when the argument goes down to `y′` with `B < y′ ≤ y`. -/
theorem ph3cKind_squeeze {B s y y' : T} (hK : PH3cKind B (split y (psi (succ s) z z)).1
      (split y (psi (succ s) z z)).2 s) (h1 : B < y') (h2 : y' ≤ y) :
    PH3cKind B (split y' (psi (succ s) z z)).1 (split y' (psi (succ s) z z)).2 s := by
  set θ := psi (succ s) z z
  have hy : app (split y θ).1 (split y θ).2 = y := split_app θ y
  have hge := split_fst_ge θ y
  rcases hK with ⟨hhi, hlo⟩ | ⟨hne, (⟨R, hR, hhi⟩ | ⟨hs, hc⟩)⟩
  · -- eq
    rcases (le_iff _ _).mp h2 with h2 | rfl
    swap
    · exact Or.inl ⟨hhi, hlo⟩
    rw [← hy, hhi] at h2
    obtain ⟨r, hr, rfl⟩ := app_squeeze B h1 (le_of_lt h2)
    have hrl : r < (split y θ).2 := (app_lt_app_left_iff B).mp h2
    have hlow : r = z ∨ head r < θ := by
      rcases split_snd_head θ y with h | h
      · rw [h] at hrl; exact absurd hrl (T.not_lt_z _)
      · exact Or.inr (lt_of_le_of_lt (head_le_of_lt hrl) h)
    have hB : ∀ q ∈ summands B, ¬ q < θ := by rw [← hhi]; exact hge
    rw [split_app_of hB hlow]
    exact Or.inl ⟨rfl, hr⟩
  · -- pre
    have hB : ∀ q ∈ summands B, ¬ q < θ := fun q hq => hge q (by rw [hhi]; exact summands_app_left hq)
    have hy' : y = app B (app R (split y θ).2) := by
      have := hy.symm; rw [hhi, app_assoc] at this; exact this
    rw [hy'] at h2
    obtain ⟨r, hr, rfl⟩ := app_squeeze B h1 h2
    rw [split_app_ge r hB]
    by_cases hr1 : (split r θ).1 = z
    · have hr2 : (split r θ).2 = r := by
        have := split_app θ r; rw [hr1] at this; exact this
      rw [hr1, hr2]
      exact Or.inl ⟨by simp, hr⟩
    · refine Or.inr ⟨fun h => hr1 (app_eq_self h), Or.inl ⟨_, hr1, rfl⟩⟩
  · -- cut
    have hc' := cutsNS_squeeze hge hc h1 (by rw [hy]; exact h2)
    by_cases hh : (split y' θ).1 = B
    · refine Or.inl ⟨hh, fun hl => ?_⟩
      have := split_app θ y'
      rw [hh, hl, app_z_right] at this
      rw [this] at h1
      exact lt_irrefl' _ h1
    · exact Or.inr ⟨hh, Or.inr ⟨hs, hc'⟩⟩

/-! ## FC3 の結論 -/

/-- The high part of `psi a x c` at `Ω_{s+1}`, when the head is high. -/
theorem split_hi_psi {s a x c : T} (h : ¬ psi a x z < psi (succ s) z z) :
    (split (psi a x c) (psi (succ s) z z)).1 = psi a x (split c (psi (succ s) z z)).1 := by
  simp only [split]; rw [if_neg (show ¬ (lt _ _ = true) from h)]

theorem split_hi_ne_z {s a x c : T} (h : (split (psi a x c) (psi (succ s) z z)).1 ≠ z) :
    ¬ psi a x z < psi (succ s) z z := by
  intro h'; apply h; simp only [split]; rw [if_pos (show lt _ _ = true from h')]

/-- **The FC3 conclusion is kept** when the argument goes down to `y′ ≤ y` (same `v`, `s`). -/
theorem fc3_squeeze {v s y y' : T}
    (hM : y ≠ z → lt (psi v z z) (psi s y z) = true → (split y (psi (succ s) z z)).1 ≠ z →
      (s = v → s ≠ z ∧ last s ≠ one) ∧
      (s ≠ v → ∃ X, X ≠ z ∧ lev (split y (psi (succ s) z z)).1 = app s X))
    (h2 : y' ≤ y) (hrw : lt (psi v z z) (psi s y' z) = true) (hhi : (split y' (psi (succ s) z z)).1 ≠ z) :
    (s = v → s ≠ z ∧ last s ≠ one) ∧
      (s ≠ v → ∃ X, X ≠ z ∧ lev (split y' (psi (succ s) z z)).1 = app s X) := by
  cases y' with
  | z => simp [split] at hhi
  | psi a' x' c' =>
    cases y with
    | z => exact absurd ((le_iff _ _).mp h2) (by simp)
    | psi a x c =>
      have ha : a' ≤ a := sub_le_of_le h2
      have hge' := split_hi_ne_z hhi
      have hsa : succ s ≤ a' := by
        rcases lt_or_ge a' (succ s) with h | h
        · exact absurd (by rw [psi_lt_psi_z_iff]; exact Or.inl h) hge'
        · exact h
      have hge : ¬ psi a x z < psi (succ s) z z := by
        intro h; rw [psi_lt_psi_z_iff] at h
        rcases h with h | ⟨rfl, h⟩
        · exact absurd (lt_of_le_of_lt (le_trans hsa ha) h) (lt_irrefl' _)
        · exact T.not_lt_z _ h
      have hrwM : lt (psi v z z) (psi s (psi a x c) z) = true := by
        have : psi s (psi a' x' c') z ≤ psi s (psi a x c) z := by
          rcases (le_iff _ _).mp h2 with h | h
          · exact le_of_lt (by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h⟩)
          · rw [h]
        exact lt_of_lt_of_le (show psi v z z < _ from hrw) this
      have hhiM : (split (psi a x c) (psi (succ s) z z)).1 ≠ z := by
        rw [split_hi_psi hge]; simp
      obtain ⟨hA, hB⟩ := hM (by simp) hrwM hhiM
      refine ⟨hA, fun hne => ?_⟩
      obtain ⟨X, hX, hlev⟩ := hB hne
      rw [split_hi_psi hge] at hlev
      rw [split_hi_psi hge']
      simp only [lev] at hlev ⊢
      have hs : s < a' := lt_of_lt_of_le (lt_succ_self s) hsa
      exact app_squeeze s hs (by rw [← hlev]; exact ha)

end Ytosk
