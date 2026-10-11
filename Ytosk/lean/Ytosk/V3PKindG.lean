/-
**G3 の切り口の挟み込み（closure、2026-10-12）。**

V3PKind の `mem_cutsH_squeeze`・`cutsNS_squeeze`・`ph3cKind_squeeze` の G3 版。新しい場合（添字の中の位置）は
同じ帰納法で通る。状態の段では「切り口の要素は s より大きい」（`cutsHG_gt`、標準形の仮定つき）を使う。
-/
import Ytosk.V3PKind
import Ytosk.V3PSh

namespace Ytosk

open T

/-! ## 基本 -/

theorem psi_le_psi_anyG {s a x c : T} (h : s ≤ a) : psi s z z ≤ psi a x c :=
  le_trans (psi_le_psi_z (y := x) h) (by
    rcases (le_iff _ _).mp (z_le c) with h' | h'
    · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h'⟩))
    · rw [h'])

/-- Membership in `cutsHG` at a summand. -/
theorem mem_cutsHG_psi {s a x c t : T} : t ∈ cutsHG s (psi a x c) ↔
    (le s a = true ∧ t = psi s z z) ∨ (∃ u ∈ cutsHG s a, t = psi u z z) ∨
      (le s a = true ∧ ∃ u ∈ cutsHG s x, t = psi a u z) ∨ (le s a = true ∧ ∃ u ∈ cutsHG s c, t = psi a x u) := by
  show t ∈ (cutsHG s a).map (fun t => psi t z z) ++
    (if le s a then [psi s z z] ++ (cutsHG s x).map (fun t => psi a t z) ++
      (cutsHG s c).map (fun t => psi a x t) else []) ↔ _
  by_cases h : le s a = true
  · simp only [h, if_true, List.mem_append, List.mem_singleton, List.mem_map, true_and]
    constructor
    · rintro (⟨u, hu, rfl⟩ | ((rfl | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩))
      · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨u, hu, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨u, hu, rfl⟩))
    · rintro (rfl | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · exact Or.inr (Or.inl (Or.inl rfl))
      · exact Or.inl ⟨u, hu, rfl⟩
      · exact Or.inr (Or.inl (Or.inr ⟨u, hu, rfl⟩))
      · exact Or.inr (Or.inr ⟨u, hu, rfl⟩)
  · have h' : le s a = false := by simpa using h
    rw [h']
    simp only [Bool.false_eq_true, if_false, List.mem_append, List.mem_map, List.not_mem_nil, or_false,
      false_and, false_or]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

/-- Membership in `cutsNSG` at a summand. -/
theorem mem_cutsNSG_psi {s a x c t : T} : t ∈ cutsNSG s (psi a x c) ↔
    (∃ u ∈ cutsHG s a, t = psi u z z) ∨ (∃ u ∈ cutsHG s x, t = psi a u z) ∨
      (∃ u ∈ cutsNSG s c, t = psi a x u) := by
  show t ∈ (cutsHG s a).map (fun t => psi t z z) ++ (cutsHG s x).map (fun t => psi a t z) ++
    (cutsNSG s c).map (fun t => psi a x t) ↔ _
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro ((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
    · exact Or.inl ⟨u, hu, rfl⟩
    · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
    · exact Or.inr (Or.inr ⟨u, hu, rfl⟩)
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact Or.inl (Or.inl ⟨u, hu, rfl⟩)
    · exact Or.inl (Or.inr ⟨u, hu, rfl⟩)
    · exact Or.inr ⟨u, hu, rfl⟩

theorem psi_le_psi_lead {a x c a' x' c' : T} (h : a ≤ a') (hne : a < a' ∨ (a = a' ∧ psi a x c ≤ psi a' x' c')) :
    psi a x c ≤ psi a' x' c' := by
  rcases hne with h' | ⟨rfl, h'⟩
  · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inl h')
  · exact h'

/-- **A cut is at most the term.** -/
theorem cutsHG_le {s : T} : ∀ {h t : T}, t ∈ cutsHG s h → t ≤ h
  | z, _, ht => by simp [cutsHG] at ht
  | psi a x c, t, ht => by
    rcases mem_cutsHG_psi.mp ht with ⟨hs, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨_, u, hu, rfl⟩ | ⟨_, u, hu, rfl⟩
    · exact le_trans (psi_le_psi_z (le_of_le_bool hs)) (psi_le_psi_anyG (le_refl a))
    · exact psi_le_psi_anyG (cutsHG_le hu)
    · rcases (le_iff _ _).mp (cutsHG_le hu) with h | rfl
      · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, h⟩))
      · exact le_trans (le_refl _) (by
          rcases (le_iff _ _).mp (z_le c) with h | h
          · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩))
          · rw [h])
    · rcases (le_iff _ _).mp (cutsHG_le hu) with h | rfl
      · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩))
      · exact le_refl _

theorem cutsNSG_le {s : T} : ∀ {h t : T}, t ∈ cutsNSG s h → t ≤ h
  | z, _, ht => by simp [cutsNSG] at ht
  | psi a x c, t, ht => by
    rcases mem_cutsNSG_psi.mp ht with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact psi_le_psi_anyG (cutsHG_le hu)
    · rcases (le_iff _ _).mp (cutsHG_le hu) with h | rfl
      · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, h⟩))
      · rcases (le_iff _ _).mp (z_le c) with h | h
        · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩))
        · rw [h]
    · rcases (le_iff _ _).mp (cutsNSG_le hu) with h | rfl
      · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩))
      · exact le_refl _

/-- A cut is a cut of itself. -/
theorem cutsHG_self {s : T} : ∀ {h t : T}, t ∈ cutsHG s h → t ∈ cutsHG s t
  | z, _, ht => by simp [cutsHG] at ht
  | psi a x c, t, ht => by
    rcases mem_cutsHG_psi.mp ht with ⟨_, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hs, u, hu, rfl⟩ | ⟨hs, u, hu, rfl⟩
    · exact mem_cutsHG_psi.mpr (Or.inl ⟨by simp [le], rfl⟩)
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inl ⟨u, cutsHG_self hu, rfl⟩))
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨hs, u, cutsHG_self hu, rfl⟩)))
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨hs, u, cutsHG_self hu, rfl⟩)))

/-! ## 挟み込み -/

/-- **Cut squeeze** (G3): a cut of `h` stays a cut of every `w` between it and `h`. -/
theorem mem_cutsHG_squeeze {s : T} : ∀ {h t w : T}, t ∈ cutsHG s h → t ≤ w → w ≤ h → t ∈ cutsHG s w
  | z, _, _, ht, _, _ => by simp [cutsHG] at ht
  | psi a x c, t, w, ht, h1, h2 => by
    rcases (le_iff _ _).mp h1 with h1 | rfl
    swap
    · exact cutsHG_self ht
    cases w with
    | z => exact absurd h1 (T.not_lt_z _)
    | psi a' x' c' =>
      have ha : a' ≤ a := sub_le_of_le h2
      rcases mem_cutsHG_psi.mp ht with ⟨_, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hs, u, hu, rfl⟩ | ⟨hs, u, hu, rfl⟩
      · refine mem_cutsHG_psi.mpr (Or.inl ⟨?_, rfl⟩)
        rw [T.psi_lt_psi] at h1
        rcases h1 with h1 | ⟨rfl, _⟩ | ⟨rfl, _⟩
        · simp [le, show lt s a' = true from h1]
        · simp [le]
        · simp [le]
      · -- inside the subscript
        have hua : u ≤ a' := by
          rw [T.psi_lt_psi] at h1
          rcases h1 with h1 | ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact le_of_lt h1
          · exact le_refl _
          · exact le_refl _
        exact mem_cutsHG_psi.mpr (Or.inr (Or.inl ⟨u, mem_cutsHG_squeeze hu hua ha, rfl⟩))
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
        exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨hs, u, mem_cutsHG_squeeze hu hu' hx, rfl⟩)))
      · -- rest
        obtain ⟨rfl, rfl, h1', h2'⟩ := squeeze_head h1 h2
        exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨hs, u, mem_cutsHG_squeeze hu (le_of_lt h1') h2', rfl⟩)))

/-! ## 状態の段 -/

/-- **A cut is above `s`.** -/
theorem cutsHG_gt {s : T} : ∀ {h t : T}, t ∈ cutsHG s h → s < t
  | z, _, ht => by simp [cutsHG] at ht
  | psi a x c, t, ht => by
    rcases mem_cutsHG_psi.mp ht with ⟨_, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hsa, u, hu, rfl⟩ | ⟨hsa, u, hu, rfl⟩
    · exact lt_Om_self s
    · exact lt_trans (cutsHG_gt hu) (lt_Om_self u)
    · exact lt_of_lt_of_le (lt_Om_self s) (psi_le_psi_anyG (le_of_le_bool hsa))
    · exact lt_of_lt_of_le (lt_Om_self s) (psi_le_psi_anyG (le_of_le_bool hsa))

/-- **The cut positions survive** (G3): `B ∈ cutsNSG s hi` and `B < y′ ≤ hi + lo` give `B ∈ cutsNSG s hi′`. -/
theorem cutsNSG_squeeze {s : T} : ∀ {hi B y' lo : T},
    (∀ q ∈ summands hi, ¬ q < psi (succ s) z z) →
    B ∈ cutsNSG s hi → B < y' → y' ≤ app hi lo → B ∈ cutsNSG s (split y' (psi (succ s) z z)).1
  | z, _, _, _, _, hB, _, _ => by simp [cutsNSG] at hB
  | psi a x c, B, y', lo, hge, hB, h1, h2 => by
    cases y' with
    | z => exact absurd h1 (T.not_lt_z _)
    | psi a' x' c' =>
      have h2' : psi a' x' c' ≤ psi a x (app c lo) := by simpa [app] using h2
      have ha : a' ≤ a := sub_le_of_le h2'
      have hgeA : ¬ psi a x z < psi (succ s) z z := hge _ (by simp [summands])
      rcases mem_cutsNSG_psi.mp hB with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · -- inside the subscript
        have hua : u ≤ a' := by
          rw [T.psi_lt_psi] at h1
          rcases h1 with h1 | ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact le_of_lt h1
          · exact le_refl _
          · exact le_refl _
        have hsa : s < a' := lt_of_lt_of_le (cutsHG_gt hu) hua
        simp only [split]
        rw [if_neg (show ¬ lt (psi a' x' z) (psi (succ s) z z) = true from not_lt_om_succ hsa)]
        exact mem_cutsNSG_psi.mpr (Or.inl ⟨u, mem_cutsHG_squeeze hu hua ha, rfl⟩)
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
        exact mem_cutsNSG_psi.mpr (Or.inr (Or.inl ⟨u, mem_cutsHG_squeeze hu hu' hx, rfl⟩))
      · -- a later summand
        obtain ⟨rfl, rfl, h1', h2''⟩ := squeeze_head h1 h2'
        simp only [split]
        rw [if_neg (show ¬ (lt _ _ = true) from hgeA)]
        exact mem_cutsNSG_psi.mpr (Or.inr (Or.inr ⟨u, cutsNSG_squeeze
          (fun q hq => hge q (by simp [summands, hq])) hu h1' h2'', rfl⟩))

/-- **The kind is kept** (G3) when the argument goes down to `y′` with `B < y′ ≤ y`. -/
theorem ph3cKindG_squeeze {B s y y' : T}
    (hK : PH3cKindG B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s) (h1 : B < y') (h2 : y' ≤ y) :
    PH3cKindG B (split y' (psi (succ s) z z)).1 (split y' (psi (succ s) z z)).2 s := by
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
    have hc' := cutsNSG_squeeze hge hc h1 (by rw [hy]; exact h2)
    by_cases hh : (split y' θ).1 = B
    · refine Or.inl ⟨hh, fun hl => ?_⟩
      have := split_app θ y'
      rw [hh, hl, app_z_right] at this
      rw [this] at h1
      exact lt_irrefl' _ h1
    · exact Or.inr ⟨hh, Or.inr ⟨hs, hc'⟩⟩

end Ytosk
