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
      (le s a = true ∧ ∃ u ∈ cutsHG s x, t = psi a u z) ∨ (∃ u ∈ cutsHG s c, t = psi a x u) := by
  show t ∈ (if le s a then [psi s z z] else []) ++ (cutsHG s a).map (fun t => psi t z z) ++
    (if le s a then (cutsHG s x).map (fun t => psi a t z) else []) ++ (cutsHG s c).map (fun t => psi a x t) ↔ _
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
    rcases mem_cutsHG_psi.mp ht with ⟨hs, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨_, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
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
    rcases mem_cutsHG_psi.mp ht with ⟨_, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hs, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact mem_cutsHG_psi.mpr (Or.inl ⟨by simp [le], rfl⟩)
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inl ⟨u, cutsHG_self hu, rfl⟩))
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨hs, u, cutsHG_self hu, rfl⟩)))
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨u, cutsHG_self hu, rfl⟩)))

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
      rcases mem_cutsHG_psi.mp ht with ⟨_, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hs, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
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
        exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨u, mem_cutsHG_squeeze hu (le_of_lt h1') h2', rfl⟩)))

/-! ## 旧の切り口は G3 の切り口 -/

theorem scuts_sub_HG {s : T} : ∀ {h t : T}, t ∈ scuts s h → t ∈ cutsHG s h
  | z, _, ht => by simp [scuts] at ht
  | psi a x c, t, ht => by
    simp only [scuts, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨u, hu, rfl⟩
    · split at ht
      · rename_i hle; simp only [List.mem_singleton] at ht; subst ht
        exact mem_cutsHG_psi.mpr (Or.inl ⟨hle, rfl⟩)
      · simp at ht
    · cases a with
      | z => simp [scuts] at hu
      | psi a0 x0 c0 => exact mem_cutsHG_psi.mpr (Or.inr (Or.inl ⟨u, scuts_sub_HG hu, rfl⟩))

theorem cutsH_sub_HG {s : T} : ∀ {h t : T}, t ∈ cutsH s h → t ∈ cutsHG s h
  | z, _, ht => by simp [cutsH] at ht
  | psi a x c, t, ht => by
    rcases mem_cutsH_psi.mp ht with ⟨hs, rfl⟩ | ⟨hs, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact mem_cutsHG_psi.mpr (Or.inl ⟨hs, rfl⟩)
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨hs, u, cutsH_sub_HG hu, rfl⟩)))
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨u, cutsH_sub_HG hu, rfl⟩)))

theorem cutsNS_sub_G {s : T} : ∀ {h t : T}, t ∈ cutsNS s h → t ∈ cutsNSG s h
  | z, _, ht => by simp [cutsNS] at ht
  | psi a x c, t, ht => by
    simp only [cutsNS, List.mem_append, List.mem_map] at ht
    rcases ht with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩
    · exact mem_cutsNSG_psi.mpr (Or.inl ⟨u, scuts_sub_HG hu, rfl⟩)
    · exact mem_cutsNSG_psi.mpr (Or.inr (Or.inl ⟨u, cutsH_sub_HG hu, rfl⟩))
    · exact mem_cutsNSG_psi.mpr (Or.inr (Or.inr ⟨u, cutsNS_sub_G hu, rfl⟩))

theorem ph3cKindG_of {B hi lo s : T} (h : PH3cKind B hi lo s) : PH3cKindG B hi lo s := by
  rcases h with h | ⟨hne, (h | ⟨hs, hc⟩)⟩
  · exact Or.inl h
  · exact Or.inr ⟨hne, Or.inl h⟩
  · exact Or.inr ⟨hne, Or.inr ⟨hs, cutsNS_sub_G hc⟩⟩

theorem ph3cG_of {M : Mat} {ρ : Valn} (h : PH3c M ρ) : PH3cG M ρ :=
  fun i hi L c R hCL s y hc hB ht => ph3cKindG_of (h i hi L c R hCL s y hc hB ht)

/-! ## 状態の段 -/

/-- **A cut is above `s`** (standard terms). -/
theorem cutsHG_gt {s : T} (hs : isOT s = true) : ∀ {h t : T}, isOT h = true → t ∈ cutsHG s h → s < t
  | z, _, _, ht => by simp [cutsHG] at ht
  | psi a x c, t, hh, ht => by
    rcases mem_cutsHG_psi.mp ht with ⟨_, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hsa, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact lt_Om_self s
    · exact lt_trans (cutsHG_gt hs (isOT_sub hh) hu) (lt_Om_self u)
    · exact lt_of_lt_of_le (lt_Om_self s) (psi_le_psi_anyG (le_of_le_bool hsa))
    · have hsu := cutsHG_gt hs (isOT_rest hh) hu
      have huc := cutsHG_le hu
      by_cases h0 : s < psi a x z
      · refine lt_of_lt_of_le h0 ?_
        rcases (le_iff _ _).mp (z_le u) with h' | h'
        · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h'⟩))
        · rw [← h']
      · have hle : psi a x z ≤ s := le_of_not_gt h0
        have hsc : s < c := lt_of_lt_of_le hsu huc
        cases c with
        | z => exact absurd hsc (T.not_lt_z _)
        | psi c0 c1 c2 =>
          have hhc : head (psi c0 c1 c2) ≤ psi a x z := (isOT_psi_iff.mp hh).2.2.2.1
          cases s with
          | z => exact absurd (lt_of_lt_of_le (T.z_lt_psi a x z) hle) (lt_irrefl' _)
          | psi s0 s1 s2 =>
            have h1 : head (psi s0 s1 s2) ≤ head (psi c0 c1 c2) := head_le_of_lt hsc
            have h2 : psi a x z ≤ head (psi s0 s1 s2) := by
              rcases (le_iff _ _).mp hle with h' | h'
              · simpa [head] using head_le_of_lt h'
              · rw [← h']; simp [head]
            have heq : psi s0 s1 z = psi a x z := le_antisymm (le_trans (by simpa [head] using h1) hhc) h2
            simp only [psi.injEq, and_true] at heq
            obtain ⟨rfl, rfl⟩ := heq
            rw [T.psi_lt_psi]
            exact Or.inr (Or.inr ⟨rfl, rfl, lt_trans (rest_lt hs) hsu⟩)

/-- **The cut positions survive** (G3): `B ∈ cutsNSG s hi` and `B < y′ ≤ hi + lo` give `B ∈ cutsNSG s hi′`. -/
theorem cutsNSG_squeeze {s : T} (hs : isOT s = true) : ∀ {hi B y' lo : T}, isOT hi = true →
    (∀ q ∈ summands hi, ¬ q < psi (succ s) z z) →
    B ∈ cutsNSG s hi → B < y' → y' ≤ app hi lo → B ∈ cutsNSG s (split y' (psi (succ s) z z)).1
  | z, _, _, _, _, _, hB, _, _ => by simp [cutsNSG] at hB
  | psi a x c, B, y', lo, hot, hge, hB, h1, h2 => by
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
        have hsa : s < a' := lt_of_lt_of_le (cutsHG_gt hs (isOT_sub hot) hu) hua
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
        exact mem_cutsNSG_psi.mpr (Or.inr (Or.inr ⟨u, cutsNSG_squeeze hs (isOT_rest hot)
          (fun q hq => hge q (by simp [summands, hq])) hu h1' h2'', rfl⟩))

/-- **The kind is kept** (G3) when the argument goes down to `y′` with `B < y′ ≤ y`. -/
theorem ph3cKindG_squeeze {B s y y' : T} (hs : isOT s = true) (hyot : isOT y = true)
    (hK : PH3cKindG B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s) (h1 : B < y') (h2 : y' ≤ y) :
    PH3cKindG B (split y' (psi (succ s) z z)).1 (split y' (psi (succ s) z z)).2 s := by
  set θ := psi (succ s) z z
  have hy : app (split y θ).1 (split y θ).2 = y := split_app θ y
  have hge := split_fst_ge θ y
  rcases hK with ⟨hhi, hlo⟩ | ⟨hne, (⟨R, hR, hhi⟩ | ⟨hs0, hc⟩)⟩
  · exact ph3cKindG_of (ph3cKind_squeeze (s := s) (Or.inl ⟨hhi, hlo⟩) h1 h2)
  · exact ph3cKindG_of (ph3cKind_squeeze (s := s) (Or.inr ⟨hne, Or.inl ⟨R, hR, hhi⟩⟩) h1 h2)
  · have hhot : isOT (split y θ).1 = true := isOT_app_left (by rw [hy]; exact hyot)
    have hc' := cutsNSG_squeeze hs hhot hge hc h1 (by rw [hy]; exact h2)
    by_cases hh : (split y' θ).1 = B
    · refine Or.inl ⟨hh, fun hl => ?_⟩
      have := split_app θ y'
      rw [hh, hl, app_z_right] at this
      rw [this] at h1
      exact lt_irrefl' _ h1
    · exact Or.inr ⟨hh, Or.inr ⟨hs0, hc'⟩⟩

end Ytosk
