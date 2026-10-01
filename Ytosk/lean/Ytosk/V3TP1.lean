/-
**持続の不変条件 TP1 から (W) へ。**

TP1（書き換えありの枠で B < fsD(y, ψ_μ(1))）があれば、穴のある y（`OHole`）について鎖のどの項 ζ でも B < fsD(y, ζ)
（`hW_of_tp1`）。穴 `HoleT` なら `OHole`（`ohole_of_holeT`）、鎖の項はどれも ψ_μ(1) 以上（`gamS_ge_one`）。
-/
import Ytosk.V3HoleT1
import Ytosk.TwoRowV
import Ytosk.TwoRowL

namespace Ytosk

open T

theorem ohole_of_cof_big : ∀ {t μ : T}, cof t = .big μ → OHole t
  | z, _, h => by simp [cof] at h
  | psi a b (psi c d e), μ, h => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    show OHole (psi c d e)
    exact ohole_of_cof_big (t := psi c d e) h'
  | psi a b z, μ, h => by
    unfold OHole
    unfold cof at h
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h ⊢
      by_cases ha : a = z
      · rw [if_pos ha] at h; cases h
      · rw [if_neg ha] at h
        refine ⟨ha, ?_⟩
        by_cases hs : isSucc a = true
        · exact Or.inl hs
        · rw [if_neg hs] at h; exact Or.inr (ohole_of_cof_big h)
    · rw [if_neg hb] at h ⊢
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h ⊢
        cases hcb : cof b with
        | big ν => simp
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

theorem ohole_of_diag {a br μ : T} {t : T} (h : DiagAt a br μ t) : OHole t := by
  induction h with
  | here hb hc _ =>
    unfold OHole
    rw [if_neg hb, if_neg (by rw [not_succ_of_cof_big hc]; simp), hc]
    trivial
  | rest _ ih => exact ih
  | @arg a' b' hb hs _ ih =>
    unfold OHole
    rw [if_neg hb, if_neg (by rw [hs]; simp)]
    cases hcb : cof b' with
    | big ν => simp
    | zero => exact ih
    | succ => exact ih
    | omega => exact ih
  | @sub a' ha _ _ ih =>
    unfold OHole
    rw [if_pos rfl]
    exact ⟨ha, Or.inr ih⟩

theorem ohole_of_holeT {μ br vr t : T} (h : HoleT μ br vr t) : OHole t := by
  rcases h with h | ⟨_, _, hD⟩
  · exact ohole_of_cof_big h
  · exact ohole_of_diag hD

/-- The argument of a single summand with a hole has a hole. -/
theorem holeT_arg {μ br vr s y : T} (hy : y ≠ z) (h : HoleT μ br vr (psi s y z))
    (hbr : cof br = .big μ) : HoleT μ br vr y := by
  rcases h with h | ⟨a', ha', hD⟩
  · exact Or.inl (cof_psi_inv hy h).1
  · by_cases hne : s = a' ∧ y = br
    · obtain ⟨_, rfl⟩ := hne; exact Or.inl hbr
    · exact Or.inr ⟨a', ha', DiagAt.arg_inv hD hy hne⟩

theorem fs_ne_z_big : ∀ {b μ η : T}, cof b = .big μ → η ≠ z → fs b η ≠ z
  | z, _, _, h, _ => by simp [cof] at h
  | psi a b (psi c d e), _, _, _, _ => by simp [fs]
  | psi a b z, μ, η, h, hη => by
    unfold fs
    unfold cof at h
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h ⊢
      by_cases ha : a = z
      · rw [if_pos ha] at h; cases h
      · rw [if_neg ha]
        by_cases hs : isSucc a = true
        · rw [if_pos hs]; exact hη
        · rw [if_neg hs]; simp
    · rw [if_neg hb] at h ⊢
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h ⊢
        cases hcb : cof b with
        | big ν =>
          simp only
          split <;> simp
        | zero => simp
        | succ => simp
        | omega => simp

/-- **Every term of the chain is at least `ψ_μ(1)`.** -/
theorem gamS_ge_one {μ br seed : T} (hcb : cof br = .big μ) (hseed : psi μ one z ≤ seed) :
    ∀ m, psi μ one z ≤ gamS μ br seed m
  | 0 => hseed
  | m + 1 => by
    show psi μ one z ≤ psi μ (fs br (gamS μ br seed m)) z
    have hne : gamS μ br seed m ≠ z := by
      cases m with
      | zero =>
        intro h
        have h0 : seed = z := h
        rw [h0] at hseed
        exact absurd hseed (by intro h'; exact T.not_lt_z _ (lt_of_lt_of_le (T.z_lt_psi μ one z) h'))
      | succ k => simp [gamS]
    have h1 := one_le_of_ne_z (fs_ne_z_big hcb hne)
    rcases (le_iff _ _).mp h1 with h | h
    · apply le_of_lt; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h⟩
    · rw [h]

/-- **Persistence from TP1** on the whole chain. -/
theorem hW_of_tp1 {B y μ br seed : T} (hy : OHole y) (hcb : cof br = .big μ)
    (hseed : psi μ one z ≤ seed) (h : B < fsD y (psi μ one z)) :
    ∀ m, lt B (fsD y (gamS μ br seed m)) = true :=
  fun m => persist_of_tp1 hy (gamS_ge_one hcb hseed m) h

/-- The hole survives in a nonzero tail. -/
theorem holeT_app_inv {μ br vr : T} : ∀ {P c : T}, c ≠ z → HoleT μ br vr (app P c) → HoleT μ br vr c
  | z, c, _, h => by simpa using h
  | psi a b P, c, hc, h => by
    simp only [app_psi] at h
    have hPc : app P c ≠ z := fun he => hc (app_eq_z he).2
    exact holeT_app_inv hc (holeT_rest hPc h)

/-- **`fsD` of a term with a hole is nonzero** (for a nonzero index). -/
theorem fsD_ne_z_of_holeT {μ br vr ζ : T} (hζ : ζ ≠ z) :
    ∀ {t : T}, HoleT μ br vr t → fsD t ζ ≠ z
  | z, h => absurd rfl (holeT_ne_z h)
  | psi a b (psi c d e), _ => by simp [fsD]
  | psi a b z, h => by
    by_cases hb : b = z
    · subst hb
      by_cases ha : a = z
      · subst ha
        have := holeT_not_succ h
        have h1 : isSucc (psi z z z) = true := rfl
        rw [h1] at this; cases this
      · by_cases hs : isSucc a = true
        · rw [fsD_leaf hs ha]; exact hζ
        · rw [fsD_sub ha (by simpa using hs)]; simp
    · rw [fsD_psi hb (not_succ_arg_of_holeT hb h)]; simp

/-- **(L)(i)**: a nonzero low part stays nonzero. -/
theorem lo_ne_z_of_holeT {μ br vr ζ s y : T} (hζ : ζ ≠ z) (hy : HoleT μ br vr y)
    (hl : (split y (psi (succ s) z z)).2 ≠ z) :
    fsD (split y (psi (succ s) z z)).2 ζ ≠ z := by
  have e := split_app (psi (succ s) z z) y
  have hlo : HoleT μ br vr (split y (psi (succ s) z z)).2 := by
    rw [← e] at hy; exact holeT_app_inv hl hy
  exact fsD_ne_z_of_holeT hζ hlo

theorem last_ne_z' : ∀ {t : T}, t ≠ z → last t ≠ z
  | z, h => absurd rfl h
  | psi a b z, _ => by simp [last]
  | psi a b (psi c d e), _ => by
    show last (psi c d e) ≠ z
    exact last_ne_z' (by simp)

/-- **(L)(ii)**: with no low part, `fsD` keeps no low part when the new last summand stays high. -/
theorem lo_z_keep {ζ θ y : T} (hy : y ≠ z) (hl : (split y θ).2 = z)
    (hlast : ∀ q ∈ summands (fsD (last y) ζ), ¬ q < θ) :
    (split (fsD y ζ) θ).2 = z := by
  have hyall : ∀ q ∈ summands y, ¬ q < θ := by
    intro q hq
    have e := split_app θ y
    rw [hl, app_z_right] at e
    rw [← e] at hq
    exact split_fst_ge θ y q hq
  have hlz : last y ≠ z := last_ne_z' hy
  rw [← init_app_last y, fsD_app _ hlz]
  apply split_snd_z_of_ge
  intro q hq
  rw [summands_app] at hq
  rcases List.mem_append.mp hq with hq | hq
  · apply hyall; rw [← init_app_last y, summands_app]; exact List.mem_append_left _ hq
  · exact hlast q hq

/-- The last summand of a term with a hole has a hole. -/
theorem holeT_last {μ br vr : T} : ∀ {t : T}, HoleT μ br vr t → HoleT μ br vr (last t)
  | z, h => absurd rfl (holeT_ne_z h)
  | psi a b z, h => h
  | psi a b (psi c d e), h => by
    show HoleT μ br vr (last (psi c d e))
    exact holeT_last (holeT_rest (by simp) h)

/-- **(L)** at a frame, from the hole and a condition on a last summand `Ω_a` with `a` a limit. -/
theorem hL_of_holeT {μ br vr ζ s y X : T} (hζ : ζ = psi μ X z) (hsμ : lt μ s = true)
    (hy : y ≠ z) (hH : HoleT μ br vr (psi s y z)) (hbr : cof br = .big μ)
    (hlim : ∀ a, last y = psi a z z → isSucc a = false → ¬ psi (fsD a ζ) z z < psi (succ s) z z) :
    ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 ζ ≠ z) ∧
    ((split y (psi (succ s) z z)).2 = z → (split (fsD y ζ) (psi (succ s) z z)).2 = z) := by
  have hHy := holeT_arg hy hH hbr
  have hζz : ζ ≠ z := by rw [hζ]; simp
  refine ⟨lo_ne_z_of_holeT hζz hHy, ?_⟩
  intro hl
  apply lo_z_keep hy hl
  -- the last summand is high
  have hyall : ∀ q ∈ summands y, ¬ q < psi (succ s) z z := by
    intro q hq
    have e := split_app (psi (succ s) z z) y
    rw [hl, app_z_right] at e
    rw [← e] at hq
    exact split_fst_ge _ y q hq
  have hHl := holeT_last hHy
  have hlh := hyall _ (last_mem hy)
  cases hlc : last y with
  | z => exact absurd hlc (last_ne_z' hy)
  | psi a b c =>
    have hc0 : c = z := by
      -- `last` is a single summand
      have : ∀ t : T, t ≠ z → ∃ a b, last t = psi a b z := by
        intro t
        induction t with
        | z => intro h; exact absurd rfl h
        | psi a b c _ _ ihc =>
          intro _
          cases c with
          | z => exact ⟨a, b, rfl⟩
          | psi c1 c2 c3 => exact ihc (by simp)
      obtain ⟨a', b', h'⟩ := this y hy
      rw [hlc] at h'; cases h'; rfl
    subst hc0
    rw [hlc] at hlh hHl
    by_cases hb : b = z
    · subst hb
      by_cases ha : isSucc a = true
      · -- `Ω_{μ+1}` at the end would be below `Ω_{s+1}`: impossible since `μ < s`
        exfalso
        have haz : a ≠ z := by
          intro h; subst h
          have h0 : isSucc z = false := rfl
          rw [h0] at ha; cases ha
        have hcf : cof (psi a z z) = .big (init a) := by
          unfold cof; rw [if_pos rfl, if_neg haz, if_pos ha]
        have hia : init a = μ := by
          rcases hHl with h | ⟨_, _, hD⟩
          · rw [hcf] at h; cases h; rfl
          · cases hD with
            | here hb _ _ => exact absurd rfl hb
            | arg hb _ _ => exact absurd rfl hb
            | sub _ hs _ => rw [ha] at hs; cases hs
        have hsa : succ μ = a := by rw [← hia]; unfold succ; exact init_app_one ha
        apply hlh
        rw [← hsa, psi_lt_psi_z_iff]
        left
        exact lt_of_le_of_lt (le_refl _) (show succ μ < succ s from by
          rw [lt_succ_iff]; exact succ_le_of_lt (show μ < s from hsμ))
      · have haz : a ≠ z := by
          intro h; subst h
          have := holeT_not_succ hHl
          have h1 : isSucc (psi z z z) = true := rfl
          rw [h1] at this; cases this
        rw [fsD_sub haz (by simpa using ha)]
        intro q hq
        simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
        subst hq
        exact hlim a hlc (by simpa using ha)
    · rw [fsD_psi hb (not_succ_arg_of_holeT hb hHl)]
      intro q hq
      simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
      subst hq
      intro hlt
      apply hlh
      rw [psi_lt_psi_z_iff] at hlt ⊢
      rcases hlt with h | ⟨h, h'⟩
      · exact Or.inl h
      · exact absurd h' (T.not_lt_z _)

end Ytosk
