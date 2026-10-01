/-
**持続の不変条件 TP1 から (W) へ。**

TP1（書き換えありの枠で B < fsD(y, ψ_μ(1))）があれば、穴のある y（`OHole`）について鎖のどの項 ζ でも B < fsD(y, ζ)
（`hW_of_tp1`）。穴 `HoleT` なら `OHole`（`ohole_of_holeT`）、鎖の項はどれも ψ_μ(1) 以上（`gamS_ge_one`）。
-/
import Ytosk.V3HoleT1

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

end Ytosk
