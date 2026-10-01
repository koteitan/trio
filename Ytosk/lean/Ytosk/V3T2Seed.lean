/-
**3 行・t = 2: 種の補題（T の段）。**

- `seed_closed`: ψ_v(X) の引数 X が閉じていて（Closed v X）、o の基本列の項 ψ_v(b)[K] 以下なら、
  ψ_v(X) ◁ ψ_v(b)（`lhdE_psi_closed` と `lhd_fs`）。t = 2・q = r の種 o(r) に使う
  （実測: o_M(r) の共終数は ω、o_N(r) の引数は閉じていて、ある K で o_N(r) ≤ o_M(r)[K]）。
-/
import Ytosk.V3T0F

namespace Ytosk

open T

/-- The fundamental sequence of `ψ_a(b)` (`b ≠ 0` not a successor) is again a `ψ_a(·)`. -/
theorem fs_psi_form {a b : T} (hb : b ≠ z) (hs : isSucc b = false) (η : T) :
    ∃ b', fs (psi a b z) η = psi a b' z := by
  unfold fs
  rw [if_neg hb, if_neg (by simp [hs])]
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **The seed with a closed argument**: `ψ_v(X) ◁ ψ_v(b)` from `ψ_v(X) ≤ ψ_v(b)[K]`. -/
theorem seed_closed {v b X : T} {K : Nat} (hot : isOT (psi v b z) = true) (hb : b ≠ z)
    (hsm : Closed v X) (hle : psi v X z ≤ fs (psi v b z) (natT K)) :
    Lhd z (psi v X z) (psi v b z) := by
  have hl := lhd_natT_z (lhd_fs hot (validLt_natT hb K))
  have hE : LhdE (psi v X z) (fs (psi v b z) (natT K)) := by
    by_cases hs : isSucc b = true
    · -- `ψ_v(init b) · K`
      have hfs : fs (psi v b z) (natT K) = mulT (psi v (init b) z) K := by
        unfold fs; rw [if_neg hb, if_pos hs, count_natT]
      rw [hfs] at hle ⊢
      cases K with
      | zero => exact absurd hle (not_le_of_gt (T.z_lt_psi _ _ _))
      | succ K =>
        have hle' : psi v X z ≤ psi v (init b) z := by
          simp only [mulT, app_psi, app_z] at hle
          rcases (le_iff _ _).mp hle with h | h
          · rw [psi_lt_psi] at h
            rcases h with h | ⟨_, h⟩ | ⟨_, hX, _⟩
            · exact absurd h (lt_irrefl' _)
            · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h⟩))
            · rw [hX]
          · simp only [psi.injEq] at h; rw [h.2.1]
        have hXle : X ≤ init b := by
          rcases (le_iff _ _).mp hle' with h | h
          · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
            · exact absurd h (lt_irrefl' _)
            · exact le_of_lt h
          · simp only [psi.injEq] at h; rw [h.2.1]
        refine LhdE.trans (lhdE_psi_closed hXle hsm) ?_
        have := lhdE_prefix (psi v (init b) z) (mulT (psi v (init b) z) K)
        simpa [mulT] using this
    · obtain ⟨b', hb'⟩ := fs_psi_form (a := v) hb (by simpa using hs) (natT K)
      rw [hb'] at hle ⊢
      have hXle : X ≤ b' := by
        rcases (le_iff _ _).mp hle with h | h
        · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact le_of_lt h
        · simp only [psi.injEq] at h; rw [h.2.1]
      exact lhdE_psi_closed hXle hsm
  exact lhd_of_lhdE_lt (LhdE.trans hE (Or.inr hl)) (lt_of_le_of_lt hE.le hl.1)

end Ytosk
