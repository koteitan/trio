/-
**2 行・t = 1 の組み立て: コピーの根の値は始点つきの対角化の列。**

c_k = o_{M[k]}(r)、始点 c_1 = o_{M[1]}(r)、o_M(r) = ψ_μ(b) とすると c_k = γ′_{k−1}（γ′_0 = c_1、γ′_{j+1} = ψ_μ(b[γ′_j])）、
すべての k ≥ 2 で経路上の列 h は o_{M[k]}(h) = fsD(o_M(h), γ′_{k−2})。
(P)（`TwoRowP`）、(C)（`TwoRowC`）、始点つきの補題 3.3（`FSS`）から。枠の条件・始点の条件・経路の値の形は仮定に置く。
-/
import Ytosk.TwoRowC
import Ytosk.FSS

namespace Ytosk

open T

theorem twoRow_chain {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hG : Good2 M) (hb1 : 0 < entry M 1 (M.length - 1))
    {μ b : T} (hrv : o2r M r = psi μ b z) (hb : b ≠ z) (hcb : cof b = .big μ)
    (hS : SeedOK μ b μ (o2r (expand M 1) r))
    (hF1 : ∀ k, 1 ≤ k → F1 (expand M k))
    (hclass : ∀ p, Anc0 M p (M.length - 1) → cof (o2r M p) = .big μ ∨ DiagAt μ b μ (o2r M p))
    (hFr : ∀ m h p, Anc0 M p (M.length - 1) → par M 0 p = some h →
      FrameD (vr M h) (bst M h p) (o2r M p) (gamS μ b (o2r (expand M 1) r) m)) :
    ∀ k, 2 ≤ k →
      o2r (expand M k) r = gamS μ b (o2r (expand M 1) r) (k - 1) ∧
      ∀ h, Anc0 M h (M.length - 1) →
        o2r (expand M k) h = fsD (o2r M h) (gamS μ b (o2r (expand M 1) r) (k - 2)) := by
  have hrx := par_lt M _ _ _ hr
  have hA := anc0_of_par M _ _ _ hr
  have ht : 0 < TRIO.srow M (M.length - 1) := by omega
  generalize hc1 : o2r (expand M 1) r = c1 at hS hFr
  have hot : isOT (psi μ b z) = true := by rw [← hrv]; exact hG.ot r
  have hμ : ¬ lt μ μ = true := by simp [Bool.eq_false_iff.mpr (lt_irrefl' μ)]
  -- the gexp form
  have hgexp := fun k => expand_eq_gexp_t1 M k hM hz hr ht1
  have hlen : r + (M.length - 1 - r) + 1 = M.length := by omega
  have hL : 0 < M.length - 1 - r := by omega
  have hA' : Anc0 M r (r + (M.length - 1 - r)) := by rw [show r + (M.length - 1 - r) = M.length - 1 by omega]; exact hA
  have hd0e : entry M 0 (r + (M.length - 1 - r)) =
      entry M 0 r + (entry M 0 (M.length - 1) - entry M 0 r) := by
    rw [show r + (M.length - 1 - r) = M.length - 1 by omega]
    have := anc0_interval hA (M.length - 1) hrx (Nat.le_refl _); omega
  -- copy shift at the copy root
  have hshift : ∀ k, 2 ≤ k → o2r (expand M k) (M.length - 1) = o2r (expand M (k - 1)) r := by
    intro k hk
    have h1 := o2r_gexp_shift hlen hL hA' hd0e hk (by rw [← hgexp]; exact hF1 k (by omega))
      (by rw [← hgexp]; exact hF1 (k - 1) (by omega)) 0
      (by have := Nat.mul_le_mul_right (M.length - 1 - r) (show 1 ≤ k - 1 by omega); simp at this; omega)
    rw [hgexp, hgexp]
    simpa [show r + (M.length - 1 - r) = M.length - 1 by omega] using h1
  -- one step: from the copy root value to the path
  have step : ∀ k, 2 ≤ k → ∀ m, o2r (expand M k) (M.length - 1) = gamS μ b c1 m →
      o2r (expand M k) r = gamS μ b c1 (m + 1) ∧
      ∀ h, Anc0 M h (M.length - 1) → o2r (expand M k) h = fsD (o2r M h) (gamS μ b c1 m) := by
    intro k hk m hY
    have hpath := o2r_expand_path hM hz hr ht hk hG hb1
      (by
        intro p hp
        rw [hY]
        rcases hclass p hp with hc | hD
        · rw [fsD_eq_fs hc]
          exact fs_ot_lt (hG.ot p) ⟨gamS_ot hot hcb hμ hS m, by rw [hc]; exact gamS_lt_om hot hcb hμ hS m⟩
        · obtain ⟨h1, h2⟩ := fsD_seed hS hD (hG.ot p) m
          exact ⟨h1, h2.1⟩)
      (by intro h p hp hph; rw [hY]; exact hFr m h p hp hph)
    rw [hY] at hpath
    refine ⟨?_, hpath⟩
    rw [hpath r hA, hrv, fsD_here hb hcb]
    rfl
  -- the main induction
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hY : o2r (expand M 2) (M.length - 1) = gamS μ b c1 0 := by
      rw [hshift 2 (Nat.le_refl _), show 2 - 1 = 1 from rfl, hc1]; rfl
    exact step 2 (Nat.le_refl _) 0 hY
  | succ k hk ih =>
    have hY : o2r (expand M (k + 1)) (M.length - 1) = gamS μ b c1 (k - 1) := by
      rw [hshift (k + 1) (by omega), show k + 1 - 1 = k by omega, ih.1]
    have := step (k + 1) (by omega) (k - 1) hY
    rw [show k + 1 - 1 = k - 1 + 1 by omega, show k + 1 - 2 = k - 1 by omega]
    exact this

end Ytosk
