/-
GxY.lean: 基準 u+σ の持ち上げで作る型紙（錨つきの子の並び）。

    PV b σ W := ∀ t, Gof (σ+t) b (mlift W (b+σ) t)

σ 節点の下の字の潰れは基準 b+σ で持ち上げる。行 1 が b+σ 以下の列（σ 節点の写しを含む）は持ち上がらない。
-/
import GxW

namespace TRIO
namespace GxY

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ
open GxD
open GxG
open GxJ
open GxK
open GxL
open GxN
open GxP
open GxR
open GxT
open GxV
open GxW

theorem mlift_commk (X : TrioSeq) (u k s d : ℕ) :
    mlift (mlift X (u + k) s) u d = mlift (mlift X u d) (u + k + d) s := by
  rw [mlift_eq_slift, mlift_eq_slift, mlift_eq_slift, mlift_eq_slift,
    slift_slift (stair_step (u + k) s) (stair_step u d),
    slift_slift (stair_step u d) (stair_step (u + k + d) s)]
  congr 1
  funext m
  split_ifs <;> omega

def PV (b σ : ℕ) (W : TrioSeq) : Prop := ∀ t, Gof (σ + t) b (mlift W (b + σ) t)

/-- 任意の子の並びの後ろの空の字。 -/
theorem Gof_snocz_core {b σ : ℕ} (hσ : 1 ≤ σ) {W : TrioSeq} (hW : Fr W)
    (hPV : ∀ t, Gof (σ + t) b (mlift W (b + σ) t)) :
    Gof σ b (W ++ [((1, b + σ + 1, 1) : ℕ × ℕ × ℕ)]) := by
  rw [Gof_eq]
  intro Q hQ hF u' hu X hX hQX
  obtain ⟨d, hd⟩ : ∃ d, d = u' - b := ⟨_, rfl⟩
  rw [← hd]
  obtain ⟨V, hV⟩ : ∃ V : ℕ → TrioSeq, V = fun τ => mlift (mlift W b d) (u' + σ) (τ - σ) :=
    ⟨_, rfl⟩
  have hVFr : ∀ τ, Fr (V τ) := fun τ => by rw [hV]; exact Fr_mlift (Fr_mlift hW _ _) _ _
  have hBase : ∀ τ, σ ≤ τ → Gof τ u' (V τ) := by
    intro τ hτ
    have h0 := hPV (τ - σ)
    rw [show σ + (τ - σ) = τ by omega] at h0
    have h1 := (Gof_ax (by omega : 1 ≤ τ)).lift b _ (Fr_mlift hW _ _) h0 u' hu
    rw [← hd, mlift_commk, show b + σ + d = u' + σ by omega] at h1
    rw [hV]; exact h1
  have eStep : ∀ τ, σ ≤ τ → mlift (V τ) (u' + τ) 1 = V (τ + 1) := by
    intro τ hτ
    rw [hV]
    have := mlift_mlift (mlift W b d) (u' + σ) (τ - σ) 1
    rw [show u' + σ + (τ - σ) = u' + τ by omega, show τ - σ + 1 = τ + 1 - σ by omega] at this
    exact this
  have claim : ∀ m τ, σ ≤ τ →
      Gof τ u' (V τ ++ shiftr01 1 0 ((((0, u' + τ + 1, 0) : ℕ × ℕ × ℕ) ::
        (V (τ + 1) ++ [((1, u' + τ + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m⟧)) := by
    intro m
    induction m with
    | zero =>
        intro τ hτ
        rw [oper_zcone (hVFr (τ + 1)) le_rfl (coneV_top1 (hVFr (τ + 1)) (by omega)) 0]
        simp only [List.range_zero, List.flatMap_nil, shiftr01, List.map_nil, List.append_nil]
        exact hBase τ hτ
    | succ m ih =>
        intro τ hτ
        rw [oper_zcone_succ (hVFr (τ + 1)) le_rfl (coneV_top1 (hVFr (τ + 1)) (by omega)) m,
          show u' + τ + 1 = u' + (τ + 1) by omega, eStep (τ + 1) (by omega)]
        have eS : shiftr01 1 0 (((0, u' + (τ + 1), 0) : ℕ × ℕ × ℕ) ::
            (V (τ + 1) ++ shiftr01 1 0 ((((0, u' + (τ + 1) + 1, 0) : ℕ × ℕ × ℕ) ::
              (V (τ + 1 + 1) ++ [((1, u' + (τ + 1) + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m⟧)))
            = ((1, u' + (τ + 1), 0) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (V (τ + 1) ++ shiftr01 1 0 ((((0, u' + (τ + 1) + 1, 0) : ℕ × ℕ × ℕ) ::
                (V (τ + 1 + 1) ++ [((1, u' + (τ + 1) + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m⟧)) := by
          simp [shiftr01]
        rw [eS]
        exact Gof_node (ρ := τ) (σ := τ + 1) (by omega) (by omega) (hVFr τ) (hBase τ hτ)
          (ih (τ + 1) (by omega))
  have hcA := coneV_top1 hW (show b < b + σ + 1 by omega)
  rw [mlift_snoc_cone W _ hcA d]
  have eL1 : (((1, b + σ + 1, 1) : ℕ × ℕ × ℕ).1, ((1, b + σ + 1, 1) : ℕ × ℕ × ℕ).2.1 + d,
      ((1, b + σ + 1, 1) : ℕ × ℕ × ℕ).2.2) = ((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ) := by
    show ((1, b + σ + 1 + d, 1) : ℕ × ℕ × ℕ) = _
    rw [show b + σ + 1 + d = u' + σ + 1 by omega]
  have eV0 : mlift W b d = V σ := by rw [hV]; simp [mlift_zero]
  rw [eL1, eV0]
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq,
      U0 = ((0, u' + σ, 0) : ℕ × ℕ × ℕ) :: (V σ ++ [((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ)]) := ⟨_, rfl⟩
  have eU : ((1, u' + σ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (V σ ++ [((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ)])
      = shiftr01 1 0 U0 := by rw [hU0]; simp [shiftr01]
  rw [eU]
  have hlen : 2 ≤ U0.length := by rw [hU0]; simp
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom (hVFr σ) le_rfl (coneV_top1 (hVFr σ) (show u' + σ < u' + σ + 1 by omega))
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h | h
    · exfalso
      have hl : U0.length - 1 = (((0, u' + σ, 0) : ℕ × ℕ × ℕ) :: V σ).length + 0 := by
        rw [hU0]; simp
      rw [hl] at h
      unfold lev at h
      rw [hU0, show ((0, u' + σ, 0) : ℕ × ℕ × ℕ) :: (V σ ++ [((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ)])
        = (((0, u' + σ, 0) : ℕ × ℕ × ℕ) :: V σ) ++ [((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ)] by simp,
        entry_append_right, entry_append_right] at h
      simp [entry] at h
    · exact h
  refine hQ.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
    (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp), hU0]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] U0 1 m hlen hpV
  simp only [List.nil_append] at eO
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [eO, hU0, oper_zcone_succ (hVFr σ) le_rfl (coneV_top1 (hVFr σ) (by omega)) m', eStep σ le_rfl]
  have eS : shiftr01 1 0 (((0, u' + σ, 0) : ℕ × ℕ × ℕ) ::
      (V σ ++ shiftr01 1 0 ((((0, u' + σ + 1, 0) : ℕ × ℕ × ℕ) ::
        (V (σ + 1) ++ [((1, u' + σ + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m'⟧)))
      = ((1, u' + σ, 0) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (V σ ++ shiftr01 1 0 ((((0, u' + σ + 1, 0) : ℕ × ℕ × ℕ) ::
          (V (σ + 1) ++ [((1, u' + σ + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m'⟧)) := by
    simp [shiftr01]
  rw [eS]
  have h := (Gof_eq σ u' _).mp (claim m' σ le_rfl) Q hQ hF u' le_rfl X hX hQX
  rwa [Nat.sub_self, mlift_zero] at h

#print axioms Gof_snocz_core

theorem PV_snocz {b σ : ℕ} (hσ : 1 ≤ σ) {W : TrioSeq} (hW : Fr W) (h : PV b σ W) :
    PV b σ (W ++ [((1, b + σ + 1, 1) : ℕ × ℕ × ℕ)]) := by
  intro t
  have hcA := coneV_top1 hW (show b + σ < b + σ + 1 by omega)
  rw [mlift_snoc_cone W _ hcA t]
  have eL : (((1, b + σ + 1, 1) : ℕ × ℕ × ℕ).1, ((1, b + σ + 1, 1) : ℕ × ℕ × ℕ).2.1 + t,
      ((1, b + σ + 1, 1) : ℕ × ℕ × ℕ).2.2) = ((1, b + (σ + t) + 1, 1) : ℕ × ℕ × ℕ) := by
    show ((1, b + σ + 1 + t, 1) : ℕ × ℕ × ℕ) = _
    rw [show b + σ + 1 + t = b + (σ + t) + 1 by omega]
  rw [eL]
  refine Gof_snocz_core (by omega) (Fr_mlift hW _ _) (fun t' => ?_)
  have := h (t + t')
  rw [show σ + (t + t') = σ + t + t' by omega] at this
  have e := mlift_mlift W (b + σ) t t'
  rw [show b + σ + t = b + (σ + t) by omega] at e
  rwa [e]

#print axioms PV_snocz

end GxY
end TRIO
