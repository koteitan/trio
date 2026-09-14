/-
HcY.lean: 遠い字つきの字の中身の状態の層 FRLC と、その差し込み口の公理（GyI の写し）。

    FRLC A k H b V := ∀ g b', b ≤ b' →
      FLC A (k + (H+g) k) (H+g) b' (reliftX b' H g (k :: A) (mlift V b (b' − b)))
    遠い字は V の先頭で段 b + liftOff H A (k + H k) + 1（錨 k の持ち上げで F の段と一緒に動く）。

- FRLC_far: 遠い字だけの中身。FRLC_ax: 差し込み口の公理（HcX の FLC_oper / orph / tie / flat）。
-/
import HcX

namespace TRIO
namespace HcY

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcJ HcK HcL HcM HcN HcO HcU HcV HcW HcX

def FRLC (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (b : ℕ) (V : TrioSeq) : Prop :=
  ∀ g b', b ≤ b' →
    FLC A (k + addF H g k) (addF H g) b' (reliftX b' H g (k :: A) (mlift V b (b' - b)))

theorem liftOff_cons_k {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) (F : ℕ → ℕ) :
    liftOff F (k :: A) (k + 1) = liftOff F A (k + F k) + 1 := by
  rw [show liftOff F (k :: A) (k + 1) = liftVal F (k :: A) k + 1 by unfold liftOff liftVal; omega,
    liftVal_cons_top hAk]

theorem FLC_congr {A : List ℕ} {k : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A, H a = H' a) {b0 : ℕ}
    {V : TrioSeq} (h : FLC A k H b0 V) : FLC A k H' b0 V := by
  intro W hW hP
  have el : liftOff H A k = liftOff H' A k := by unfold liftOff; rw [stepSum_congr 0 k hH]
  have := h W hW (PVE_congr (fun a ha => (hH a ha).symm) hP)
  rw [el] at this
  exact PVE_congr hH this

theorem FRLC_congr {A : List ℕ} {k : ℕ} {H1 H2 : ℕ → ℕ} (hH : ∀ a ∈ k :: A, H1 a = H2 a) {b : ℕ}
    {V : TrioSeq} (h : FRLC A k H1 b V) : FRLC A k H2 b V := by
  intro g b' hb'
  have hk : H1 k = H2 k := hH k (by simp)
  have hA' : ∀ a ∈ A, addF H1 g a = addF H2 g a := fun a ha => by
    unfold addF; rw [hH a (by simp [ha])]
  have h1 := h g b' hb'
  rw [reliftX_congr b' hH (fun a _ => rfl)] at h1
  have eO : addF H1 g k = addF H2 g k := by unfold addF; rw [hk]
  rw [eO] at h1
  exact FLC_congr hA' h1

theorem FRLC_lift {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b : ℕ} {V : TrioSeq}
    (h : FRLC A k H b V) (g : ℕ → ℕ) : FRLC A k (addF H g) b (reliftX b H g (k :: A) V) := by
  intro g' b' hb'
  rw [mlift_reliftX, show b + (b' - b) = b' by omega, reliftX_comp, addF_assoc]
  exact h (addF g g') b' hb'

theorem FRLC_okF {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b : ℕ} {V : TrioSeq} (h : FRLC A k H b V) :
    FLC A (k + H k) H b V := by
  have := h (fun _ => 0) b le_rfl
  rwa [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero] at this

/-- ★ 遠い字だけの中身。 -/
theorem FRLC_far {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) (H : ℕ → ℕ) (b : ℕ) :
    FRLC A k H b [((1, b + liftOff H A (k + H k) + 1, 1) : ℕ × ℕ × ℕ)] := by
  intro g b' hb'
  have hAk' : ∀ a ∈ A, a < k + addF H g k := fun a ha => by have := hAk a ha; omega
  rw [mlift_one (show b < b + liftOff H A (k + H k) + 1 by omega),
    show b + liftOff H A (k + H k) + 1 + (b' - b) = b' + liftOff H (k :: A) (k + 1) by
      rw [liftOff_cons_k hAk H]; omega,
    reliftX_one, reOff_liftOff, liftOff_cons_k hAk (addF H g), ← Nat.add_assoc]
  exact FLC_far hAk' (addF H g) b'

/-- ★ 遠い字つきの字の中身の族の差し込み口の公理。 -/
theorem FRLC_ax {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) (hA1 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k)
    (H : ℕ → ℕ) : SlotAx (FRLC A k H) where
  lift := by
    intro u W hW h u1 hu1 g b' hb'
    have e := mlift_mlift W u (u1 - u) (b' - u1)
    rw [show u + (u1 - u) = u1 by omega, show u1 - u + (b' - u1) = b' - u by omega] at e
    rw [e]
    exact h g b' (le_trans hu1 hb')
  oper := by
    intro u W U hW hU hH hlen hp hIH g b' hb'
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    rw [mlift_app hW hH u (b' - u), reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _)]
    refine FLC_oper (fun a ha => by have := hAk a ha; omega)
      (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
      (Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) (by rw [reliftX_length, mlift_length]; exact hlen)
      ?_ (fun m hm => ?_)
    · unfold reliftX
      rw [slift_length, srow_slift (reStair_stair _ _ _ _) (by rw [mlift_length]; omega),
        hasParent_slift (reStair_stair _ _ _ _)]
      exact (hasParent_mlift_iff u (b' - u) hUne).mpr hp
    · have h1 := hIH m hm g b' hb'
      rw [mlift_app hW (Hd_oper hH hUne hm),
        reliftX_app (Fr_mlift hW _ _) (Hd_mlift (Hd_oper hH hUne hm) _ _)] at h1
      unfold reliftX at h1 ⊢
      rwa [← mlift_oper', slift_oper (reStair_stair _ _ _ _)] at h1
  orph := by
    intro u W U h j hW hU hH hj1 hj hnp hz g b' hb'
    have hfix : ∀ m, m ≤ j → reStair b' H g (k :: A) m = m :=
      fun m hm => reStair_low b' H g _ (by omega)
    have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u := hj
    have eU : reliftX b' H g (k :: A) (mlift U u (b' - u)) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]
        = slift (mlift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) (reStair b' H g (k :: A)) := by
      unfold reliftX; rw [mlift_snoc_low U _ hc, slift_snoc_fix _ _ hfix]
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _)]
    have eU2 : reliftX b' H g (k :: A) (mlift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) u (b' - u))
        = reliftX b' H g (k :: A) (mlift U u (b' - u)) ++ [((h, j, 0) : ℕ × ℕ × ℕ)] := by
      rw [eU]; rfl
    rw [eU2]
    refine FLC_orph (fun a ha => by have := hAk a ha; omega)
      (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (by rw [eU]; exact Fr_slift (Fr_mlift hU _ _) _)
      (by rw [eU]; exact Hd_slift (Hd_mlift hH _ _) _) hj1 (le_trans hj hb') ?_
      (fun z hz' hbz => ?_)
    · intro hh; apply hnp
      rw [eU, reliftX_length, mlift_length, hasParent_slift (reStair_stair _ _ _ _),
        mlift_eq_slift, hasParent_slift (stair_step _ _)] at hh
      exact hh
    · have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
      have h1 := hz z hz' hbz g b' hb'
      have hHz := Hd_append_shift hH hbz
      rw [mlift_app hW hHz, mlift_append_low (low_of_Wg hzW h (show j ≤ u by omega))] at h1
      have hH2 : Hd (mlift U u (b' - u) ++ shiftr01 h 0 z) := by
        have := Hd_mlift hHz u (b' - u)
        rwa [mlift_append_low (low_of_Wg hzW h (show j ≤ u by omega))] at this
      rw [reliftX_app (Fr_mlift hW _ _) hH2] at h1
      unfold reliftX at h1 ⊢
      rwa [slift_append_low (low_of_Wg hzW h (show j ≤ b' by omega))
        (fun m hm => reStair_low b' H g _ hm)] at h1
  tie := by
    intro u W U x hW hU hH hc hload g b' hb'
    have hA'1 : ∀ a ∈ k :: A, 1 ≤ a := by
      intro a ha; simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hk1
      · exact hA1 a ha
    have eT : mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)
        = mlift U u (b' - u) ++ [((x, b' + 1, 0) : ℕ × ℕ × ℕ)] := by
      rw [mlift_snoc_cone U _ hc]
      show _ ++ [((x, u + 1 + (b' - u), 0) : ℕ × ℕ × ℕ)] = _
      rw [show u + 1 + (b' - u) = b' + 1 by omega]
    have hfix : ∀ m, m ≤ b' + 1 → reStair b' H g (k :: A) m = m :=
      fun m hm => reStair_tie b' H g hA'1 hm
    have eU : reliftX b' H g (k :: A) (mlift U u (b' - u)) ++ [((x, b' + 1, 0) : ℕ × ℕ × ℕ)]
        = reliftX b' H g (k :: A) (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) := by
      rw [eT]; unfold reliftX; rw [slift_snoc_fix _ _ hfix]
    have hHU : Hd U := by
      intro hne
      have := hH (by simp)
      rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), ← eU]
    refine FLC_tie (fun a ha => by have := hAk a ha; omega) (by omega)
      (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (by rw [eU]; exact Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
      (by rw [eU]; exact Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) ?_ (fun b'' hb'' Z hZ hbZ => ?_)
    · rw [eU, reliftX_length, mlift_length]
      unfold reliftX
      rw [coneV_iff_amin, amin_slift (reStair_stair _ _ _ _) (by simp)]
      have h0 : coneV (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) (u + (b' - u)) U.length :=
        coneV_mlift (by simp) hc (b' - u)
      rw [show u + (b' - u) = b' by omega, coneV_iff_amin] at h0
      have h1 := (reStair_stair b' H g (k :: A)).ge
        (amin (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) U.length)
      omega
    · have h1 := hload b'' (le_trans hb' hb'') Z hZ hbZ g b'' le_rfl
      rw [Nat.sub_self, mlift_zero] at h1
      have e1 : reliftX b'' H g (k :: A) (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z)
          = reliftX b'' H g (k :: A) (mlift (W ++ U) u (b'' - u)) ++ shiftr01 x 0 Z := by
        unfold reliftX
        exact slift_append_low (low_of_Wg hZ x le_rfl) (fun m hm => reStair_low b'' H g _ hm)
      have e2 : reliftX b'' H g (k :: A) (mlift (W ++ U) u (b'' - u))
          = mlift (reliftX b' H g (k :: A) (mlift W u (b' - u)) ++
              reliftX b' H g (k :: A) (mlift U u (b' - u))) b' (b'' - b') := by
        rw [← reliftX_app (Fr_mlift hW _ _) (Hd_mlift hHU _ _), ← mlift_app hW hHU, mlift_reliftX,
          show b' + (b'' - b') = b'' by omega]
        have e := mlift_mlift (W ++ U) u (b' - u) (b'' - b')
        rw [show u + (b' - u) = b' by omega, show b' - u + (b'' - b') = b'' - u by omega] at e
        rw [e]
      rw [e1, e2] at h1
      exact h1
  flat := by
    intro u W hW h g b' hb'
    rw [mlift_snoc_flat W 1 u (b' - u) hW]
    have e : reliftX b' H g (k :: A) (mlift W u (b' - u) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
        = reliftX b' H g (k :: A) (mlift W u (b' - u)) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
      unfold reliftX
      refine slift_snoc_fix _ _ (fun m hm => ?_)
      have hm0 : m = 0 := by simpa using hm
      subst hm0; exact (reStair_stair _ _ _ _).zero
    rw [e]
    exact FLC_flat (fun a ha => by have := hAk a ha; omega) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
      (h g b' hb')

end HcY
end TRIO
