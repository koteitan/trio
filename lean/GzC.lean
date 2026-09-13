/-
GzC.lean: 語の節点の位置の挿入で閉じた字の中身の族 U と、その差し込み口の公理（flat を含む）。

    LCI A o H S j F b Y := LC1x (S ++ A) (o + j) F b (mlift Y (b + liftOff H A o) (j + Σ_{s ∈ S} F s))
    U A o H b Y := ∀ g b', b ≤ b' → ∀ S j F, S ⊆ [o + (H+g) o, o + (H+g) o + j) → F = H+g（A の上）→
      LCI A (o + (H+g) o) (H+g) S j F b' (reliftX b' H g (o :: A) (mlift Y b (b' - b)))

flat（字の複写）は、複写した語が PVX であることを U の別の挿入の成分から出す。
-/
import GzB

namespace TRIO
namespace GzC

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzB

/-! ## 挿入した形の字の中身 -/

def LCI (A : List ℕ) (o : ℕ) (H : ℕ → ℕ) (S : List ℕ) (j : ℕ) (F : ℕ → ℕ) (b : ℕ) (Y : TrioSeq) :
    Prop :=
  LC1x (S ++ A) (o + j) F b (mlift Y (b + liftOff H A o) (j + sumOn F S))

theorem LCI_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {S : List ℕ} {j : ℕ} (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) (H F : ℕ → ℕ) (b : ℕ) :
    LCI A o H S j F b [] := by
  unfold LCI; rw [mlift_nil]
  exact LC1x_nil (hA_ins hA hS) (hA1_ins hA1 ho hS) (by omega) _ _

theorem LCI_oper {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {S : List ℕ} {j : ℕ} (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) {F : ℕ → ℕ}
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} (hY : Fr Y) (hU : Fr U) (hH : Hd U)
    (hlen : 2 ≤ U.length) (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → LCI A o H S j F b (Y ++ U⟦m⟧)) : LCI A o H S j F b (Y ++ U) := by
  unfold LCI at hIH ⊢
  have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  rw [mlift_app hY hH]
  refine LC1x_oper (hA_ins hA hS) (hA1_ins hA1 ho hS) (by omega) (Fr_mlift hY _ _) (Fr_mlift hU _ _)
    (Hd_mlift hH _ _) (by rw [mlift_length]; exact hlen) ((hasParent_mlift_iff _ _ hUne).mpr hp)
    (fun m hm => ?_)
  have h := hIH m hm
  rwa [mlift_app hY (Hd_oper hH hUne hm), ← mlift_oper'] at h

theorem LCI_orph {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {S : List ℕ} {j : ℕ} (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) {F : ℕ → ℕ}
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} {h j0 : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((h, j0, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((h, j0, 0) : ℕ × ℕ × ℕ)]))
    (hj1 : 1 ≤ j0) (hj : j0 ≤ b)
    (hnp : ¬ hasParent (U ++ [((h, j0, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j0 - 1), based z → LCI A o H S j F b (Y ++ (U ++ shiftr01 h 0 z))) :
    LCI A o H S j F b (Y ++ (U ++ [((h, j0, 0) : ℕ × ℕ × ℕ)])) := by
  unfold LCI at hz ⊢
  have hc : (((h, j0, 0) : ℕ × ℕ × ℕ)).2.1 ≤ b + liftOff H A o := by
    show j0 ≤ b + liftOff H A o; omega
  rw [mlift_app hY hH, mlift_snoc_low U _ hc]
  refine LC1x_orph (hA_ins hA hS) (hA1_ins hA1 ho hS) (by omega) (Fr_mlift hY _ _)
    (by rw [← mlift_snoc_low U _ hc]; exact Fr_mlift hU _ _)
    (by rw [← mlift_snoc_low U _ hc]; exact Hd_mlift hH _ _) hj1 hj ?_ (fun z hz' hbz => ?_)
  · intro hh
    apply hnp
    rw [← mlift_snoc_low U _ hc, mlift_eq_slift, hasParent_slift (stair_step _ _), mlift_length] at hh
    exact hh
  · have hzW : z ∈ Wg (2 * j0) := Wg_mono (by omega) hz'
    have hHz := Hd_append_shift hH hbz
    have h1 := hz z hz' hbz
    rw [mlift_app hY hHz, mlift_append_low (low_of_Wg hzW h (by omega))] at h1
    exact h1

theorem LCI_tie {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {S : List ℕ} {j : ℕ} (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) {F : ℕ → ℕ}
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} {x : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) b U.length)
    (hload : ∀ b', b ≤ b' → ∀ Z ∈ Wg (2 * b'), based Z →
      LCI A o H S j F b' (mlift (Y ++ U) b (b' - b) ++ shiftr01 x 0 Z)) :
    LCI A o H S j F b (Y ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) := by
  unfold LCI at hload ⊢
  have hk1 : 1 ≤ liftOff H A o := by unfold liftOff; omega
  have hcl : (((x, b + 1, 0) : ℕ × ℕ × ℕ)).2.1 ≤ b + liftOff H A o := by
    show b + 1 ≤ b + liftOff H A o; omega
  have hHU : Hd U := by
    intro hne
    have := hH (by simp)
    rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
  rw [mlift_app hY hH, mlift_snoc_low U _ hcl]
  refine LC1x_tie (hA_ins hA hS) (hA1_ins hA1 ho hS) (by omega) (Fr_mlift hY _ _)
    (by rw [← mlift_snoc_low U _ hcl]; exact Fr_mlift hU _ _)
    (by rw [← mlift_snoc_low U _ hcl]; exact Hd_mlift hH _ _) ?_ (fun b'' hb'' Z hZ hbZ => ?_)
  · have := coneV_mlift_up (by simp) hc (b + liftOff H A o) (j + sumOn F S)
    rwa [mlift_snoc_low U _ hcl, ← mlift_length U (b + liftOff H A o) (j + sumOn F S)] at this
  · have h1 := hload b'' hb'' Z hZ hbZ
    rw [mlift_append_low (low_of_Wg hZ x (by omega))] at h1
    rw [← mlift_app hY hHU, mlift_commk, show b + liftOff H A o + (b'' - b) = b'' + liftOff H A o by omega]
    exact h1

theorem LCI_congr {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {S : List ℕ} {j : ℕ}
    (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) {H1 H2 F1 F2 : ℕ → ℕ} (hH : ∀ a ∈ A, H1 a = H2 a)
    (hF : ∀ a ∈ S ++ A, F1 a = F2 a) {b : ℕ}
    {Y : TrioSeq} (h : LCI A o H1 S j F1 b Y) : LCI A o H2 S j F2 b Y := by
  unfold LCI at h ⊢
  rw [← liftOff_congrA hH, ← sumOn_congr (fun s hs => hF s (List.mem_append_left _ hs))]
  exact LC1x_congr (hA_ins hA hS) hF h

/-! ## 挿入で閉じた字の中身の族 -/

def U (A : List ℕ) (o : ℕ) (H : ℕ → ℕ) (b : ℕ) (Y : TrioSeq) : Prop :=
  ∀ g b', b ≤ b' → ∀ S j F, (∀ s ∈ S, o + addF H g o ≤ s ∧ s < o + addF H g o + j) →
    (∀ a ∈ A, F a = addF H g a) →
    LCI A (o + addF H g o) (addF H g) S j F b' (reliftX b' H g (o :: A) (mlift Y b (b' - b)))

theorem U_congr {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {H1 H2 : ℕ → ℕ}
    (hH : ∀ a ∈ o :: A, H1 a = H2 a) {b : ℕ} {Y : TrioSeq} (h : U A o H1 b Y) : U A o H2 b Y := by
  intro g b' hb' S j F hS hF
  have eO : addF H1 g o = addF H2 g o := by unfold addF; rw [hH o (by simp)]
  have hA' : ∀ a ∈ A, addF H1 g a = addF H2 g a := fun a ha => by
    unfold addF; rw [hH a (by simp [ha])]
  rw [← eO] at hS ⊢
  have h1 := h g b' hb' S j F hS (fun a ha => by rw [hF a ha, hA' a ha])
  rw [reliftX_congr b' hH (fun a _ => rfl)] at h1
  exact LCI_congr (fun a ha => by have := hA a ha; omega) hS hA' (fun _ _ => rfl) h1

theorem U_lift {A : List ℕ} {o : ℕ} {H : ℕ → ℕ} {b : ℕ} {Y : TrioSeq}
    (h : U A o H b Y) (g : ℕ → ℕ) : U A o (addF H g) b (reliftX b H g (o :: A) Y) := by
  intro g' b' hb' S j F hS hF
  rw [addF_assoc] at hS hF ⊢
  rw [mlift_reliftX, show b + (b' - b) = b' by omega, reliftX_comp]
  exact h (addF g g') b' hb' S j F hS hF

theorem U_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (H : ℕ → ℕ) (b : ℕ) : U A o H b [] := by
  intro g b' _ S j F hS _
  rw [mlift_nil]
  have e : reliftX b' H g (o :: A) [] = [] := by unfold reliftX; exact slift_nil _
  rw [e]
  exact LCI_nil (fun a ha => by have := hA a ha; omega) hA1 (by omega) hS _ _ _

/-- ★ U の差し込み口の公理（flat を除く）。 -/
theorem U_ax {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (H : ℕ → ℕ) : SlotAx0 (U A o H) where
  lift := by
    intro u W hW h u1 hu1 g b' hb' S j F hS hF
    have e := mlift_mlift W u (u1 - u) (b' - u1)
    rw [show u + (u1 - u) = u1 by omega, show u1 - u + (b' - u1) = b' - u by omega] at e
    rw [e]
    exact h g b' (le_trans hu1 hb') S j F hS hF
  oper := by
    intro u W U hW hU hH hlen hp hIH g b' hb' S j F hS hF
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    rw [mlift_app hW hH u (b' - u), reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _)]
    refine LCI_oper (fun a ha => by have := hA a ha; omega) hA1 (by omega) hS
      (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
      (Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) (by rw [reliftX_length, mlift_length]; exact hlen)
      ?_ (fun m hm => ?_)
    · unfold reliftX
      rw [slift_length, srow_slift (reStair_stair _ _ _ _) (by rw [mlift_length]; omega),
        hasParent_slift (reStair_stair _ _ _ _)]
      exact (hasParent_mlift_iff u (b' - u) hUne).mpr hp
    · have h1 := hIH m hm g b' hb' S j F hS hF
      rw [mlift_app hW (Hd_oper hH hUne hm),
        reliftX_app (Fr_mlift hW _ _) (Hd_mlift (Hd_oper hH hUne hm) _ _)] at h1
      unfold reliftX at h1 ⊢
      rwa [← mlift_oper', slift_oper (reStair_stair _ _ _ _)] at h1
  orph := by
    intro u W U h j0 hW hU hH hj1 hj hnp hz g b' hb' S j F hS hF
    have hfix : ∀ m, m ≤ j0 → reStair b' H g (o :: A) m = m :=
      fun m hm => reStair_low b' H g _ (by omega)
    have hc : (((h, j0, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u := hj
    have eU : reliftX b' H g (o :: A) (mlift U u (b' - u)) ++ [((h, j0, 0) : ℕ × ℕ × ℕ)]
        = slift (mlift (U ++ [((h, j0, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) (reStair b' H g (o :: A)) := by
      unfold reliftX; rw [mlift_snoc_low U _ hc, slift_snoc_fix _ _ hfix]
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _)]
    have eU2 : reliftX b' H g (o :: A) (mlift (U ++ [((h, j0, 0) : ℕ × ℕ × ℕ)]) u (b' - u))
        = reliftX b' H g (o :: A) (mlift U u (b' - u)) ++ [((h, j0, 0) : ℕ × ℕ × ℕ)] := by
      rw [eU]; rfl
    rw [eU2]
    refine LCI_orph (fun a ha => by have := hA a ha; omega) hA1 (by omega) hS
      (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (by rw [eU]; exact Fr_slift (Fr_mlift hU _ _) _)
      (by rw [eU]; exact Hd_slift (Hd_mlift hH _ _) _) hj1 (le_trans hj hb') ?_
      (fun z hz' hbz => ?_)
    · intro hh; apply hnp
      rw [eU, reliftX_length, mlift_length, hasParent_slift (reStair_stair _ _ _ _),
        mlift_eq_slift, hasParent_slift (stair_step _ _)] at hh
      exact hh
    · have hzW : z ∈ Wg (2 * j0) := Wg_mono (by omega) hz'
      have h1 := hz z hz' hbz g b' hb' S j F hS hF
      have hHz := Hd_append_shift hH hbz
      rw [mlift_app hW hHz, mlift_append_low (low_of_Wg hzW h (show j0 ≤ u by omega))] at h1
      have hH2 : Hd (mlift U u (b' - u) ++ shiftr01 h 0 z) := by
        have := Hd_mlift hHz u (b' - u)
        rwa [mlift_append_low (low_of_Wg hzW h (show j0 ≤ u by omega))] at this
      rw [reliftX_app (Fr_mlift hW _ _) hH2] at h1
      unfold reliftX at h1 ⊢
      rwa [slift_append_low (low_of_Wg hzW h (show j0 ≤ b' by omega))
        (fun m hm => reStair_low b' H g _ hm)] at h1
  tie := by
    intro u W U x hW hU hH hc hload g b' hb' S j F hS hF
    have hA'1 : ∀ a ∈ o :: A, 1 ≤ a := by
      intro a ha; simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ho
      · exact hA1 a ha
    have eT : mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)
        = mlift U u (b' - u) ++ [((x, b' + 1, 0) : ℕ × ℕ × ℕ)] := by
      rw [mlift_snoc_cone U _ hc]
      show _ ++ [((x, u + 1 + (b' - u), 0) : ℕ × ℕ × ℕ)] = _
      rw [show u + 1 + (b' - u) = b' + 1 by omega]
    have hfix : ∀ m, m ≤ b' + 1 → reStair b' H g (o :: A) m = m :=
      fun m hm => reStair_tie b' H g hA'1 hm
    have eU : reliftX b' H g (o :: A) (mlift U u (b' - u)) ++ [((x, b' + 1, 0) : ℕ × ℕ × ℕ)]
        = reliftX b' H g (o :: A) (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) := by
      rw [eT]; unfold reliftX; rw [slift_snoc_fix _ _ hfix]
    have hHU : Hd U := by
      intro hne
      have := hH (by simp)
      rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), ← eU]
    refine LCI_tie (fun a ha => by have := hA a ha; omega) hA1 (by omega) hS
      (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (by rw [eU]; exact Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
      (by rw [eU]; exact Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) ?_ (fun b'' hb'' Z hZ hbZ => ?_)
    · rw [eU, reliftX_length, mlift_length]
      unfold reliftX
      rw [coneV_iff_amin, amin_slift (reStair_stair _ _ _ _) (by simp)]
      have h0 : coneV (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) (u + (b' - u)) U.length :=
        coneV_mlift (by simp) hc (b' - u)
      rw [show u + (b' - u) = b' by omega, coneV_iff_amin] at h0
      have h1 := (reStair_stair b' H g (o :: A)).ge
        (amin (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) U.length)
      omega
    · have h1 := hload b'' (le_trans hb' hb'') Z hZ hbZ g b'' le_rfl S j F hS hF
      rw [Nat.sub_self, mlift_zero] at h1
      have e1 : reliftX b'' H g (o :: A) (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z)
          = reliftX b'' H g (o :: A) (mlift (W ++ U) u (b'' - u)) ++ shiftr01 x 0 Z := by
        unfold reliftX
        exact slift_append_low (low_of_Wg hZ x le_rfl) (fun m hm => reStair_low b'' H g _ hm)
      have e2 : reliftX b'' H g (o :: A) (mlift (W ++ U) u (b'' - u))
          = mlift (reliftX b' H g (o :: A) (mlift W u (b' - u)) ++
              reliftX b' H g (o :: A) (mlift U u (b' - u))) b' (b'' - b') := by
        rw [← reliftX_app (Fr_mlift hW _ _) (Hd_mlift hHU _ _), ← mlift_app hW hHU, mlift_reliftX,
          show b' + (b'' - b') = b'' by omega]
        have e := mlift_mlift (W ++ U) u (b' - u) (b'' - b')
        rw [show u + (b' - u) = b' by omega, show b' - u + (b'' - b') = b'' - u by omega] at e
        rw [e]
      rw [e1, e2] at h1
      exact h1

/-! ## flat（字の複写） -/

/-- LCI の flat: 複写した語 W ++ (ℓ :: Y↑1)^m が PVX であることを、挿入を合成した LCI から出す。 -/
theorem LCI_flat_of {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {Y0 : TrioSeq} (hY0 : Fr Y0)
    (hall : ∀ S j F, (∀ s ∈ S, o ≤ s ∧ s < o + j) → (∀ a ∈ A, F a = H a) → LCI A o H S j F b Y0)
    {S : List ℕ} {j : ℕ} {F : ℕ → ℕ} (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) (hF : ∀ a ∈ A, F a = H a) :
    LCI A o H S j F b (Y0 ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := by
  unfold LCI
  rw [mlift_snoc_flat Y0 1 _ _ hY0]
  obtain ⟨A', hA'def⟩ : ∃ A', A' = S ++ A := ⟨_, rfl⟩
  obtain ⟨o', ho'def⟩ : ∃ o', o' = o + j := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = mlift Y0 (b + liftOff H A o) (j + sumOn F S) := ⟨_, rfl⟩
  rw [← hA'def, ← ho'def, ← hYdef]
  have hAo' : ∀ a ∈ A', a < o' := by rw [hA'def, ho'def]; exact hA_ins hA hS
  have hA1' : ∀ a ∈ A', 1 ≤ a := by rw [hA'def]; exact hA1_ins hA1 ho hS
  have hY : Fr Y := by rw [hYdef]; exact Fr_mlift hY0 _ _
  have hk : liftOff F A' o' = liftOff H A o + j + sumOn F S := by
    rw [hA'def, ho'def, liftOff_ins hA hS, liftOff_congrA hF]
  -- 複写した語が PVX
  have hstep : ∀ W0, Fr W0 → PVX A' o' F b W0 →
      PVX A' o' F b (W0 ++ ((1, b + liftOff F A' o' + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y) := by
    intro W0 hW0 hPV0 S2 j2 F2 hS2 hF2
    have hS' : ∀ s ∈ S2 ++ S, o ≤ s ∧ s < o + (j + j2) := by
      intro s hs
      rcases List.mem_append.mp hs with h2 | h2
      · have := hS2 s h2; rw [ho'def] at this; omega
      · have := hS s h2; omega
    have hF2S : ∀ s ∈ S, F2 s = F s := fun s hs =>
      hF2 s (by rw [hA'def]; exact List.mem_append_left _ hs)
    have hF2A : ∀ a ∈ A, F2 a = H a := fun a ha => by
      rw [hF2 a (by rw [hA'def]; exact List.mem_append_right _ ha)]; exact hF a ha
    have h2 := hall (S2 ++ S) (j + j2) F2 hS' hF2A
    unfold LCI at h2
    rw [List.append_assoc, show o + (j + j2) = o + j + j2 by omega, sumOn_append, sumOn_congr hF2S,
      show j + j2 + (sumOn F2 S2 + sumOn F S) = (j + sumOn F S) + (j2 + sumOn F2 S2) by omega,
      ← mlift_mlift, ← hA'def, ← ho'def, ← hYdef,
      show b + liftOff H A o + (j + sumOn F S) = b + liftOff F A' o' by omega] at h2
    have hPVr := PVX_refine hAo' hPV0 S2 j2 F2 hS2 hF2
    have h3 := h2 _ (Fr_mlift hW0 _ _) hPVr
    rw [mlift_letterU hW0 hY (show b + liftOff F A' o' < b + liftOff F A' o' + 1 by omega)]
    have ek : liftOff F2 (S2 ++ A') (o' + j2) = liftOff F A' o' + j2 + sumOn F2 S2 := by
      rw [liftOff_ins hAo' hS2, liftOff_congrA hF2]
    rw [ek, show b + (liftOff F A' o' + j2 + sumOn F2 S2) + 1
      = b + liftOff F A' o' + 1 + (j2 + sumOn F2 S2) by omega] at h3
    exact h3
  intro W hW hPV t
  have hrep : ∀ m, PVX A' o' F b (W ++ (List.range m).flatMap
      (fun _ => ((1, b + liftOff F A' o' + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y)) ∧
      Fr (W ++ (List.range m).flatMap
        (fun _ => ((1, b + liftOff F A' o' + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y)) := by
    intro m
    induction m with
    | zero => simpa using And.intro hPV hW
    | succ m ih =>
        rw [List.range_succ, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [← List.append_assoc]
        exact ⟨hstep _ ih.2 ih.1, Fr_append ih.2 (Fr_letter _ _)⟩
  have hY1 : Fr (Y ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) :=
    Fr_append hY (by intro y hy; simp at hy; subst hy; show 1 ≤ 1; omega)
  rw [mlift_letterU hW hY1 (show b + liftOff F A' o' < b + liftOff F A' o' + 1 by omega),
    mlift_snoc_flat Y 1 (b + liftOff F A' o') t hY]
  obtain ⟨M, hM⟩ : ∃ M : TrioSeq,
      M = ((1, b + liftOff F A' o' + 1 + t, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift Y (b + liftOff F A' o') t) := ⟨_, rfl⟩
  have eV : ((1, b + liftOff F A' o' + 1 + t, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (mlift Y (b + liftOff F A' o') t ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
      = M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
    rw [hM, node_split, shift_col]
  rw [eV]
  have hMne : M ≠ [] := by rw [hM]; simp
  have hhead : entry M 0 0 < 2 := by rw [hM]; show 1 < 2; omega
  have htail : ∀ r, 1 ≤ r → r < M.length → 2 ≤ entry M 0 r := by
    intro r hr1 hr2
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hr' : r' < (mlift Y (b + liftOff F A' o') t).length := by
      rw [hM] at hr2; simp only [List.length_cons, shiftr01_length] at hr2; omega
    rw [hM, entry_cons, entry0_shiftr01 hr']
    have := getD_row0_ge (Fr_mlift hY (b + liftOff F A' o') t) hr'
    omega
  have hpV : hasParent (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)])
      (srow (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1))
      ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
    have hidx : (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1 = M.length + 0 := by simp
    rw [hidx, srow_append_right]
    have hs : srow [((2, 0, 0) : ℕ × ℕ × ℕ)] 0 = 0 := rfl
    rw [hs]
    refine (hasParent_zero_iff (by simp)).mpr ⟨0, by rw [hM]; simp, ?_⟩
    rw [Small.entry_append_left (by rw [hM]; simp), entry_append_right]
    exact hhead
  refine (GpT_ax (fun a ha => by have := hAo' a ha; omega) hA1' (by omega) F).oper b _
    (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) (Fr_mlift hW _ _)
    (Fr_append (by rw [hM]; exact Fr_letter _ _)
      (by intro y hy; simp at hy; subst hy; show 1 ≤ 2; omega))
    (fun _ => by rw [hM]; rfl) (by simp only [List.length_append, List.length_singleton]; rw [hM]; simp)
    hpV (fun m _ => ?_)
  have eO := oper_snoc00'' [] hMne hhead htail m
  simp only [List.nil_append] at eO
  rw [eO]
  have h2 := PVX_to_PVP (hrep m).1 t
  rw [mlift_rep hW (Fr_letter _ _) (Hd_letter _ _),
    mlift_letter (show b + liftOff F A' o' < b + liftOff F A' o' + 1 by omega) hY, ← hM] at h2
  exact h2

theorem U_flat {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {u : ℕ} {W : TrioSeq} (hW : Fr W) (h : U A o H u W) :
    U A o H u (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := by
  intro g b' hb' S j F hS hF
  rw [mlift_snoc_flat W 1 u (b' - u) hW]
  have e : reliftX b' H g (o :: A) (mlift W u (b' - u) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
      = reliftX b' H g (o :: A) (mlift W u (b' - u)) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
    unfold reliftX
    refine slift_snoc_fix _ _ (fun m hm => ?_)
    have hm0 : m = 0 := by simpa using hm
    subst hm0; exact (reStair_stair _ _ _ _).zero
  rw [e]
  exact LCI_flat_of (fun a ha => by have := hA a ha; omega) hA1 (by omega)
    (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (fun S' j' F' hS' hF' => h g b' hb' S' j' F' hS' hF') hS hF

/-- ★ U は flat を含む差し込み口の公理を満たす。 -/
theorem U_slot {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (H : ℕ → ℕ) : SlotAx (U A o H) :=
  (U_ax hA hA1 ho H).full (fun _ _ hW h => U_flat hA hA1 ho hW h)

theorem U_load {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {K Z : TrioSeq} (hK : Fr K) (h : U A o H b K) (hZ : Z ∈ Wg (2 * b))
    (hb : based Z) : U A o H b (K ++ shiftr01 1 0 Z) :=
  slot_load (U_slot hA hA1 ho H) hK h Z hZ hb

end GzC
end TRIO
