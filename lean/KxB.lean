/-
KxB.lean: 語を PVK に限った字の中身 LC1k（GzB の LC1x の写し）。

    LC1k A o H b Y := ∀ W, Fr W → PVK A o H b W → PVP A o H b (W ++ (1, b + liftOff H A o + 1, 1) :: Y↑1)
-/
import KxA
import GzB

namespace TRIO
namespace KxB

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzB KxA

/-! ## 語を PVK に限った字の中身 -/

def LC1k (A : List ℕ) (o : ℕ) (H : ℕ → ℕ) (b : ℕ) (Y : TrioSeq) : Prop :=
  ∀ W, Fr W → PVK A o H b W →
    PVP A o H b (W ++ ((1, b + liftOff H A o + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y)

theorem LC1k_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (H : ℕ → ℕ) (b : ℕ) : LC1k A o H b [] := by
  intro W hW hPV
  have := PVP_snocz hA hA1 ho hW (PVK_to_PVP hPV)
  simpa [shiftr01] using this

theorem LC1k_oper {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} (hY : Fr Y) (hU : Fr U) (hH : Hd U)
    (hlen : 2 ≤ U.length) (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → LC1k A o H b (Y ++ U⟦m⟧)) : LC1k A o H b (Y ++ U) := by
  intro W hW hPV t
  have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  rw [mlift_letterU hW (Fr_append hY hU)
    (show b + liftOff H A o < b + liftOff H A o + 1 by omega), mlift_app hY hH]
  have hlen' : 2 ≤ (mlift U (b + liftOff H A o) t).length := by rw [mlift_length]; exact hlen
  have hUlne : mlift U (b + liftOff H A o) t ≠ [] := by
    intro h; have := congrArg List.length h; rw [mlift_length, List.length_nil] at this; omega
  have hp' := (hasParent_mlift_iff (b + liftOff H A o) t hUne).mpr hp
  refine (GpT_ax (fun a ha => by have := hA a ha; omega) hA1 (by omega) H).oper b _ _
    (Fr_mlift hW _ _) (Fr_letter _ _) (Hd_letter _ _)
    (by simp only [List.length_cons, List.length_append, shiftr01_length]; omega)
    (node_hasParent _ _ _ hp' hUlne) (fun m hm => ?_)
  rw [node_oper _ _ _ hlen' hp' m, mlift_oper', ← mlift_app hY (Hd_oper hH hUne hm)]
  have h := hIH m hm W hW hPV t
  rwa [mlift_letterU hW (Fr_append hY (Fr_oper hU m))
    (show b + liftOff H A o < b + liftOff H A o + 1 by omega)] at h

theorem LC1k_orph {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} {h j : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
    (hj1 : 1 ≤ j) (hj : j ≤ b)
    (hnp : ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z → LC1k A o H b (Y ++ (U ++ shiftr01 h 0 z))) :
    LC1k A o H b (Y ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
  intro W hW hPV t
  have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ b + liftOff H A o := by
    show j ≤ b + liftOff H A o; omega
  have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
  have eL : mlift (Y ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (b + liftOff H A o) t
      = mlift Y (b + liftOff H A o) t ++ (mlift U (b + liftOff H A o) t ++
          [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_app hY hH, mlift_snoc_low U _ hc]
  rw [mlift_letterU hW (Fr_append hY hU)
    (show b + liftOff H A o < b + liftOff H A o + 1 by omega), eL]
  have eV : ((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ (mlift U (b + liftOff H A o) t ++
          [((h, j, 0) : ℕ × ℕ × ℕ)]))
      = (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t))
        ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by
    rw [← List.append_assoc, shiftr01_append0, shift_col]; rfl
  rw [eV]
  refine (GpT_ax (fun a ha => by have := hA a ha; omega) hA1 (by omega) H).orph b _ _ (h + 1) j
    (Fr_mlift hW _ _) (by rw [← eV]; exact Fr_letter _ _) (by rw [← eV]; exact Hd_letter _ _)
    hj1 hj ?_ (fun z hz' hbz => ?_)
  · have eAB : (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t))
          ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]
        = (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift Y (b + liftOff H A o) t)) ++
          shiftr01 1 0 (mlift U (b + liftOff H A o) t ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      rw [← eV, node_split]
    have eidx : (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t)).length
        = (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift Y (b + liftOff H A o) t)).length +
          (mlift U (b + liftOff H A o) t).length := by simp [shiftr01]; omega
    rw [eAB, eidx]
    have hBH : Hd (mlift U (b + liftOff H A o) t ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      rw [← mlift_snoc_low U _ hc]; exact Hd_mlift hH _ _
    refine noParent_ctx (j := j) (by simp [shiftr01]) (fun k' hk' hrt => ?_) ?_ ?_
    · have := letter_anc_row1 (Fr_mlift hY (b + liftOff H A o) t) hBH (by simp) hk'
        (by simp [shiftr01]) hrt
      subst this
      show j ≤ b + liftOff H A o + 1 + t
      omega
    · rw [entry1_shiftr01, show (mlift U (b + liftOff H A o) t).length
          = (mlift U (b + liftOff H A o) t).length + 0 from rfl, entry_append_right]; rfl
    · intro hh
      apply hnp
      rw [hasParent_shiftr01, ← mlift_snoc_low U _ hc, mlift_eq_slift,
        hasParent_slift (stair_step (b + liftOff H A o) t), mlift_length] at hh
      exact hh
  · have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
    have hHz : Hd (U ++ shiftr01 h 0 z) := Hd_append_shift hH hbz
    have hFrz : Fr (U ++ shiftr01 h 0 z) := by
      have hh1 : 1 ≤ h := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
      refine Fr_append hUc (fun y hy => ?_)
      simp only [shiftr01, List.mem_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      dsimp only; omega
    have hzz := hz z hz' hbz W hW hPV t
    rw [mlift_letterU hW (Fr_append hY hFrz)
        (show b + liftOff H A o < b + liftOff H A o + 1 by omega), mlift_app hY hHz,
      mlift_append_low (low_of_Wg hzW h (by omega))] at hzz
    rw [show (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t)) ++
            shiftr01 (h + 1) 0 z
        = ((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++
              (mlift U (b + liftOff H A o) t ++ shiftr01 h 0 z)) by
      rw [← List.append_assoc, shiftr01_append0 _
        (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t), shiftr01_add0]; rfl]
    exact hzz

theorem LC1k_tie {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} {x : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) b U.length)
    (hload : ∀ b', b ≤ b' → ∀ Z ∈ Wg (2 * b'), based Z →
      LC1k A o H b' (mlift (Y ++ U) b (b' - b) ++ shiftr01 x 0 Z)) :
    LC1k A o H b (Y ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) := by
  intro W hW hPV t
  have hk1 : 1 ≤ liftOff H A o := by unfold liftOff; omega
  have hcl : (((x, b + 1, 0) : ℕ × ℕ × ℕ)).2.1 ≤ b + liftOff H A o := by
    show b + 1 ≤ b + liftOff H A o; omega
  have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
  have eL : mlift (Y ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) (b + liftOff H A o) t
      = mlift Y (b + liftOff H A o) t ++ (mlift U (b + liftOff H A o) t ++
          [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_app hY hH, mlift_snoc_low U _ hcl]
  rw [mlift_letterU hW (Fr_append hY hU)
    (show b + liftOff H A o < b + liftOff H A o + 1 by omega), eL]
  have eV : ((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ (mlift U (b + liftOff H A o) t ++
          [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
      = (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t))
        ++ [((x + 1, b + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [← List.append_assoc, shiftr01_append0, shift_col]; rfl
  rw [eV]
  have hHU : Hd U := by
    intro hne
    have := hH (by simp)
    rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
  refine (GpT_ax (fun a ha => by have := hA a ha; omega) hA1 (by omega) H).tie b _ _ (x + 1)
    (Fr_mlift hW _ _) (by rw [← eV]; exact Fr_letter _ _) (by rw [← eV]; exact Hd_letter _ _) ?_
    (fun b'' hb'' Z hZ hbZ => ?_)
  · have eAB : (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t))
          ++ [((x + 1, b + 1, 0) : ℕ × ℕ × ℕ)]
        = (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift Y (b + liftOff H A o) t)) ++
          shiftr01 1 0 (mlift U (b + liftOff H A o) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
      rw [← eV, node_split]
    have eidx : (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t)).length
        = (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift Y (b + liftOff H A o) t)).length +
          (mlift U (b + liftOff H A o) t).length := by simp [shiftr01]; omega
    rw [eAB, eidx]
    have hPCA : PathCone b 1 (((1, b + liftOff H A o + 1 + t, 1) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift Y (b + liftOff H A o) t)) := by
      intro y hy _ hd
      rcases y with _ | y
      · show b < b + liftOff H A o + 1 + t; omega
      · exfalso
        rw [entry_cons] at hd
        have hy' : y < (mlift Y (b + liftOff H A o) t).length := by
          rw [mlift_length]; simp [shiftr01] at hy; omega
        rw [entry0_shiftr01 hy'] at hd
        have := getD_row0_ge (Fr_mlift hY (b + liftOff H A o) t) hy'
        omega
    have hB0 : shiftr01 1 0 (mlift U (b + liftOff H A o) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) ≠ [] →
        entry (shiftr01 1 0 (mlift U (b + liftOff H A o) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) 0 0
          = 1 + 1 := by
      intro _
      have hBH : Hd (mlift U (b + liftOff H A o) t ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
        have := Hd_mlift hH (b + liftOff H A o) t
        rwa [mlift_snoc_low U _ hcl] at this
      rw [entry0_shiftr01 (by simp), hBH (by simp)]
    rw [coneV_pathB hPCA hB0 (by simp [shiftr01]), coneV_shift0]
    have := coneV_mlift_up (by simp) hc (b + liftOff H A o) t
    rwa [mlift_snoc_low U _ hcl, ← mlift_length U (b + liftOff H A o) t] at this
  · have hFrYU : Fr (Y ++ U) := Fr_append hY hUc
    have hFrZ : Fr (mlift (Y ++ U) b (b'' - b) ++ shiftr01 x 0 Z) := by
      have hx1 : 1 ≤ x := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
      refine Fr_append (Fr_mlift hFrYU _ _) (fun y hy => ?_)
      simp only [shiftr01, List.mem_map] at hy
      obtain ⟨p, -, rfl⟩ := hy
      dsimp only; omega
    have h1 := hload b'' hb'' Z hZ hbZ (mlift W b (b'' - b)) (Fr_mlift hW _ _)
      (PVK_lift hA hA1 ho hW hPV hb'') t
    rw [mlift_letterU (Fr_mlift hW _ _) hFrZ
        (show b'' + liftOff H A o < b'' + liftOff H A o + 1 by omega),
      mlift_append_low (low_of_Wg hZ x (by omega))] at h1
    have hWU : Fr (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t) :=
      Fr_append (Fr_mlift hY _ _) (Fr_mlift hUc _ _)
    have eW : mlift (mlift W (b + liftOff H A o) t) b (b'' - b)
        = mlift (mlift W b (b'' - b)) (b'' + liftOff H A o) t := by
      rw [mlift_commk, show b + liftOff H A o + (b'' - b) = b'' + liftOff H A o by omega]
    have eKU : mlift (mlift Y (b + liftOff H A o) t ++ mlift U (b + liftOff H A o) t) b (b'' - b)
        = mlift (mlift (Y ++ U) b (b'' - b)) (b'' + liftOff H A o) t := by
      rw [← mlift_app hY hHU, mlift_commk,
        show b + liftOff H A o + (b'' - b) = b'' + liftOff H A o by omega]
    rw [mlift_app (Fr_mlift hW _ _) (Hd_letter _ _), eW, mlift_letter (by omega) hWU, eKU,
      show b + liftOff H A o + 1 + t + (b'' - b) = b'' + liftOff H A o + 1 + t by omega,
      List.append_assoc]
    rw [shiftr01_append0, shiftr01_add0] at h1
    simpa [List.append_assoc] using h1

end KxB
end TRIO
