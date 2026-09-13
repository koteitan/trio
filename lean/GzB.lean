/-
GzB.lean: 語を挿入で閉じた PVX に限った字の中身（GyH / GyI の写し）。

    LC1x A o H b Y := ∀ W, PVX A o H b W → PVP A o H b (W ++ (1, b + liftOff H A o + 1, 1) :: Y↑1)
    RLCL A o H b Y := ∀ g b', b ≤ b' →
      LC1x A (o + (H+g) o) (H+g) b' (reliftX b' H g (o :: A) (mlift Y b (b' - b)))

flat（字の複写）は、語の複写が PVX であることを要るので、ここでは出さない（GzD で挿入で閉じた族にして出す）。
-/
import GzA

namespace TRIO
namespace GzB

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA

/-- flat を除いた差し込み口の公理。 -/
structure SlotAx0 (ok : ℕ → TrioSeq → Prop) : Prop where
  lift : ∀ u W, Fr W → ok u W → ∀ u', u ≤ u' → ok u' (mlift W u (u' - u))
  oper : ∀ u W U, Fr W → Fr U → Hd U → 2 ≤ U.length →
    hasParent U (srow U (U.length - 1)) (U.length - 1) →
    (∀ m, 1 ≤ m → ok u (W ++ U⟦m⟧)) → ok u (W ++ U)
  orph : ∀ u W U h j, Fr W → Fr (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) →
    Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) → 1 ≤ j → j ≤ u →
    ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length →
    (∀ z ∈ Wg (2 * j - 1), based z → ok u (W ++ (U ++ shiftr01 h 0 z))) →
    ok u (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
  tie : ∀ u W U x, Fr W → Fr (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) →
    Hd (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) →
    coneV (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u U.length →
    (∀ u', u ≤ u' → ∀ Z ∈ Wg (2 * u'), based Z →
      ok u' (mlift (W ++ U) u (u' - u) ++ shiftr01 x 0 Z)) →
    ok u (W ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]))

theorem SlotAx0.full {ok : ℕ → TrioSeq → Prop} (h : SlotAx0 ok)
    (hflat : ∀ u W, Fr W → ok u W → ok u (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])) : SlotAx ok :=
  ⟨h.lift, h.oper, h.orph, h.tie, hflat⟩

/-! ## 語を PVX に限った字の中身 -/

def LC1x (A : List ℕ) (o : ℕ) (H : ℕ → ℕ) (b : ℕ) (Y : TrioSeq) : Prop :=
  ∀ W, Fr W → PVX A o H b W →
    PVP A o H b (W ++ ((1, b + liftOff H A o + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y)

theorem LC1x_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (H : ℕ → ℕ) (b : ℕ) : LC1x A o H b [] := by
  intro W hW hPV
  have := PVP_snocz hA hA1 ho hW (PVX_to_PVP hPV)
  simpa [shiftr01] using this

theorem LC1x_oper {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} (hY : Fr Y) (hU : Fr U) (hH : Hd U)
    (hlen : 2 ≤ U.length) (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → LC1x A o H b (Y ++ U⟦m⟧)) : LC1x A o H b (Y ++ U) := by
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

theorem LC1x_orph {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} {h j : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
    (hj1 : 1 ≤ j) (hj : j ≤ b)
    (hnp : ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z → LC1x A o H b (Y ++ (U ++ shiftr01 h 0 z))) :
    LC1x A o H b (Y ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
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

theorem LC1x_tie {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} {x : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) b U.length)
    (hload : ∀ b', b ≤ b' → ∀ Z ∈ Wg (2 * b'), based Z →
      LC1x A o H b' (mlift (Y ++ U) b (b' - b) ++ shiftr01 x 0 Z)) :
    LC1x A o H b (Y ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) := by
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
      (PVX_lift hA hA1 ho hW hPV hb'') t
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

/-! ## 状態で添字づけた族 RLCL -/

def RLCL (A : List ℕ) (o : ℕ) (H : ℕ → ℕ) (b : ℕ) (Y : TrioSeq) : Prop :=
  ∀ g b', b ≤ b' →
    LC1x A (o + addF H g o) (addF H g) b' (reliftX b' H g (o :: A) (mlift Y b (b' - b)))

theorem LC1x_congr {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {H1 H2 : ℕ → ℕ}
    (hH : ∀ a ∈ A, H1 a = H2 a) {b : ℕ} {Y : TrioSeq} (h : LC1x A o H1 b Y) : LC1x A o H2 b Y := by
  intro W hW hPV
  have e : liftOff H1 A o = liftOff H2 A o := by unfold liftOff; rw [stepSum_congr 0 o hH]
  have := h W hW (PVX_congr (fun a ha => (hH a ha).symm) hPV)
  rw [e] at this
  exact PVP_congr hA hH this

theorem RLCL_congr {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {H1 H2 : ℕ → ℕ}
    (hH : ∀ a ∈ o :: A, H1 a = H2 a) {b : ℕ} {Y : TrioSeq} (h : RLCL A o H1 b Y) :
    RLCL A o H2 b Y := by
  intro g b' hb'
  have ho : H1 o = H2 o := hH o (by simp)
  have hA' : ∀ a ∈ A, addF H1 g a = addF H2 g a := fun a ha => by
    unfold addF; rw [hH a (by simp [ha])]
  have h1 := h g b' hb'
  rw [reliftX_congr b' hH (fun a _ => rfl)] at h1
  have eO : addF H1 g o = addF H2 g o := by unfold addF; rw [ho]
  rw [eO] at h1
  exact LC1x_congr (fun a ha => by have := hA a ha; omega) hA' h1

theorem RLCL_lift {A : List ℕ} {o : ℕ} {H : ℕ → ℕ} {b : ℕ} {Y : TrioSeq}
    (h : RLCL A o H b Y) (g : ℕ → ℕ) : RLCL A o (addF H g) b (reliftX b H g (o :: A) Y) := by
  intro g' b' hb'
  rw [mlift_reliftX, show b + (b' - b) = b' by omega, reliftX_comp, addF_assoc]
  exact h (addF g g') b' hb'

theorem RLCL_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (H : ℕ → ℕ) (b : ℕ) : RLCL A o H b [] := by
  intro g b' _
  rw [mlift_nil]
  have e : reliftX b' H g (o :: A) [] = [] := by unfold reliftX; exact slift_nil _
  rw [e]
  exact LC1x_nil (fun a ha => by have := hA a ha; omega) hA1 (by omega) _ _

/-- ★ RLCL の差し込み口の公理（flat を除く）。 -/
theorem RLCL_ax {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (H : ℕ → ℕ) : SlotAx0 (RLCL A o H) where
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
    refine LC1x_oper (fun a ha => by have := hA a ha; omega) hA1 (by omega)
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
    have hfix : ∀ m, m ≤ j → reStair b' H g (o :: A) m = m :=
      fun m hm => reStair_low b' H g _ (by omega)
    have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u := hj
    have eU : reliftX b' H g (o :: A) (mlift U u (b' - u)) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]
        = slift (mlift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) (reStair b' H g (o :: A)) := by
      unfold reliftX; rw [mlift_snoc_low U _ hc, slift_snoc_fix _ _ hfix]
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _)]
    have eU2 : reliftX b' H g (o :: A) (mlift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) u (b' - u))
        = reliftX b' H g (o :: A) (mlift U u (b' - u)) ++ [((h, j, 0) : ℕ × ℕ × ℕ)] := by
      rw [eU]; rfl
    rw [eU2]
    refine LC1x_orph (fun a ha => by have := hA a ha; omega) hA1 (by omega)
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
    refine LC1x_tie (fun a ha => by have := hA a ha; omega) hA1 (by omega)
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
    · have h1 := hload b'' (le_trans hb' hb'') Z hZ hbZ g b'' le_rfl
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

end GzB
end TRIO
