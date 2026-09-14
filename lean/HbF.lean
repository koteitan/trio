/-
HbF.lean: F のタイの本数つきの遠い語の中の段（接頭辞一般、HaS.fwWP_*_step の写し）。

語 fwWn b r n u (W ++ U) の最後の列の潰れを、接頭辞 P と語の頭（遠い字と F のタイ FT r n）を固定して GpT の段に移す。
F のタイは行 0 が 2 で行 1 が r なので、中身の列の祖先の道にも錐にも入らない。
-/
import HbD

namespace TRIO
namespace HbF

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HbD

theorem fwWn_oper_step {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (f : ℕ → ℕ) {b r n u : ℕ} {P : TrioSeq} (hP : Fr P) {W U : TrioSeq} (hW : Fr W)
    (hU : Fr U) (hH : Hd U) (hlen : 2 ≤ U.length)
    (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → GpT A o f b (P ++ fwWn b r n u (W ++ U⟦m⟧))) :
    GpT A o f b (P ++ fwWn b r n u (W ++ U)) := by
  have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  rw [fwWn_append b r n u hW hH]
  have hlen' : 2 ≤ (mlift U u (b - u)).length := by rw [mlift_length]; exact hlen
  have hp' := (hasParent_mlift_iff u (b - u) hUne).mpr hp
  have hfpos : 0 < (fwWn b r n u W).length := by simp [fwWn]
  refine (GpT_ax hA hA1 ho f).oper b _ (fwWn b r n u W ++ shiftr01 1 0 (mlift U u (b - u)))
    hP (Fr_append (Fr_fwWn _ _ _ _ _) (Fr_shift1 _))
    (fun _ => by rw [Small.entry_append_left hfpos]; exact Hd_fwWn b r n u W (by simp [fwWn]))
    (by simp only [List.length_append, shiftr01_length]; omega) ?_ (fun m hm => ?_)
  · have hidx : (fwWn b r n u W ++ shiftr01 1 0 (mlift U u (b - u))).length - 1
        = (fwWn b r n u W).length + ((mlift U u (b - u)).length - 1) := by
      simp only [List.length_append, shiftr01_length]; omega
    rw [hidx, srow_append_right, srow_shiftr01]
    exact hasParent_append_right_of _ _ (hasParent_shiftr01.mpr hp')
  · rw [oper_shift (fwWn b r n u W) (mlift U u (b - u)) 1 m hlen' hp', mlift_oper',
      ← fwWn_append b r n u hW (Hd_oper hH hUne hm)]
    exact hIH m hm

theorem fwWn_orph_step {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (f : ℕ → ℕ) {b r n u : ℕ} (hub : u ≤ b) (hbr : b < r) {P : TrioSeq} (hP : Fr P)
    {W U : TrioSeq} {h j : ℕ} (hW : Fr W) (hU : Fr (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
    (hH : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hj1 : 1 ≤ j) (hj : j ≤ u)
    (hnp : ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z →
      GpT A o f b (P ++ fwWn b r n u (W ++ (U ++ shiftr01 h 0 z)))) :
    GpT A o f b (P ++ fwWn b r n u (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))) := by
  have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u := hj
  obtain ⟨CW, hCW⟩ : ∃ CW, CW = mlift W u (b - u) := ⟨_, rfl⟩
  obtain ⟨CU, hCU⟩ : ∃ CU, CU = mlift U u (b - u) := ⟨_, rfl⟩
  have eL : fwWn b r n u (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
      = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ (CW ++ CU)))
        ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by
    unfold fwWn
    rw [mlift_app hW hH, mlift_snoc_low U _ hc, ← hCW, ← hCU]
    simp [shiftr01]
  rw [eL]
  have hFrA : Fr (FT r n ++ CW) := Fr_FTY (by rw [hCW]; exact Fr_mlift hW _ _)
  refine (GpT_ax hA hA1 ho f).orph b _ _ (h + 1) j hP
    (by rw [← eL]; exact Fr_fwWn _ _ _ _ _) (by rw [← eL]; exact Hd_fwWn _ _ _ _ _)
    hj1 (by omega) ?_ (fun z hz' hbz => ?_)
  · have eAB : (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ (CW ++ CU)))
          ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]
        = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ CW)) ++
          shiftr01 1 0 (CU ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      simp [shiftr01]
    have eidx : (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ (CW ++ CU))).length
        = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ CW)).length + CU.length := by
      simp [shiftr01]; omega
    rw [eAB, eidx]
    have hBH : Hd (CU ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      rw [hCU, ← mlift_snoc_low U _ hc]; exact Hd_mlift hH _ _
    refine noParent_ctx (j := j) (by simp [shiftr01]) (fun k' hk' hrt => ?_) ?_ ?_
    · have := letter_anc_row1 hFrA hBH (by simp) hk' (by simp [shiftr01]) hrt
      subst this
      show j ≤ r
      omega
    · rw [entry1_shiftr01, show CU.length = CU.length + 0 from rfl, entry_append_right]; rfl
    · intro hh
      apply hnp
      rw [hasParent_shiftr01, hCU, ← mlift_snoc_low U _ hc, mlift_eq_slift,
        hasParent_slift (stair_step u (b - u)), mlift_length] at hh
      exact hh
  · have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
    have hHz : Hd (U ++ shiftr01 h 0 z) := Hd_append_shift hH hbz
    have := hz z hz' hbz
    have ez : fwWn b r n u (W ++ (U ++ shiftr01 h 0 z))
        = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ (CW ++ CU)))
          ++ shiftr01 (h + 1) 0 z := by
      unfold fwWn
      rw [mlift_app hW hHz, mlift_append_low (low_of_Wg hzW h (by omega)), ← hCW, ← hCU]
      simp [shiftr01, Function.comp_def, Nat.add_assoc]
    rw [ez] at this
    exact this

theorem fwWn_tie_step {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (f : ℕ → ℕ) {b n u : ℕ} (hub : u ≤ b) {P : TrioSeq} (hP : Fr P)
    (Pb : ℕ → TrioSeq) (hPl : ∀ b'', b ≤ b'' → mlift P b (b'' - b) = Pb b'')
    {W U : TrioSeq} {x : ℕ} (hW : Fr W)
    (hU : Fr (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u U.length) (hHWU : Hd (W ++ U))
    (hload : ∀ b'', b ≤ b'' → ∀ Z ∈ Wg (2 * b''), based Z →
      GpT A o f b'' (Pb b'' ++
        fwWn b'' (b'' + liftOff f A o + 1) n b'' (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z))) :
    GpT A o f b (P ++ fwWn b (b + liftOff f A o + 1) n u
      (W ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]))) := by
  have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
  have hHU : Hd U := by
    intro hne
    have := hH (by simp)
    rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
  have hko' : o ≤ liftOff f A o := by unfold liftOff; omega
  obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f A o + 1 := ⟨_, rfl⟩
  rw [← hr]
  obtain ⟨CW, hCW⟩ : ∃ CW, CW = mlift W u (b - u) := ⟨_, rfl⟩
  obtain ⟨CU, hCU⟩ : ∃ CU, CU = mlift U u (b - u) := ⟨_, rfl⟩
  have hlift : mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b - u)
      = CU ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_cone U _ hc, ← hCU]
    show CU ++ [((x, u + 1 + (b - u), 0) : ℕ × ℕ × ℕ)] = _
    rw [show u + 1 + (b - u) = b + 1 by omega]
  have eL : fwWn b r n u (W ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]))
      = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ (CW ++ CU)))
        ++ [((x + 1, b + 1, 0) : ℕ × ℕ × ℕ)] := by
    unfold fwWn
    rw [mlift_app hW hH, hlift, ← hCW]
    simp [shiftr01]
  rw [eL]
  refine (GpT_ax hA hA1 ho f).tie b _ _ (x + 1) hP
    (by rw [← eL]; exact Fr_fwWn _ _ _ _ _) (by rw [← eL]; exact Hd_fwWn _ _ _ _ _) ?_
    (fun b'' hb'' Z hZ hbZ => ?_)
  · have eAB : (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ (CW ++ CU)))
          ++ [((x + 1, b + 1, 0) : ℕ × ℕ × ℕ)]
        = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ CW)) ++
          shiftr01 1 0 (CU ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
      simp [shiftr01]
    have eidx : (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ (CW ++ CU))).length
        = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ CW)).length + CU.length := by
      simp [shiftr01]; omega
    rw [eAB, eidx]
    have hFrCW : Fr CW := by rw [hCW]; exact Fr_mlift hW _ _
    have hPCA : PathCone b 1 (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FT r n ++ CW)) := by
      intro y hy _ hd
      rcases y with _ | y
      · show b < r; omega
      · exfalso
        rw [entry_cons] at hd
        have hy' : y < (FT r n ++ CW).length := by
          simp only [List.length_cons, shiftr01_length] at hy; omega
        rw [entry0_shiftr01 hy'] at hd
        have := getD_row0_ge (Fr_FTY hFrCW) hy'
        omega
    have hB0 : shiftr01 1 0 (CU ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) ≠ [] →
        entry (shiftr01 1 0 (CU ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) 0 0 = 1 + 1 := by
      intro _
      have hBH : Hd (CU ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
        have := Hd_mlift hH u (b - u)
        rwa [hlift] at this
      rw [entry0_shiftr01 (by simp), hBH (by simp)]
    rw [coneV_pathB hPCA hB0 (by simp [shiftr01]), coneV_shift0]
    have hcm := coneV_mlift (by simp) hc (b - u)
    rw [hlift, show u + (b - u) = b by omega] at hcm
    rw [show CU.length = U.length by rw [hCU, mlift_length]]
    exact hcm
  · have hFrWU : Fr (W ++ U) := Fr_append hW hUc
    have := hload b'' hb'' Z hZ hbZ
    have eP : mlift (P ++ (((1, r, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (FT r n ++ (CW ++ CU)))) b (b'' - b) ++ shiftr01 (x + 1) 0 Z
        = Pb b'' ++
          fwWn b'' (b'' + liftOff f A o + 1) n b'' (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z) := by
      have hCWU : CW ++ CU = mlift (W ++ U) u (b - u) := by rw [hCW, hCU, mlift_app hW hHU]
      rw [mlift_app hP (Hd_letter _ _), hPl b'' hb'',
        mlift_letter (by omega) (Fr_FTY (by rw [hCWU]; exact Fr_mlift hFrWU _ _)), hCWU,
        mlift_app (Fr_FT r n) (Hd_mlift hHWU u (b - u)) b (b'' - b),
        mlift_FT (show b < r by omega) (b'' - b) n]
      have e2 := mlift_mlift (W ++ U) u (b - u) (b'' - b)
      rw [show u + (b - u) = b by omega, show b - u + (b'' - b) = b'' - u by omega] at e2
      rw [e2, show r + (b'' - b) = b'' + liftOff f A o + 1 by omega]
      unfold fwWn
      rw [Nat.sub_self, mlift_zero]
      simp [shiftr01, Function.comp_def, Nat.add_assoc, List.append_assoc]
    rw [eP]
    exact this

theorem fwWn_flat_step {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (f : ℕ → ℕ) {b r n u : ℕ} {P : TrioSeq} (hP : Fr P) {W : TrioSeq} (hW : Fr W)
    (hrep : ∀ m, GpT A o f b (P ++ (List.range m).flatMap (fun _ => fwWn b r n u W))) :
    GpT A o f b (P ++ fwWn b r n u (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])) := by
  have eZ : fwWn b r n u (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
      = fwWn b r n u W ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
    rw [fwWn_append b r n u hW (fun _ => rfl)]
    have := mlift_snoc_low ([] : TrioSeq) ((1, 0, 0) : ℕ × ℕ × ℕ)
      (show ((1, 0, 0) : ℕ × ℕ × ℕ).2.1 ≤ u by show 0 ≤ u; omega) (b - u)
    simp only [List.nil_append, mlift_nil] at this
    rw [this]
    simp [shiftr01]
  rw [eZ]
  obtain ⟨M, hM⟩ : ∃ M, M = fwWn b r n u W := ⟨_, rfl⟩
  rw [← hM]
  have hMne : M ≠ [] := by rw [hM]; simp [fwWn]
  have hMpos : 0 < M.length := List.length_pos_iff.mpr hMne
  have hhead : entry M 0 0 < 2 := by rw [hM]; show 1 < 2; omega
  have htail : ∀ r', 1 ≤ r' → r' < M.length → 2 ≤ entry M 0 r' := by
    intro r' hr1 hr2
    obtain ⟨w, rfl⟩ : ∃ w, r' = w + 1 := ⟨r' - 1, by omega⟩
    have hw' : w < (FT r n ++ mlift W u (b - u)).length := by
      rw [hM] at hr2; simp only [fwWn, List.length_cons, shiftr01_length] at hr2; omega
    rw [hM, fwWn, entry_cons, entry0_shiftr01 hw']
    have := getD_row0_ge (Fr_FTY (Fr_mlift hW u (b - u))) hw'
    omega
  have hlast : hasParent (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)])
      (srow (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1))
      ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
    have hidx : (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1 = M.length + 0 := by simp
    rw [hidx, srow_append_right]
    have hs : srow [((2, 0, 0) : ℕ × ℕ × ℕ)] 0 = 0 := rfl
    rw [hs]
    refine (hasParent_zero_iff (by simp)).mpr ⟨0, by omega, ?_⟩
    rw [Small.entry_append_left hMpos, entry_append_right]
    exact hhead
  refine (GpT_ax hA hA1 ho f).oper b _ (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) hP
    (Fr_append (by rw [hM]; exact Fr_fwWn _ _ _ _ _) (GzF.Fr_single (by omega) _ _))
    (fun _ => by rw [Small.entry_append_left hMpos, hM]; rfl)
    (by simp; omega) hlast (fun m hm => ?_)
  have eO := oper_snoc00'' [] hMne hhead htail m
  simp only [List.nil_append] at eO
  rw [eO, hM]
  exact hrep m

end HbF
end TRIO
