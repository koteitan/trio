/-
GzV.lean: GzN の okW を閾値 k に上げた族 okWk（差し込み口の公理を満たす）。

    GTWk k b0 w  := ∀ ws, FarCWk k b0 ws → FarCWk k b0 (ws ++ [w])
    okWk k u X   := Hd X ∧ LowC (u+k) X ∧ ∀ b0, GTWk k b0 (u, X)

okWk_ax は GzN.okW_ax の写し（低い閾値を u+1 から u+k に替えただけ）。
-/
import GzN
import GzU

namespace TRIO
namespace GzV

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzM GzN GzU

def GTWk (k b0 : ℕ) (w : ℕ × TrioSeq) : Prop := ∀ ws, FarCWk k b0 ws → FarCWk k b0 (ws ++ [w])

def okWk (k u : ℕ) (X : TrioSeq) : Prop := Hd X ∧ LowC (u + k) X ∧ ∀ b0, GTWk k b0 (u, X)

theorem GTWk_nil (k b0 c0 : ℕ) : GTWk k b0 (c0, []) := fun _ hC => farWk_collapse hC

theorem GTWk_rep {k b0 : ℕ} {w : ℕ × TrioSeq} (h : GTWk k b0 w) {ws : List (ℕ × TrioSeq)}
    (hC : FarCWk k b0 ws) : ∀ m, FarCWk k b0 (ws ++ List.replicate m w)
  | 0 => by simpa using hC
  | m + 1 => by
      have := h _ (GTWk_rep h hC m)
      rwa [List.append_assoc, ← List.replicate_succ'] at this

theorem RawWsk_snoc {k b : ℕ} {ws : List (ℕ × TrioSeq)} {w : ℕ × TrioSeq} (h : RawWsk k b ws)
    (hw : RawWk k b w) : RawWsk k b (ws ++ [w]) := by
  intro w' h'
  rcases List.mem_append.mp h' with h' | h'
  · exact h w' h'
  · simp at h'; subst h'; exact hw

/-! ## 差し込み口の公理 -/

theorem okWk_ax {k : ℕ} (hk1 : 1 ≤ k) : SlotAx (okWk k) where
  lift := by
    intro u W hW h u' hu
    refine ⟨Hd_mlift h.1 u (u' - u), ?_, fun b0 ws hC A o f b hb hR hA hA1 ho hAk hko => ?_⟩
    · have := LowC_mliftk h.2.1 (u' - u)
      rwa [show u + k + (u' - u) = u' + k by omega] at this
    · have hw : RawWk k b (u', mlift W u (u' - u)) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u' ≤ b := hw.1
      have hR0 : RawWsk k b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      have := h.2.2 b0 ws hC A o f b hb (RawWsk_snoc hR0 ⟨by omega, hW, h.1, h.2.1⟩) hA hA1 ho
        hAk hko
      rw [farW_snoc] at this ⊢
      have e : fwW b (b + liftOff f A o + 1) u' (mlift W u (u' - u))
          = fwW b (b + liftOff f A o + 1) u W := by
        unfold fwW
        have e2 := mlift_mlift W u (u' - u) (b - u')
        rw [show u + (u' - u) = u' by omega, show u' - u + (b - u') = b - u by omega] at e2
        rw [e2]
      exact e ▸ this
  oper := by
    intro u W U hW hU hH hlen hp hIH
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    have hI1 := hIH 1 le_rfl
    have hU1 : U⟦1⟧ = U.dropLast := oper_one_eq_dropLast (by omega)
    refine ⟨Hd_append_of hH hI1.1, ?_, fun b0 ws hC A o f b hb hR hA hA1 ho hAk hko => ?_⟩
    · rw [hU1] at hI1
      obtain ⟨q, hq, -⟩ := hp
      have hqlt : q < U.length - 1 := nextR_index_lt hq
      have hrt := rtg_nextrel0_lift W U (rtg0_of_nextR' hq)
      have hsplit : W ++ U = (W ++ U.dropLast) ++ [U.getLast hUne] := by
        rw [List.append_assoc, List.dropLast_append_getLast hUne]
      rw [hsplit] at hrt ⊢
      have hlenD : (W ++ U.dropLast).length = W.length + (U.length - 1) := by
        rw [List.length_append, List.length_dropLast]
      rw [← hlenD] at hrt
      exact LowC_snoc_anc hI1.2.1 (by rw [hlenD]; omega) hrt
    · have hw : RawWk k b (u, W ++ U) := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u ≤ b := hw.1
      have hR0 : RawWsk k b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f A o + 1 := ⟨_, rfl⟩
      rw [← hr, farW_snoc]
      change GpT A o f b (farW b r ws ++ fwW b r u (W ++ U))
      rw [fwW_append b r u hW hH]
      have hlen' : 2 ≤ (mlift U u (b - u)).length := by rw [mlift_length]; exact hlen
      have hp' := (hasParent_mlift_iff u (b - u) hUne).mpr hp
      have hfpos : 0 < (fwW b r u W).length := by simp [fwW]
      refine (GpT_ax hA hA1 ho f).oper b _ (fwW b r u W ++ shiftr01 1 0 (mlift U u (b - u)))
        (Fr_farW _ _ _) (Fr_append (Fr_fwW _ _ _ _) (Fr_shift1 _))
        (fun _ => by rw [Small.entry_append_left hfpos]; exact Hd_fwW b r u W (by simp [fwW]))
        (by simp only [List.length_append, shiftr01_length]; omega) ?_ (fun m hm => ?_)
      · have hidx : (fwW b r u W ++ shiftr01 1 0 (mlift U u (b - u))).length - 1
            = (fwW b r u W).length + ((mlift U u (b - u)).length - 1) := by
          simp only [List.length_append, shiftr01_length]; omega
        rw [hidx, srow_append_right, srow_shiftr01]
        exact hasParent_append_right_of _ _ (hasParent_shiftr01.mpr hp')
      · rw [oper_shift (fwW b r u W) (mlift U u (b - u)) 1 m hlen' hp', mlift_oper',
          ← fwW_append b r u hW (Hd_oper hH hUne hm)]
        have hIm := hIH m hm
        have := hIm.2.2 b0 ws hC A o f b hb
          (RawWsk_snoc hR0 ⟨hub, Fr_append hW (Fr_oper hU m), hIm.1, hIm.2.1⟩) hA hA1 ho hAk hko
        rw [← hr, farW_snoc] at this
        exact this
  orph := by
    intro u W U h j hW hU hH hj1 hj hnp hz
    have hz0 := hz [] (Wg_nil _) based_nil
    have e0 : W ++ (U ++ shiftr01 h 0 []) = W ++ U := by simp [shiftr01]
    rw [e0] at hz0
    refine ⟨Hd_append_of hH hz0.1, ?_, fun b0 ws hC A o f b hb hR hA hA1 ho hAk hko => ?_⟩
    · rw [← List.append_assoc]; exact LowC_snoc hz0.2.1 _ (by show j ≤ u + k; omega)
    · have hw : RawWk k b (u, W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u ≤ b := hw.1
      have hR0 : RawWsk k b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
      have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u := hj
      obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f A o + 1 := ⟨_, rfl⟩
      rw [← hr, farW_snoc]
      change GpT A o f b (farW b r ws ++ fwW b r u (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])))
      obtain ⟨CW, hCW⟩ : ∃ CW, CW = mlift W u (b - u) := ⟨_, rfl⟩
      obtain ⟨CU, hCU⟩ : ∃ CU, CU = mlift U u (b - u) := ⟨_, rfl⟩
      have eL : fwW b r u (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
          = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: (CW ++ CU)))
            ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by
        unfold fwW
        rw [mlift_app hW hH, mlift_snoc_low U _ hc, ← hCW, ← hCU]
        simp [shiftr01]
      rw [eL]
      have hFrA : Fr (((1, r, 1) : ℕ × ℕ × ℕ) :: CW) := Fr_FLW (by rw [hCW]; exact Fr_mlift hW _ _)
      refine (GpT_ax hA hA1 ho f).orph b _ _ (h + 1) j (Fr_farW _ _ _)
        (by rw [← eL]; exact Fr_fwW _ _ _ _) (by rw [← eL]; exact Hd_fwW _ _ _ _)
        hj1 (by omega) ?_ (fun z hz' hbz => ?_)
      · have eAB : (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: (CW ++ CU)))
              ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]
            = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: CW)) ++
              shiftr01 1 0 (CU ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
          simp [shiftr01]
        have eidx : (((1, r, 1) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: (CW ++ CU))).length
            = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: CW)).length +
              CU.length := by simp [shiftr01]; omega
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
        have hFrz : Fr (U ++ shiftr01 h 0 z) := by
          have hh1 : 1 ≤ h := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
          refine Fr_append hUc (fun y hy => ?_)
          simp only [shiftr01, List.mem_map] at hy
          obtain ⟨p, -, rfl⟩ := hy
          dsimp only; omega
        have hzz := hz z hz' hbz
        have := hzz.2.2 b0 ws hC A o f b hb
          (RawWsk_snoc hR0 ⟨hub, Fr_append hW hFrz, hzz.1, hzz.2.1⟩) hA hA1 ho hAk hko
        rw [← hr, farW_snoc] at this
        change GpT A o f b (farW b r ws ++ fwW b r u (W ++ (U ++ shiftr01 h 0 z))) at this
        have ez : fwW b r u (W ++ (U ++ shiftr01 h 0 z))
            = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: (CW ++ CU)))
              ++ shiftr01 (h + 1) 0 z := by
          unfold fwW
          rw [mlift_app hW hHz, mlift_append_low (low_of_Wg hzW h (by omega)), ← hCW, ← hCU]
          simp [shiftr01, Function.comp_def, Nat.add_assoc]
        rw [ez] at this
        exact this
  tie := by
    intro u W U x hW hU hH hc hload
    have h0 := hload u le_rfl [] (Wg_nil _) based_nil
    have e0 : mlift (W ++ U) u (u - u) ++ shiftr01 x 0 [] = W ++ U := by
      simp [shiftr01, mlift_zero]
    rw [e0] at h0
    refine ⟨Hd_append_of hH h0.1, ?_, fun b0 ws hC A o f b hb hR hA hA1 ho hAk hko => ?_⟩
    · rw [← List.append_assoc]; exact LowC_snoc h0.2.1 _ (by show u + 1 ≤ u + k; omega)
    · have hw : RawWk k b (u, W ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u ≤ b := hw.1
      have hR0 : RawWsk k b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
      have hHU : Hd U := by
        intro hne
        have := hH (by simp)
        rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
      have hko' : o ≤ liftOff f A o := by unfold liftOff; omega
      obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f A o + 1 := ⟨_, rfl⟩
      rw [← hr, farW_snoc]
      change GpT A o f b (farW b r ws ++ fwW b r u (W ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])))
      obtain ⟨CW, hCW⟩ : ∃ CW, CW = mlift W u (b - u) := ⟨_, rfl⟩
      obtain ⟨CU, hCU⟩ : ∃ CU, CU = mlift U u (b - u) := ⟨_, rfl⟩
      have hlift : mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b - u)
          = CU ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)] := by
        rw [mlift_snoc_cone U _ hc, ← hCU]
        show CU ++ [((x, u + 1 + (b - u), 0) : ℕ × ℕ × ℕ)] = _
        rw [show u + 1 + (b - u) = b + 1 by omega]
      have eL : fwW b r u (W ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]))
          = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: (CW ++ CU)))
            ++ [((x + 1, b + 1, 0) : ℕ × ℕ × ℕ)] := by
        unfold fwW
        rw [mlift_app hW hH, hlift, ← hCW]
        simp [shiftr01]
      rw [eL]
      refine (GpT_ax hA hA1 ho f).tie b _ _ (x + 1) (Fr_farW _ _ _)
        (by rw [← eL]; exact Fr_fwW _ _ _ _) (by rw [← eL]; exact Hd_fwW _ _ _ _) ?_
        (fun b'' hb'' Z hZ hbZ => ?_)
      · have eAB : (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: (CW ++ CU)))
              ++ [((x + 1, b + 1, 0) : ℕ × ℕ × ℕ)]
            = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: CW)) ++
              shiftr01 1 0 (CU ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) := by
          simp [shiftr01]
        have eidx : (((1, r, 1) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: (CW ++ CU))).length
            = (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: CW)).length +
              CU.length := by simp [shiftr01]; omega
        rw [eAB, eidx]
        have hFrCW : Fr CW := by rw [hCW]; exact Fr_mlift hW _ _
        have hPCA : PathCone b 1 (((1, r, 1) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: CW)) := by
          intro y hy _ hd
          rcases y with _ | y
          · show b < r; omega
          · exfalso
            rw [entry_cons] at hd
            have hy' : y < (((1, r, 1) : ℕ × ℕ × ℕ) :: CW).length := by
              simp [shiftr01] at hy ⊢; omega
            rw [entry0_shiftr01 hy'] at hd
            have := getD_row0_ge (Fr_FLW hFrCW) hy'
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
        have hx1 : 1 ≤ x := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
        have hFrZ : Fr (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z) := by
          refine Fr_append (Fr_mlift hFrWU _ _) (fun y hy => ?_)
          simp only [shiftr01, List.mem_map] at hy
          obtain ⟨p, -, rfl⟩ := hy
          dsimp only; omega
        have hL := hload b'' (by omega) Z hZ hbZ
        have := hL.2.2 b0 ws hC A o f b'' (by omega)
          (RawWsk_snoc (RawWsk_mono hb'' hR0) ⟨le_rfl, hFrZ, hL.1, hL.2.1⟩) hA hA1 ho hAk hko
        rw [farW_snoc] at this
        change GpT A o f b'' (farW b'' (b'' + liftOff f A o + 1) ws ++
          fwW b'' (b'' + liftOff f A o + 1) b'' (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z)) at this
        have eP : mlift (farW b r ws ++ (((1, r, 1) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: (CW ++ CU)))) b (b'' - b) ++ shiftr01 (x + 1) 0 Z
            = farW b'' (b'' + liftOff f A o + 1) ws ++
              fwW b'' (b'' + liftOff f A o + 1) b'' (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z) := by
          have hCWU : CW ++ CU = mlift (W ++ U) u (b - u) := by rw [hCW, hCU, mlift_app hW hHU]
          have hHWU : Hd (W ++ U) := h0.1
          rw [mlift_app (Fr_farW _ _ _) (Hd_letter _ _), mlift_farW_basek (by omega) _ ws hR0,
            mlift_letter (by omega) (Fr_FLW (by rw [hCWU]; exact Fr_mlift hFrWU _ _)),
            hCWU]
          have eFL := mlift_app (W := [((1, r, 1) : ℕ × ℕ × ℕ)]) (U := mlift (W ++ U) u (b - u))
            (Fr_single le_rfl _ _) (Hd_mlift hHWU u (b - u)) b (b'' - b)
          simp only [List.singleton_append] at eFL
          rw [eFL, mlift_one (by omega)]
          have e2 := mlift_mlift (W ++ U) u (b - u) (b'' - b)
          rw [show u + (b - u) = b by omega, show b - u + (b'' - b) = b'' - u by omega] at e2
          rw [e2, show b + (b'' - b) = b'' by omega,
            show r + (b'' - b) = b'' + liftOff f A o + 1 by omega]
          unfold fwW
          rw [Nat.sub_self, mlift_zero]
          simp [shiftr01, Function.comp_def, Nat.add_assoc, List.append_assoc]
        rw [eP]
        exact this
  flat := by
    intro u W hW h
    refine ⟨Hd_append_of (V' := []) (fun _ => rfl) (by simpa using h.1), ?_,
      fun b0 ws hC A o f b hb hR hA hA1 ho hAk hko => ?_⟩
    · exact LowC_snoc h.2.1 _ (by show 0 ≤ u + k; omega)
    · have hw : RawWk k b (u, W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u ≤ b := hw.1
      have hR0 : RawWsk k b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f A o + 1 := ⟨_, rfl⟩
      rw [← hr, farW_snoc]
      change GpT A o f b (farW b r ws ++ fwW b r u (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]))
      have eZ : fwW b r u (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) = fwW b r u W ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
        rw [fwW_append b r u hW (fun _ => rfl)]
        have := mlift_snoc_low ([] : TrioSeq) ((1, 0, 0) : ℕ × ℕ × ℕ)
          (show ((1, 0, 0) : ℕ × ℕ × ℕ).2.1 ≤ u by show 0 ≤ u; omega) (b - u)
        simp only [List.nil_append, mlift_nil] at this
        rw [this]
        simp [shiftr01]
      rw [eZ]
      obtain ⟨M, hM⟩ : ∃ M, M = fwW b r u W := ⟨_, rfl⟩
      rw [← hM]
      have hMne : M ≠ [] := by rw [hM]; simp [fwW]
      have hMpos : 0 < M.length := List.length_pos_iff.mpr hMne
      have hhead : entry M 0 0 < 2 := by rw [hM]; show 1 < 2; omega
      have htail : ∀ r', 1 ≤ r' → r' < M.length → 2 ≤ entry M 0 r' := by
        intro r' hr1 hr2
        obtain ⟨w, rfl⟩ : ∃ w, r' = w + 1 := ⟨r' - 1, by omega⟩
        have hw' : w < (((1, r, 1) : ℕ × ℕ × ℕ) :: mlift W u (b - u)).length := by
          rw [hM] at hr2; simp only [fwW, List.length_cons, shiftr01_length] at hr2 ⊢; omega
        rw [hM, fwW, entry_cons, entry0_shiftr01 hw']
        have := getD_row0_ge (Fr_FLW (Fr_mlift hW u (b - u))) hw'
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
      refine (GpT_ax hA hA1 ho f).oper b _ (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) (Fr_farW _ _ _)
        (Fr_append (by rw [hM]; exact Fr_fwW _ _ _ _) (Fr_single (by omega) _ _))
        (fun _ => by rw [Small.entry_append_left hMpos, hM]; rfl)
        (by simp; omega) hlast (fun m hm => ?_)
      have eO := oper_snoc00'' [] hMne hhead htail m
      simp only [List.nil_append] at eO
      rw [eO, hM]
      have hrep := farW_rep b r ws (u, W) m
      have hRm : RawWsk k b (ws ++ List.replicate m (u, W)) := by
        intro w' h'
        rcases List.mem_append.mp h' with h' | h'
        · exact hR0 w' h'
        · rw [List.eq_of_mem_replicate h']; exact ⟨hub, hW, h.1, h.2.1⟩
      have := GTWk_rep (h.2.2 b0) hC m A o f b hb hRm hA hA1 ho hAk hko
      rw [← hr, hrep] at this
      exact this

/-! ## 規則 -/

theorem okWk_nil (k u : ℕ) : okWk k u [] :=
  ⟨fun h => absurd rfl h, LowC_nil _, fun b0 => GTWk_nil k b0 u⟩

theorem FarCWk_of (k b0 : ℕ) :
    ∀ ws : List (ℕ × TrioSeq), (∀ w ∈ ws, okWk k w.1 w.2) → FarCWk k b0 ws := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil => intro _; exact FarCWk_nil k b0
  | append_singleton ws w ih =>
      intro hok
      have hw := hok w (List.mem_append_right _ (List.mem_singleton_self _))
      exact hw.2.2 b0 ws (ih (fun w' h' => hok w' (List.mem_append_left _ h')))

def okWkF (k u : ℕ) (X : TrioSeq) : Prop := Fr X ∧ okWk k u X

theorem okWkF_nil (k u : ℕ) : okWkF k u [] := ⟨Fr_nil, okWk_nil k u⟩

theorem okWkF_load {k u : ℕ} (hk1 : 1 ≤ k) {X : TrioSeq} (h : okWkF k u X) {Z : TrioSeq}
    (hZ : Z ∈ Wg (2 * u)) (hb : based Z) : okWkF k u (X ++ shiftr01 1 0 Z) :=
  ⟨Fr_append h.1 (Fr_shift1 Z), slot_load (okWk_ax hk1) h.1 h.2 Z hZ hb⟩

theorem okWkF_lift {k u u' : ℕ} (hk1 : 1 ≤ k) (hu : u ≤ u') {X : TrioSeq} (h : okWkF k u X) :
    okWkF k u' (mlift X u (u' - u)) :=
  ⟨Fr_mlift h.1 _ _, (okWk_ax hk1).lift u X h.1 h.2 u' hu⟩

def OkWsk (k b : ℕ) (ws : List (ℕ × TrioSeq)) : Prop := RawWsk k b ws ∧ ∀ w ∈ ws, okWk k w.1 w.2

theorem OkWsk_nil (k b : ℕ) : OkWsk k b [] := ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

theorem OkWsk_cons {k b u : ℕ} (hub : u ≤ b) {X : TrioSeq} (h : okWkF k u X)
    {ws : List (ℕ × TrioSeq)} (hs : OkWsk k b ws) : OkWsk k b ((u, X) :: ws) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨hub, h.1, h.2.1, h.2.2.1⟩
    · exact hs.1 w hw
  · rcases List.mem_cons.mp hw with rfl | hw
    · exact h.2
    · exact hs.2 w hw

theorem OkWsk_snoc {k b u : ℕ} (hub : u ≤ b) {X : TrioSeq} (h : okWkF k u X)
    {ws : List (ℕ × TrioSeq)} (hs : OkWsk k b ws) : OkWsk k b (ws ++ [(u, X)]) := by
  refine ⟨RawWsk_snoc hs.1 ⟨hub, h.1, h.2.1, h.2.2.1⟩, fun w hw => ?_⟩
  rcases List.mem_append.mp hw with hw | hw
  · exact hs.2 w hw
  · simp at hw; subst hw; exact h.2

theorem OkWsk_mono {k b b' : ℕ} (h : b ≤ b') {ws : List (ℕ × TrioSeq)} (hs : OkWsk k b ws) :
    OkWsk k b' ws :=
  ⟨RawWsk_mono h hs.1, hs.2⟩

theorem GpT_farWsk {k : ℕ} {A : List ℕ} {o b : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (hAk : ∀ a ∈ A, k ≤ a) (hko : k ≤ o) {ws : List (ℕ × TrioSeq)} (hs : OkWsk k b ws)
    (f : ℕ → ℕ) : GpT A o f b (farW b (b + liftOff f A o + 1) ws) :=
  FarCWk_of k b ws hs.2 A o f b le_rfl hs.1 hA hA1 ho hAk hko

/-- ★ 遠い字のあとが okWk の列の遠い語の並びは、節点の子の並び（語の述語）。 -/
theorem PVF_farWsk {k : ℕ} {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (hAk : ∀ a ∈ A, k ≤ a) (hko : k ≤ o) (b : ℕ) (ws : List (ℕ × TrioSeq))
    (hs : OkWsk k b ws) : PVF A o b (farW b (b + o + 1) ws) := by
  have := farWk_PVP (FarCWk_of k b ws hs.2) hA hA1 ho hAk hko (fun _ => 0) b le_rfl hs.1
  rw [liftOff_zeroF] at this
  exact ⟨this, Fr_farW _ _ ws⟩

end GzV
end TRIO
