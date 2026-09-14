/-
GzN.lean: 低い列の遠い語の続きの族 okW（差し込み口の公理を満たす）と、荷・子つきのタイを足す規則（追記539）。

    GTW b0 w  := ∀ ws, FarCW b0 ws → FarCW b0 (ws ++ [w])
    okW u X   := Hd X ∧ LowC (u+1) X ∧ ∀ b0, GTW b0 (u, X)

okW は SlotAx を満たす（okW_ax）。flat は同じ語の繰り返し（GTW_rep）、oper / orph / tie は GpT_ax の深さ 2 の場合。
よって荷は slot_load、子つきのタイは GTs の nslot で足せる。
-/
import GzM

namespace TRIO
namespace GzN

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzM

def GTW (b0 : ℕ) (w : ℕ × TrioSeq) : Prop := ∀ ws, FarCW b0 ws → FarCW b0 (ws ++ [w])

def okW (u : ℕ) (X : TrioSeq) : Prop := Hd X ∧ LowC (u + 1) X ∧ ∀ b0, GTW b0 (u, X)

theorem GTW_nil (b0 c0 : ℕ) : GTW b0 (c0, []) := fun _ hC => farW_collapse hC

theorem GTW_rep {b0 : ℕ} {w : ℕ × TrioSeq} (h : GTW b0 w) {ws : List (ℕ × TrioSeq)}
    (hC : FarCW b0 ws) : ∀ m, FarCW b0 (ws ++ List.replicate m w)
  | 0 => by simpa using hC
  | m + 1 => by
      have := h _ (GTW_rep h hC m)
      rwa [List.append_assoc, ← List.replicate_succ'] at this

theorem farW_rep (b r : ℕ) (ws : List (ℕ × TrioSeq)) (w : ℕ × TrioSeq) :
    ∀ m, farW b r (ws ++ List.replicate m w)
      = farW b r ws ++ (List.range m).flatMap (fun _ => fwW b r w.1 w.2)
  | 0 => by simp [farW]
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, farW_snoc, farW_rep b r ws w m,
        List.range_succ, List.flatMap_append, List.append_assoc]
      simp

/-! ## 低い列と先頭の補題 -/

theorem LowC_nil (v : ℕ) : LowC v [] := fun i hi => by simp at hi

theorem LowC_snoc_anc {v : ℕ} {D : TrioSeq} {c : ℕ × ℕ × ℕ} (h : LowC v D) {q : ℕ} (hq : q < D.length)
    (hr : Relation.ReflTransGen (nextrel0 (D ++ [c])) q D.length) : LowC v (D ++ [c]) := by
  have key : ∀ j, j < D.length → ∃ k, Relation.ReflTransGen (nextrel0 (D ++ [c])) k j ∧
      entry (D ++ [c]) 1 k ≤ v := by
    intro j hj
    obtain ⟨k, hk, hle⟩ := h j hj
    have hkD : k < D.length := lt_of_le_of_lt (rtg0_le hk) hj
    exact ⟨k, rtg0_append_left hk hj, by rw [Small.entry_append_left hkD]; exact hle⟩
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i D.length with hiD | hiD
  · exact key i hiD
  · have hi' : i = D.length := by omega
    subst hi'
    obtain ⟨k, hk, hle⟩ := key q hq
    exact ⟨k, hk.trans hr, hle⟩

theorem LowC_snoc {v : ℕ} {D : TrioSeq} (h : LowC v D) (c : ℕ × ℕ × ℕ) (hc : c.2.1 ≤ v) :
    LowC v (D ++ [c]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i D.length with hiD | hiD
  · obtain ⟨k, hk, hle⟩ := h i hiD
    have hkD : k < D.length := lt_of_le_of_lt (rtg0_le hk) hiD
    exact ⟨k, rtg0_append_left hk hiD, by rw [Small.entry_append_left hkD]; exact hle⟩
  · have hi' : i = D.length := by omega
    subst hi'
    refine ⟨D.length, .refl, ?_⟩
    rw [show D.length = D.length + 0 from rfl, entry_append_right]
    exact hc

theorem Hd_append_of {W V V' : TrioSeq} (hV : Hd V) (hV' : Hd (W ++ V')) : Hd (W ++ V) := by
  intro hne
  by_cases hWn : W = []
  · subst hWn
    simp only [List.nil_append] at hne ⊢
    exact hV hne
  · have hpos : 0 < W.length := List.length_pos_iff.mpr hWn
    have h1 := hV' (by simp [hWn])
    rw [Small.entry_append_left hpos] at h1 ⊢
    exact h1

theorem fwW_append (b r c : ℕ) {W U : TrioSeq} (hW : Fr W) (hU : Hd U) :
    fwW b r c (W ++ U) = fwW b r c W ++ shiftr01 1 0 (mlift U c (b - c)) := by
  unfold fwW
  rw [mlift_app hW hU]
  simp [shiftr01]

theorem RawWs_snoc {b : ℕ} {ws : List (ℕ × TrioSeq)} {w : ℕ × TrioSeq} (h : RawWs b ws)
    (hw : RawW b w) : RawWs b (ws ++ [w]) := by
  intro w' h'
  rcases List.mem_append.mp h' with h' | h'
  · exact h w' h'
  · simp at h'; subst h'; exact hw

theorem rtg0_of_nextR' {M : TrioSeq} {i a b : ℕ} (h : nextR M i a b) :
    Relation.ReflTransGen (nextrel0 M) a b := by
  unfold nextR at h
  split at h
  · exact Relation.ReflTransGen.single h
  · split at h
    · exact h.2.2.2.2.1.2.2
    · exact rtg1_to_rtg0 h.2.2.2.2.1.2.2

/-! ## 差し込み口の公理 -/

theorem okW_ax : SlotAx okW where
  lift := by
    intro u W hW h u' hu
    refine ⟨Hd_mlift h.1 u (u' - u), ?_, fun b0 ws hC A o f b hb hR hA hA1 ho => ?_⟩
    · have := LowC_mlift h.2.1 (u' - u)
      rwa [show u + 1 + (u' - u) = u' + 1 by omega] at this
    · have hw : RawW b (u', mlift W u (u' - u)) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u' ≤ b := hw.1
      have hR0 : RawWs b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      have := h.2.2 b0 ws hC A o f b hb (RawWs_snoc hR0 ⟨by omega, hW, h.1, h.2.1⟩) hA hA1 ho
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
    refine ⟨Hd_append_of hH hI1.1, ?_, fun b0 ws hC A o f b hb hR hA hA1 ho => ?_⟩
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
    · have hw : RawW b (u, W ++ U) := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u ≤ b := hw.1
      have hR0 : RawWs b ws := fun w' h' => hR w' (List.mem_append_left _ h')
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
          (RawWs_snoc hR0 ⟨hub, Fr_append hW (Fr_oper hU m), hIm.1, hIm.2.1⟩) hA hA1 ho
        rw [← hr, farW_snoc] at this
        exact this
  orph := by
    intro u W U h j hW hU hH hj1 hj hnp hz
    have hz0 := hz [] (Wg_nil _) based_nil
    have e0 : W ++ (U ++ shiftr01 h 0 []) = W ++ U := by simp [shiftr01]
    rw [e0] at hz0
    refine ⟨Hd_append_of hH hz0.1, ?_, fun b0 ws hC A o f b hb hR hA hA1 ho => ?_⟩
    · rw [← List.append_assoc]; exact LowC_snoc hz0.2.1 _ (by show j ≤ u + 1; omega)
    · have hw : RawW b (u, W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u ≤ b := hw.1
      have hR0 : RawWs b ws := fun w' h' => hR w' (List.mem_append_left _ h')
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
          (RawWs_snoc hR0 ⟨hub, Fr_append hW hFrz, hzz.1, hzz.2.1⟩) hA hA1 ho
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
    refine ⟨Hd_append_of hH h0.1, ?_, fun b0 ws hC A o f b hb hR hA hA1 ho => ?_⟩
    · rw [← List.append_assoc]; exact LowC_snoc h0.2.1 _ (by show u + 1 ≤ u + 1; omega)
    · have hw : RawW b (u, W ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u ≤ b := hw.1
      have hR0 : RawWs b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
      have hHU : Hd U := by
        intro hne
        have := hH (by simp)
        rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
      have hk : o ≤ liftOff f A o := by unfold liftOff; omega
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
          (RawWs_snoc (RawWs_mono hb'' hR0) ⟨le_rfl, hFrZ, hL.1, hL.2.1⟩) hA hA1 ho
        rw [farW_snoc] at this
        change GpT A o f b'' (farW b'' (b'' + liftOff f A o + 1) ws ++
          fwW b'' (b'' + liftOff f A o + 1) b'' (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z)) at this
        have eP : mlift (farW b r ws ++ (((1, r, 1) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: (CW ++ CU)))) b (b'' - b) ++ shiftr01 (x + 1) 0 Z
            = farW b'' (b'' + liftOff f A o + 1) ws ++
              fwW b'' (b'' + liftOff f A o + 1) b'' (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z) := by
          have hCWU : CW ++ CU = mlift (W ++ U) u (b - u) := by rw [hCW, hCU, mlift_app hW hHU]
          have hHWU : Hd (W ++ U) := h0.1
          rw [mlift_app (Fr_farW _ _ _) (Hd_letter _ _), mlift_farW_base (by omega) _ ws hR0,
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
      fun b0 ws hC A o f b hb hR hA hA1 ho => ?_⟩
    · exact LowC_snoc h.2.1 _ (by show 0 ≤ u + 1; omega)
    · have hw : RawW b (u, W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u ≤ b := hw.1
      have hR0 : RawWs b ws := fun w' h' => hR w' (List.mem_append_left _ h')
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
      have hRm : RawWs b (ws ++ List.replicate m (u, W)) := by
        intro w' h'
        rcases List.mem_append.mp h' with h' | h'
        · exact hR0 w' h'
        · rw [List.eq_of_mem_replicate h']; exact ⟨hub, hW, h.1, h.2.1⟩
      have := GTW_rep (h.2.2 b0) hC m A o f b hb hRm hA hA1 ho
      rw [← hr, hrep] at this
      exact this

/-! ## 規則 -/

theorem okW_nil (u : ℕ) : okW u [] :=
  ⟨fun h => absurd rfl h, LowC_nil _, fun b0 => GTW_nil b0 u⟩

theorem okW_load {u : ℕ} {X : TrioSeq} (hX : Fr X) (h : okW u X) {Z : TrioSeq}
    (hZ : Z ∈ Wg (2 * u)) (hb : based Z) : okW u (X ++ shiftr01 1 0 Z) :=
  slot_load okW_ax hX h Z hZ hb

/-- ★ 子つきのタイ（子の並び D は段 c のタイの子の級）を足す。 -/
theorem okW_tieD {u c : ℕ} (hcu : c ≤ u) {X D : TrioSeq} (hX : Fr X) (h : okW u X) (hD : GTs c D) :
    okW u (X ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift D c (u - c))) :=
  hD okW okW_ax u hcu X hX h

theorem FarCW_of (b0 : ℕ) : ∀ ws : List (ℕ × TrioSeq), (∀ w ∈ ws, okW w.1 w.2) → FarCW b0 ws := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil => intro _; exact FarCW_nil b0
  | append_singleton ws w ih =>
      intro hok
      have hw := hok w (List.mem_append_right _ (List.mem_singleton_self _))
      exact hw.2.2 b0 ws (ih (fun w' h' => hok w' (List.mem_append_left _ h')))

theorem PVF_farW {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (b : ℕ) (ws : List (ℕ × TrioSeq)) (hR : RawWs b ws) (hok : ∀ w ∈ ws, okW w.1 w.2) :
    PVF A o b (farW b (b + o + 1) ws) := by
  have := farW_PVP (FarCW_of b ws hok) hA hA1 ho (fun _ => 0) b le_rfl hR
  rw [liftOff_zeroF] at this
  exact ⟨this, Fr_farW _ _ ws⟩

/-! ## 生成器の部品 -/

def okWF (u : ℕ) (X : TrioSeq) : Prop := Fr X ∧ okW u X

theorem okWF_nil (u : ℕ) : okWF u [] := ⟨Fr_nil, okW_nil u⟩

theorem okWF_load {u : ℕ} {X : TrioSeq} (h : okWF u X) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * u))
    (hb : based Z) : okWF u (X ++ shiftr01 1 0 Z) :=
  ⟨Fr_append h.1 (Fr_shift1 Z), okW_load h.1 h.2 hZ hb⟩

theorem okWF_tie {u : ℕ} {X : TrioSeq} (h : okWF u X) {D : TrioSeq} (hD : GF 1 u D) :
    okWF u (X ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) := by
  have := okW_tieD le_rfl h.1 h.2 ((Gof_one_iff u D).mp hD.1)
  rw [Nat.sub_self, mlift_zero] at this
  exact ⟨Fr_append h.1 (Fr_node _ _), this⟩

def OkWs (b : ℕ) (ws : List (ℕ × TrioSeq)) : Prop := RawWs b ws ∧ ∀ w ∈ ws, okW w.1 w.2

theorem OkWs_nil (b : ℕ) : OkWs b [] := ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

theorem OkWs_cons {b u : ℕ} (hub : u ≤ b) {X : TrioSeq} (h : okWF u X) {ws : List (ℕ × TrioSeq)}
    (hs : OkWs b ws) : OkWs b ((u, X) :: ws) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨hub, h.1, h.2.1, h.2.2.1⟩
    · exact hs.1 w hw
  · rcases List.mem_cons.mp hw with rfl | hw
    · exact h.2
    · exact hs.2 w hw

/-- ★ 遠い字のあとが荷と子つきのタイの遠い語の並びは、節点の子の並び。 -/
theorem PVF_farWs {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (b : ℕ) (ws : List (ℕ × TrioSeq)) (h : OkWs b ws) : PVF A o b (farW b (b + o + 1) ws) :=
  PVF_farW hA hA1 ho b ws h.1 h.2

end GzN
end TRIO
