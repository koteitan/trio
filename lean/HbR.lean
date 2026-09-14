/-
HbR.lean: F のタイごとに荷の子を持つ遠い語の族の第 2 部: 最後の語の中身の族 okWA0 と差し込み口の公理（HbG の写し）。

    GTWA0 A0 k0 H b0 Lds u X := ∀ ws, FarCA0 A0 k0 H b0 ws → FarCA0 A0 k0 H b0 (ws ++ [(Lds, u, X)])
    okWA0 A0 k0 H Lds u X    := Hd X ∧ LowC (u + reOff (fun _ => 0) H A0 k0) X ∧ ∀ b0, GTWA0 A0 k0 H b0 Lds u X

F のタイの子 Lds は固定（級の段で低いので持ち上げで動かない）。段の補題は HbM.fwH_*_step（頭 FTL0 r Lds）。
-/
import HbQ

namespace TRIO
namespace HbR

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HbD HbM HbP HbQ

def GTWA0 (A0 : List ℕ) (k0 : ℕ) (H : ℕ → ℕ) (b0 : ℕ) (Lds : List TrioSeq) (u : ℕ) (X : TrioSeq) :
    Prop :=
  ∀ ws, FarCA0 A0 k0 H b0 ws → FarCA0 A0 k0 H b0 (ws ++ [(Lds, u, X)])

def okWA0 (A0 : List ℕ) (k0 : ℕ) (H : ℕ → ℕ) (Lds : List TrioSeq) (u : ℕ) (X : TrioSeq) : Prop :=
  Hd X ∧ LowC (u + reOff (fun _ => 0) H A0 k0) X ∧ ∀ b0, GTWA0 A0 k0 H b0 Lds u X

theorem GTWA0_nil0 (A0 : List ℕ) (k0 : ℕ) (H : ℕ → ℕ) (b0 c0 : ℕ) : GTWA0 A0 k0 H b0 [] c0 [] :=
  fun _ hC => farWA0_collapse hC

theorem GTWA0_rep {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b0 : ℕ} {Lds : List TrioSeq} {u : ℕ}
    {X : TrioSeq} (h : GTWA0 A0 k0 H b0 Lds u X) {ws : List (List TrioSeq × ℕ × TrioSeq)}
    (hC : FarCA0 A0 k0 H b0 ws) : ∀ m, FarCA0 A0 k0 H b0 (ws ++ List.replicate m (Lds, u, X))
  | 0 => by simpa using hC
  | m + 1 => by
      have := h _ (GTWA0_rep h hC m)
      rwa [List.append_assoc, ← List.replicate_succ'] at this

/-- ★ 最後の語の中身の族の差し込み口の公理。 -/
theorem okWA0_ax {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0) (H : ℕ → ℕ)
    (Lds : List TrioSeq) : SlotAx (okWA0 A0 k0 H Lds) where
  lift := by
    intro u W hW h u' hu
    refine ⟨Hd_mlift h.1 u (u' - u), ?_, fun b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
    · have := LowC_mliftk h.2.1 (u' - u)
      rwa [show u + reOff (fun _ => 0) H A0 k0 + (u' - u) = u' + reOff (fun _ => 0) H A0 k0 by omega]
        at this
    · have hw : RawWA0 A0 k0 H b (Lds, u', mlift W u (u' - u)) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub' : u' ≤ b := hw.1
      have hR0 : RawWsA0 A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      have := h.2.2 b0 ws hC g S o f b hf hb
        (RawWsA0_snoc hR0 ⟨show u ≤ b by omega, hw.2.1, hW, h.1, h.2.1⟩) hSA hA hA1 ho hK hKo
      simp only [relWs0_snoc, farW0_snoc] at this ⊢
      have e : reliftX u' H g A0 (mlift W u (u' - u)) = mlift (reliftX u H g A0 W) u (u' - u) := by
        rw [mlift_reliftX, show u + (u' - u) = u' by omega]
      rw [e, fwH_lift_eq _ _ _ hu hub']
      exact this
  oper := by
    intro u W U hW hU hH hlen hp hIH
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    have hI1 := hIH 1 le_rfl
    have hU1 : U⟦1⟧ = U.dropLast := oper_one_eq_dropLast (by omega)
    refine ⟨Hd_append_of hH hI1.1, ?_, fun b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
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
    · have hw : RawWA0 A0 k0 H b (Lds, u, W ++ U) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u ≤ b := hw.1
      have hR0 : RawWsA0 A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      simp only [relWs0_snoc, farW0_snoc]
      rw [reliftX_app hW hH]
      refine fwH_oper_step hA hA1 ho f (Fr_farW0 _ _ _) (Fr_reliftX hW _ _ _ _)
        (Fr_reliftX hU _ _ _ _) (Hd_reliftX hH _ _ _ _) (by rw [reliftX_length]; exact hlen) ?_
        (fun m hm => ?_)
      · unfold reliftX
        rw [slift_length, srow_slift (reStair_stair _ _ _ _) (by omega),
          hasParent_slift (reStair_stair _ _ _ _)]
        exact hp
      · have hIm := hIH m hm
        have := hIm.2.2 b0 ws hC g S o f b hf hb
          (RawWsA0_snoc hR0 ⟨hub, hw.2.1, Fr_append hW (Fr_oper hU m), hIm.1, hIm.2.1⟩) hSA hA hA1
          ho hK hKo
        simp only [relWs0_snoc, farW0_snoc] at this
        rw [reliftX_app hW (Hd_oper hH hUne hm)] at this
        unfold reliftX at this ⊢
        rwa [slift_oper (reStair_stair _ _ _ _)] at this
  orph := by
    intro u W U h j hW hU hH hj1 hj hnp hz
    have hz0 := hz [] (Wg_nil _) based_nil
    have e0 : W ++ (U ++ shiftr01 h 0 []) = W ++ U := by simp [shiftr01]
    rw [e0] at hz0
    refine ⟨Hd_append_of hH hz0.1, ?_, fun b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
    · rw [← List.append_assoc]
      exact LowC_snoc hz0.2.1 _ (by show j ≤ u + reOff (fun _ => 0) H A0 k0; omega)
    · have hw : RawWA0 A0 k0 H b (Lds, u, W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hR0 : RawWsA0 A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
      have hub : u ≤ b := hw.1
      have hfix : ∀ m, m ≤ j → reStair u H g A0 m = m := fun m hm => reStair_low u H g A0 (by omega)
      have eU : reliftX u H g A0 (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])
          = reliftX u H g A0 U ++ [((h, j, 0) : ℕ × ℕ × ℕ)] := by
        unfold reliftX; rw [slift_snoc_fix _ _ hfix]
      simp only [relWs0_snoc, farW0_snoc]
      rw [reliftX_app hW hH, eU]
      refine fwH_orph_step hA hA1 ho f hub (show b < b + liftOff f (S ++ A0) o + 1 by omega)
        (Fr_FTL0 _ _) (Fr_farW0 _ _ _) (Fr_reliftX hW _ _ _ _)
        (by rw [← eU]; exact Fr_reliftX hU _ _ _ _) (by rw [← eU]; exact Hd_reliftX hH _ _ _ _)
        hj1 hj ?_ (fun z hz' hbz => ?_)
      · intro hh
        apply hnp
        rw [reliftX_length, ← eU] at hh
        unfold reliftX at hh
        rwa [hasParent_slift (reStair_stair _ _ _ _)] at hh
      · have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
        have hHz : Hd (U ++ shiftr01 h 0 z) := Hd_append_shift hH hbz
        have hFrz : Fr (U ++ shiftr01 h 0 z) := by
          have hh1 : 1 ≤ h := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
          refine Fr_append hUc (fun y hy => ?_)
          simp only [shiftr01, List.mem_map] at hy
          obtain ⟨p, -, rfl⟩ := hy
          dsimp only; omega
        have hzz := hz z hz' hbz
        have := hzz.2.2 b0 ws hC g S o f b hf hb
          (RawWsA0_snoc hR0 ⟨hub, hw.2.1, Fr_append hW hFrz, hzz.1, hzz.2.1⟩) hSA hA hA1 ho hK hKo
        simp only [relWs0_snoc, farW0_snoc] at this
        rw [reliftX_app hW hHz] at this
        have e1 : reliftX u H g A0 (U ++ shiftr01 h 0 z) = reliftX u H g A0 U ++ shiftr01 h 0 z := by
          unfold reliftX
          exact slift_append_low (low_of_Wg hzW h (show j ≤ u by omega))
            (fun m hm => reStair_low u H g A0 hm)
        rw [e1] at this
        exact this
  tie := by
    intro u W U x hW hU hH hc hload
    have h0 := hload u le_rfl [] (Wg_nil _) based_nil
    have e0 : mlift (W ++ U) u (u - u) ++ shiftr01 x 0 [] = W ++ U := by
      simp [shiftr01, mlift_zero]
    rw [e0] at h0
    have hKge : k0 ≤ reOff (fun _ => 0) H A0 k0 := by unfold reOff; omega
    refine ⟨Hd_append_of hH h0.1, ?_, fun b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
    · rw [← List.append_assoc]
      exact LowC_snoc h0.2.1 _ (by show u + 1 ≤ u + reOff (fun _ => 0) H A0 k0; omega)
    · have hw : RawWA0 A0 k0 H b (Lds, u, W ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hR0 : RawWsA0 A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
      have hHU : Hd U := by
        intro hne
        have := hH (by simp)
        rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
      have hub : u ≤ b := hw.1
      have hLds : ∀ Ld ∈ Lds, Fr Ld ∧ LowC b Ld := hw.2.1
      have hfix : ∀ m, m ≤ u + 1 → reStair u H g A0 m = m := fun m hm => reStair_tie u H g hA01 hm
      have eU : reliftX u H g A0 (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])
          = reliftX u H g A0 U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)] := by
        unfold reliftX; rw [slift_snoc_fix _ _ hfix]
      simp only [relWs0_snoc, farW0_snoc]
      rw [reliftX_app hW hH, eU]
      refine fwH_tie_step hA hA1 ho f hub (Fr_FTL0 _ _) (Fr_farW0 _ _ _)
        (fun b'' => farW0 b'' (b'' + liftOff f (S ++ A0) o + 1) (relWs0 A0 H g ws))
        (fun b'' => FTL0 (b'' + liftOff f (S ++ A0) o + 1) Lds)
        (fun b'' hb'' => ?_) (fun b'' hb'' => ?_) (Fr_reliftX hW _ _ _ _)
        (by rw [← eU]; exact Fr_reliftX hU _ _ _ _) (by rw [← eU]; exact Hd_reliftX hH _ _ _ _) ?_
        (by rw [← reliftX_app hW hHU]; exact Hd_reliftX h0.1 _ _ _ _) (fun b'' hb'' Z hZ hbZ => ?_)
      · show mlift (farW0 b (b + liftOff f (S ++ A0) o + 1) (relWs0 A0 H g ws)) b (b'' - b)
          = farW0 b'' (b'' + liftOff f (S ++ A0) o + 1) (relWs0 A0 H g ws)
        rw [mlift_farW0_basek (show b < b + liftOff f (S ++ A0) o + 1 by omega) (b'' - b) _
            (RawWsk0_relWs0 hR0 g), show b + (b'' - b) = b'' by omega,
          show b + liftOff f (S ++ A0) o + 1 + (b'' - b) = b'' + liftOff f (S ++ A0) o + 1 by omega]
      · show mlift (FTL0 (b + liftOff f (S ++ A0) o + 1) Lds) b (b'' - b)
          = FTL0 (b'' + liftOff f (S ++ A0) o + 1) Lds
        rw [mlift_FTL0 (show b < b + liftOff f (S ++ A0) o + 1 by omega) (b'' - b) Lds hLds,
          show b + liftOff f (S ++ A0) o + 1 + (b'' - b) = b'' + liftOff f (S ++ A0) o + 1 by omega]
      · rw [reliftX_length, ← eU]
        unfold reliftX
        rw [coneV_iff_amin, amin_slift (reStair_stair _ _ _ _) (by simp)]
        rw [coneV_iff_amin] at hc
        have h1 := (reStair_stair u H g A0).ge (amin (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) U.length)
        omega
      · have hFrWU : Fr (W ++ U) := Fr_append hW hUc
        have hx1 : 1 ≤ x := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
        have hFrZ : Fr (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z) := by
          refine Fr_append (Fr_mlift hFrWU _ _) (fun y hy => ?_)
          simp only [shiftr01, List.mem_map] at hy
          obtain ⟨p, -, rfl⟩ := hy
          dsimp only; omega
        have hL := hload b'' (by omega) Z hZ hbZ
        have := hL.2.2 b0 ws hC g S o f b'' hf (by omega)
          (RawWsA0_snoc (RawWsA0_mono hb'' hR0)
            ⟨le_rfl, fun Ld hLd => ⟨(hLds Ld hLd).1, LowC_mono hb'' (hLds Ld hLd).2⟩, hFrZ, hL.1,
              hL.2.1⟩) hSA hA hA1 ho hK hKo
        simp only [relWs0_snoc, farW0_snoc] at this
        have e1a : reliftX b'' H g A0 (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z)
            = reliftX b'' H g A0 (mlift (W ++ U) u (b'' - u)) ++ shiftr01 x 0 Z := by
          unfold reliftX
          exact slift_append_low (low_of_Wg hZ x le_rfl) (fun m hm => reStair_low b'' H g A0 hm)
        have e1b : reliftX b'' H g A0 (mlift (W ++ U) u (b'' - u))
            = mlift (reliftX u H g A0 W ++ reliftX u H g A0 U) u (b'' - u) := by
          rw [← reliftX_app hW hHU, mlift_reliftX, show u + (b'' - u) = b'' by omega]
        rw [e1a, e1b] at this
        exact this
  flat := by
    intro u W hW h
    refine ⟨Hd_append_of (V' := []) (fun _ => rfl) (by simpa using h.1), ?_,
      fun b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
    · exact LowC_snoc h.2.1 _ (by show 0 ≤ u + reOff (fun _ => 0) H A0 k0; omega)
    · have hw : RawWA0 A0 k0 H b (Lds, u, W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) :=
        hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u ≤ b := hw.1
      have hR0 : RawWsA0 A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      have e : reliftX u H g A0 (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
          = reliftX u H g A0 W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
        unfold reliftX
        refine slift_snoc_fix _ _ (fun m hm => ?_)
        have hm0 : m = 0 := by simpa using hm
        subst hm0; exact (reStair_stair _ _ _ _).zero
      simp only [relWs0_snoc, farW0_snoc]
      rw [e]
      refine fwH_flat_step hA hA1 ho f (Fr_FTL0 _ _) (Fr_farW0 _ _ _) (Fr_reliftX hW _ _ _ _)
        (fun m => ?_)
      have hRm : RawWsA0 A0 k0 H b (ws ++ List.replicate m (Lds, u, W)) := by
        intro w' h'
        rcases List.mem_append.mp h' with h' | h'
        · exact hR0 w' h'
        · rw [List.eq_of_mem_replicate h']; exact ⟨hub, hw.2.1, hW, h.1, h.2.1⟩
      have := GTWA0_rep (h.2.2 b0) hC m g S o f b hf hb hRm hSA hA hA1 ho hK hKo
      rw [relWs0_rep, farW0_rep] at this
      exact this

end HbR
end TRIO
