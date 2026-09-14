/-
HcC.lean: 子を中身と同じ形にした遠い語の、最後の語の中身の族（HbR の写し）。

    GTWAc A0 k0 H b0 Lds u X := ∀ ws, FarCAc A0 k0 H b0 ws → FarCAc A0 k0 H b0 (ws ++ [(Lds, u, X)])
    GoodCh A0 k0 H u Lds := 子が低い ∧ ∀ b0, GTWAc A0 k0 H b0 Lds u []
    okWAc A0 k0 H u X := Hd X ∧ LowC (u + reOff 0 H A0 k0) X ∧
      ∀ u', u ≤ u' → ∀ Lds, GoodCh A0 k0 H u' Lds → ∀ b0, GTWAc A0 k0 H b0 Lds u' (mlift X u (u' − u))

中身は、全ての上の段 u' と、そこで良い全ての子の並びについて足せる（lift の場は定義から出る）。
-/
import HcB

namespace TRIO
namespace HcC

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HbD HbM HbP HcA HcB

def GTWAc (A0 : List ℕ) (k0 : ℕ) (H : ℕ → ℕ) (b0 : ℕ) (Lds : List TrioSeq) (u : ℕ) (X : TrioSeq) :
    Prop :=
  ∀ ws, FarCAc A0 k0 H b0 ws → FarCAc A0 k0 H b0 (ws ++ [(Lds, u, X)])

def GoodCh (A0 : List ℕ) (k0 : ℕ) (H : ℕ → ℕ) (u : ℕ) (Lds : List TrioSeq) : Prop :=
  (∀ D ∈ Lds, Fr D ∧ LowC (u + reOff (fun _ => 0) H A0 k0) D) ∧
    ∀ g b0, GTWAc A0 k0 (addF H g) b0 (Lds.map (reliftX u H g A0)) u []

def okWAc (A0 : List ℕ) (k0 : ℕ) (H : ℕ → ℕ) (u : ℕ) (X : TrioSeq) : Prop :=
  Hd X ∧ LowC (u + reOff (fun _ => 0) H A0 k0) X ∧
    ∀ u', u ≤ u' → ∀ Lds, GoodCh A0 k0 H u' Lds → ∀ b0, GTWAc A0 k0 H b0 Lds u' (mlift X u (u' - u))

theorem GTWAc_rep {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b0 : ℕ} {Lds : List TrioSeq} {u : ℕ}
    {X : TrioSeq} (h : GTWAc A0 k0 H b0 Lds u X) {ws : List (List TrioSeq × ℕ × TrioSeq)}
    (hC : FarCAc A0 k0 H b0 ws) : ∀ m, FarCAc A0 k0 H b0 (ws ++ List.replicate m (Lds, u, X))
  | 0 => by simpa using hC
  | m + 1 => by
      have := h _ (GTWAc_rep h hC m)
      rwa [List.append_assoc, ← List.replicate_succ'] at this

/-! ## 子の段の付け替え -/

theorem FTLc_rebase {b r c c' : ℕ} (hcc : c ≤ c') (hcb : c' ≤ b) :
    ∀ Lds : List TrioSeq, FTLc b r c' (Lds.map (fun D => mlift D c (c' - c))) = FTLc b r c Lds := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil => simp [FTLc]
  | append_singleton Lds D ih =>
      rw [List.map_append, List.map_singleton, FTLc_snoc, FTLc_snoc, ih]
      have e := mlift_mlift D c (c' - c) (b - c')
      rw [show c + (c' - c) = c' by omega, show c' - c + (b - c') = b - c by omega] at e
      rw [e]

theorem map_relift_mlift (A0 : List ℕ) (H g : ℕ → ℕ) {u u' : ℕ} (hu : u ≤ u') (Lds : List TrioSeq) :
    (Lds.map (fun D => mlift D u (u' - u))).map (reliftX u' H g A0)
      = (Lds.map (reliftX u H g A0)).map (fun D => mlift D u (u' - u)) := by
  simp only [List.map_map]
  refine List.map_congr_left (fun D _ => ?_)
  simp only [Function.comp_apply]
  rw [mlift_reliftX, show u + (u' - u) = u' by omega]

theorem GoodCh_lift {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {u : ℕ} {Lds : List TrioSeq}
    (hG : GoodCh A0 k0 H u Lds) {u' : ℕ} (hu : u ≤ u') :
    GoodCh A0 k0 H u' (Lds.map (fun D => mlift D u (u' - u))) := by
  refine ⟨fun D hD => ?_, fun g b0 ws hC g2 S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
  · simp only [List.mem_map] at hD
    obtain ⟨D0, hD0, rfl⟩ := hD
    refine ⟨Fr_mlift (hG.1 D0 hD0).1 _ _, ?_⟩
    have := LowC_mliftk (hG.1 D0 hD0).2 (u' - u)
    rwa [show u + reOff (fun _ => 0) H A0 k0 + (u' - u) = u' + reOff (fun _ => 0) H A0 k0 by omega]
      at this
  · have hw := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hub : u' ≤ b := hw.1
    have hR0 : RawWsAc A0 k0 (addF H g) b ws := fun w' h' => hR w' (List.mem_append_left _ h')
    have := hG.2 g b0 ws hC g2 S o f b hf hb
      (RawWsAc_snoc hR0 ⟨show u ≤ b by omega, RawLds_relift hG.1 g, Fr_nil, fun h => absurd rfl h,
        LowC_nil _⟩) hSA hA hA1 ho hK hKo
    have e0 : ∀ c (K G : ℕ → ℕ), reliftX c K G A0 ([] : TrioSeq) = [] := fun c K G => by
      unfold reliftX; exact slift_nil _
    simp only [relWsc_snoc, farWc_snoc] at this ⊢
    rw [e0] at this
    rw [e0, map_relift_mlift A0 H g hu, map_relift_mlift A0 (addF H g) g2 hu, FTLc_rebase hu hub]
    simpa [fwH, mlift_nil] using this

/-! ## 差し込み口の公理 -/

theorem LowC_lift_shift {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {u u' : ℕ} (hu : u ≤ u') {X : TrioSeq}
    (h : LowC (u + reOff (fun _ => 0) H A0 k0) X) :
    LowC (u' + reOff (fun _ => 0) H A0 k0) (mlift X u (u' - u)) := by
  have := LowC_mliftk h (u' - u)
  rwa [show u + reOff (fun _ => 0) H A0 k0 + (u' - u) = u' + reOff (fun _ => 0) H A0 k0 by omega]
    at this

/-- ★ 最後の語の中身の族の差し込み口の公理。 -/
theorem okWAc_ax {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0) (H : ℕ → ℕ) :
    SlotAx (okWAc A0 k0 H) where
  lift := by
    intro u W hW h u1 hu1
    refine ⟨Hd_mlift h.1 u (u1 - u), LowC_lift_shift hu1 h.2.1, fun u' hu' Lds hG b0 => ?_⟩
    have e := mlift_mlift W u (u1 - u) (u' - u1)
    rw [show u + (u1 - u) = u1 by omega, show u1 - u + (u' - u1) = u' - u by omega] at e
    rw [e]
    exact h.2.2 u' (le_trans hu1 hu') Lds hG b0
  oper := by
    intro u W U hW hU hH hlen hp hIH
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    have hI1 := hIH 1 le_rfl
    have hU1 : U⟦1⟧ = U.dropLast := oper_one_eq_dropLast (by omega)
    refine ⟨Hd_append_of hH hI1.1, ?_,
      fun u' hu' Lds hG b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
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
    · have hw := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u' ≤ b := hw.1
      have hR0 : RawWsAc A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      simp only [relWsc_snoc, farWc_snoc]
      rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _)]
      refine fwH_oper_step hA hA1 ho f (Fr_farWc _ _ _) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
        (Fr_reliftX (Fr_mlift hU _ _) _ _ _ _) (Hd_reliftX (Hd_mlift hH _ _) _ _ _ _)
        (by rw [reliftX_length, mlift_length]; exact hlen) ?_ (fun m hm => ?_)
      · unfold reliftX
        rw [slift_length, srow_slift (reStair_stair _ _ _ _) (by rw [mlift_length]; omega),
          hasParent_slift (reStair_stair _ _ _ _)]
        exact (hasParent_mlift_iff u (u' - u) hUne).mpr hp
      · have hIm := hIH m hm
        have hRm : RawWsAc A0 k0 H b (ws ++ [(Lds, u', mlift (W ++ U⟦m⟧) u (u' - u))]) :=
          RawWsAc_snoc hR0 ⟨hub, hw.2.1, Fr_mlift (Fr_append hW (Fr_oper hU m)) _ _,
            Hd_mlift hIm.1 _ _, LowC_lift_shift hu' hIm.2.1⟩
        have := hIm.2.2 u' hu' Lds hG b0 ws hC g S o f b hf hb hRm hSA hA hA1 ho hK hKo
        simp only [relWsc_snoc, farWc_snoc] at this
        rw [mlift_app hW (Hd_oper hH hUne hm),
          reliftX_app (Fr_mlift hW _ _) (Hd_mlift (Hd_oper hH hUne hm) _ _)] at this
        unfold reliftX at this ⊢
        rwa [← mlift_oper', slift_oper (reStair_stair _ _ _ _)] at this
  orph := by
    intro u W U h j hW hU hH hj1 hj hnp hz
    have hz0 := hz [] (Wg_nil _) based_nil
    have e0 : W ++ (U ++ shiftr01 h 0 []) = W ++ U := by simp [shiftr01]
    rw [e0] at hz0
    refine ⟨Hd_append_of hH hz0.1, ?_,
      fun u' hu' Lds hG b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
    · rw [← List.append_assoc]
      exact LowC_snoc hz0.2.1 _ (by show j ≤ u + reOff (fun _ => 0) H A0 k0; omega)
    · have hw := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u' ≤ b := hw.1
      have hR0 : RawWsAc A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
      have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u := hj
      have hfix : ∀ m, m ≤ j → reStair u' H g A0 m = m :=
        fun m hm => reStair_low u' H g A0 (by omega)
      have eU : reliftX u' H g A0 (mlift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) u (u' - u))
          = reliftX u' H g A0 (mlift U u (u' - u)) ++ [((h, j, 0) : ℕ × ℕ × ℕ)] := by
        unfold reliftX; rw [mlift_snoc_low U _ hc, slift_snoc_fix _ _ hfix]
      simp only [relWsc_snoc, farWc_snoc]
      rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), eU]
      refine fwH_orph_step hA hA1 ho f hub (show b < b + liftOff f (S ++ A0) o + 1 by omega)
        (Fr_FTLc _ _ _ _) (Fr_farWc _ _ _) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
        (by rw [← eU]; exact Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
        (by rw [← eU]; exact Hd_reliftX (Hd_mlift hH _ _) _ _ _ _)
        hj1 (by omega) ?_ (fun z hz' hbz => ?_)
      · intro hh
        apply hnp
        rw [← eU, reliftX_length, mlift_length] at hh
        unfold reliftX at hh
        rw [hasParent_slift (reStair_stair _ _ _ _), mlift_eq_slift,
          hasParent_slift (stair_step _ _)] at hh
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
        have hlowz := low_of_Wg hzW h (show j ≤ u by omega)
        have hRz : RawWsAc A0 k0 H b (ws ++ [(Lds, u', mlift (W ++ (U ++ shiftr01 h 0 z)) u (u' - u))]) :=
          RawWsAc_snoc hR0 ⟨hub, hw.2.1, Fr_mlift (Fr_append hW hFrz) _ _, Hd_mlift hzz.1 _ _,
            LowC_lift_shift hu' hzz.2.1⟩
        have := hzz.2.2 u' hu' Lds hG b0 ws hC g S o f b hf hb hRz hSA hA hA1 ho hK hKo
        simp only [relWsc_snoc, farWc_snoc] at this
        rw [mlift_app hW hHz, mlift_append_low hlowz] at this
        have hH2 : Hd (mlift U u (u' - u) ++ shiftr01 h 0 z) := by
          have := Hd_mlift hHz u (u' - u)
          rwa [mlift_append_low hlowz] at this
        rw [reliftX_app (Fr_mlift hW _ _) hH2] at this
        have e1 : reliftX u' H g A0 (mlift U u (u' - u) ++ shiftr01 h 0 z)
            = reliftX u' H g A0 (mlift U u (u' - u)) ++ shiftr01 h 0 z := by
          unfold reliftX
          exact slift_append_low (low_of_Wg hzW h (show j ≤ u' by omega))
            (fun m hm => reStair_low u' H g _ hm)
        rw [e1] at this
        exact this
  tie := by
    intro u W U x hW hU hH hc hload
    have h0 := hload u le_rfl [] (Wg_nil _) based_nil
    have e0 : mlift (W ++ U) u (u - u) ++ shiftr01 x 0 [] = W ++ U := by
      simp [shiftr01, mlift_zero]
    rw [e0] at h0
    have hKge : k0 ≤ reOff (fun _ => 0) H A0 k0 := by unfold reOff; omega
    refine ⟨Hd_append_of hH h0.1, ?_,
      fun u' hu' Lds hG b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
    · rw [← List.append_assoc]
      exact LowC_snoc h0.2.1 _ (by show u + 1 ≤ u + reOff (fun _ => 0) H A0 k0; omega)
    · have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
      have hHU : Hd U := by
        intro hne
        have := hH (by simp)
        rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
      have hw := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u' ≤ b := hw.1
      have hLds : ∀ D ∈ Lds, Fr D ∧ LowC (u' + reOff (fun _ => 0) H A0 k0) D := hG.1
      have hR0 : RawWsAc A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      have eT : mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (u' - u)
          = mlift U u (u' - u) ++ [((x, u' + 1, 0) : ℕ × ℕ × ℕ)] := by
        rw [mlift_snoc_cone U _ hc]
        show _ ++ [((x, u + 1 + (u' - u), 0) : ℕ × ℕ × ℕ)] = _
        rw [show u + 1 + (u' - u) = u' + 1 by omega]
      have hfix : ∀ m, m ≤ u' + 1 → reStair u' H g A0 m = m :=
        fun m hm => reStair_tie u' H g hA01 hm
      have eU : reliftX u' H g A0 (mlift U u (u' - u)) ++ [((x, u' + 1, 0) : ℕ × ℕ × ℕ)]
          = reliftX u' H g A0 (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (u' - u)) := by
        rw [eT]; unfold reliftX; rw [slift_snoc_fix _ _ hfix]
      simp only [relWsc_snoc, farWc_snoc]
      rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), ← eU]
      refine fwH_tie_step hA hA1 ho f hub (Fr_FTLc _ _ _ _) (Fr_farWc _ _ _)
        (fun b'' => farWc b'' (b'' + liftOff f (S ++ A0) o + 1) (relWsc A0 H g ws))
        (fun b'' => FTLc b'' (b'' + liftOff f (S ++ A0) o + 1) u' (Lds.map (reliftX u' H g A0)))
        (fun b'' hb'' => ?_) (fun b'' hb'' => ?_) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
        (by rw [eU]; exact Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
        (by rw [eU]; exact Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) ?_
        (by
          rw [← reliftX_app (Fr_mlift hW _ _) (Hd_mlift hHU _ _), ← mlift_app hW hHU]
          exact Hd_reliftX (Hd_mlift h0.1 _ _) _ _ _ _)
        (fun b'' hb'' Z hZ hbZ => ?_)
      · show mlift (farWc b (b + liftOff f (S ++ A0) o + 1) (relWsc A0 H g ws)) b (b'' - b)
          = farWc b'' (b'' + liftOff f (S ++ A0) o + 1) (relWsc A0 H g ws)
        rw [mlift_farWc_basek (show b < b + liftOff f (S ++ A0) o + 1 by omega) (b'' - b) _
            (RawWskc_relWsc hR0 g), show b + (b'' - b) = b'' by omega,
          show b + liftOff f (S ++ A0) o + 1 + (b'' - b) = b'' + liftOff f (S ++ A0) o + 1 by omega]
      · show mlift (FTLc b (b + liftOff f (S ++ A0) o + 1) u' (Lds.map (reliftX u' H g A0))) b (b'' - b)
          = FTLc b'' (b'' + liftOff f (S ++ A0) o + 1) u' (Lds.map (reliftX u' H g A0))
        rw [mlift_FTLc_base (show b < b + liftOff f (S ++ A0) o + 1 by omega) hub (b'' - b) _
            (fun D hD => (RawLds_relift hLds g D hD).1),
          show b + (b'' - b) = b'' by omega,
          show b + liftOff f (S ++ A0) o + 1 + (b'' - b) = b'' + liftOff f (S ++ A0) o + 1 by omega]
      · rw [eU, reliftX_length, mlift_length]
        unfold reliftX
        rw [coneV_iff_amin, amin_slift (reStair_stair _ _ _ _) (by simp)]
        have h0' : coneV (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (u' - u)) (u + (u' - u))
            U.length := coneV_mlift (by simp) hc (u' - u)
        rw [show u + (u' - u) = u' by omega, coneV_iff_amin] at h0'
        have h1 := (reStair_stair u' H g A0).ge
          (amin (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (u' - u)) U.length)
        omega
      · have hFrWU : Fr (W ++ U) := Fr_append hW hUc
        have hx1 : 1 ≤ x := hU _ (List.mem_append_right _ (List.mem_singleton_self _))
        have hL := hload b'' (by omega) Z hZ hbZ
        obtain ⟨Y, hY⟩ : ∃ Y, Y = mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z := ⟨_, rfl⟩
        rw [← hY] at hL
        have hGb : GoodCh A0 k0 H b'' (Lds.map (fun D => mlift D u' (b'' - u'))) :=
          GoodCh_lift hG (by omega)
        have hFrY : Fr Y := by
          rw [hY]
          refine Fr_append (Fr_mlift hFrWU _ _) (fun y hy => ?_)
          simp only [shiftr01, List.mem_map] at hy
          obtain ⟨p, -, rfl⟩ := hy
          dsimp only; omega
        have hRb : RawWsAc A0 k0 H b''
            (ws ++ [(Lds.map (fun D => mlift D u' (b'' - u')), b'', mlift Y b'' (b'' - b''))]) := by
          rw [Nat.sub_self, mlift_zero]
          exact RawWsAc_snoc (RawWsAc_mono hb'' hR0) ⟨le_rfl, hGb.1, hFrY, hL.1, hL.2.1⟩
        have := hL.2.2 b'' le_rfl _ hGb b0 ws hC g S o f b'' hf (by omega) hRb hSA hA hA1 ho hK hKo
        simp only [relWsc_snoc, farWc_snoc] at this
        rw [Nat.sub_self, mlift_zero] at this
        have eH2 : FTLc b'' (b'' + liftOff f (S ++ A0) o + 1) b''
            ((Lds.map (fun D => mlift D u' (b'' - u'))).map (reliftX b'' H g A0))
            = FTLc b'' (b'' + liftOff f (S ++ A0) o + 1) u' (Lds.map (reliftX u' H g A0)) := by
          rw [map_relift_mlift A0 H g (show u' ≤ b'' by omega),
            FTLc_rebase (show u' ≤ b'' by omega) le_rfl]
        have eY : reliftX b'' H g A0 Y
            = mlift (reliftX u' H g A0 (mlift W u (u' - u)) ++ reliftX u' H g A0 (mlift U u (u' - u)))
                u' (b'' - u') ++ shiftr01 x 0 Z := by
          rw [hY]
          have e1 : reliftX b'' H g A0 (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z)
              = reliftX b'' H g A0 (mlift (W ++ U) u (b'' - u)) ++ shiftr01 x 0 Z := by
            unfold reliftX
            exact slift_append_low (low_of_Wg hZ x le_rfl) (fun m hm => reStair_low b'' H g _ hm)
          rw [e1]
          congr 1
          rw [← reliftX_app (Fr_mlift hW _ _) (Hd_mlift hHU _ _), ← mlift_app hW hHU, mlift_reliftX,
            show u' + (b'' - u') = b'' by omega]
          have e := mlift_mlift (W ++ U) u (u' - u) (b'' - u')
          rw [show u + (u' - u) = u' by omega, show u' - u + (b'' - u') = b'' - u by omega] at e
          rw [e]
        rw [eH2, eY] at this
        exact this
  flat := by
    intro u W hW h
    refine ⟨Hd_append_of (V' := []) (fun _ => rfl) (by simpa using h.1), ?_,
      fun u' hu' Lds hG b0 ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
    · exact LowC_snoc h.2.1 _ (by show 0 ≤ u + reOff (fun _ => 0) H A0 k0; omega)
    · have hw := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hub : u' ≤ b := hw.1
      have hR0 : RawWsAc A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      rw [mlift_snoc_flat W 1 u (u' - u) hW]
      have e : reliftX u' H g A0 (mlift W u (u' - u) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
          = reliftX u' H g A0 (mlift W u (u' - u)) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
        unfold reliftX
        refine slift_snoc_fix _ _ (fun m hm => ?_)
        have hm0 : m = 0 := by simpa using hm
        subst hm0; exact (reStair_stair _ _ _ _).zero
      simp only [relWsc_snoc, farWc_snoc]
      rw [e]
      refine fwH_flat_step hA hA1 ho f (Fr_FTLc _ _ _ _) (Fr_farWc _ _ _)
        (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (fun m => ?_)
      have hRm : RawWsAc A0 k0 H b (ws ++ List.replicate m (Lds, u', mlift W u (u' - u))) := by
        intro w' h'
        rcases List.mem_append.mp h' with h' | h'
        · exact hR0 w' h'
        · rw [List.eq_of_mem_replicate h']
          exact ⟨hub, hG.1, Fr_mlift hW _ _, Hd_mlift h.1 _ _, LowC_lift_shift hu' h.2.1⟩
      have := GTWAc_rep (h.2.2 u' hu' Lds hG b0) hC m g S o f b hf hb hRm hSA hA hA1 ho hK hKo
      rw [relWsc_rep, farWc_rep] at this
      exact this

end HcC
end TRIO
