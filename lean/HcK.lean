/-
HcK.lean: 子を塊と F の位置のタイの並びにした遠い語の、最後の語の中身の族（HcC の写し）。

    GTWAu A0 k0 H b0 Lds u X := ∀ ws, FarCAu A0 k0 H b0 ws → FarCAu A0 k0 H b0 (ws ++ [(Lds, u, X)])
    GoodChu A0 k0 H u Lds := 子の塊が低い ∧ ∀ g b0, GTWAu A0 k0 (H+g) b0（子の塊を g で持ち上げた並び）u []
    okWAu A0 k0 H u X := Hd X ∧ LowC (u + reOff 0 H A0 k0) X ∧
      ∀ u', u ≤ u' → ∀ Lds, GoodChu A0 k0 H u' Lds → ∀ b0, GTWAu A0 k0 H b0 Lds u' (mlift X u (u' − u))
-/
import HcJ

namespace TRIO
namespace HcK

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HbD HbM HbP HcA HcI HcJ

def GTWAu (A0 : List ℕ) (k0 : ℕ) (H : ℕ → ℕ) (b0 : ℕ) (Lds : List (List (Option TrioSeq))) (u : ℕ)
    (X : TrioSeq) : Prop :=
  ∀ ws, FarCAu A0 k0 H b0 ws → FarCAu A0 k0 H b0 (ws ++ [(Lds, u, X)])

def GoodChu (A0 : List ℕ) (k0 : ℕ) (H : ℕ → ℕ) (u : ℕ) (Lds : List (List (Option TrioSeq))) : Prop :=
  (∀ us ∈ Lds, RawUc (u + reOff (fun _ => 0) H A0 k0) us) ∧
    ∀ g b0, GTWAu A0 k0 (addF H g) b0 (Lds.map (fun us => us.map (Option.map (reliftX u H g A0)))) u []

def okWAu (A0 : List ℕ) (k0 : ℕ) (H : ℕ → ℕ) (u : ℕ) (X : TrioSeq) : Prop :=
  Hd X ∧ LowC (u + reOff (fun _ => 0) H A0 k0) X ∧
    ∀ u', u ≤ u' → ∀ Lds, GoodChu A0 k0 H u' Lds → ∀ b0, GTWAu A0 k0 H b0 Lds u' (mlift X u (u' - u))

theorem GTWAu_rep {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b0 : ℕ} {Lds : List (List (Option TrioSeq))}
    {u : ℕ} {X : TrioSeq} (h : GTWAu A0 k0 H b0 Lds u X)
    {ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)} (hC : FarCAu A0 k0 H b0 ws) :
    ∀ m, FarCAu A0 k0 H b0 (ws ++ List.replicate m (Lds, u, X))
  | 0 => by simpa using hC
  | m + 1 => by
      have := h _ (GTWAu_rep h hC m)
      rwa [List.append_assoc, ← List.replicate_succ'] at this

/-! ## 子の段の付け替え -/

theorem chF_rebase {b r c c' : ℕ} (hcc : c ≤ c') (hcb : c' ≤ b) :
    ∀ us : List (Option TrioSeq),
      chF b r c' (us.map (Option.map (fun X => mlift X c (c' - c)))) = chF b r c us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => simp [chF]
  | append_singleton us o ih =>
      rw [List.map_append, List.map_singleton, chF_snoc, chF_snoc, ih]
      congr 1
      cases o with
      | none => rfl
      | some X =>
          show mlift (mlift X c (c' - c)) c' (b - c') = mlift X c (b - c)
          have e := mlift_mlift X c (c' - c) (b - c')
          rw [show c + (c' - c) = c' by omega, show c' - c + (b - c') = b - c by omega] at e
          exact e

theorem FTLu_rebase {b r c c' : ℕ} (hcc : c ≤ c') (hcb : c' ≤ b) :
    ∀ Lds : List (List (Option TrioSeq)),
      FTLu b r c' (Lds.map (fun us => us.map (Option.map (fun X => mlift X c (c' - c)))))
        = FTLu b r c Lds := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil => simp [FTLu]
  | append_singleton Lds us ih =>
      rw [List.map_append, List.map_singleton, FTLu_snoc, FTLu_snoc, ih, chF_rebase hcc hcb]

theorem mapu_relift_mlift (A0 : List ℕ) (H g : ℕ → ℕ) {u u' : ℕ} (hu : u ≤ u')
    (Lds : List (List (Option TrioSeq))) :
    (Lds.map (fun us => us.map (Option.map (fun X => mlift X u (u' - u))))).map
        (fun us => us.map (Option.map (reliftX u' H g A0)))
      = (Lds.map (fun us => us.map (Option.map (reliftX u H g A0)))).map
          (fun us => us.map (Option.map (fun X => mlift X u (u' - u)))) := by
  simp only [List.map_map]
  refine List.map_congr_left (fun us _ => ?_)
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left (fun o _ => ?_)
  cases o with
  | none => rfl
  | some X =>
      simp only [Function.comp_apply, Option.map]
      rw [mlift_reliftX, show u + (u' - u) = u' by omega]

theorem RawUc_lift {K u u' : ℕ} (hu : u ≤ u') {us : List (Option TrioSeq)} (h : RawUc (u + K) us) :
    RawUc (u' + K) (us.map (Option.map (fun X => mlift X u (u' - u)))) := by
  intro X hX
  simp only [List.mem_map] at hX
  obtain ⟨o, ho, hoX⟩ := hX
  cases o with
  | none => simp at hoX
  | some X0 =>
      simp at hoX
      subst hoX
      obtain ⟨h1, h2, h3⟩ := h X0 ho
      refine ⟨Fr_mlift h1 _ _, Hd_mlift h2 _ _, ?_⟩
      have := LowC_mliftk h3 (u' - u)
      rwa [show u + K + (u' - u) = u' + K by omega] at this

theorem GoodChu_lift {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {u : ℕ} {Lds : List (List (Option TrioSeq))}
    (hG : GoodChu A0 k0 H u Lds) {u' : ℕ} (hu : u ≤ u') :
    GoodChu A0 k0 H u' (Lds.map (fun us => us.map (Option.map (fun X => mlift X u (u' - u))))) := by
  refine ⟨fun us hus => ?_, fun g b0 ws hC g2 S o f b hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
  · simp only [List.mem_map] at hus
    obtain ⟨us0, hus0, rfl⟩ := hus
    exact RawUc_lift hu (hG.1 us0 hus0)
  · have hw := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hub : u' ≤ b := hw.1
    have hR0 : RawWsAu A0 k0 (addF H g) b ws := fun w' h' => hR w' (List.mem_append_left _ h')
    have := hG.2 g b0 ws hC g2 S o f b hf hb
      (RawWsAu_snoc hR0 ⟨show u ≤ b by omega, RawLdsu_relift hG.1 g, Fr_nil, fun h => absurd rfl h,
        LowC_nil _⟩) hSA hA hA1 ho hK hKo
    have e0 : ∀ c (K G : ℕ → ℕ), reliftX c K G A0 ([] : TrioSeq) = [] := fun c K G => by
      unfold reliftX; exact slift_nil _
    simp only [relWsu_snoc, farWu_snoc] at this ⊢
    rw [e0] at this
    rw [e0, mapu_relift_mlift A0 H g hu, mapu_relift_mlift A0 (addF H g) g2 hu, FTLu_rebase hu hub]
    simpa [fwH, mlift_nil] using this

/-! ## 差し込み口の公理 -/

theorem LowC_lift_shift {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {u u' : ℕ} (hu : u ≤ u') {X : TrioSeq}
    (h : LowC (u + reOff (fun _ => 0) H A0 k0) X) :
    LowC (u' + reOff (fun _ => 0) H A0 k0) (mlift X u (u' - u)) := by
  have := LowC_mliftk h (u' - u)
  rwa [show u + reOff (fun _ => 0) H A0 k0 + (u' - u) = u' + reOff (fun _ => 0) H A0 k0 by omega]
    at this

/-- ★ 最後の語の中身の族の差し込み口の公理。 -/
theorem okWAu_ax {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0) (H : ℕ → ℕ) :
    SlotAx (okWAu A0 k0 H) where
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
      have hR0 : RawWsAu A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      simp only [relWsu_snoc, farWu_snoc]
      rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _)]
      refine fwH_oper_step hA hA1 ho f (Fr_farWu _ _ _) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
        (Fr_reliftX (Fr_mlift hU _ _) _ _ _ _) (Hd_reliftX (Hd_mlift hH _ _) _ _ _ _)
        (by rw [reliftX_length, mlift_length]; exact hlen) ?_ (fun m hm => ?_)
      · unfold reliftX
        rw [slift_length, srow_slift (reStair_stair _ _ _ _) (by rw [mlift_length]; omega),
          hasParent_slift (reStair_stair _ _ _ _)]
        exact (hasParent_mlift_iff u (u' - u) hUne).mpr hp
      · have hIm := hIH m hm
        have hRm : RawWsAu A0 k0 H b (ws ++ [(Lds, u', mlift (W ++ U⟦m⟧) u (u' - u))]) :=
          RawWsAu_snoc hR0 ⟨hub, hw.2.1, Fr_mlift (Fr_append hW (Fr_oper hU m)) _ _,
            Hd_mlift hIm.1 _ _, LowC_lift_shift hu' hIm.2.1⟩
        have := hIm.2.2 u' hu' Lds hG b0 ws hC g S o f b hf hb hRm hSA hA hA1 ho hK hKo
        simp only [relWsu_snoc, farWu_snoc] at this
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
      have hR0 : RawWsAu A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
      have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u := hj
      have hfix : ∀ m, m ≤ j → reStair u' H g A0 m = m :=
        fun m hm => reStair_low u' H g A0 (by omega)
      have eU : reliftX u' H g A0 (mlift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) u (u' - u))
          = reliftX u' H g A0 (mlift U u (u' - u)) ++ [((h, j, 0) : ℕ × ℕ × ℕ)] := by
        unfold reliftX; rw [mlift_snoc_low U _ hc, slift_snoc_fix _ _ hfix]
      simp only [relWsu_snoc, farWu_snoc]
      rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), eU]
      refine fwH_orph_step hA hA1 ho f hub (show b < b + liftOff f (S ++ A0) o + 1 by omega)
        (Fr_FTLu _ _ _ _) (Fr_farWu _ _ _) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
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
        have hRz : RawWsAu A0 k0 H b
            (ws ++ [(Lds, u', mlift (W ++ (U ++ shiftr01 h 0 z)) u (u' - u))]) :=
          RawWsAu_snoc hR0 ⟨hub, hw.2.1, Fr_mlift (Fr_append hW hFrz) _ _, Hd_mlift hzz.1 _ _,
            LowC_lift_shift hu' hzz.2.1⟩
        have := hzz.2.2 u' hu' Lds hG b0 ws hC g S o f b hf hb hRz hSA hA hA1 ho hK hKo
        simp only [relWsu_snoc, farWu_snoc] at this
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
      have hLds : ∀ us ∈ Lds, RawUc (u' + reOff (fun _ => 0) H A0 k0) us := hG.1
      have hR0 : RawWsAu A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
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
      simp only [relWsu_snoc, farWu_snoc]
      rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), ← eU]
      refine fwH_tie_step hA hA1 ho f hub (Fr_FTLu _ _ _ _) (Fr_farWu _ _ _)
        (fun b'' => farWu b'' (b'' + liftOff f (S ++ A0) o + 1) (relWsu A0 H g ws))
        (fun b'' => FTLu b'' (b'' + liftOff f (S ++ A0) o + 1) u'
          (Lds.map (fun us => us.map (Option.map (reliftX u' H g A0)))))
        (fun b'' hb'' => ?_) (fun b'' hb'' => ?_) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
        (by rw [eU]; exact Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
        (by rw [eU]; exact Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) ?_
        (by
          rw [← reliftX_app (Fr_mlift hW _ _) (Hd_mlift hHU _ _), ← mlift_app hW hHU]
          exact Hd_reliftX (Hd_mlift h0.1 _ _) _ _ _ _)
        (fun b'' hb'' Z hZ hbZ => ?_)
      · show mlift (farWu b (b + liftOff f (S ++ A0) o + 1) (relWsu A0 H g ws)) b (b'' - b)
          = farWu b'' (b'' + liftOff f (S ++ A0) o + 1) (relWsu A0 H g ws)
        rw [mlift_farWu_basek (show b < b + liftOff f (S ++ A0) o + 1 by omega) (b'' - b) _
            (RawWsku_relWsu hR0 g), show b + (b'' - b) = b'' by omega,
          show b + liftOff f (S ++ A0) o + 1 + (b'' - b) = b'' + liftOff f (S ++ A0) o + 1 by omega]
      · show mlift (FTLu b (b + liftOff f (S ++ A0) o + 1) u'
            (Lds.map (fun us => us.map (Option.map (reliftX u' H g A0))))) b (b'' - b)
          = FTLu b'' (b'' + liftOff f (S ++ A0) o + 1) u'
            (Lds.map (fun us => us.map (Option.map (reliftX u' H g A0))))
        rw [mlift_FTLu_base (show b < b + liftOff f (S ++ A0) o + 1 by omega) hub (b'' - b) _
            (RawLdsu_relift hLds g),
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
        have hGb : GoodChu A0 k0 H b''
            (Lds.map (fun us => us.map (Option.map (fun X => mlift X u' (b'' - u'))))) :=
          GoodChu_lift hG (by omega)
        have hFrY : Fr Y := by
          rw [hY]
          refine Fr_append (Fr_mlift hFrWU _ _) (fun y hy => ?_)
          simp only [shiftr01, List.mem_map] at hy
          obtain ⟨p, -, rfl⟩ := hy
          dsimp only; omega
        have hRb : RawWsAu A0 k0 H b''
            (ws ++ [(Lds.map (fun us => us.map (Option.map (fun X => mlift X u' (b'' - u')))), b'',
              mlift Y b'' (b'' - b''))]) := by
          rw [Nat.sub_self, mlift_zero]
          exact RawWsAu_snoc (RawWsAu_mono hb'' hR0) ⟨le_rfl, hGb.1, hFrY, hL.1, hL.2.1⟩
        have := hL.2.2 b'' le_rfl _ hGb b0 ws hC g S o f b'' hf (by omega) hRb hSA hA hA1 ho hK hKo
        simp only [relWsu_snoc, farWu_snoc] at this
        rw [Nat.sub_self, mlift_zero] at this
        have eH2 : FTLu b'' (b'' + liftOff f (S ++ A0) o + 1) b''
            ((Lds.map (fun us => us.map (Option.map (fun X => mlift X u' (b'' - u'))))).map
              (fun us => us.map (Option.map (reliftX b'' H g A0))))
            = FTLu b'' (b'' + liftOff f (S ++ A0) o + 1) u'
                (Lds.map (fun us => us.map (Option.map (reliftX u' H g A0)))) := by
          rw [mapu_relift_mlift A0 H g (show u' ≤ b'' by omega),
            FTLu_rebase (show u' ≤ b'' by omega) le_rfl]
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
      have hR0 : RawWsAu A0 k0 H b ws := fun w' h' => hR w' (List.mem_append_left _ h')
      rw [mlift_snoc_flat W 1 u (u' - u) hW]
      have e : reliftX u' H g A0 (mlift W u (u' - u) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
          = reliftX u' H g A0 (mlift W u (u' - u)) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
        unfold reliftX
        refine slift_snoc_fix _ _ (fun m hm => ?_)
        have hm0 : m = 0 := by simpa using hm
        subst hm0; exact (reStair_stair _ _ _ _).zero
      simp only [relWsu_snoc, farWu_snoc]
      rw [e]
      refine fwH_flat_step hA hA1 ho f (Fr_FTLu _ _ _ _) (Fr_farWu _ _ _)
        (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (fun m => ?_)
      have hRm : RawWsAu A0 k0 H b (ws ++ List.replicate m (Lds, u', mlift W u (u' - u))) := by
        intro w' h'
        rcases List.mem_append.mp h' with h' | h'
        · exact hR0 w' h'
        · rw [List.eq_of_mem_replicate h']
          exact ⟨hub, hG.1, Fr_mlift hW _ _, Hd_mlift h.1 _ _, LowC_lift_shift hu' h.2.1⟩
      have := GTWAu_rep (h.2.2 u' hu' Lds hG b0) hC m g S o f b hf hb hRm hSA hA hA1 ho hK hKo
      rw [relWsu_rep, farWu_rep] at this
      exact this

end HcK
end TRIO
