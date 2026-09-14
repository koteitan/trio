/-
HdN.lean: 低い塊の族 NXs の差し込み口の tie / flat と SlotAx（NXs_ax）。

- tie: HdJ.tstep_tie。荷は段 b'' の族で、道 Q と Lds を段 b'' へ持ち上げて置く（FTLt_rebase / chT_rebase）。
- flat: 高さ 0 は F のタイの複製（BotT_Fflat、HbU.child_flat_step）、
  高さ s+1 は道の最後のタイの複製（BotT_tieflat、HdJ.tstep_flat。複製の良さは GT_jump の繰り返し）。
-/
import HdM

namespace TRIO
namespace HdN

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcE HcF HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdL HdM

theorem fwH_nil_c (b r : ℕ) (H0 : TrioSeq) (c c' : ℕ) : fwH b r H0 c [] = fwH b r H0 c' [] := by
  simp only [fwH, mlift_nil]

theorem fwH_nil_rebase (b r : ℕ) (H0 K : TrioSeq) (u : ℕ) : fwH b r (H0 ++ K) u [] = fwH b r H0 b K := by
  simp only [fwH, mlift_nil, Nat.sub_self, mlift_zero, List.append_nil]

theorem chT_snoc_ch (b r u : ℕ) (x : List UT) (Y : TrioSeq) :
    chT b r u (x ++ [UT.ch Y]) = chT b r u x ++ mlift Y u (b - u) := by
  simp [chT_append, chT, unitT]

theorem chT_rep_tie (b r u : ℕ) (us0 y : List UT) : ∀ m,
    chT b r u (us0 ++ List.replicate m (UT.tie 0 y))
      = chT b r u us0 ++ (List.range m).flatMap
          (fun _ => ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r u y))
  | 0 => by simp
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, chT_append, chT_rep_tie b r u us0 y m,
        List.range_succ, List.flatMap_append]
      simp [chT, unitT]

theorem imgT_snoc_ch {A : List ℕ} (H G : ℕ → ℕ) {c c' u : ℕ} (hcc : c ≤ c') (hcu : c' ≤ u)
    (us : List UT) (Y : TrioSeq) :
    imgT A H G c' u (us ++ [UT.ch (mlift Y c (c' - c))])
      = imgT A H G c' u us ++ [UT.ch (reliftX u H G A (mlift Y c (u - c)))] := by
  rw [imgT_append, imgT_ch, mlift_comp_vub hcc hcu]

/-! ## tie -/

theorem NXs_tie {s : ℕ} {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) {H : ℕ → ℕ}
    (c : ℕ) (W U : TrioSeq) (x : ℕ) (hW : Fr W) (hU : Fr (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)]))
    (hH : Hd (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)]) c U.length)
    (hload : ∀ c'', c ≤ c'' → ∀ Z ∈ Wg (2 * c''), based Z →
      NXs s A k H c'' (mlift (W ++ U) c (c'' - c) ++ shiftr01 x 0 Z)) :
    NXs s A k H c (W ++ (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)])) := by
  have h0 := hload c le_rfl [] (Wg_nil _) based_nil
  have e0 : mlift (W ++ U) c (c - c) ++ shiftr01 x 0 [] = W ++ U := by
    simp [shiftr01, mlift_zero]
  rw [e0] at h0
  have hKge : k ≤ reOff (fun _ => 0) H A k := by unfold reOff; omega
  have hLow : LowC (c + reOff (fun _ => 0) H A k) (W ++ (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)])) := by
    rw [← List.append_assoc]
    exact LowC_snoc h0.2.1 _ (by show c + 1 ≤ c + reOff (fun _ => 0) H A k; omega)
  refine ⟨Hd_append_of hH h0.1, hLow, fun c' hcc us hus => ?_⟩
  refine NXs_snoc_of hus hcc (Fr_append hW hU) (Hd_append_of hH h0.1) hLow
    (fun G S o f hE u hcu Lds hL Q hQ b hub ws hC hR => ?_)
  have hA := hE.2.2.1
  have hA1 := hE.2.2.2.1
  have ho := hE.2.2.2.2.1
  have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
  have hHU : Hd U := by
    intro hne
    have := hH (by simp)
    rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
  have hHW : Hd W := by
    intro hne
    have := h0.1 (by simp [hne])
    rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
  have eT : mlift (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)]) c (b - c)
      = mlift U c (b - c) ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_cone U _ hc]
    show _ ++ [((x, c + 1 + (b - c), 0) : ℕ × ℕ × ℕ)] = _
    rw [show c + 1 + (b - c) = b + 1 by omega]
  have hfix : ∀ m, m ≤ b + 1 → reStair b H G A m = m := fun m hm => reStair_tie b H G hA01 hm
  have eU : reliftX b H G A (mlift (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)]) c (b - c))
      = reliftX b H G A (mlift U c (b - c)) ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [eT]; unfold reliftX; rw [slift_snoc_fix _ _ hfix]
  have hbr : b < b + liftOff f (S ++ A) o + 1 := by omega
  have hRaw := RawTs_imgT hE hcu hus.1
  have hV : Fr (chT b (b + liftOff f (S ++ A) o + 1) u (imgT A H G c' u us) ++
      reliftX b H G A (mlift W c (b - c))) :=
    Fr_append (Fr_chT _ hRaw) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
  have hHV : Hd (chT b (b + liftOff f (S ++ A) o + 1) u (imgT A H G c' u us) ++
      reliftX b H G A (mlift W c (b - c))) :=
    Hd_app (Hd_chT _ hRaw) (Hd_reliftX (Hd_mlift hHW _ _) _ _ _ _)
  obtain ⟨hYF, hYH, hYne, hPC⟩ := botY_facts hbr u _ Lds Q (PG_raw hQ) hV
  rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), eU, bot_assoc]
  refine tstep_tie hA hA1 ho f (Fr_farWt _ _ _) hYF hYH hYne hPC
    (by rw [← eU]; exact Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
    (by rw [← eU]; exact Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) ?_ (fun b'' hb'' Z hZ hbZ => ?_)
  · rw [← eU, reliftX_length, mlift_length]
    unfold reliftX
    rw [coneV_iff_amin, amin_slift (reStair_stair _ _ _ _) (by simp)]
    have h0' : coneV (mlift (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)]) c (b - c)) (c + (b - c))
        U.length := coneV_mlift (by simp) hc (b - c)
    rw [show c + (b - c) = b by omega, coneV_iff_amin] at h0'
    have h1 := (reStair_stair b H G A).ge
      (amin (mlift (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)]) c (b - c)) U.length)
    omega
  · -- 荷: 段 b'' の族
    have hL2 := hload b'' (by omega) Z hZ hbZ
    have hub'' : u ≤ b'' := by omega
    have := NXs_snoc_elim (hL2.2.2 b'' le_rfl _ (GT_lift hus (show c' ≤ b'' by omega))) le_rfl
      G S o f hE b'' le_rfl _ (GoodChtX_lift hL hub'') _ (PG_lift hQ hub'') b'' le_rfl ws
      (FarCAt_mono (by omega) hC) (RawWsAt_mono (by omega) hR)
    have eL2 : Lds.map (mlTs u (b'' - u)) ++ [plugQ (Q.map (mlTs u (b'' - u))) []]
        = (Lds ++ [plugQ Q []]).map (mlTs u (b'' - u)) := by
      simp [mlTs_plugQ, mlTs]
    have eimg : imgT A H G b'' b'' (mlTs c' (b'' - c') us) = mlTs u (b'' - u) (imgT A H G c' u us) := by
      unfold imgT
      rw [Nat.sub_self, mlTs_zero, ← mlTs_comp hcu hub'', relTs_mlTs A H G hub'']
    have eY : reliftX b'' H G A (mlift (W ++ U) c (b'' - c) ++ shiftr01 x 0 Z)
        = mlift (reliftX b H G A (mlift W c (b - c)) ++ reliftX b H G A (mlift U c (b - c)))
            b (b'' - b) ++ shiftr01 x 0 Z := by
      have e1 : reliftX b'' H G A (mlift (W ++ U) c (b'' - c) ++ shiftr01 x 0 Z)
          = reliftX b'' H G A (mlift (W ++ U) c (b'' - c)) ++ shiftr01 x 0 Z := by
        unfold reliftX
        exact slift_append_low (low_of_Wg hZ x le_rfl) (fun m hm => reStair_low b'' H G _ hm)
      rw [e1]
      congr 1
      rw [← reliftX_app (Fr_mlift hW _ _) (Hd_mlift hHU _ _), ← mlift_app hW hHU, mlift_reliftX,
        show b + (b'' - b) = b'' by omega]
      have e := mlift_mlift (W ++ U) c (b - c) (b'' - b)
      rw [show c + (b - c) = b by omega, show b - c + (b'' - b) = b'' - c by omega] at e
      rw [e]
    rw [List.length_map, Nat.sub_self, mlift_zero, eL2, FTLt_rebase hub'' le_rfl, fwH_nil_c _ _ _ b'' u,
      eimg, chT_rebase hub'' le_rfl, eY] at this
    have hL2raw : ∀ us' ∈ Lds ++ [plugQ Q []], RawTs (u + reOff (fun _ => 0) f (S ++ A) o) us' := by
      intro us' h'
      rcases List.mem_append.mp h' with h' | h'
      · exact hL.1 us' h'
      · simp at h'; subst h'; exact RawTs_plugQ Q [] (PG_raw hQ) (by simp [RawTs])
    have hB0 : shiftr01 (Q.length + 2) 0 (chT b (b + liftOff f (S ++ A) o + 1) u (imgT A H G c' u us) ++
        reliftX b H G A (mlift W c (b - c))) ≠ [] →
        entry (shiftr01 (Q.length + 2) 0 (chT b (b + liftOff f (S ++ A) o + 1) u (imgT A H G c' u us) ++
          reliftX b H G A (mlift W c (b - c)))) 0 0 = Q.length + 2 + 1 := by
      intro hne
      have hVne : chT b (b + liftOff f (S ++ A) o + 1) u (imgT A H G c' u us) ++
          reliftX b H G A (mlift W c (b - c)) ≠ [] := by
        intro h0; apply hne; rw [h0]; rfl
      rw [entry0_shiftr01 (List.length_pos_iff.mpr hVne), hHV hVne]; omega
    have eSV : ∀ V : TrioSeq, mlift (shiftr01 (Q.length + 2) 0 V) b (b'' - b)
        = shiftr01 (Q.length + 2) 0 (mlift V b (b'' - b)) := by
      intro V; rw [mlift_eq_slift, mlift_eq_slift, slift_shift0]
    rw [mlift_farWt_self hR hb'', mlift_pathB (PathCone_fwQ hbr b u _ Lds Q (PG_raw hQ)) hB0,
      mlift_fwt_base hbr hub hL2raw Fr_nil (fun h => absurd rfl h) (b'' - b), eSV,
      mlift_app (Fr_chT _ hRaw) (Hd_reliftX (Hd_mlift hHW _ _) _ _ _ _),
      mlift_chT_base hbr hub (b'' - b) _ hRaw,
      show b + (b'' - b) = b'' by omega,
      show b + liftOff f (S ++ A) o + 1 + (b'' - b) = b'' + liftOff f (S ++ A) o + 1 by omega]
    rw [mlift_app (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (Hd_reliftX (Hd_mlift hHU _ _) _ _ _ _)] at this
    simp only [List.append_assoc, shiftr01_append0] at this ⊢
    exact this

/-! ## flat -/

theorem BotT_Fflat {C : List ℕ} {o : ℕ} {f : ℕ → ℕ} (hC : ∀ a ∈ C, a < o) (hC1 : ∀ a ∈ C, 1 ≤ a)
    (ho : 1 ≤ o) {u K : ℕ} {Lds : List (List UT)} {x : List UT} (hx : RawTs K x) {W1 : TrioSeq}
    (hW1 : Fr W1) (hG : ∀ m, GoodChtX C o f u (Lds ++ List.replicate m (x ++ [UT.ch W1]))) :
    BotT C o f u Lds [] (x ++ [UT.ch (W1 ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])]) := by
  intro b hub ws hFC hR
  show GpT C o f b (farWt b (b + liftOff f C o + 1)
    (ws ++ [(Lds ++ [x ++ [UT.ch (W1 ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])]], u, [])]))
  rw [farWt_snoc]
  dsimp only
  rw [FTLt_snoc, chT_snoc_ch, mlift_snoc_flat W1 1 u (b - u) hW1, fwH_nil_rebase, ← List.append_assoc]
  refine HbU.child_flat_step hC hC1 ho f (Fr_FTLt _ _ _ _) (Fr_farWt _ _ _)
    (Fr_append (Fr_chT _ hx) (Fr_mlift hW1 _ _)) (fun m => ?_)
  have := GoodChtX_bot (hG m) hC hC1 ho hub hFC hR
  rw [farWt_snoc] at this
  dsimp only at this
  rw [FTLt_rep, chT_snoc_ch, fwH_nil_c _ _ _ u b] at this
  exact this

theorem BotT_tieflat {C : List ℕ} {o : ℕ} {f : ℕ → ℕ} (hC : ∀ a ∈ C, a < o) (hC1 : ∀ a ∈ C, 1 ≤ a)
    (ho : 1 ≤ o) {u K : ℕ} {Lds Q : List (List UT)} {us0 x : List UT}
    (hus0 : RawTs K us0) (hx : RawTs K x) {W1 : TrioSeq} (hW1 : Fr W1)
    (hrep : ∀ m, BotT C o f u Lds Q (us0 ++ List.replicate m (UT.tie 0 (x ++ [UT.ch W1])))) :
    BotT C o f u Lds Q (us0 ++ [UT.tie 0 (x ++ [UT.ch (W1 ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])])]) := by
  intro b hub ws hFC hR
  obtain ⟨R, hRd⟩ : ∃ R, R = b + liftOff f C o + 1 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = chT b R u x ++ mlift W1 u (b - u) := ⟨_, rfl⟩
  have hDF : Fr D := by rw [hD]; exact Fr_append (Fr_chT _ hx) (Fr_mlift hW1 _ _)
  obtain ⟨Yfw, hYfw⟩ : ∃ Y, Y = fwH b R (FTLt b R u (Lds ++ [plugQ Q []])) u [] := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = Q.length + 2 := ⟨_, rfl⟩
  have eT : chT b R u (us0 ++ [UT.tie 0 (x ++ [UT.ch (W1 ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])])])
      = chT b R u us0 ++ ((1, R, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := by
    rw [chT_append, hD]
    simp only [chT, unitT, List.append_nil, Nat.add_zero]
    rw [chT_snoc_ch, mlift_snoc_flat W1 1 u (b - u) hW1, List.append_assoc]
  have eG : Yfw ++ shiftr01 d 0 (chT b R u us0 ++ ((1, R, 0) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (D ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]))
      = (Yfw ++ shiftr01 d 0 (chT b R u us0)) ++ shiftr01 d 0 (((1, R, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) ++
          [((d + 1 + 1, 0, 0) : ℕ × ℕ × ℕ)] := by
    simp only [shiftr01, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [show ((1 + 1 + d, 0 + 0 + 0, 0) : ℕ × ℕ × ℕ) = (d + 1 + 1, 0, 0) by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> omega]
  rw [← hRd, farWt_botT, ← hYfw, ← hd, eT, eG]
  have hYfwF : Fr Yfw := by rw [hYfw]; exact Fr_fwH _ _ _ _ _
  have hYfwH : Hd Yfw := by rw [hYfw]; exact Hd_fwH _ _ _ _ _
  have hYfwne : Yfw ≠ [] := by rw [hYfw]; simp [fwH]
  refine tstep_flat hC hC1 ho f (Fr_farWt _ _ _)
    (Fr_append (Fr_append hYfwF (Fr_shiftr (Fr_chT _ hus0) d)) (Fr_shiftr (Fr_node _ _) d))
    (Hd_app_ne (Hd_app_ne hYfwH hYfwne) (by simp [hYfwne])) (by simp [shiftr01]) ?_ ?_ (fun n => ?_)
  · rw [entry0_shiftr01 (by simp)]; show 1 + d = d + 1; omega
  · intro r' hr1 hr2
    obtain ⟨w, rfl⟩ : ∃ w, r' = w + 1 := ⟨r' - 1, by omega⟩
    have hw : w < D.length := by simp only [shiftr01_length, List.length_cons] at hr2; omega
    have hr2' : w + 1 < (((1, R, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D).length := by
      simp only [shiftr01_length, List.length_cons] at hr2 ⊢; omega
    rw [entry0_shiftr01 hr2', entry_cons, entry0_shiftr01 hw]
    have := getD_row0_ge hDF hw
    omega
  · have := hrep n b hub ws hFC hR
    rw [← hRd, farWt_botT, ← hYfw, ← hd, chT_rep_tie, chT_snoc_ch, ← hD] at this
    have eF : ∀ (l : List ℕ) (g : ℕ → TrioSeq),
        shiftr01 d 0 (l.flatMap g) = l.flatMap (fun i => shiftr01 d 0 (g i)) := by
      intro l g; simp [shiftr01, List.map_flatMap]
    rw [shiftr01_append0, eF] at this
    simp only [List.append_assoc] at this ⊢
    exact this

theorem NXs_flat {s : ℕ} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} (c : ℕ) (W : TrioSeq) (hW : Fr W)
    (h : NXs s A k H c W) : NXs s A k H c (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := by
  have hLow : LowC (c + reOff (fun _ => 0) H A k) (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) :=
    LowC_snoc h.2.1 _ (by show 0 ≤ c + reOff (fun _ => 0) H A k; omega)
  have hHd : Hd (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) :=
    Hd_append_of (V' := []) (fun _ => rfl) (by simpa using h.1)
  have hFrW1 : Fr (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := Fr_append hW (GzF.Fr_single le_rfl _ _)
  refine ⟨hHd, hLow, fun c' hcc us hus => ?_⟩
  have hW1gt := h.2.2 c' hcc us hus
  refine ⟨RawTs_snoc.mpr ⟨hus.1, RawT_ch (Fr_mlift hFrW1 _ _) (Hd_mlift hHd _ _) (LowC_lift_shift hcc hLow)⟩,
    fun G S o f hE u hcu Lds hL Q hQ => ?_⟩
  have eW1 : reliftX u H G A (mlift (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) c (u - c))
      = reliftX u H G A (mlift W c (u - c)) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_flat W 1 c (u - c) hW]
    unfold reliftX
    refine slift_snoc_fix _ _ (fun m hm => ?_)
    have hm0 : m = 0 := by simpa using hm
    subst hm0; exact (reStair_stair _ _ _ _).zero
  rw [imgT_snoc_ch H G hcc hcu, eW1]
  have hRaw := RawTs_imgT hE hcu hus.1
  have hW1F : Fr (reliftX u H G A (mlift W c (u - c))) := Fr_reliftX (Fr_mlift hW _ _) _ _ _ _
  cases s with
  | zero =>
      simp only [PG] at hQ
      subst hQ
      refine BotT_Fflat hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 hRaw hW1F (fun m => ?_)
      refine GoodChtX_rep (fun L hL' => ?_) hL m
      have := GT_good hW1gt hE hcu hL' PG_zero
      simpa only [plugQ, imgT_snoc_ch H G hcc hcu] using this
  | succ s' =>
      obtain ⟨Q', us0, rfl, hQ', hus0⟩ := hQ
      rw [BotT_snoc_eq]
      refine BotT_tieflat hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 hus0.1 hRaw hW1F (fun m => ?_)
      have hrep : GT s' (S ++ A) o f u (us0 ++ List.replicate m
          (UT.tie 0 (imgT A H G c' u (us ++ [UT.ch (mlift W c (c' - c))])))) := by
        induction m with
        | zero => simpa using hus0
        | succ m ih => rw [List.replicate_succ', ← List.append_assoc]; exact GT_jump hW1gt hE hcu ih
      have := hrep.2 (fun _ => 0) [] o f (EmbU_triv hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 f) u le_rfl Lds hL Q' hQ'
      rwa [imgT_zero, imgT_snoc_ch H G hcc hcu] at this

/-! ## 差し込み口の公理 -/

/-- ★ 高さ s の低い塊の族の差し込み口の公理。 -/
theorem NXs_ax {s : ℕ} {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (H : ℕ → ℕ) :
    SlotAx (NXs s A k H) where
  lift := fun u W _ h u' hu => NXs_lift u W h u' hu
  oper := fun u W U hW hU hH hlen hp hIH => NXs_oper u W U hW hU hH hlen hp hIH
  orph := fun u W U h j hW hU hH hj1 hj hnp hz => NXs_orph u W U h j hW hU hH hj1 hj hnp hz
  tie := fun u W U x hW hU hH hc hload => NXs_tie hA01 hk1 u W U x hW hU hH hc hload
  flat := fun u W hW h => NXs_flat u W hW h

end HdN
end TRIO
