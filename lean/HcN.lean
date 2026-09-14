/-
HcN.lean: 低い子の並び GoodLow と、F のタイの子の位置に置く節点の族 NX（差し込み口の公理）。

    GoodLow c us := 塊が段 c+1 以下 ∧ ∀ 族 (A, k, H) と段 u ≥ c、∀ Lds, GoodChuX A k H u Lds →
      GoodChuX A k H u (Lds ++ [us を u へ持ち上げた並び])
    NX A k H c X := Hd X ∧ LowC (c + reOff 0 H A k) X ∧
      ∀ c' ≥ c, ∀ us, GoodLow c' us → ∀ Lds, GoodChuX A k H c' Lds →
        GoodChuX A k H c' (Lds ++ [us ++ [some (X を c' へ持ち上げた形)]])

- 低い塊は錨 ≥ 1 の再持ち上げで動かない（mapu_tie_inv）。
- 子の段: HcF.cstep_oper / cstep_orph / cstep_tie、flat は HbU.child_flat_step（GoodChuX の反復）。
-/
import HcM
import HcF

namespace TRIO
namespace HcN

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcE HcF HcI HcJ HcK HcL HcM

/-! ## 低い塊 -/

theorem mapu_tie_inv {A : List ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) {c : ℕ} {us : List (Option TrioSeq)}
    (hus : RawUc (c + 1) us) (H g : ℕ → ℕ) : us.map (Option.map (reliftX c H g A)) = us := by
  conv_rhs => rw [← List.map_id us]
  refine List.map_congr_left (fun x hx => ?_)
  cases x with
  | none => rfl
  | some X =>
      simp only [Option.map, id]
      rw [reliftX_tie_inv hA01 (hus X hx).2.2 H g]

theorem chF_lastX {A : List ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (H g : ℕ → ℕ) {b r c c' : ℕ} (hcc : c ≤ c')
    (hcb : c' ≤ b) {us : List (Option TrioSeq)} (hus : RawUc (c' + 1) us) (X : TrioSeq) :
    chF b r c' ((us ++ [some (mlift X c (c' - c))]).map (Option.map (reliftX c' H g A)))
      = chF b r c' us ++ reliftX b H g A (mlift X c (b - c)) := by
  rw [List.map_append, mapu_tie_inv hA01 hus H g, List.map_singleton, chF_snoc]
  show chF b r c' us ++ mlift (reliftX c' H g A (mlift X c (c' - c))) c' (b - c') = _
  rw [mlift_reliftX, show c' + (b - c') = b by omega, mlift_comp_vub hcc hcb]

theorem farWu_lastX {A : List ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (H g : ℕ → ℕ) {b r c c' : ℕ} (hcc : c ≤ c')
    (hcb : c' ≤ b) (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq))
    (Lds : List (List (Option TrioSeq))) {us : List (Option TrioSeq)} (hus : RawUc (c' + 1) us)
    (X : TrioSeq) :
    farWu b r (ws ++ [((Lds ++ [us ++ [some (mlift X c (c' - c))]]).map
        (fun us => us.map (Option.map (reliftX c' H g A))), c', [])])
      = farWu b r ws ++ fwH b r (FTLu b r c' (Lds.map (fun us => us.map (Option.map (reliftX c' H g A))))) b
          (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chF b r c' us ++ reliftX b H g A (mlift X c (b - c)))) := by
  rw [farWu_snoc]
  dsimp only
  rw [List.map_append, List.map_singleton, FTLu_snoc, chF_lastX hA01 H g hcc hcb hus X]
  simp only [fwH, mlift_nil, Nat.sub_self, mlift_zero, List.append_nil]

theorem FTLu_low_row1 (b r c K : ℕ) : ∀ (Lds : List (List (Option TrioSeq))), (∀ us ∈ Lds, RawUc K us) →
    ∀ y, y < (FTLu b r c Lds).length → entry (FTLu b r c Lds) 0 y ≤ 1 →
      entry (FTLu b r c Lds) 1 y = r := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil =>
      intro _ y hy _
      have hy0 : y = 0 := by
        simp only [FTLu, List.flatMap_nil, List.length_cons, List.length_nil] at hy; omega
      subst hy0; rfl
  | append_singleton Lds us ih =>
      intro hR y hy h0
      have hFrD : Fr (chF b r c us) :=
        Fr_chF b r c (hR us (List.mem_append_right _ (List.mem_singleton_self _)))
      have ih' := ih (fun L h' => hR L (List.mem_append_left _ h'))
      rw [FTLu_snoc] at hy h0 ⊢
      rcases Nat.lt_or_ge y (FTLu b r c Lds).length with hlt | hge
      · rw [Small.entry_append_left hlt] at h0 ⊢
        exact ih' y hlt h0
      · obtain ⟨w, rfl⟩ : ∃ w, y = (FTLu b r c Lds).length + w :=
          ⟨y - (FTLu b r c Lds).length, by omega⟩
        rw [entry_append_right] at h0 ⊢
        rcases w with _ | w
        · rfl
        · exfalso
          rw [entry_cons] at h0
          have hw : w < (chF b r c us).length := by
            simp only [List.length_append, List.length_cons, shiftr01_length] at hy; omega
          rw [entry0_shiftr01 hw] at h0
          have := getD_row0_ge hFrD hw
          omega

theorem FTLu_rep (b r u : ℕ) (Lds : List (List (Option TrioSeq))) (us : List (Option TrioSeq)) : ∀ m,
    FTLu b r u (Lds ++ List.replicate m us)
      = FTLu b r u Lds ++ (List.range m).flatMap
          (fun _ => ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chF b r u us))
  | 0 => by simp
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, FTLu_snoc, FTLu_rep b r u Lds us m,
        List.range_succ, List.flatMap_append]
      simp

theorem GoodChuX_rep {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {u : ℕ} {us : List (Option TrioSeq)}
    (hD : ∀ Lds, GoodChuX A k H u Lds → GoodChuX A k H u (Lds ++ [us]))
    {Lds : List (List (Option TrioSeq))} (hL : GoodChuX A k H u Lds) :
    ∀ m, GoodChuX A k H u (Lds ++ List.replicate m us)
  | 0 => by simpa using hL
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc]
      exact hD _ (GoodChuX_rep hD hL m)

/-! ## 低い子の並び -/

def GoodLow (c : ℕ) (us : List (Option TrioSeq)) : Prop :=
  RawUc (c + 1) us ∧ ∀ (A : List ℕ) (k : ℕ), (∀ a ∈ A, 1 ≤ a) → 1 ≤ k → (∀ a ∈ A, a < k) →
    ∀ (H : ℕ → ℕ) (u : ℕ), c ≤ u → ∀ Lds, GoodChuX A k H u Lds →
      GoodChuX A k H u (Lds ++ [us.map (Option.map (fun X => mlift X c (u - c)))])

theorem GoodLow_nil (c : ℕ) : GoodLow c [] :=
  ⟨fun _ h => by simp at h, fun _ _ _ _ _ _ _ _ _ hL => by simpa using GoodChuX_Fsucc hL⟩

theorem GoodLow_lift {c : ℕ} {us : List (Option TrioSeq)} (h : GoodLow c us) {c' : ℕ} (hcc : c ≤ c') :
    GoodLow c' (us.map (Option.map (fun X => mlift X c (c' - c)))) := by
  refine ⟨RawUc_lift (K := 1) hcc h.1, fun A k hA01 hk hAk H u hu Lds hL => ?_⟩
  have e : (us.map (Option.map (fun X => mlift X c (c' - c)))).map (Option.map (fun X => mlift X c' (u - c')))
      = us.map (Option.map (fun X => mlift X c (u - c))) := by
    simp only [List.map_map]
    refine List.map_congr_left (fun x _ => ?_)
    cases x with
    | none => rfl
    | some X =>
        simp only [Function.comp_apply, Option.map]
        rw [mlift_comp_vub hcc hu]
  rw [e]
  exact h.2 A k hA01 hk hAk H u (by omega) Lds hL

theorem GoodChuX_snoc_low {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {u : ℕ} {Lds : List (List (Option TrioSeq))}
    (hL : GoodChuX A k H u Lds) {us : List (Option TrioSeq)} (hus : GoodLow u us)
    (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k) (hAk : ∀ a ∈ A, a < k) : GoodChuX A k H u (Lds ++ [us]) := by
  have := hus.2 A k hA01 hk hAk H u le_rfl Lds hL
  have e : us.map (Option.map (fun X => mlift X u (u - u))) = us := by
    simp [mlift_zero]
  rwa [e] at this

/-! ## 子の位置の節点の族 -/

def NX (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (c : ℕ) (X : TrioSeq) : Prop :=
  Hd X ∧ LowC (c + reOff (fun _ => 0) H A k) X ∧
    ∀ c', c ≤ c' → ∀ us, GoodLow c' us → ∀ Lds, GoodChuX A k H c' Lds →
      GoodChuX A k H c' (Lds ++ [us ++ [some (mlift X c (c' - c))]])

theorem NX_snoc_of {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) {c' : ℕ}
    {Lds : List (List (Option TrioSeq))} (hL : GoodChuX A k H c' Lds)
    {us : List (Option TrioSeq)} (hus : GoodLow c' us) {c : ℕ} (hcc : c ≤ c') {X : TrioSeq}
    (hXF : Fr X) (hXH : Hd X) (hXL : LowC (c + reOff (fun _ => 0) H A k) X)
    (hstep : ∀ (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), EmbU A k H g S o f → c' ≤ b →
      ∀ ws, FarCAu (S ++ A) o f b ws → RawWsAu (S ++ A) o f b ws →
        GpT (S ++ A) o f b (farWu b (b + liftOff f (S ++ A) o + 1) ws ++
          fwH b (b + liftOff f (S ++ A) o + 1)
            (FTLu b (b + liftOff f (S ++ A) o + 1) c'
              (Lds.map (fun us => us.map (Option.map (reliftX c' H g A))))) b
            (((1, b + liftOff f (S ++ A) o + 1, 0) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (chF b (b + liftOff f (S ++ A) o + 1) c' us ++
                reliftX b H g A (mlift X c (b - c)))))) :
    GoodChuX A k H c' (Lds ++ [us ++ [some (mlift X c (c' - c))]]) := by
  have hKge : k ≤ reOff (fun _ => 0) H A k := by unfold reOff; omega
  have hnew : RawUc (c' + reOff (fun _ => 0) H A k) (us ++ [some (mlift X c (c' - c))]) := by
    intro Y hY
    rcases List.mem_append.mp hY with hY | hY
    · exact ⟨(hus.1 Y hY).1, (hus.1 Y hY).2.1, LowC_mono (by omega) (hus.1 Y hY).2.2⟩
    · rw [List.mem_singleton, Option.some.injEq] at hY
      subst hY
      exact ⟨Fr_mlift hXF _ _, Hd_mlift hXH _ _, LowC_lift_shift hcc hXL⟩
  refine ⟨fun us' hus' => ?_, fun g S o f b hE hub ws hC hR => ?_⟩
  · rcases List.mem_append.mp hus' with hus' | hus'
    · exact hL.1 us' hus'
    · rw [List.mem_singleton] at hus'; rw [hus']; exact hnew
  · rw [farWu_lastX hA01 H g hcc hub ws Lds hus.1 X]
    exact hstep g S o f b hE hub ws hC hR

theorem NX_snoc_elim {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c' : ℕ} {Lds : List (List (Option TrioSeq))}
    {us : List (Option TrioSeq)} {c : ℕ} {X : TrioSeq}
    (h : GoodChuX A k H c' (Lds ++ [us ++ [some (mlift X c (c' - c))]]))
    (hA01 : ∀ a ∈ A, 1 ≤ a) (hus : RawUc (c' + 1) us) (hcc : c ≤ c')
    (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ) (hE : EmbU A k H g S o f) (hub : c' ≤ b)
    (ws : List (List (List (Option TrioSeq)) × ℕ × TrioSeq)) (hC : FarCAu (S ++ A) o f b ws)
    (hR : RawWsAu (S ++ A) o f b ws) :
    GpT (S ++ A) o f b (farWu b (b + liftOff f (S ++ A) o + 1) ws ++
      fwH b (b + liftOff f (S ++ A) o + 1)
        (FTLu b (b + liftOff f (S ++ A) o + 1) c'
          (Lds.map (fun us => us.map (Option.map (reliftX c' H g A))))) b
        (((1, b + liftOff f (S ++ A) o + 1, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (chF b (b + liftOff f (S ++ A) o + 1) c' us ++
            reliftX b H g A (mlift X c (b - c))))) := by
  have := h.2 g S o f b hE hub ws hC hR
  rwa [farWu_lastX hA01 H g hcc hub ws Lds hus X] at this

/-- ★ 子の位置の節点の族の差し込み口の公理。 -/
theorem NX_ax {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (H : ℕ → ℕ) :
    SlotAx (NX A k H) where
  lift := by
    intro c W hW h c1 hc1
    refine ⟨Hd_mlift h.1 c (c1 - c), LowC_lift_shift hc1 h.2.1, fun c' hc' us hus Lds hL => ?_⟩
    have e := mlift_mlift W c (c1 - c) (c' - c1)
    rw [show c + (c1 - c) = c1 by omega, show c1 - c + (c' - c1) = c' - c by omega] at e
    rw [e]
    exact h.2.2 c' (le_trans hc1 hc') us hus Lds hL
  oper := by
    intro c W U hW hU hH hlen hp hIH
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    have hI1 := hIH 1 le_rfl
    have hU1 : U⟦1⟧ = U.dropLast := oper_one_eq_dropLast (by omega)
    have hLow : LowC (c + reOff (fun _ => 0) H A k) (W ++ U) := by
      have hI1' := hI1.2.1
      rw [hU1] at hI1'
      obtain ⟨q, hq, -⟩ := hp
      have hqlt : q < U.length - 1 := nextR_index_lt hq
      have hrt := rtg_nextrel0_lift W U (rtg0_of_nextR' hq)
      have hsplit : W ++ U = (W ++ U.dropLast) ++ [U.getLast hUne] := by
        rw [List.append_assoc, List.dropLast_append_getLast hUne]
      rw [hsplit] at hrt ⊢
      have hlenD : (W ++ U.dropLast).length = W.length + (U.length - 1) := by
        rw [List.length_append, List.length_dropLast]
      rw [← hlenD] at hrt
      exact LowC_snoc_anc hI1' (by rw [hlenD]; omega) hrt
    refine ⟨Hd_append_of hH hI1.1, hLow, fun c' hcc us hus Lds hL => ?_⟩
    refine NX_snoc_of hA01 hk1 hL hus hcc (Fr_append hW hU) (Hd_append_of hH hI1.1) hLow
      (fun g S o f b hE hub ws hC hR => ?_)
    have hA := hE.2.2.1
    have hA1 := hE.2.2.2.1
    have ho := hE.2.2.2.2.1
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), ← List.append_assoc]
    refine cstep_oper hA hA1 ho f (Fr_farWu _ _ _) (by rw [reliftX_length, mlift_length]; exact hlen)
      ?_ (fun m hm => ?_)
    · unfold reliftX
      rw [slift_length, srow_slift (reStair_stair _ _ _ _) (by rw [mlift_length]; omega),
        hasParent_slift (reStair_stair _ _ _ _)]
      exact (hasParent_mlift_iff c (b - c) hUne).mpr hp
    · have hIm := hIH m hm
      have := NX_snoc_elim (hIm.2.2 c' hcc us hus Lds hL) hA01 hus.1 hcc g S o f b hE hub ws hC hR
      rw [mlift_app hW (Hd_oper hH hUne hm),
        reliftX_app (Fr_mlift hW _ _) (Hd_mlift (Hd_oper hH hUne hm) _ _), ← List.append_assoc] at this
      unfold reliftX at this ⊢
      rwa [← mlift_oper', slift_oper (reStair_stair _ _ _ _)] at this
  orph := by
    intro c W U h j hW hU hH hj1 hj hnp hz
    have hz0 := hz [] (Wg_nil _) based_nil
    have e0 : W ++ (U ++ shiftr01 h 0 []) = W ++ U := by simp [shiftr01]
    rw [e0] at hz0
    have hLow : LowC (c + reOff (fun _ => 0) H A k) (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
      rw [← List.append_assoc]
      exact LowC_snoc hz0.2.1 _ (by show j ≤ c + reOff (fun _ => 0) H A k; omega)
    refine ⟨Hd_append_of hH hz0.1, hLow, fun c' hcc us hus Lds hL => ?_⟩
    refine NX_snoc_of hA01 hk1 hL hus hcc (Fr_append hW hU) (Hd_append_of hH hz0.1) hLow
      (fun g S o f b hE hub ws hC hR => ?_)
    have hA := hE.2.2.1
    have hA1 := hE.2.2.2.1
    have ho := hE.2.2.2.2.1
    have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ c := hj
    have hfix : ∀ m, m ≤ j → reStair b H g A m = m := fun m hm => reStair_low b H g A (by omega)
    have eU : reliftX b H g A (mlift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) c (b - c))
        = reliftX b H g A (mlift U c (b - c)) ++ [((h, j, 0) : ℕ × ℕ × ℕ)] := by
      unfold reliftX; rw [mlift_snoc_low U _ hc, slift_snoc_fix _ _ hfix]
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), eU, ← List.append_assoc]
    refine cstep_orph hA hA1 ho f (show b < b + liftOff f (S ++ A) o + 1 by omega) (Fr_FTLu _ _ _ _)
      (Fr_farWu _ _ _) (Fr_append (Fr_chF _ _ _ hus.1) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _))
      (by rw [← eU]; exact Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) hj1 (by omega) ?_
      (fun z hz' hbz => ?_)
    · intro hh
      apply hnp
      rw [← eU, reliftX_length, mlift_length] at hh
      unfold reliftX at hh
      rw [hasParent_slift (reStair_stair _ _ _ _), mlift_eq_slift,
        hasParent_slift (stair_step _ _)] at hh
      exact hh
    · have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
      have hHz : Hd (U ++ shiftr01 h 0 z) := Hd_append_shift hH hbz
      have hzz := hz z hz' hbz
      have hlowz := low_of_Wg hzW h (show j ≤ c by omega)
      have := NX_snoc_elim (hzz.2.2 c' hcc us hus Lds hL) hA01 hus.1 hcc g S o f b hE hub ws hC hR
      rw [mlift_app hW hHz, mlift_append_low hlowz] at this
      have hH2 : Hd (mlift U c (b - c) ++ shiftr01 h 0 z) := by
        have := Hd_mlift hHz c (b - c)
        rwa [mlift_append_low hlowz] at this
      rw [reliftX_app (Fr_mlift hW _ _) hH2] at this
      have e1 : reliftX b H g A (mlift U c (b - c) ++ shiftr01 h 0 z)
          = reliftX b H g A (mlift U c (b - c)) ++ shiftr01 h 0 z := by
        unfold reliftX
        exact slift_append_low (low_of_Wg hzW h (show j ≤ b by omega))
          (fun m hm => reStair_low b H g _ hm)
      rw [e1] at this
      simp only [List.append_assoc] at this ⊢
      exact this
  tie := by
    intro c W U x hW hU hH hc hload
    have h0 := hload c le_rfl [] (Wg_nil _) based_nil
    have e0 : mlift (W ++ U) c (c - c) ++ shiftr01 x 0 [] = W ++ U := by
      simp [shiftr01, mlift_zero]
    rw [e0] at h0
    have hKge : k ≤ reOff (fun _ => 0) H A k := by unfold reOff; omega
    have hLow : LowC (c + reOff (fun _ => 0) H A k) (W ++ (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)])) := by
      rw [← List.append_assoc]
      exact LowC_snoc h0.2.1 _ (by show c + 1 ≤ c + reOff (fun _ => 0) H A k; omega)
    refine ⟨Hd_append_of hH h0.1, hLow, fun c' hcc us hus Lds hL => ?_⟩
    refine NX_snoc_of hA01 hk1 hL hus hcc (Fr_append hW hU) (Hd_append_of hH h0.1) hLow
      (fun g S o f b hE hub ws hC hR => ?_)
    have hA := hE.2.2.1
    have hA1 := hE.2.2.2.1
    have ho := hE.2.2.2.2.1
    have hUc : Fr U := fun y hy => hU y (List.mem_append_left _ hy)
    have hHU : Hd U := by
      intro hne
      have := hH (by simp)
      rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
    have eT : mlift (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)]) c (b - c)
        = mlift U c (b - c) ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)] := by
      rw [mlift_snoc_cone U _ hc]
      show _ ++ [((x, c + 1 + (b - c), 0) : ℕ × ℕ × ℕ)] = _
      rw [show c + 1 + (b - c) = b + 1 by omega]
    have hfix : ∀ m, m ≤ b + 1 → reStair b H g A m = m := fun m hm => reStair_tie b H g hA01 hm
    have eU : reliftX b H g A (mlift (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)]) c (b - c))
        = reliftX b H g A (mlift U c (b - c)) ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)] := by
      rw [eT]; unfold reliftX; rw [slift_snoc_fix _ _ hfix]
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), eU, ← List.append_assoc]
    obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f (S ++ A) o + 1 := ⟨_, rfl⟩
    rw [← hr]
    have hFrW' : Fr (chF b r c' us ++ reliftX b H g A (mlift W c (b - c))) :=
      Fr_append (Fr_chF _ _ _ hus.1) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
    refine cstep_tie hA hA1 ho f (show b < r by omega) (Fr_FTLu _ _ _ _) (Fr_farWu _ _ _) hFrW'
      (fun y hy h0y => by rw [FTLu_low_row1 b r c' _ _ (RawLdsu_relift hL.1 g) y hy h0y]; omega)
      (fun b'' => farWu b'' (b'' + liftOff f (S ++ A) o + 1) ws)
      (fun b'' => FTLu b'' (b'' + liftOff f (S ++ A) o + 1) c'
        (Lds.map (fun us => us.map (Option.map (reliftX c' H g A)))))
      (fun b'' hb'' => ?_) (fun b'' hb'' => ?_)
      (by rw [← eU]; exact Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
      (by rw [← eU]; exact Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) ?_
      (fun b'' hb'' Z hZ hbZ => ?_)
    · show mlift (farWu b r ws) b (b'' - b) = farWu b'' (b'' + liftOff f (S ++ A) o + 1) ws
      rw [hr]; exact mlift_farWu_self hR hb''
    · show mlift (FTLu b r c' (Lds.map (fun us => us.map (Option.map (reliftX c' H g A))))) b (b'' - b)
        = FTLu b'' (b'' + liftOff f (S ++ A) o + 1) c'
          (Lds.map (fun us => us.map (Option.map (reliftX c' H g A))))
      rw [mlift_FTLu_base (show b < r by omega) hub (b'' - b) _ (RawLdsu_relift hL.1 g),
        show b + (b'' - b) = b'' by omega, hr,
        show b + liftOff f (S ++ A) o + 1 + (b'' - b) = b'' + liftOff f (S ++ A) o + 1 by omega]
    · rw [← eU, reliftX_length, mlift_length]
      unfold reliftX
      rw [coneV_iff_amin, amin_slift (reStair_stair _ _ _ _) (by simp)]
      have h0' : coneV (mlift (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)]) c (b - c)) (c + (b - c))
          U.length := coneV_mlift (by simp) hc (b - c)
      rw [show c + (b - c) = b by omega, coneV_iff_amin] at h0'
      have h1 := (reStair_stair b H g A).ge
        (amin (mlift (U ++ [((x, c + 1, 0) : ℕ × ℕ × ℕ)]) c (b - c)) U.length)
      omega
    · have hL2 := hload b'' (by omega) Z hZ hbZ
      obtain ⟨Y, hY⟩ : ∃ Y, Y = mlift (W ++ U) c (b'' - c) ++ shiftr01 x 0 Z := ⟨_, rfl⟩
      rw [← hY] at hL2
      have hGb := GoodChuX_lift hL (show c' ≤ b'' by omega)
      have husb := GoodLow_lift hus (show c' ≤ b'' by omega)
      have := NX_snoc_elim (hL2.2.2 b'' le_rfl _ husb _ hGb) hA01 husb.1 le_rfl g S o f b'' hE le_rfl
        ws (FarCAu_mono (by omega) hC) (RawWsAu_mono (by omega) hR)
      rw [Nat.sub_self, mlift_zero, mapu_relift_mlift A H g (show c' ≤ b'' by omega),
        FTLu_rebase (show c' ≤ b'' by omega) le_rfl, chF_rebase (show c' ≤ b'' by omega) le_rfl] at this
      have eY : reliftX b'' H g A Y
          = mlift (reliftX b H g A (mlift W c (b - c)) ++ reliftX b H g A (mlift U c (b - c)))
              b (b'' - b) ++ shiftr01 x 0 Z := by
        rw [hY]
        have e1 : reliftX b'' H g A (mlift (W ++ U) c (b'' - c) ++ shiftr01 x 0 Z)
            = reliftX b'' H g A (mlift (W ++ U) c (b'' - c)) ++ shiftr01 x 0 Z := by
          unfold reliftX
          exact slift_append_low (low_of_Wg hZ x le_rfl) (fun m hm => reStair_low b'' H g _ hm)
        rw [e1]
        congr 1
        rw [← reliftX_app (Fr_mlift hW _ _) (Hd_mlift hHU _ _), ← mlift_app hW hHU, mlift_reliftX,
          show b + (b'' - b) = b'' by omega]
        have e := mlift_mlift (W ++ U) c (b - c) (b'' - b)
        rw [show c + (b - c) = b by omega, show b - c + (b'' - b) = b'' - c by omega] at e
        rw [e]
      rw [eY] at this
      have hHWU : Hd (reliftX b H g A (mlift W c (b - c)) ++ reliftX b H g A (mlift U c (b - c))) := by
        rw [← reliftX_app (Fr_mlift hW _ _) (Hd_mlift hHU _ _), ← mlift_app hW hHU]
        exact Hd_reliftX (Hd_mlift h0.1 _ _) _ _ _ _
      have eW : mlift ((chF b r c' us ++ reliftX b H g A (mlift W c (b - c))) ++
            reliftX b H g A (mlift U c (b - c))) b (b'' - b)
          = chF b'' (b'' + liftOff f (S ++ A) o + 1) c' us ++
            mlift (reliftX b H g A (mlift W c (b - c)) ++ reliftX b H g A (mlift U c (b - c))) b (b'' - b) := by
        rw [List.append_assoc, mlift_app (Fr_chF _ _ _ hus.1) hHWU,
          mlift_chF_base (show b < r by omega) hub (b'' - b) us hus.1,
          show b + (b'' - b) = b'' by omega, hr,
          show b + liftOff f (S ++ A) o + 1 + (b'' - b) = b'' + liftOff f (S ++ A) o + 1 by omega]
      dsimp only
      rw [eW, show r + (b'' - b) = b'' + liftOff f (S ++ A) o + 1 by omega]
      simp only [List.append_assoc] at this ⊢
      exact this
  flat := by
    intro c W hW h
    have hLow : LowC (c + reOff (fun _ => 0) H A k) (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) :=
      LowC_snoc h.2.1 _ (by show 0 ≤ c + reOff (fun _ => 0) H A k; omega)
    have hHd : Hd (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) :=
      Hd_append_of (V' := []) (fun _ => rfl) (by simpa using h.1)
    have hFrW1 : Fr (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) := Fr_append hW (GzF.Fr_single le_rfl _ _)
    refine ⟨hHd, hLow, fun c' hcc us hus Lds hL => ?_⟩
    refine NX_snoc_of hA01 hk1 hL hus hcc hFrW1 hHd hLow (fun g S o f b hE hub ws hC hR => ?_)
    have hA := hE.2.2.1
    have hA1 := hE.2.2.2.1
    have ho := hE.2.2.2.2.1
    rw [mlift_snoc_flat W 1 c (b - c) hW]
    have e : reliftX b H g A (mlift W c (b - c) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
        = reliftX b H g A (mlift W c (b - c)) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
      unfold reliftX
      refine slift_snoc_fix _ _ (fun m hm => ?_)
      have hm0 : m = 0 := by simpa using hm
      subst hm0; exact (reStair_stair _ _ _ _).zero
    rw [e, ← List.append_assoc]
    refine HbU.child_flat_step hA hA1 ho f (Fr_FTLu _ _ _ _) (Fr_farWu _ _ _)
      (Fr_append (Fr_chF _ _ _ hus.1) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)) (fun m => ?_)
    have hstepL : ∀ Lds', GoodChuX A k H c' Lds' →
        GoodChuX A k H c' (Lds' ++ [us ++ [some (mlift W c (c' - c))]]) :=
      fun Lds' hL' => h.2.2 c' hcc us hus Lds' hL'
    have hGm := GoodChuX_rep hstepL hL m
    have := hGm.2 g S o f b hE hub ws hC hR
    rw [farWu_snoc, List.map_append, List.map_replicate] at this
    dsimp only at this
    rw [FTLu_rep, chF_lastX hA01 H g hcc hub hus.1 W] at this
    simpa [fwH, mlift_nil] using this

end HcN
end TRIO
