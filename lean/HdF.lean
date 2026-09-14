/-
HdF.lean: 木の単位の低い子の並び GoodLowT と、F のタイの子の位置に置く節点の族 NXt（差し込み口の公理）。

    GoodLowT c us := 塊が段 c+1 以下 ∧ ∀ 族 (A, k, H) と段 u ≥ c、∀ Lds, GoodChtX A k H u Lds →
      GoodChtX A k H u (Lds ++ [us を u へ持ち上げた並び])
    NXt A k H c X := Hd X ∧ LowC (c + reOff 0 H A k) X ∧
      ∀ c' ≥ c, ∀ us, GoodLowT c' us → ∀ Lds, GoodChtX A k H c' Lds →
        GoodChtX A k H c' (Lds ++ [us ++ [UT.ch (X を c' へ持ち上げた形)]])

- 低い塊は錨 ≥ 1 の再持ち上げで動かない（mapt_tie_inv）。
- 子の段: HcF.cstep_oper / cstep_orph / cstep_tie、flat は HbU.child_flat_step（GoodChtX の反復）。
-/
import HdE
import HcF

namespace TRIO
namespace HdF

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcE HcF HcI HcM HdA HdB HdC HdD HdE

/-! ## 低い塊 -/

mutual
theorem mlT_zero (c : ℕ) : ∀ x : UT, mlT c 0 x = x
  | .ch X => by simp only [mlT, mlift_zero]
  | .tie us => by simp only [mlT, mlTs_zero c us]
theorem mlTs_zero (c : ℕ) : ∀ us : List UT, mlTs c 0 us = us
  | [] => by simp [mlTs]
  | x :: us => by simp only [mlTs, mlT_zero c x, mlTs_zero c us]
end

mutual
theorem mlT_comp {c c' u : ℕ} (hcc : c ≤ c') (hu : c' ≤ u) :
    ∀ x : UT, mlT c' (u - c') (mlT c (c' - c) x) = mlT c (u - c) x
  | .ch X => by simp only [mlT, mlift_comp_vub hcc hu]
  | .tie us => by simp only [mlT, mlTs_comp hcc hu us]
theorem mlTs_comp {c c' u : ℕ} (hcc : c ≤ c') (hu : c' ≤ u) :
    ∀ us : List UT, mlTs c' (u - c') (mlTs c (c' - c) us) = mlTs c (u - c) us
  | [] => by simp [mlTs]
  | x :: us => by simp only [mlTs, mlT_comp hcc hu x, mlTs_comp hcc hu us]
end

theorem mlTs_append (c t : ℕ) : ∀ us vs : List UT, mlTs c t (us ++ vs) = mlTs c t us ++ mlTs c t vs
  | [], vs => by simp [mlTs]
  | x :: us, vs => by simp only [List.cons_append, mlTs, mlTs_append c t us vs]

theorem RawT_ch {k : ℕ} {X : TrioSeq} (h1 : Fr X) (h2 : Hd X) (h3 : LowC k X) : RawT k (UT.ch X) := by
  simp only [RawT]; exact ⟨h1, h2, h3⟩

mutual
theorem relT_tie_inv {A : List ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) {c : ℕ} (H g : ℕ → ℕ) :
    ∀ x : UT, RawT (c + 1) x → relT A H g c x = x
  | .ch X, h => by simp only [relT]; rw [reliftX_tie_inv hA01 h.2.2 H g]
  | .tie us, h => by simp only [relT]; rw [relTs_tie_inv hA01 H g us h]
theorem relTs_tie_inv {A : List ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) {c : ℕ} (H g : ℕ → ℕ) :
    ∀ us : List UT, RawTs (c + 1) us → relTs A H g c us = us
  | [], _ => by simp [relTs]
  | x :: us, h => by simp only [relTs]; rw [relT_tie_inv hA01 H g x h.1, relTs_tie_inv hA01 H g us h.2]
end

theorem mapt_tie_inv {A : List ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) {c : ℕ} {us : List UT}
    (hus : RawTs (c + 1) us) (H g : ℕ → ℕ) : relTs A H g c us = us := relTs_tie_inv hA01 H g us hus

theorem chT_lastX {A : List ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (H g : ℕ → ℕ) {b r c c' : ℕ} (hcc : c ≤ c')
    (hcb : c' ≤ b) {us : List UT} (hus : RawTs (c' + 1) us) (X : TrioSeq) :
    chT b r c' (relTs A H g c' (us ++ [UT.ch (mlift X c (c' - c))]))
      = chT b r c' us ++ reliftX b H g A (mlift X c (b - c)) := by
  rw [relTs_snoc, mapt_tie_inv hA01 hus H g, chT_snoc]
  simp only [relT, unitT]
  rw [mlift_reliftX, show c' + (b - c') = b by omega, mlift_comp_vub hcc hcb]

theorem farWt_lastX {A : List ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (H g : ℕ → ℕ) {b r c c' : ℕ} (hcc : c ≤ c')
    (hcb : c' ≤ b) (ws : List (List (List UT) × ℕ × TrioSeq))
    (Lds : List (List UT)) {us : List UT} (hus : RawTs (c' + 1) us)
    (X : TrioSeq) :
    farWt b r (ws ++ [((Lds ++ [us ++ [UT.ch (mlift X c (c' - c))]]).map
        (relTs A H g c'), c', [])])
      = farWt b r ws ++ fwH b r (FTLt b r c' (Lds.map (relTs A H g c'))) b
          (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r c' us ++ reliftX b H g A (mlift X c (b - c)))) := by
  rw [farWt_snoc]
  dsimp only
  rw [List.map_append, List.map_singleton, FTLt_snoc, chT_lastX hA01 H g hcc hcb hus X]
  simp only [fwH, mlift_nil, Nat.sub_self, mlift_zero, List.append_nil]

theorem FTLt_low_row1 (b r c K : ℕ) : ∀ (Lds : List (List UT)), (∀ us ∈ Lds, RawTs K us) →
    ∀ y, y < (FTLt b r c Lds).length → entry (FTLt b r c Lds) 0 y ≤ 1 →
      entry (FTLt b r c Lds) 1 y = r := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil =>
      intro _ y hy _
      have hy0 : y = 0 := by
        simp only [FTLt, List.flatMap_nil, List.length_cons, List.length_nil] at hy; omega
      subst hy0; rfl
  | append_singleton Lds us ih =>
      intro hR y hy h0
      have hFrD : Fr (chT b r c us) :=
        Fr_chT (b := b) (r := r) (c := c) _ (hR us (List.mem_append_right _ (List.mem_singleton_self _)))
      have ih' := ih (fun L h' => hR L (List.mem_append_left _ h'))
      rw [FTLt_snoc] at hy h0 ⊢
      rcases Nat.lt_or_ge y (FTLt b r c Lds).length with hlt | hge
      · rw [Small.entry_append_left hlt] at h0 ⊢
        exact ih' y hlt h0
      · obtain ⟨w, rfl⟩ : ∃ w, y = (FTLt b r c Lds).length + w :=
          ⟨y - (FTLt b r c Lds).length, by omega⟩
        rw [entry_append_right] at h0 ⊢
        rcases w with _ | w
        · rfl
        · exfalso
          rw [entry_cons] at h0
          have hw : w < (chT b r c us).length := by
            simp only [List.length_append, List.length_cons, shiftr01_length] at hy; omega
          rw [entry0_shiftr01 hw] at h0
          have := getD_row0_ge hFrD hw
          omega

theorem FTLt_rep (b r u : ℕ) (Lds : List (List UT)) (us : List UT) : ∀ m,
    FTLt b r u (Lds ++ List.replicate m us)
      = FTLt b r u Lds ++ (List.range m).flatMap
          (fun _ => ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r u us))
  | 0 => by simp
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, FTLt_snoc, FTLt_rep b r u Lds us m,
        List.range_succ, List.flatMap_append]
      simp

theorem GoodChtX_rep {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {u : ℕ} {us : List UT}
    (hD : ∀ Lds, GoodChtX A k H u Lds → GoodChtX A k H u (Lds ++ [us]))
    {Lds : List (List UT)} (hL : GoodChtX A k H u Lds) :
    ∀ m, GoodChtX A k H u (Lds ++ List.replicate m us)
  | 0 => by simpa using hL
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc]
      exact hD _ (GoodChtX_rep hD hL m)

/-! ## 低い子の並び -/

def GoodLowT (c : ℕ) (us : List UT) : Prop :=
  RawTs (c + 1) us ∧ ∀ (A : List ℕ) (k : ℕ), (∀ a ∈ A, 1 ≤ a) → 1 ≤ k → (∀ a ∈ A, a < k) →
    ∀ (H : ℕ → ℕ) (u : ℕ), c ≤ u → ∀ Lds, GoodChtX A k H u Lds →
      GoodChtX A k H u (Lds ++ [mlTs c (u - c) us])

theorem GoodLowT_nil (c : ℕ) : GoodLowT c [] :=
  ⟨by simp [RawTs], fun _ _ _ _ _ _ _ _ _ hL => by simpa [mlTs] using GoodChtX_Fsucc hL⟩

theorem GoodLowT_lift {c : ℕ} {us : List UT} (h : GoodLowT c us) {c' : ℕ} (hcc : c ≤ c') :
    GoodLowT c' (mlTs c (c' - c) us) := by
  refine ⟨RawTs_lift (K := 1) hcc h.1, fun A k hA01 hk hAk H u hu Lds hL => ?_⟩
  have e : mlTs c' (u - c') (mlTs c (c' - c) us) = mlTs c (u - c) us := mlTs_comp hcc hu us
  rw [e]
  exact h.2 A k hA01 hk hAk H u (by omega) Lds hL

theorem GoodChtX_snoc_low {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {u : ℕ} {Lds : List (List UT)}
    (hL : GoodChtX A k H u Lds) {us : List UT} (hus : GoodLowT u us)
    (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k) (hAk : ∀ a ∈ A, a < k) : GoodChtX A k H u (Lds ++ [us]) := by
  have := hus.2 A k hA01 hk hAk H u le_rfl Lds hL
  have e : mlTs u (u - u) us = us := by rw [Nat.sub_self]; exact mlTs_zero u us
  rwa [e] at this

/-! ## 子の位置の節点の族 -/

def NXt (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (c : ℕ) (X : TrioSeq) : Prop :=
  Hd X ∧ LowC (c + reOff (fun _ => 0) H A k) X ∧
    ∀ c', c ≤ c' → ∀ us, GoodLowT c' us → ∀ Lds, GoodChtX A k H c' Lds →
      GoodChtX A k H c' (Lds ++ [us ++ [UT.ch (mlift X c (c' - c))]])

theorem NXt_snoc_of {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) {c' : ℕ}
    {Lds : List (List UT)} (hL : GoodChtX A k H c' Lds)
    {us : List UT} (hus : GoodLowT c' us) {c : ℕ} (hcc : c ≤ c') {X : TrioSeq}
    (hXF : Fr X) (hXH : Hd X) (hXL : LowC (c + reOff (fun _ => 0) H A k) X)
    (hstep : ∀ (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), EmbU A k H g S o f → c' ≤ b →
      ∀ ws, FarCAt (S ++ A) o f b ws → RawWsAt (S ++ A) o f b ws →
        GpT (S ++ A) o f b (farWt b (b + liftOff f (S ++ A) o + 1) ws ++
          fwH b (b + liftOff f (S ++ A) o + 1)
            (FTLt b (b + liftOff f (S ++ A) o + 1) c'
              (Lds.map (relTs A H g c'))) b
            (((1, b + liftOff f (S ++ A) o + 1, 0) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (chT b (b + liftOff f (S ++ A) o + 1) c' us ++
                reliftX b H g A (mlift X c (b - c)))))) :
    GoodChtX A k H c' (Lds ++ [us ++ [UT.ch (mlift X c (c' - c))]]) := by
  have hKge : k ≤ reOff (fun _ => 0) H A k := by unfold reOff; omega
  have hnew : RawTs (c' + reOff (fun _ => 0) H A k) (us ++ [UT.ch (mlift X c (c' - c))]) :=
    RawTs_snoc.mpr ⟨RawTs_mono' (by omega) hus.1,
      RawT_ch (Fr_mlift hXF _ _) (Hd_mlift hXH _ _) (LowC_lift_shift hcc hXL)⟩
  refine ⟨fun us' hus' => ?_, fun g S o f b hE hub ws hC hR => ?_⟩
  · rcases List.mem_append.mp hus' with hus' | hus'
    · exact hL.1 us' hus'
    · rw [List.mem_singleton] at hus'; rw [hus']; exact hnew
  · rw [farWt_lastX hA01 H g hcc hub ws Lds hus.1 X]
    exact hstep g S o f b hE hub ws hC hR

theorem NXt_snoc_elim {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c' : ℕ} {Lds : List (List UT)}
    {us : List UT} {c : ℕ} {X : TrioSeq}
    (h : GoodChtX A k H c' (Lds ++ [us ++ [UT.ch (mlift X c (c' - c))]]))
    (hA01 : ∀ a ∈ A, 1 ≤ a) (hus : RawTs (c' + 1) us) (hcc : c ≤ c')
    (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ) (hE : EmbU A k H g S o f) (hub : c' ≤ b)
    (ws : List (List (List UT) × ℕ × TrioSeq)) (hC : FarCAt (S ++ A) o f b ws)
    (hR : RawWsAt (S ++ A) o f b ws) :
    GpT (S ++ A) o f b (farWt b (b + liftOff f (S ++ A) o + 1) ws ++
      fwH b (b + liftOff f (S ++ A) o + 1)
        (FTLt b (b + liftOff f (S ++ A) o + 1) c'
          (Lds.map (relTs A H g c'))) b
        (((1, b + liftOff f (S ++ A) o + 1, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (chT b (b + liftOff f (S ++ A) o + 1) c' us ++
            reliftX b H g A (mlift X c (b - c))))) := by
  have := h.2 g S o f b hE hub ws hC hR
  rwa [farWt_lastX hA01 H g hcc hub ws Lds hus X] at this

/-- ★ 子の位置の節点の族の差し込み口の公理。 -/
theorem NXt_ax {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (H : ℕ → ℕ) :
    SlotAx (NXt A k H) where
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
    refine NXt_snoc_of hA01 hk1 hL hus hcc (Fr_append hW hU) (Hd_append_of hH hI1.1) hLow
      (fun g S o f b hE hub ws hC hR => ?_)
    have hA := hE.2.2.1
    have hA1 := hE.2.2.2.1
    have ho := hE.2.2.2.2.1
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), ← List.append_assoc]
    refine cstep_oper hA hA1 ho f (Fr_farWt _ _ _) (by rw [reliftX_length, mlift_length]; exact hlen)
      ?_ (fun m hm => ?_)
    · unfold reliftX
      rw [slift_length, srow_slift (reStair_stair _ _ _ _) (by rw [mlift_length]; omega),
        hasParent_slift (reStair_stair _ _ _ _)]
      exact (hasParent_mlift_iff c (b - c) hUne).mpr hp
    · have hIm := hIH m hm
      have := NXt_snoc_elim (hIm.2.2 c' hcc us hus Lds hL) hA01 hus.1 hcc g S o f b hE hub ws hC hR
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
    refine NXt_snoc_of hA01 hk1 hL hus hcc (Fr_append hW hU) (Hd_append_of hH hz0.1) hLow
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
    refine cstep_orph hA hA1 ho f (show b < b + liftOff f (S ++ A) o + 1 by omega) (Fr_FTLt _ _ _ _)
      (Fr_farWt _ _ _) (Fr_append (Fr_chT _ hus.1) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _))
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
      have := NXt_snoc_elim (hzz.2.2 c' hcc us hus Lds hL) hA01 hus.1 hcc g S o f b hE hub ws hC hR
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
    refine NXt_snoc_of hA01 hk1 hL hus hcc (Fr_append hW hU) (Hd_append_of hH h0.1) hLow
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
    have hFrW' : Fr (chT b r c' us ++ reliftX b H g A (mlift W c (b - c))) :=
      Fr_append (Fr_chT _ hus.1) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
    refine cstep_tie hA hA1 ho f (show b < r by omega) (Fr_FTLt _ _ _ _) (Fr_farWt _ _ _) hFrW'
      (fun y hy h0y => by rw [FTLt_low_row1 b r c' _ _ (RawLdst_relift hL.1 g) y hy h0y]; omega)
      (fun b'' => farWt b'' (b'' + liftOff f (S ++ A) o + 1) ws)
      (fun b'' => FTLt b'' (b'' + liftOff f (S ++ A) o + 1) c'
        (Lds.map (relTs A H g c')))
      (fun b'' hb'' => ?_) (fun b'' hb'' => ?_)
      (by rw [← eU]; exact Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
      (by rw [← eU]; exact Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) ?_
      (fun b'' hb'' Z hZ hbZ => ?_)
    · show mlift (farWt b r ws) b (b'' - b) = farWt b'' (b'' + liftOff f (S ++ A) o + 1) ws
      rw [hr]; exact mlift_farWt_self hR hb''
    · show mlift (FTLt b r c' (Lds.map (relTs A H g c'))) b (b'' - b)
        = FTLt b'' (b'' + liftOff f (S ++ A) o + 1) c'
          (Lds.map (relTs A H g c'))
      rw [mlift_FTLt_base (show b < r by omega) hub (b'' - b) _ (RawLdst_relift hL.1 g),
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
      have hGb := GoodChtX_lift hL (show c' ≤ b'' by omega)
      have husb := GoodLowT_lift hus (show c' ≤ b'' by omega)
      have := NXt_snoc_elim (hL2.2.2 b'' le_rfl _ husb _ hGb) hA01 husb.1 le_rfl g S o f b'' hE le_rfl
        ws (FarCAt_mono (by omega) hC) (RawWsAt_mono (by omega) hR)
      rw [Nat.sub_self, mlift_zero, mapt_relift_mlift A H g (show c' ≤ b'' by omega),
        FTLt_rebase (show c' ≤ b'' by omega) le_rfl, chT_rebase (show c' ≤ b'' by omega) le_rfl] at this
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
      have eW : mlift ((chT b r c' us ++ reliftX b H g A (mlift W c (b - c))) ++
            reliftX b H g A (mlift U c (b - c))) b (b'' - b)
          = chT b'' (b'' + liftOff f (S ++ A) o + 1) c' us ++
            mlift (reliftX b H g A (mlift W c (b - c)) ++ reliftX b H g A (mlift U c (b - c))) b (b'' - b) := by
        rw [List.append_assoc, mlift_app (Fr_chT _ hus.1) hHWU,
          mlift_chT_base (show b < r by omega) hub (b'' - b) us hus.1,
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
    refine NXt_snoc_of hA01 hk1 hL hus hcc hFrW1 hHd hLow (fun g S o f b hE hub ws hC hR => ?_)
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
    refine HbU.child_flat_step hA hA1 ho f (Fr_FTLt _ _ _ _) (Fr_farWt _ _ _)
      (Fr_append (Fr_chT _ hus.1) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)) (fun m => ?_)
    have hstepL : ∀ Lds', GoodChtX A k H c' Lds' →
        GoodChtX A k H c' (Lds' ++ [us ++ [UT.ch (mlift W c (c' - c))]]) :=
      fun Lds' hL' => h.2.2 c' hcc us hus Lds' hL'
    have hGm := GoodChtX_rep hstepL hL m
    have := hGm.2 g S o f b hE hub ws hC hR
    rw [farWt_snoc, List.map_append, List.map_replicate] at this
    dsimp only at this
    rw [FTLt_rep, chT_lastX hA01 H g hcc hub hus.1 W] at this
    simpa [fwH, mlift_nil] using this

end HdF
end TRIO
