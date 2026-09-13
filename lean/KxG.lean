/-
KxG.lean: UK の FarP（low: 底が o の本当の段より下）。FarP_RLC の形で、語の t は世界の挿入 j に吸収する。
-/
import KxF

namespace TRIO
namespace KxG

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzB KxA KxB KxC KxD KxE KxF KlA KlB KlE KlG KlH

theorem reOff_lt_liftVal {H g : ℕ → ℕ} {L : List ℕ} {o s : ℕ} (hs : s < liftVal H L o) :
    reOff H g L s < liftVal (addF H g) L o := by
  unfold reOff
  have h1 := reStep_le 0 H g L o s (by omega) L
  rw [liftVal_add]
  omega

theorem reOff_low_eq {A S : List ℕ} {o o' j : ℕ} (hA : ∀ a ∈ A, a < o) (hoo : o ≤ o')
    (hS : ∀ s ∈ S, o' ≤ s ∧ s < o' + j) {H g F G : ℕ → ℕ} (hF : ∀ a ∈ A, F a = addF H g a)
    (ho' : o' = o + addF H g o) {s1 : ℕ} (hs1 : s1 < liftOff F A o') :
    reOff F G (S ++ A) s1 = reOff (addF H g) (maskF A G) (o :: A) s1 := by
  have hAo' : ∀ a ∈ A, a < o' := fun a ha => by have := hA a ha; omega
  unfold reOff
  congr 1
  rw [reStep_append, reStep_none (A0 := S ++ A) S
    (fun s hs => by have := (liftVal_ins_S hAo' hS F hs).1; omega), Nat.zero_add]
  simp only [reStep]
  rw [if_neg (by rw [liftVal_cons_top hA, ← ho', ← liftOff_congrA hF]; omega), Nat.zero_add]
  rw [reStep_congrA0 0 s1 F G (A0 := S ++ A) (A1 := A)
      (fun a ha => liftVal_ins hAo' (fun s hs => (hS s hs).1) F ha),
    reStep_congrA0 0 s1 (addF H g) (maskF A G) (A0 := o :: A) (A1 := A)
      (fun a ha => liftVal_cons_low hA ha)]
  exact reStep_congr 0 s1 (fun a ha => hF a ha) (fun a ha => by unfold maskF; rw [if_pos ha])

theorem lowP_ins_low {S A : List ℕ} {o j : ℕ} (hA : ∀ a ∈ A, a < o)
    (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) {F : ℕ → ℕ} {τ : ℕ} (hτ : τ ≤ liftOff F A o) :
    lowP F (S ++ A) τ = lowP F A τ := by
  unfold lowP
  rw [List.filter_append]
  have h1 : S.filter (fun a => decide (liftVal F (S ++ A) a < τ)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs
    have := (liftVal_ins_S hA hS F hs).1
    simp; omega
  rw [h1, List.nil_append]
  exact List.filter_congr (fun a ha => by rw [liftVal_ins hA (fun s hs => (hS s hs).1) F ha])

theorem GC_ins_low {S A : List ℕ} {o j : ℕ} (hA : ∀ a ∈ A, a < o)
    (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) {F : ℕ → ℕ} {τ b : ℕ} {L : TrioSeq}
    (hτ : τ ≤ liftOff F A o) (h : GC (S ++ A) F τ b L) : GC A F τ b L := by
  unfold GC at h ⊢
  rwa [lowP_ins_low hA hS hτ] at h

theorem FarP_UK_low {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {s : ℕ} (hs2 : 2 ≤ s) (hs : s < liftVal H (o :: A) o) :
    FarP (GC (o :: A)) (UK A o) (o :: A) H s := by
  intro b P d hP hd hbot h1 h2 g b' hb' S j F K hS hF
  have hbotb : BotGe (mlift P b (b' - b)) d (b' + s) := by
    have := BotGe_slift hbot (stair_step b (b' - b))
    rw [← mlift_eq_slift, if_pos (by omega), show b + s + (b' - b) = b' + s by omega] at this
    exact this
  have eB1 : mlift (P ++ [((d, b + s, 0) : ℕ × ℕ × ℕ)]) b (b' - b)
      = mlift P b (b' - b) ++ [((d, b' + s, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_bottom hbot, if_pos (by omega), show b + s + (b' - b) = b' + s by omega]
  rw [eB1, reliftX_snoc_bottom hd b' hbotb H g (o :: A)]
  obtain ⟨P1, hP1⟩ : ∃ P1, P1 = reliftX b' H g (o :: A) (mlift P b (b' - b)) := ⟨_, rfl⟩
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = reOff H g (o :: A) s := ⟨_, rfl⟩
  rw [← hP1, ← hs1]
  have hP1Fr : Fr P1 := by rw [hP1]; exact Fr_reliftX (Fr_mlift hP _ _) _ _ _ _
  have hbotP1 : BotGe P1 d (b' + s1) := by
    have := BotGe_slift hbotb (reStair_stair b' H g (o :: A))
    change BotGe (reliftX b' H g (o :: A) (mlift P b (b' - b))) d _ at this
    rwa [reStair_base, ← hP1, ← hs1] at this
  have hs1ge : 2 ≤ s1 := by rw [hs1]; unfold reOff; omega
  obtain ⟨o', ho'⟩ : ∃ o', o' = o + addF H g o := ⟨_, rfl⟩
  rw [← ho'] at hS ⊢
  have hAo' : ∀ a ∈ A, a < o' := fun a ha => by have := hA a ha; omega
  obtain ⟨k, hk⟩ : ∃ k, k = liftOff (addF H g) A o' := ⟨_, rfl⟩
  have hs1k : s1 < k := by
    rw [hk, hs1, ho', ← liftVal_cons_top hA]
    exact reOff_lt_liftVal hs
  unfold LCK
  rw [← hk, klift_snoc_low (show ((d, b' + s1, 0) : ℕ × ℕ × ℕ).2.1 < b' + k by
    show b' + s1 < b' + k; omega)]
  intro W hW hPVW t
  obtain ⟨J, hJ⟩ : ∃ J, J = j + sumOn F S := ⟨_, rfl⟩
  have hkF : liftOff F A o' = k := by rw [hk]; exact liftOff_congrA hF
  have hv' : liftOff F (S ++ A) (o' + j) = k + J := by
    rw [liftOff_ins hAo' hS, hkF, hJ]; omega
  rw [← hJ, hv']
  obtain ⟨Y, hY⟩ : ∃ Y, Y = klift P1 (b' + k) J K := ⟨_, rfl⟩
  rw [← hY]
  have hYFr : Fr Y := by rw [hY]; exact Fr_klift hP1Fr _ _ _
  have hbotY : BotGe Y d (b' + s1) := by rw [hY]; exact BotGe_klift hbotP1 _ _ _
  have hFrB : Fr (Y ++ [((d, b' + s1, 0) : ℕ × ℕ × ℕ)]) :=
    Fr_append hYFr (fun y hy => by simp at hy; subst hy; show 1 ≤ d; omega)
  rw [mlift_letterU hW hFrB (show b' + (k + J) < b' + (k + J) + 1 by omega),
    mlift_snoc_bottom hbotY, if_neg (by omega), Nat.add_zero]
  have hbotY2 : BotGe (mlift Y (b' + (k + J)) t) d (b' + s1) := by
    have := BotGe_slift hbotY (stair_step (b' + (k + J)) t)
    rw [← mlift_eq_slift, if_neg (by omega), Nat.add_zero] at this
    exact this
  have eQ : mlift W (b' + (k + J)) t ++ ((1, b' + (k + J) + 1 + t, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (mlift Y (b' + (k + J)) t ++ [((d, b' + s1 + 0, 0) : ℕ × ℕ × ℕ)])
      = (mlift W (b' + (k + J)) t ++ ((1, b' + (k + J) + 1 + t, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift Y (b' + (k + J)) t)) ++ [((d + 1, b' + s1, 0) : ℕ × ℕ × ℕ)] := by
    simp [shiftr01, List.append_assoc]
  rw [eQ]
  have hSAo : ∀ a ∈ S ++ A, a < o' + j := hA_ins hAo' hS
  have hSA : ∀ a ∈ S ++ A, a < o' + j + t := fun a ha => by have := hSAo a ha; omega
  have ho'1 : 1 ≤ o' := by omega
  have hSA1 : ∀ a ∈ S ++ A, 1 ≤ a := hA1_ins hA1 ho'1 hS
  have hnode : liftOff F (S ++ A) (o' + j + t) = k + J + t := by
    rw [liftOff_add_t hSAo, hv']
  have hFP := ((CtxP_GpT hSA hSA1 (by omega) (o' + j + t)) F).2.2.2 s1 hs1ge (by rw [hnode]; omega)
  refine hFP b' _ (d + 1) (Fr_append (Fr_mlift hW _ _) (Fr_letter _ _)) (by omega)
    (BotGe_node (Fr_mlift hW _ _) (show b' + s1 ≤ b' + (k + J) + 1 + t by omega) hbotY2)
    (fun G b3 hb3 => ?_) (fun G b3 hb3 τ L h1τ hτ hL hGL => ?_)
  · -- h1
    have hb'b3 : b' ≤ b3 := hb3
    -- 語の部分
    have hW1 : PVK (S ++ A) (o' + j + t) F b' (mlift W (b' + (k + J)) t) := by
      have := PVK_refine hSAo hPVW [] t F (fun _ => 0) (by simp) (fun _ _ => rfl)
      simpa [sumOn, hv', KlC.klift_zero_eq_mlift] using this
    have hW2 := PVK_lift hSA hSA1 (by omega) (Fr_mlift hW _ _) hW1 hb'b3
    have hW3 := PVK_relift hSA hW2 G
    -- 字と中身の書き換え
    rw [mlift_letterU (Fr_mlift hW _ _) (Fr_mlift hYFr _ _) (show b' < b' + (k + J) + 1 + t by omega),
      reliftX_app (Fr_mlift (Fr_mlift hW _ _) _ _) (Hd_letter _ _),
      show b' + (k + J) + 1 + t + (b3 - b') = b3 + (k + J + t + 1) by omega,
      reliftX_node (Fr_mlift (Fr_mlift hYFr _ _) _ _) b3 (k + J + t + 1) 1 F G (S ++ A)]
    have hlowA : lowP F (S ++ A) (k + J + t + 1) = S ++ A := lowP_all (fun a ha => by
      have := liftVal_lt_liftOff (f := F) hSA ha; omega)
    have hro : reOff F G (S ++ A) (k + J + t + 1) = liftOff (addF F G) (S ++ A) (o' + j + t) + 1 := by
      have := reOff_above hSA F G 1
      rw [hnode] at this
      rw [show k + J + t + 1 = k + J + t + 1 by rfl]; exact this
    rw [hlowA, hro]
    -- 中身の移し替え
    have hS' : ∀ s ∈ S, o + addF H g o ≤ s ∧ s < o + addF H g o + j := fun s hs => by
      rw [← ho']; exact hS s hs
    obtain ⟨K2, hK2⟩ := content_transport (G := G) (t := t) (K := K) (P := P) hA ho hS' hF hb' hb'b3
    rw [← ho', ← hk, ← hJ, ← hP1, show b' + k + J = b' + (k + J) by omega, ← hY] at hK2
    rw [hK2]
    -- 族の h1 の成分
    have hgo : addF H (addF g (maskF A G)) o = addF H g o := by
      unfold addF; rw [KxF.maskF_not_mem (fun ha => by have := hA o ha; omega)]; omega
    have hR := h1 (addF g (maskF A G)) b3 (by omega) (fun _ => 0) b3 le_rfl S (j + t) (addF F G) K2
      (fun s hs => by
        have := hS s hs
        simp only [addF_zero]; rw [hgo, ← ho']; omega)
      (fun a ha => by
        simp only [addF_zero]
        unfold addF
        rw [hF a ha]
        unfold maskF; rw [if_pos ha]; unfold addF; omega)
    simp only [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero] at hR
    unfold LCK at hR
    rw [hgo, ← ho'] at hR
    have hkk : liftOff (addF H (addF g (maskF A G))) A o' = liftOff (addF F (maskF A G)) A o' :=
      liftOff_congrA (fun a ha => by
        unfold addF; rw [hF a ha]; unfold addF; omega)
    rw [hkk] at hR
    have h3 := hR _ (Fr_reliftX (Fr_mlift (Fr_mlift hW _ _) _ _) _ _ _ _)
      (by rw [show o' + (j + t) = o' + j + t by omega]; exact hW3)
    have h4 := PVP_to_GpT h3
    rw [show o' + (j + t) = o' + j + t by omega] at h4
    exact h4
  · -- h2
    have hb'b3 : b' ≤ b3 := hb3
    have hW1 : PVK (S ++ A) (o' + j + t) F b' (mlift W (b' + (k + J)) t) := by
      have := PVK_refine hSAo hPVW [] t F (fun _ => 0) (by simp) (fun _ _ => rfl)
      simpa [sumOn, hv', KlC.klift_zero_eq_mlift] using this
    have hW2 := PVK_lift hSA hSA1 (by omega) (Fr_mlift hW _ _) hW1 hb'b3
    have hW3 := PVK_relift hSA hW2 G
    rw [show d + 1 - 1 = d by omega]
    rw [mlift_letterU (Fr_mlift hW _ _) (Fr_mlift hYFr _ _) (show b' < b' + (k + J) + 1 + t by omega),
      reliftX_app (Fr_mlift (Fr_mlift hW _ _) _ _) (Hd_letter _ _),
      show b' + (k + J) + 1 + t + (b3 - b') = b3 + (k + J + t + 1) by omega,
      reliftX_node (Fr_mlift (Fr_mlift hYFr _ _) _ _) b3 (k + J + t + 1) 1 F G (S ++ A)]
    have hlowA : lowP F (S ++ A) (k + J + t + 1) = S ++ A := lowP_all (fun a ha => by
      have := liftVal_lt_liftOff (f := F) hSA ha; omega)
    have hro : reOff F G (S ++ A) (k + J + t + 1) = liftOff (addF F G) (S ++ A) (o' + j + t) + 1 := by
      have := reOff_above hSA F G 1
      rw [hnode] at this
      exact this
    rw [hlowA, hro]
    have hS' : ∀ s ∈ S, o + addF H g o ≤ s ∧ s < o + addF H g o + j := fun s hs => by
      rw [← ho']; exact hS s hs
    obtain ⟨K2, hK2⟩ := content_transport (G := G) (t := t) (K := K) (P := P) hA ho hS' hF hb' hb'b3
    rw [← ho', ← hk, ← hJ, ← hP1, show b' + k + J = b' + (k + J) by omega, ← hY] at hK2
    rw [hK2]
    have hgo : addF H (addF g (maskF A G)) o = addF H g o := by
      unfold addF; rw [KxF.maskF_not_mem (fun ha => by have := hA o ha; omega)]; omega
    have hGA : ∀ a ∈ A, addF F G a = addF H (addF g (maskF A G)) a := fun a ha => by
      unfold addF maskF; rw [hF a ha, if_pos ha]; unfold addF; omega
    have hkF' : ∀ a ∈ A, addF F (maskF A G) a = addF F G a := fun a ha => by
      unfold addF maskF; rw [if_pos ha]
    have hs1F : s1 < liftOff F A o' := by rw [hkF]; exact hs1k
    have hτ3 : τ < liftVal (addF H (addF g (maskF A G))) (o :: A) o := by
      have e1 := reOff_low_eq (G := G) hA (by omega) hS hF ho' hs1F
      rw [e1] at hτ
      have e2 := reOff_lt_liftVal (H := addF H g) (g := maskF A G) (L := o :: A) (o := o) (s := s1)
        (by rw [liftVal_cons_top hA, ← ho', ← hk]; exact hs1k)
      rw [addF_assoc] at e2
      omega
    have hliftv : liftVal (addF H (addF g (maskF A G))) (o :: A) o = liftOff (addF F G) A o' := by
      rw [liftVal_cons_top hA, hgo, ← ho']
      exact liftOff_congrA (fun a ha => (hGA a ha).symm)
    have hτ' : τ < reOff H (addF g (maskF A G)) (o :: A) s := by
      rw [← reOff_comp, ← hs1, ← reOff_low_eq (G := G) hA (by omega) hS hF ho' hs1F]
      exact hτ
    have hGL' : GC (o :: A) (addF H (addF g (maskF A G))) τ b3 L := by
      refine GC_cons_low hA (le_of_lt hτ3) ?_
      exact GC_congr hGA (GC_ins_low hAo' hS (by rw [hliftv] at hτ3; omega) hGL)
    have hR := h2 (addF g (maskF A G)) b3 (by omega) τ L h1τ hτ' hL hGL' (fun _ => 0) b3 le_rfl
      S (j + t) (addF F G) K2
      (fun s hs => by
        have := hS s hs
        simp only [addF_zero]; rw [hgo, ← ho']; omega)
      (fun a ha => by simp only [addF_zero]; exact hGA a ha)
    simp only [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero] at hR
    unfold LCK at hR
    rw [hgo, ← ho'] at hR
    have hkk : liftOff (addF H (addF g (maskF A G))) A o' = liftOff (addF F (maskF A G)) A o' :=
      liftOff_congrA (fun a ha => by rw [hkF' a ha]; exact (hGA a ha).symm)
    rw [hkk] at hR
    have hthr : liftOff (addF F (maskF A G)) A o' = liftOff (addF F G) A o' := liftOff_congrA hkF'
    have hZlow : ∀ i, i < (shiftr01 (d - 1) 0 (((1, b3 + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)).length →
        ∃ k0, Relation.ReflTransGen (nextrel0 (shiftr01 (d - 1) 0
            (((1, b3 + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L))) k0 i ∧
          entry (shiftr01 (d - 1) 0 (((1, b3 + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) 1 k0
            < b3 + liftOff (addF F (maskF A G)) A o' := by
      intro i hi
      refine ⟨0, rtg0_of_window hi (Nat.zero_le _) (fun l hl0 hl1 => ?_), ?_⟩
      · have hl : l < (((1, b3 + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L).length := by
          rw [shiftr01_length] at hi; omega
        rw [entry0_shiftr01 (by simp), entry0_shiftr01 hl]
        obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        have hl' : l' < L.length := by simp [shiftr01] at hl; omega
        rw [entry_cons, entry0_shiftr01 hl']
        have := getD_row0_ge hL hl'
        show 1 + (d - 1) < _
        omega
      · rw [entry1_shiftr01]
        show b3 + τ < _
        rw [hthr]; rw [hliftv] at hτ3; omega
    rw [klift_append_low hZlow] at hR
    have h3 := hR _ (Fr_reliftX (Fr_mlift (Fr_mlift hW _ _) _ _) _ _ _ _)
      (by rw [show o' + (j + t) = o' + j + t by omega]; exact hW3)
    have h4 := PVP_to_GpT h3
    rw [show o' + (j + t) = o' + j + t by omega] at h4
    have eS : ∀ (X Y U : TrioSeq) (c : ℕ × ℕ × ℕ),
        X ++ c :: shiftr01 1 0 (Y ++ shiftr01 (d - 1) 0 U) = (X ++ c :: shiftr01 1 0 Y) ++ shiftr01 d 0 U := by
      intro X Y U c
      rw [shiftr01_append0, shiftr01_add0, show d - 1 + 1 = d by omega]
      simp [List.append_assoc]
    rw [eS] at h4
    exact h4

end KxG
end TRIO
