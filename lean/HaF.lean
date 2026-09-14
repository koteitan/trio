/-
HaF.lean: 錨つきの中身の遠い語の族（notes 追記546）の第 4 部: RA は錨の列 A0・上限 k0 の文脈の族（CtxP）。

FarP の場（段 b+s の子のない節点、2 ≤ s ≤ liftOff H A0 k0）: 遠い語の中で FarP_GpT_ge を使う。
- h1: 節点の前の中身 P1 の okWA の続き（FarCA の snoc）と、S ++ A0 の再持ち上げ（reliftX_farWA）。
- h2: 外側の FarP の h2 が与える中身の okWA と、接頭辞の並びの再持ち上げ（FarCA_relift）。
  子の段 τ は S の錨より下なので、子の級 GC (S ++ A0) は GC A0 に一致する（GC_ins_low）。
よって R_child で、錨つきの子の級 GC A0 H τ の並びを持つ節点（τ ≤ liftOff H A0 k0）を中身に置ける（RA_node）。
-/
import HaE

namespace TRIO
namespace HaF

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE

/-! ## 補助 -/

theorem liftOff_eq_reOff0 (H : ℕ → ℕ) (A0 : List ℕ) (k0 : ℕ) :
    liftOff H A0 k0 = reOff (fun _ => 0) H A0 k0 := by
  unfold liftOff reOff; rw [reStep_zeroF]

theorem lowP_one {A0 : List ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (h : ℕ → ℕ) : lowP h A0 1 = [] := by
  unfold lowP
  apply List.filter_eq_nil_iff.mpr
  intro a ha
  have h1 : a ≤ liftVal h A0 a := by unfold liftVal; omega
  have h2 := hA01 a ha
  simp only [decide_eq_true_eq]
  omega

theorem reOff_ins_low {S A0 : List ℕ} (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) {f f0 : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = f0 a) (g : ℕ → ℕ) {K : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s)
    {m : ℕ} (hm : m ≤ K) : reOff f g (S ++ A0) m = reOff f0 g A0 m :=
  reStair_ins_low hSA hf 0 g hK (by omega)

theorem lowP_ins_low {S A0 : List ℕ} (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) {f f0 : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = f0 a) {τ : ℕ} (hτ : ∀ s ∈ S, τ ≤ liftVal f (S ++ A0) s) :
    lowP f (S ++ A0) τ = lowP f0 A0 τ := by
  have hA0 : ∀ a ∈ A0, liftVal f (S ++ A0) a = liftVal f0 A0 a := by
    intro a ha
    unfold liftVal
    rw [stepSum_append, stepSum_none 0 f (a + 1) S (fun s hs => by have := hSA s hs a ha; omega),
      Nat.zero_add, stepSum_congr 0 (a + 1) hf]
  unfold lowP
  rw [List.filter_append]
  have hSnil : S.filter (fun a => decide (liftVal f (S ++ A0) a < τ)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs
    have := hτ s hs
    simp only [decide_eq_true_eq]; omega
  rw [hSnil, List.nil_append]
  apply List.filter_congr
  intro a ha
  rw [hA0 a ha]

theorem GC_ins_low {S A0 : List ℕ} (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) {f f0 : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = f0 a) {τ b : ℕ} (hτ : ∀ s ∈ S, τ ≤ liftVal f (S ++ A0) s) {L : TrioSeq}
    (h : GC (S ++ A0) f τ b L) : GC A0 f0 τ b L := by
  unfold GC at h ⊢
  rw [lowP_ins_low hSA hf hτ] at h
  have hsub : ∀ a ∈ lowP f0 A0 τ, f a = f0 a := fun a ha => hf a (List.mem_filter.mp ha).1
  rw [sumOn_congr hsub] at h
  exact GpT_congr (fun x hx => (lowP_lt_o1 x hx).1) hsub h

theorem relWs_zero (A0 : List ℕ) (H : ℕ → ℕ) (ws : List (ℕ × TrioSeq)) :
    relWs A0 H (fun _ => 0) ws = ws := by
  simp [relWs, reliftX_zero]

theorem RawWsA_relWs {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ} {ws : List (ℕ × TrioSeq)}
    (hR : RawWsA A0 k0 H b ws) (g : ℕ → ℕ) : RawWsA A0 k0 (addF H g) b (relWs A0 H g ws) := by
  intro w hw
  simp only [relWs, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, Fr_reliftX h0.2.1 _ _ _ _, Hd_reliftX h0.2.2.1 _ _ _ _, ?_⟩
  have := LowC_reliftX h0.2.2.2 H g A0
  rwa [reOff_zero_comp] at this

theorem FarCA_conds_lift {S A0 : List ℕ} {o k0 : ℕ} (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s)
    (hA : ∀ a ∈ S ++ A0, a < o) {H g f : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = addF H g a)
    (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF H g) A0 k0 ≤ liftVal f (S ++ A0) s)
    (hKo : reOff (fun _ => 0) (addF H g) A0 k0 ≤ liftOff f (S ++ A0) o) (g' : ℕ → ℕ) :
    (∀ a ∈ A0, addF f g' a = addF H (addF g g') a) ∧
    (∀ s ∈ S, reOff (fun _ => 0) (addF H (addF g g')) A0 k0 ≤ liftVal (addF f g') (S ++ A0) s) ∧
    reOff (fun _ => 0) (addF H (addF g g')) A0 k0 ≤ liftOff (addF f g') (S ++ A0) o := by
  have hKg := reOff_zero_le_sum (addF H g) g' A0 k0
  have eaddF : addF (addF H g) g' = addF H (addF g g') := by funext a; simp [addF]; omega
  rw [eaddF] at hKg
  refine ⟨fun a ha => ?_, fun s hs => ?_, ?_⟩
  · have := hf a ha
    simp only [addF] at this ⊢; omega
  · rw [liftVal_add]
    have h1 := hK s hs
    have h2 : sumOn g' A0 ≤ stepSum 0 g' (S ++ A0) (s + 1) := by
      rw [stepSum_append,
        stepSum_all 0 (s + 1) g' (A := A0) (fun a ha => by have := hSA s hs a ha; omega)]
      omega
    omega
  · rw [liftOff_addF hA, sumOn_append]; omega

/-! ## FarP の場 -/

theorem FarP_RA {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) {H : ℕ → ℕ} {s : ℕ}
    (hs2 : 2 ≤ s) (hs : s ≤ liftOff H A0 k0) : FarP (GC A0) (RA A0 k0) A0 H s := by
  intro b P d hP hd hbot h1 h2 g1 b1 hb1
  have hbotb : BotGe (mlift P b (b1 - b)) d (b1 + s) := by
    have := BotGe_slift hbot (stair_step b (b1 - b))
    rw [← mlift_eq_slift, if_pos (by omega), show b + s + (b1 - b) = b1 + s by omega] at this
    exact this
  have eB1 : mlift (P ++ [((d, b + s, 0) : ℕ × ℕ × ℕ)]) b (b1 - b)
      = mlift P b (b1 - b) ++ [((d, b1 + s, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_bottom hbot, if_pos (by omega), show b + s + (b1 - b) = b1 + s by omega]
  rw [eB1, reliftX_snoc_bottom hd b1 hbotb H g1 A0]
  obtain ⟨P1, hP1⟩ : ∃ P1, P1 = reliftX b1 H g1 A0 (mlift P b (b1 - b)) := ⟨_, rfl⟩
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = reOff H g1 A0 s := ⟨_, rfl⟩
  obtain ⟨H1, hH1⟩ : ∃ H1, H1 = addF H g1 := ⟨_, rfl⟩
  rw [← hP1, ← hs1, ← hH1]
  have hP1Fr : Fr P1 := by rw [hP1]; exact Fr_reliftX (Fr_mlift hP _ _) _ _ _ _
  have hbotP1 : BotGe P1 d (b1 + s1) := by
    have := BotGe_slift hbotb (reStair_stair b1 H g1 A0)
    change BotGe (reliftX b1 H g1 A0 (mlift P b (b1 - b))) d _ at this
    rwa [reStair_base, ← hP1, ← hs1] at this
  have hP1ok : okWA A0 k0 H1 b1 P1 := by
    have := RA_okWA (h1 g1 b1 hb1); rwa [← hP1, ← hH1] at this
  have hs1ge : s ≤ s1 := by rw [hs1]; unfold reOff; omega
  have hsK : s1 ≤ reOff (fun _ => 0) H1 A0 k0 := by
    rw [hs1, hH1, ← reOff_zero_comp H g1 A0 k0]
    exact reOff_mono H g1 A0 (by rw [← liftOff_eq_reOff0]; exact hs)
  have h2' : ∀ (g2 : ℕ → ℕ) b', b1 ≤ b' → ∀ τ L, 1 ≤ τ → τ < reOff H1 g2 A0 s1 → Fr L →
      GC A0 (addF H1 g2) τ b' L →
      okWA A0 k0 (addF H1 g2) b' (reliftX b' H1 g2 A0 (mlift P1 b1 (b' - b1)) ++
        shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) := by
    intro g2 b' hb' τ L h1τ hτ hL hGL
    have eH : addF H1 g2 = addF H (addF g1 g2) := by rw [hH1, addF_assoc]
    have hτ' : τ < reOff H (addF g1 g2) A0 s := by
      rw [← reOff_comp, ← hs1, ← hH1]; exact hτ
    rw [eH] at hGL ⊢
    have := RA_okWA (h2 (addF g1 g2) b' (by omega) τ L h1τ hτ' hL hGL)
    have eP : reliftX b' H1 g2 A0 (mlift P1 b1 (b' - b1))
        = reliftX b' H (addF g1 g2) A0 (mlift P b (b' - b)) := by
      rw [hP1, mlift_reliftX, show b1 + (b' - b1) = b' by omega, hH1, reliftX_comp]
      have e := mlift_mlift P b (b1 - b) (b' - b1)
      rw [show b + (b1 - b) = b1 by omega, show b1 - b + (b' - b1) = b' - b by omega] at e
      rw [e]
    rw [eP]; exact this
  refine ⟨?_, LowC_snoc hP1ok.2.1 _ (by show b1 + s1 ≤ b1 + reOff (fun _ => 0) H1 A0 k0; omega),
    fun b0 ws hC g S o f bb hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
  · -- 先頭
    have hGC1 : GC A0 (addF H1 (fun _ => 0)) 1 b1 [] := by
      unfold GC; rw [lowP_one hA01]; simpa [sumOn] using GpT_nil1 (addF H1 (fun _ => 0)) b1
    have hH := (h2' (fun _ => 0) b1 le_rfl 1 [] le_rfl
      (by unfold reOff; rw [reStep_zeroG]; omega) Fr_nil hGC1).1
    rw [Nat.sub_self, mlift_zero, reliftX_zero] at hH
    intro _
    have h0 := hH (by simp [shiftr01])
    rcases P1 with _ | ⟨x, P1⟩
    · simp [shiftr01, entry] at h0 ⊢; omega
    · exact h0
  · -- 遠い語の中
    have hw : RawWA A0 k0 H1 bb (b1, P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)]) :=
      hR _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hR0 : RawWsA A0 k0 H1 bb ws := fun w' h' => hR w' (List.mem_append_left _ h')
    have hb1bb : b1 ≤ bb := hw.1
    have hbotP3 : BotGe (reliftX b1 H1 g A0 P1) d (b1 + reOff H1 g A0 s1) := by
      have := BotGe_slift hbotP1 (reStair_stair b1 H1 g A0)
      change BotGe (reliftX b1 H1 g A0 P1) d _ at this
      rwa [reStair_base] at this
    have hs2ge : s1 ≤ reOff H1 g A0 s1 := by unfold reOff; omega
    have hs2K : reOff H1 g A0 s1 ≤ reOff (fun _ => 0) (addF H1 g) A0 k0 := by
      rw [← reOff_zero_comp H1 g A0 k0]; exact reOff_mono H1 g A0 hsK
    simp only [relWs_snoc, farW_snoc]
    rw [reliftX_snoc_bottom hd b1 hbotP1 H1 g A0]
    have hbotP3u : BotGe (mlift (reliftX b1 H1 g A0 P1) b1 (bb - b1)) d (bb + reOff H1 g A0 s1) := by
      have := BotGe_slift hbotP3 (stair_step b1 (bb - b1))
      rw [← mlift_eq_slift] at this
      rwa [if_pos (by omega), show b1 + reOff H1 g A0 s1 + (bb - b1) = bb + reOff H1 g A0 s1 by omega]
        at this
    have eL : mlift (reliftX b1 H1 g A0 P1 ++ [((d, b1 + reOff H1 g A0 s1, 0) : ℕ × ℕ × ℕ)]) b1 (bb - b1)
        = mlift (reliftX b1 H1 g A0 P1) b1 (bb - b1) ++
          [((d, bb + reOff H1 g A0 s1, 0) : ℕ × ℕ × ℕ)] := by
      rw [mlift_snoc_cone _ _ (coneV_of_BotGe hbotP3 (by omega))]
      show _ ++ [((d, b1 + reOff H1 g A0 s1 + (bb - b1), 0) : ℕ × ℕ × ℕ)] = _
      rw [show b1 + reOff H1 g A0 s1 + (bb - b1) = bb + reOff H1 g A0 s1 by omega]
    obtain ⟨r, hr⟩ : ∃ r, r = bb + liftOff f (S ++ A0) o + 1 := ⟨_, rfl⟩
    rw [← hr]
    have eF : fwW bb r b1 (reliftX b1 H1 g A0 P1 ++ [((d, b1 + reOff H1 g A0 s1, 0) : ℕ × ℕ × ℕ)])
        = fwW bb r b1 (reliftX b1 H1 g A0 P1) ++ [((d + 1, bb + reOff H1 g A0 s1, 0) : ℕ × ℕ × ℕ)] := by
      unfold fwW; rw [eL]; simp [shiftr01]
    rw [eF, ← List.append_assoc]
    have hso : reOff H1 g A0 s1 ≤ liftOff f (S ++ A0) o := le_trans hs2K hKo
    have hFP := FarP_GpT_ge hA hA1 ho (f := f) (show 2 ≤ reOff H1 g A0 s1 by omega) hso
    have hQ : Fr (farW bb r (relWs A0 H1 g ws) ++ fwW bb r b1 (reliftX b1 H1 g A0 P1)) :=
      Fr_append (Fr_farW _ _ _) (Fr_fwW _ _ _ _)
    have hRP : ∀ b', bb ≤ b' → RawWsA A0 k0 H1 b' (ws ++ [(b1, P1)]) := fun b' hb' =>
      RawWsA_snoc (RawWsA_mono hb' hR0) ⟨by omega, hP1Fr, hP1ok.1, hP1ok.2.1⟩
    have hC1 : FarCA A0 k0 H1 b0 (ws ++ [(b1, P1)]) := hP1ok.2.2 b0 ws hC
    have eP : ∀ b', bb ≤ b' →
        mlift (farW bb r (relWs A0 H1 g ws) ++ fwW bb r b1 (reliftX b1 H1 g A0 P1)) bb (b' - bb)
          = farW b' (b' + liftOff f (S ++ A0) o + 1) (relWs A0 H1 g (ws ++ [(b1, P1)])) := by
      intro b' hb'
      have hRk := RawWsk_relWs (hRP bb le_rfl) g
      rw [relWs_snoc] at hRk
      have := mlift_farW_basek (show bb < r by omega) (b' - bb) _ hRk
      rw [farW_snoc] at this
      rw [show bb + (b' - bb) = b' by omega,
        show r + (b' - bb) = b' + liftOff f (S ++ A0) o + 1 by omega] at this
      rw [relWs_snoc]
      exact this
    refine hFP bb _ (d + 1) hQ (by omega) ?_ (fun g' b' hb' => ?_)
      (fun g' b' hb' τ L h1τ hτ hL hGL => ?_)
    · unfold fwW
      exact BotGe_node (Fr_farW _ _ _) (by omega) (BotGe_cons (by omega) hbotP3u)
    · -- h1
      obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
      rw [eP b' hb', reliftX_farWA hA hSA b' hf g' hK _ (hRP b' hb')]
      exact hC1 (addF g g') S o (addF f g') b' hfG (by omega) (hRP b' hb') hSA hA hA1 ho hKG hKoG
    · -- h2
      obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
      rw [eP b' hb', reliftX_farWA hA hSA b' hf g' hK _ (hRP b' hb'), relWs_snoc]
      have hτ1 : τ < reOff H1 (addF g g') A0 s1 := by
        have e1 : reOff f g' (S ++ A0) (reOff H1 g A0 s1)
            = reOff (addF H1 g) g' A0 (reOff H1 g A0 s1) :=
          reOff_ins_low hSA hf g' hK hs2K
        rw [e1, reOff_comp] at hτ
        exact hτ
      have hτK : τ ≤ reOff (fun _ => 0) (addF H1 (addF g g')) A0 k0 := by
        have := reOff_mono H1 (addF g g') A0 hsK
        rw [reOff_zero_comp] at this
        omega
      have hGL' : GC A0 (addF H1 (addF g g')) τ b' L :=
        GC_ins_low hSA hfG (fun s' hs' => le_trans hτK (hKG s' hs')) hGL
      have hY := h2' (addF g g') b' (by omega) τ L h1τ hτ1 hL hGL'
      have hRw : ∀ w ∈ ws, Fr w.2 ∧ Hd w.2 ∧ LowC (w.1 + reOff (fun _ => 0) H1 A0 k0) w.2 :=
        fun w hw => (hR0 w hw).2
      have hC3 := FarCA_relift hC hRw (addF g g')
      have hFrY : Fr (reliftX b' H1 (addF g g') A0 (mlift P1 b1 (b' - b1)) ++
          shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) :=
        Fr_append (Fr_reliftX (Fr_mlift hP1Fr _ _) _ _ _ _) (Fr_shift_node _ _ _)
      have hR3 := RawWsA_snoc (RawWsA_relWs (RawWsA_mono (show bb ≤ b' by omega) hR0) (addF g g'))
        (show RawWA A0 k0 (addF H1 (addF g g')) b' (b', reliftX b' H1 (addF g g') A0
          (mlift P1 b1 (b' - b1)) ++ shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 L)) from ⟨le_rfl, hFrY, hY.1, hY.2.1⟩)
      have e0 : ∀ a ∈ A0, addF f g' a = addF (addF H1 (addF g g')) (fun _ => 0) a := fun a ha => by
        rw [addF_zero]; exact hfG a ha
      have := hY.2.2 b0 _ hC3 (fun _ => 0) S o (addF f g') b' e0 (by omega) hR3 hSA hA hA1 ho
        (by rw [addF_zero]; exact hKG) (by rw [addF_zero]; exact hKoG)
      rw [relWs_zero, farW_snoc] at this
      dsimp only at this
      have eY : fwW b' (b' + liftOff (addF f g') (S ++ A0) o + 1) b'
            (reliftX b' H1 (addF g g') A0 (mlift P1 b1 (b' - b1)) ++
              shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L))
          = fwW b' (b' + liftOff (addF f g') (S ++ A0) o + 1) b1 (reliftX b1 H1 (addF g g') A0 P1) ++
            shiftr01 d 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
        unfold fwW
        rw [Nat.sub_self, mlift_zero, mlift_reliftX, show b1 + (b' - b1) = b' by omega,
          ← List.cons_append, shiftr01_append0, shiftr01_add0, show d - 1 + 1 = d by omega,
          List.cons_append]
      rw [eY] at this
      rw [farW_snoc, List.append_assoc, show d + 1 - 1 = d by omega]
      exact this

/-- ★ RA は錨の列 A0・上限 k0 の文脈の族。 -/
theorem RA_ctx {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0) :
    CtxP (GC A0) A0 k0 (RA A0 k0) := fun H =>
  ⟨RA_ax hA01 hk1 H, fun _ _ _ hH h => RA_congr hH h, fun g _ _ _ h => RA_lift h g,
    fun _ hs2 hs => FarP_RA hA01 hs2 hs⟩

/-- ★ 錨つきの中身に、子の級 GC A0 H τ の並びを持つ節点を置く。 -/
theorem RA_node {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0)
    (hAk : ∀ a ∈ A0, a < k0) {H : ℕ → ℕ} {u τ : ℕ} {X L : TrioSeq} (hX : Fr X)
    (h : RA A0 k0 H u X) (hL : GC A0 H τ u L) (hτ : τ ≤ liftOff H A0 k0) :
    RA A0 k0 H u (X ++ ((1, u + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
  R_child (RA_ctx hA01 hk1) hAk hX h hL hτ

end HaF
end TRIO
