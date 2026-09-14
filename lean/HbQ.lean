/-
HbQ.lean: F のタイごとに荷の子を持つ遠い語の錨つきの族の核（HbO の写し、頭は FTL0）。

    FarCA0 A0 k0 h b0 ws := ∀ g S o f b, 条件（HbE.FarCAn と同じ）→
      GpT (S ++ A0) o f b (farW0 b r (relWs0 A0 h g ws))      （r = b + liftOff f (S ++ A0) o + 1）
-/
import HbP

namespace TRIO
namespace HbQ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HbD HbM HbP

def FarCA0 (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b0 : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    Prop :=
  ∀ (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), (∀ a ∈ A0, f a = addF h g a) →
    b0 ≤ b → RawWsA0 A0 k0 h b ws → (∀ s ∈ S, ∀ a ∈ A0, a < s) → (∀ a ∈ S ++ A0, a < o) →
    (∀ a ∈ S ++ A0, 1 ≤ a) → 1 ≤ o →
    (∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) →
    reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftOff f (S ++ A0) o →
    GpT (S ++ A0) o f b (farW0 b (b + liftOff f (S ++ A0) o + 1) (relWs0 A0 h g ws))

theorem FarCA0_nil (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b0 : ℕ) : FarCA0 A0 k0 h b0 [] := by
  intro g S o f b _ _ _ _ hA hA1 ho _ _
  rw [show farW0 b (b + liftOff f (S ++ A0) o + 1) (relWs0 A0 h g []) = [] from rfl]
  rcases Nat.lt_or_ge o 2 with h2 | h2
  · have ho1 : o = 1 := by omega
    subst ho1
    have hA0 : S ++ A0 = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => by have := hA a ha; have := hA1 a ha; omega)
    rw [hA0]
    exact GpT_nil1 f b
  · exact GpT_nil hA h2 f b

theorem farWA0_PVP {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)}
    (hC : FarCA0 A0 k0 h b0 ws) (g : ℕ → ℕ) {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) {b : ℕ} (hb : b0 ≤ b) (hR : RawWsA0 A0 k0 h b ws)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (hA : ∀ a ∈ S ++ A0, a < o) (hA1 : ∀ a ∈ S ++ A0, 1 ≤ a)
    (ho : 1 ≤ o) (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s)
    (hKo : reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftOff f (S ++ A0) o) :
    PVP (S ++ A0) o f b (farW0 b (b + liftOff f (S ++ A0) o + 1) (relWs0 A0 h g ws)) := by
  intro t
  rw [mlift_farW0_highk
    (show b + reOff (fun _ => 0) (addF h g) A0 k0 ≤ b + liftOff f (S ++ A0) o by omega)
    (show b + liftOff f (S ++ A0) o < b + liftOff f (S ++ A0) o + 1 by omega) t _
    (RawWsk0_relWs0 hR g)]
  have := hC g S (o + t) f b hf hb hR hSA (fun a ha => by have := hA a ha; omega) hA1 (by omega)
    hK (by rw [liftOff_add_t hA]; omega)
  rwa [liftOff_add_t hA,
    show b + (liftOff f (S ++ A0) o + t) + 1 = b + liftOff f (S ++ A0) o + 1 + t by omega] at this

/-! ## 潰れの塔 -/

noncomputable def towW0 (b : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) (r : ℕ) : ℕ → TrioSeq
  | 0 => farW0 b r ws ++ [((1, r, 1) : ℕ × ℕ × ℕ)]
  | m + 1 => farW0 b r ws ++ ((1, r, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towW0 b ws (r + 1) m))

theorem Fr_towW0 (b : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : ∀ m r, Fr (towW0 b ws r m)
  | 0, r => by rw [towW0]; exact Fr_append (Fr_farW0 _ _ ws) (GzF.Fr_single le_rfl _ _)
  | m + 1, r => by rw [towW0]; exact Fr_append (Fr_farW0 _ _ ws) (Fr_letter _ _)

theorem towW0_GpT {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} (hC : FarCA0 A0 k0 h b0 ws) (g : ℕ → ℕ) :
    ∀ (m : ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), (∀ a ∈ A0, f a = addF h g a) →
    b0 ≤ b → RawWsA0 A0 k0 h b ws → (∀ s ∈ S, ∀ a ∈ A0, a < s) → (∀ a ∈ S ++ A0, a < o) →
    (∀ a ∈ S ++ A0, 1 ≤ a) → 1 ≤ o →
    (∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) →
    reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftOff f (S ++ A0) o →
    GpT (S ++ A0) o f b (towW0 b (relWs0 A0 h g ws) (b + liftOff f (S ++ A0) o + 1) m)
  | 0, S, o, f, b, hf, hb, hR, hSA, hA, hA1, ho, hK, hKo => by
      rw [towW0]
      exact PVP_to_GpT (PVP_snocz hA hA1 ho (Fr_farW0 _ _ _)
        (farWA0_PVP hC g hf hb hR hSA hA hA1 ho hK hKo))
  | m + 1, S, o, f, b, hf, hb, hR, hSA, hA, hA1, ho, hK, hKo => by
      have hAo' : ∀ a ∈ o :: (S ++ A0), a < o + 1 := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · omega
        · have := hA a ha; omega
      have hA1' : ∀ a ∈ o :: (S ++ A0), 1 ≤ a := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact ho
        · exact hA1 a ha
      obtain ⟨H, hH⟩ : ∃ H : ℕ → ℕ, H = upF o 0 f := ⟨_, rfl⟩
      have hHo : H o = 0 := by rw [hH]; simp [upF]
      have hHA : ∀ a ∈ S ++ A0, H a = f a := by rw [hH]; exact upF_low hA 0 f
      have e1 : liftOff H (o :: (S ++ A0)) (o + 1) = liftOff f (S ++ A0) o + 1 := by
        rw [sumOn_liftOff hAo', sumOn_liftOff hA]
        simp only [sumOn, hHo, sumOn_congr hHA]
        omega
      have eo : liftOff H (S ++ A0) o = liftOff f (S ++ A0) o := by
        rw [sumOn_liftOff hA, sumOn_liftOff hA, sumOn_congr hHA]
      have hSA' : ∀ s ∈ o :: S, ∀ a ∈ A0, a < s := by
        intro s hs a ha
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact hA a (List.mem_append_right _ ha)
        · exact hSA s hs a ha
      have hf' : ∀ a ∈ A0, H a = addF h g a := fun a ha => by
        rw [hHA a (List.mem_append_right _ ha)]; exact hf a ha
      have hK' : ∀ s ∈ o :: S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal H ((o :: S) ++ A0) s := by
        intro s hs
        simp only [List.mem_cons] at hs
        rw [List.cons_append]
        rcases hs with hs | hs
        · rw [hs, liftVal_cons_top hA, hHo, Nat.add_zero, eo]; exact hKo
        · rw [liftVal_cons_low hA (List.mem_append_left _ hs)]
          have e : liftVal H (S ++ A0) s = liftVal f (S ++ A0) s := by
            unfold liftVal; rw [stepSum_congr 0 (s + 1) hHA]
          rw [e]; exact hK s hs
      have hL := towW0_GpT hC g m (o :: S) (o + 1) H b hf' hb hR hSA' hAo' hA1' (by omega) hK'
        (by rw [List.cons_append, e1]; omega)
      rw [List.cons_append, e1,
        show b + (liftOff f (S ++ A0) o + 1) + 1 = b + liftOff f (S ++ A0) o + 1 + 1 by omega] at hL
      have hGC : GC (o :: (S ++ A0)) H (liftOff f (S ++ A0) o + 1) b
          (towW0 b (relWs0 A0 h g ws) (b + liftOff f (S ++ A0) o + 1 + 1) m) := by
        rw [← e1, GC_slot hAo']; exact hL
      have hRL := R_child (CtxP_RLC hA hA1 ho) hAo' Fr_nil (RLC_nil hA hA1 ho H b) hGC
        (le_of_eq e1.symm)
      have h1 := hRL (fun _ => 0) b le_rfl
      rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero, hHo, Nat.add_zero,
        List.nil_append] at h1
      have hLC := LC1_congr hA hHA h1
      have := hLC _ (Fr_farW0 _ _ _) (farWA0_PVP hC g hf hb hR hSA hA hA1 ho hK hKo)
      rw [show b + (liftOff f (S ++ A0) o + 1) = b + liftOff f (S ++ A0) o + 1 by omega] at this
      rw [towW0]
      exact PVP_to_GpT this

theorem mlift_farW0t {k b c : ℕ} (hbc : b + k ≤ c) {ws : List (List TrioSeq × ℕ × TrioSeq)}
    (hR : RawWsk0 k b ws) (j : ℕ) :
    mlift (farW0 b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j
      = farW0 b (c + 1 + j) ws ++ [((1, c + 1 + j, 1) : ℕ × ℕ × ℕ)] := by
  rw [mlift_app (Fr_farW0 _ _ ws) (fun _ => rfl), mlift_farW0_highk hbc (by omega) j ws hR,
    mlift_one (show c < c + 1 by omega)]

theorem farW0_flat {k b : ℕ} {ws : List (List TrioSeq × ℕ × TrioSeq)} (hR : RawWsk0 k b ws) :
    ∀ m c, b + k ≤ c → (List.range (m + 1)).flatMap (fun j =>
      shiftr01 (j * 2) 0 (((0, c + j, 0) : ℕ × ℕ × ℕ) ::
        mlift (farW0 b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j))
      = ((0, c, 0) : ℕ × ℕ × ℕ) :: towW0 b ws (c + 1) m
  | 0, c, hc => by simp [mlift_zero, towW0]
  | m + 1, c, hc => by
      rw [GzF.flatMap_range_cons _ (m + 1)]
      have e : ∀ j, shiftr01 ((j + 1) * 2) 0 (((0, c + (j + 1), 0) : ℕ × ℕ × ℕ) ::
          mlift (farW0 b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c (j + 1))
          = shiftr01 2 0 (shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (farW0 b (c + 1 + 1) ws ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)) := by
        intro j
        rw [mlift_farW0t hc hR, mlift_farW0t (c := c + 1) (by omega) hR, GzF.shift_shift,
          show c + (j + 1) = c + 1 + j by omega, show c + 1 + (j + 1) = c + 1 + 1 + j by omega,
          show (j + 1) * 2 = j * 2 + 2 by omega]
      simp only [e]
      rw [← GzF.shift_flatMap 2 (fun j => shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (farW0 b (c + 1 + 1) ws ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)),
        farW0_flat hR m (c + 1) (by omega)]
      have eT : shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towW0 b ws (c + 1 + 1) m))
          = shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towW0 b ws (c + 1 + 1) m) := by
        rw [show shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towW0 b ws (c + 1 + 1) m)
            = shiftr01 (1 + 1) 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towW0 b ws (c + 1 + 1) m) from rfl,
          ← GzF.shift_shift]
        rfl
      rw [show towW0 b ws (c + 1) (m + 1) = farW0 b (c + 1) ws ++
          ((1, c + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (towW0 b ws (c + 1 + 1) m)) from rfl, eT]
      simp [mlift_zero]

theorem farW0_P (b c : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) :
    Fr (farW0 b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ∧
    coneV ((farW0 b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) c
      (farW0 b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]).length := by
  refine ⟨Fr_append (Fr_farW0 _ _ ws) (GzF.Fr_single le_rfl _ _), ?_⟩
  have hbot : BotGe (farW0 b (c + 1) ws ++ ((1, c + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 [])
      (0 + 1 + 1) (c + 1) :=
    BotGe_node (Fr_farW0 _ _ ws) le_rfl (BotGe_top Fr_nil _)
  have := coneV_of_BotGe (z := 1) hbot (show c < c + 1 by omega)
  simpa [shiftr01] using this

/-- ★ 遠い語の並びの潰れ（中身も F のタイもない遠い語を足す）。 -/
theorem farWA0_collapse {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 c0 : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} (hC : FarCA0 A0 k0 h b0 ws) :
    FarCA0 A0 k0 h b0 (ws ++ [([], c0, [])]) := by
  intro g S o f b hf hb hR hSA hA hA1 ho hK hKo
  have hR0 : RawWsA0 A0 k0 h b ws := fun w hw => hR w (List.mem_append_left _ hw)
  refine GpT_intro hA (fun R hR' g' => ?_)
  rw [reliftX_farW0A hA hSA b hf g' hK _ hR]
  obtain ⟨F, hF⟩ : ∃ F, F = addF f g' := ⟨_, rfl⟩
  have hfF : ∀ a ∈ A0, F a = addF h (addF g g') a := fun a ha => by
    have := hf a ha
    rw [hF]; simp only [addF] at this ⊢; omega
  have hKg := reOff_zero_le_sum (addF h g) g' A0 k0
  have eaddF : addF (addF h g) g' = addF h (addF g g') := by funext a; simp [addF]; omega
  rw [eaddF] at hKg
  have hKF : ∀ s ∈ S, reOff (fun _ => 0) (addF h (addF g g')) A0 k0 ≤ liftVal F (S ++ A0) s := by
    intro s hs
    rw [hF, liftVal_add]
    have h1 := hK s hs
    have h2 : sumOn g' A0 ≤ stepSum 0 g' (S ++ A0) (s + 1) := by
      rw [stepSum_append, stepSum_all 0 (s + 1) g' (A := A0)
        (fun a ha => by have := hSA s hs a ha; omega)]
      omega
    omega
  have hKoF : reOff (fun _ => 0) (addF h (addF g g')) A0 k0 ≤ liftOff F (S ++ A0) o := by
    rw [hF, liftOff_addF hA, sumOn_append]; omega
  obtain ⟨kk, hkk⟩ : ∃ kk, kk = liftOff F (S ++ A0) o := ⟨_, rfl⟩
  rw [← hF, ← hkk]
  have hk1 : o ≤ kk := by rw [hkk]; unfold liftOff; omega
  have hkkk : reOff (fun _ => 0) (addF h (addF g g')) A0 k0 ≤ kk := by rw [hkk]; exact hKoF
  intro u' hu X hX hRX
  have ers : relWs0 A0 h (addF g g') (ws ++ [([], c0, [])])
      = relWs0 A0 h (addF g g') ws ++ [([], c0, [])] := by
    simp [relWs0, reliftX, slift_nil]
  have hRk : RawWsk0 (reOff (fun _ => 0) (addF h (addF g g')) A0 k0) b
      (relWs0 A0 h (addF g g') ws ++ [([], c0, [])]) := by
    have := RawWsk0_relWs0 hR (addF g g'); rwa [ers] at this
  rw [ers]
  obtain ⟨ws', hws'⟩ : ∃ ws', ws' = relWs0 A0 h (addF g g') ws := ⟨_, rfl⟩
  rw [← hws'] at hRk ⊢
  rw [mlift_farW0_basek (show b < b + kk + 1 by omega) (u' - b) _ hRk,
    show b + kk + 1 + (u' - b) = u' + kk + 1 by omega, show b + (u' - b) = u' by omega, farW0_snoc]
  have hRu : RawWsk0 (reOff (fun _ => 0) (addF h (addF g g')) A0 k0) u' ws' := by
    rw [hws']; exact RawWsk0_mono hu (RawWsk0_relWs0 hR0 (addF g g'))
  obtain ⟨c, hc⟩ : ∃ c, c = u' + kk := ⟨_, rfl⟩
  rw [← hc]
  have hbc : u' + reOff (fun _ => 0) (addF h (addF g g')) A0 k0 ≤ c := by rw [hc]; omega
  obtain ⟨hP, hcone⟩ := farW0_P u' c ws'
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq, U0 = ((0, c, 0) : ℕ × ℕ × ℕ) ::
      ((farW0 u' (c + 1) ws' ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) :=
    ⟨_, rfl⟩
  have eU : ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (farW0 u' (c + 1) ws' ++
      fwH u' (c + 1) (FTL0 (c + 1) (([] : List TrioSeq), c0, ([] : TrioSeq)).1)
        (([] : List TrioSeq), c0, ([] : TrioSeq)).2.1 (([] : List TrioSeq), c0, ([] : TrioSeq)).2.2)
      = shiftr01 1 0 U0 := by
    rw [hU0]; simp [shiftr01, fwH, FTL0, mlift_nil]
  rw [eU]
  have hlen : 2 ≤ U0.length := by
    rw [hU0]; simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]; omega
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom hP (show 1 ≤ 2 by omega) hcone
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h' | h'
    · exfalso
      have hl : U0.length - 1 = (((0, c, 0) : ℕ × ℕ × ℕ) ::
          (farW0 u' (c + 1) ws' ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])).length + 0 := by
        rw [hU0]; simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]; omega
      rw [hl] at h'
      unfold lev at h'
      rw [hU0, show ((0, c, 0) : ℕ × ℕ × ℕ) :: ((farW0 u' (c + 1) ws' ++
          [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)])
        = (((0, c, 0) : ℕ × ℕ × ℕ) :: (farW0 u' (c + 1) ws' ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])) ++
          [((2, c + 1, 1) : ℕ × ℕ × ℕ)] by simp,
        entry_append_right, entry_append_right] at h'
      simp [entry] at h'
    · exact h'
  refine (hR' F).1.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
    (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp only [List.length_cons]; omega), hU0]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] U0 1 m hlen hpV
  simp only [List.nil_append] at eO
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [eO, hU0, oper_zcone hP (show 1 ≤ 2 by omega) hcone (m' + 1), farW0_flat hRu m' c hbc]
  have eS : shiftr01 1 0 (((0, c, 0) : ℕ × ℕ × ℕ) :: towW0 u' ws' (c + 1) m')
      = ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towW0 u' ws' (c + 1) m') := by
    simp [shiftr01]
  rw [eS]
  have hD := towW0_GpT hC (addF g g') m' S o F u' hfF (by omega) (RawWsA0_mono hu hR0) hSA hA hA1
    ho hKF hKoF
  rw [← hkk, ← hc, ← hws'] at hD
  have h' := GpT_elim0 hD hR'
  rw [← hkk] at h'
  have := h' u' le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero, ← hc] at this

end HbQ
end TRIO
