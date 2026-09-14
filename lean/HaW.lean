/-
HaW.lean: 接頭辞 Q（HaN.TowP）つきの錨つきの中身の遠い語の族の第 1 部（HaC・HaR の写し）。

    FarCAQ Q A0 k0 h b0 ws := ∀ g S o f b, 条件（HaC.FarCA と同じ）→
      GpT (S ++ A0) o f b (Q r ++ farW b r (relWs A0 h g ws))      （r = b + liftOff f (S ++ A0) o + 1）

接頭辞は TowP の持ち上げ（lift）・再持ち上げ（relift）で遠い語と一緒に動き、潰れの塔の各段にそのまま入る。
-/
import HaN

namespace TRIO
namespace HaW

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaN

variable {Q : ℕ → TrioSeq}

/-! ## 接頭辞と遠い語 -/

theorem Fr_QW (hQ : TowP Q) (b r : ℕ) (ws : List (ℕ × TrioSeq)) : Fr (Q r ++ farW b r ws) :=
  Fr_append (hQ.fr r) (Fr_farW b r ws)

theorem mlift_QW_high (hQ : TowP Q) {k b v r : ℕ} (hv : b + k ≤ v) (hvr : v < r) (t : ℕ)
    {ws : List (ℕ × TrioSeq)} (hR : RawWsk k b ws) :
    mlift (Q r ++ farW b r ws) v t = Q (r + t) ++ farW b (r + t) ws := by
  rw [mlift_app (hQ.fr r) (Hd_farW b r ws), hQ.lift v r t hvr, mlift_farW_highk hv hvr t ws hR]

theorem mlift_QW_base (hQ : TowP Q) {k b r : ℕ} (hbr : b < r) (t : ℕ) {ws : List (ℕ × TrioSeq)}
    (hR : RawWsk k b ws) :
    mlift (Q r ++ farW b r ws) b t = Q (r + t) ++ farW (b + t) (r + t) ws := by
  rw [mlift_app (hQ.fr r) (Hd_farW b r ws), hQ.lift b r t hbr, mlift_farW_basek hbr t ws hR]

theorem reliftX_QWA (hQ : TowP Q) {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {k0 : ℕ} {h g f : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) (g' : ℕ → ℕ)
    (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s)
    (ws : List (ℕ × TrioSeq)) (hR : RawWsA A0 k0 h b ws) :
    reliftX b f g' (S ++ A0) (Q (b + liftOff f (S ++ A0) o + 1) ++
      farW b (b + liftOff f (S ++ A0) o + 1) (relWs A0 h g ws))
      = Q (b + liftOff (addF f g') (S ++ A0) o + 1) ++
        farW b (b + liftOff (addF f g') (S ++ A0) o + 1) (relWs A0 h (addF g g') ws) := by
  rw [reliftX_app (hQ.fr _) (Hd_farW _ _ _), hQ.relift (S ++ A0) o hA b f g',
    reliftX_farWA hA hSA b hf g' hK ws hR]

/-! ## 上に錨を足した全ての級（条件つき）で GpT -/

def FarCAQ (Q : ℕ → TrioSeq) (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b0 : ℕ)
    (ws : List (ℕ × TrioSeq)) : Prop :=
  ∀ (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), (∀ a ∈ A0, f a = addF h g a) →
    b0 ≤ b → RawWsA A0 k0 h b ws → (∀ s ∈ S, ∀ a ∈ A0, a < s) → (∀ a ∈ S ++ A0, a < o) →
    (∀ a ∈ S ++ A0, 1 ≤ a) → 1 ≤ o →
    (∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) →
    reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftOff f (S ++ A0) o →
    GpT (S ++ A0) o f b (Q (b + liftOff f (S ++ A0) o + 1) ++
      farW b (b + liftOff f (S ++ A0) o + 1) (relWs A0 h g ws))

theorem FarCAQ_nil (hQ : TowP Q) (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b0 : ℕ) :
    FarCAQ Q A0 k0 h b0 [] := by
  intro g S o f b _ _ _ _ hA hA1 ho _ _
  rw [show farW b (b + liftOff f (S ++ A0) o + 1) (relWs A0 h g []) = [] from rfl, List.append_nil]
  exact hQ.good (S ++ A0) o f b hA hA1 ho

theorem farWAQ_PVP (hQ : TowP Q) {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 : ℕ}
    {ws : List (ℕ × TrioSeq)} (hC : FarCAQ Q A0 k0 h b0 ws) (g : ℕ → ℕ) {S : List ℕ} {o : ℕ}
    {f : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = addF h g a) {b : ℕ} (hb : b0 ≤ b) (hR : RawWsA A0 k0 h b ws)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (hA : ∀ a ∈ S ++ A0, a < o) (hA1 : ∀ a ∈ S ++ A0, 1 ≤ a)
    (ho : 1 ≤ o) (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s)
    (hKo : reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftOff f (S ++ A0) o) :
    PVP (S ++ A0) o f b (Q (b + liftOff f (S ++ A0) o + 1) ++
      farW b (b + liftOff f (S ++ A0) o + 1) (relWs A0 h g ws)) := by
  intro t
  rw [mlift_QW_high hQ
    (show b + reOff (fun _ => 0) (addF h g) A0 k0 ≤ b + liftOff f (S ++ A0) o by omega)
    (show b + liftOff f (S ++ A0) o < b + liftOff f (S ++ A0) o + 1 by omega) t
    (RawWsk_relWs hR g)]
  have := hC g S (o + t) f b hf hb hR hSA (fun a ha => by have := hA a ha; omega) hA1 (by omega)
    hK (by rw [liftOff_add_t hA]; omega)
  rwa [liftOff_add_t hA,
    show b + (liftOff f (S ++ A0) o + t) + 1 = b + liftOff f (S ++ A0) o + 1 + t by omega] at this

/-! ## 潰れの塔 -/

noncomputable def towWAQ (Q : ℕ → TrioSeq) (b : ℕ) (ws : List (ℕ × TrioSeq)) (r : ℕ) : ℕ → TrioSeq
  | 0 => (Q r ++ farW b r ws) ++ [((1, r, 1) : ℕ × ℕ × ℕ)]
  | m + 1 => (Q r ++ farW b r ws) ++ ((1, r, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towWAQ Q b ws (r + 1) m))

theorem towWAQ_GpT (hQ : TowP Q) {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 : ℕ}
    {ws : List (ℕ × TrioSeq)} (hC : FarCAQ Q A0 k0 h b0 ws) (g : ℕ → ℕ) :
    ∀ (m : ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), (∀ a ∈ A0, f a = addF h g a) →
    b0 ≤ b → RawWsA A0 k0 h b ws → (∀ s ∈ S, ∀ a ∈ A0, a < s) → (∀ a ∈ S ++ A0, a < o) →
    (∀ a ∈ S ++ A0, 1 ≤ a) → 1 ≤ o →
    (∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) →
    reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftOff f (S ++ A0) o →
    GpT (S ++ A0) o f b (towWAQ Q b (relWs A0 h g ws) (b + liftOff f (S ++ A0) o + 1) m)
  | 0, S, o, f, b, hf, hb, hR, hSA, hA, hA1, ho, hK, hKo => by
      rw [towWAQ]
      exact PVP_to_GpT (PVP_snocz hA hA1 ho (Fr_QW hQ _ _ _)
        (farWAQ_PVP hQ hC g hf hb hR hSA hA hA1 ho hK hKo))
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
      have hL := towWAQ_GpT hQ hC g m (o :: S) (o + 1) H b hf' hb hR hSA' hAo' hA1' (by omega) hK'
        (by rw [List.cons_append, e1]; omega)
      rw [List.cons_append, e1,
        show b + (liftOff f (S ++ A0) o + 1) + 1 = b + liftOff f (S ++ A0) o + 1 + 1 by omega] at hL
      have hGC : GC (o :: (S ++ A0)) H (liftOff f (S ++ A0) o + 1) b
          (towWAQ Q b (relWs A0 h g ws) (b + liftOff f (S ++ A0) o + 1 + 1) m) := by
        rw [← e1, GC_slot hAo']; exact hL
      have hRL := R_child (CtxP_RLC hA hA1 ho) hAo' Fr_nil (RLC_nil hA hA1 ho H b) hGC
        (le_of_eq e1.symm)
      have h1 := hRL (fun _ => 0) b le_rfl
      rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero, hHo, Nat.add_zero,
        List.nil_append] at h1
      have hLC := LC1_congr hA hHA h1
      have := hLC _ (Fr_QW hQ _ _ _) (farWAQ_PVP hQ hC g hf hb hR hSA hA hA1 ho hK hKo)
      rw [show b + (liftOff f (S ++ A0) o + 1) = b + liftOff f (S ++ A0) o + 1 by omega] at this
      rw [towWAQ]
      exact PVP_to_GpT this

theorem mlift_QWt (hQ : TowP Q) {k b c : ℕ} (hbc : b + k ≤ c) {ws : List (ℕ × TrioSeq)}
    (hR : RawWsk k b ws) (j : ℕ) :
    mlift ((Q (c + 1) ++ farW b (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j
      = (Q (c + 1 + j) ++ farW b (c + 1 + j) ws) ++ [((1, c + 1 + j, 1) : ℕ × ℕ × ℕ)] := by
  rw [mlift_app (Fr_QW hQ _ _ ws) (fun _ => rfl), mlift_QW_high hQ hbc (by omega) j hR,
    mlift_one (show c < c + 1 by omega)]

theorem farWAQ_flat (hQ : TowP Q) {k b : ℕ} {ws : List (ℕ × TrioSeq)} (hR : RawWsk k b ws) :
    ∀ m c, b + k ≤ c → (List.range (m + 1)).flatMap (fun j =>
      shiftr01 (j * 2) 0 (((0, c + j, 0) : ℕ × ℕ × ℕ) ::
        mlift ((Q (c + 1) ++ farW b (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j))
      = ((0, c, 0) : ℕ × ℕ × ℕ) :: towWAQ Q b ws (c + 1) m
  | 0, c, hc => by simp [mlift_zero, towWAQ]
  | m + 1, c, hc => by
      rw [GzF.flatMap_range_cons _ (m + 1)]
      have e : ∀ j, shiftr01 ((j + 1) * 2) 0 (((0, c + (j + 1), 0) : ℕ × ℕ × ℕ) ::
          mlift ((Q (c + 1) ++ farW b (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c (j + 1))
          = shiftr01 2 0 (shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift ((Q (c + 1 + 1) ++ farW b (c + 1 + 1) ws) ++
              [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)) := by
        intro j
        rw [mlift_QWt hQ hc hR, mlift_QWt hQ (c := c + 1) (by omega) hR, GzF.shift_shift,
          show c + (j + 1) = c + 1 + j by omega, show c + 1 + (j + 1) = c + 1 + 1 + j by omega,
          show (j + 1) * 2 = j * 2 + 2 by omega]
      simp only [e]
      rw [← GzF.shift_flatMap 2 (fun j => shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift ((Q (c + 1 + 1) ++ farW b (c + 1 + 1) ws) ++
              [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)),
        farWAQ_flat hQ hR m (c + 1) (by omega)]
      have eT : shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towWAQ Q b ws (c + 1 + 1) m))
          = shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towWAQ Q b ws (c + 1 + 1) m) := by
        rw [show shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towWAQ Q b ws (c + 1 + 1) m)
            = shiftr01 (1 + 1) 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towWAQ Q b ws (c + 1 + 1) m) from rfl,
          ← GzF.shift_shift]
        rfl
      rw [show towWAQ Q b ws (c + 1) (m + 1) = (Q (c + 1) ++ farW b (c + 1) ws) ++
          ((1, c + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (towWAQ Q b ws (c + 1 + 1) m)) from rfl, eT]
      simp [mlift_zero]

theorem farWAQ_P (hQ : TowP Q) (b c : ℕ) (ws : List (ℕ × TrioSeq)) :
    Fr ((Q (c + 1) ++ farW b (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ∧
    coneV (((Q (c + 1) ++ farW b (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++
      [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) c
      ((Q (c + 1) ++ farW b (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]).length := by
  refine ⟨Fr_append (Fr_QW hQ _ _ ws) (GzF.Fr_single le_rfl _ _), ?_⟩
  have hbot : BotGe ((Q (c + 1) ++ farW b (c + 1) ws) ++ ((1, c + 1, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 []) (0 + 1 + 1) (c + 1) :=
    BotGe_node (Fr_QW hQ _ _ ws) le_rfl (BotGe_top Fr_nil _)
  have := coneV_of_BotGe (z := 1) hbot (show c < c + 1 by omega)
  simpa [shiftr01] using this

/-- ★ 接頭辞つきの遠い語の並びの潰れ（中身なしの遠い語を足す）。 -/
theorem farWAQ_collapse (hQ : TowP Q) {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b0 c0 : ℕ}
    {ws : List (ℕ × TrioSeq)} (hC : FarCAQ Q A0 k0 h b0 ws) :
    FarCAQ Q A0 k0 h b0 (ws ++ [(c0, [])]) := by
  intro g S o f b hf hb hR hSA hA hA1 ho hK hKo
  have hR0 : RawWsA A0 k0 h b ws := fun w hw => hR w (List.mem_append_left _ hw)
  refine GpT_intro hA (fun R hR' g' => ?_)
  rw [reliftX_QWA hQ hA hSA b hf g' hK _ hR]
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
  have ers : relWs A0 h (addF g g') (ws ++ [(c0, [])]) = relWs A0 h (addF g g') ws ++ [(c0, [])] := by
    simp [relWs, reliftX, slift_nil]
  have hRk : RawWsk (reOff (fun _ => 0) (addF h (addF g g')) A0 k0) b
      (relWs A0 h (addF g g') ws ++ [(c0, [])]) := by
    have := RawWsk_relWs hR (addF g g'); rwa [ers] at this
  rw [ers]
  obtain ⟨ws', hws'⟩ : ∃ ws', ws' = relWs A0 h (addF g g') ws := ⟨_, rfl⟩
  rw [← hws'] at hRk ⊢
  rw [mlift_QW_base hQ (show b < b + kk + 1 by omega) (u' - b) hRk,
    show b + kk + 1 + (u' - b) = u' + kk + 1 by omega, show b + (u' - b) = u' by omega, farW_snoc]
  have hRu : RawWsk (reOff (fun _ => 0) (addF h (addF g g')) A0 k0) u' ws' := by
    rw [hws']; exact RawWsk_mono hu (RawWsk_relWs hR0 (addF g g'))
  obtain ⟨c, hc⟩ : ∃ c, c = u' + kk := ⟨_, rfl⟩
  rw [← hc]
  have hbc : u' + reOff (fun _ => 0) (addF h (addF g g')) A0 k0 ≤ c := by rw [hc]; omega
  obtain ⟨hP, hcone⟩ := farWAQ_P hQ u' c ws'
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq, U0 = ((0, c, 0) : ℕ × ℕ × ℕ) ::
      (((Q (c + 1) ++ farW u' (c + 1) ws') ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++
        [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) := ⟨_, rfl⟩
  have eU : ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (Q (c + 1) ++ (farW u' (c + 1) ws' ++
      fwW u' (c + 1) c0 [])) = shiftr01 1 0 U0 := by
    rw [hU0]; simp [shiftr01, fwW, mlift_nil]
  rw [eU]
  have hlen : 2 ≤ U0.length := by
    rw [hU0]; simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]; omega
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom hP (show 1 ≤ 2 by omega) hcone
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h' | h'
    · exfalso
      have hl : U0.length - 1 = (((0, c, 0) : ℕ × ℕ × ℕ) ::
          ((Q (c + 1) ++ farW u' (c + 1) ws') ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])).length + 0 := by
        rw [hU0]; simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]; omega
      rw [hl] at h'
      unfold lev at h'
      rw [hU0, show ((0, c, 0) : ℕ × ℕ × ℕ) :: (((Q (c + 1) ++ farW u' (c + 1) ws') ++
          [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)])
        = (((0, c, 0) : ℕ × ℕ × ℕ) :: ((Q (c + 1) ++ farW u' (c + 1) ws') ++
          [((1, c + 1, 1) : ℕ × ℕ × ℕ)])) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)] by simp,
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
  rw [eO, hU0, oper_zcone hP (show 1 ≤ 2 by omega) hcone (m' + 1), farWAQ_flat hQ hRu m' c hbc]
  have eS : shiftr01 1 0 (((0, c, 0) : ℕ × ℕ × ℕ) :: towWAQ Q u' ws' (c + 1) m')
      = ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towWAQ Q u' ws' (c + 1) m') := by
    simp [shiftr01]
  rw [eS]
  have hD := towWAQ_GpT hQ hC (addF g g') m' S o F u' hfF (by omega) (RawWsA_mono hu hR0) hSA hA hA1
    ho hKF hKoF
  rw [← hkk, ← hc, ← hws'] at hD
  have h' := GpT_elim0 hD hR'
  rw [← hkk] at h'
  have := h' u' le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero, ← hc] at this

end HaW
end TRIO
