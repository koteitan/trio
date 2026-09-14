/-
HaA.lean: 錨の列 A・段 o の節点の子の並びで、遠い字と低い列のあとの、行 1 が b+s の子のない節点。
条件: 2 ≤ s ≤ o、全ての錨 a で s ≤ a+1。中身は全ての k ≥ k0 で okWk k（k0 ≤ 錨、k0 ≤ o）。

FarP_GpT_ge（状態 0）。h2 の τ は τ < reOff 0 g A s = s + stepSum 0 g A s なので、
全ての錨 a（a ≥ s-1）で τ ≤ liftVal g A a。よって子の級は錨なしの GpT [] τ で、中身は k = max τ k0 の族に入る。
s ≤ o なので節点は t の持ち上げで動かず、語の述語（PVF）にもなる。
-/
import GzY

namespace TRIO
namespace HaA

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY

theorem reStep_zeroF (g : ℕ → ℕ) (A0 : List ℕ) (m : ℕ) : ∀ A : List ℕ,
    reStep 0 (fun _ => 0) g A0 A m = stepSum 0 g A m
  | [] => rfl
  | a :: A => by
      simp only [reStep, stepSum, liftVal_zeroF, reStep_zeroF g A0 m A]

theorem liftVal_zero_add (g : ℕ → ℕ) (A : List ℕ) (a : ℕ) :
    liftVal (addF (fun _ => 0) g) A a = a + stepSum 0 g A (a + 1) := by
  rw [liftVal_add, liftVal_zeroF]

theorem stepSum_le_sumOn (g : ℕ → ℕ) (m : ℕ) : ∀ A : List ℕ, stepSum 0 g A m ≤ sumOn g A
  | [] => le_rfl
  | a :: A => by
      have := stepSum_le_sumOn g m A
      simp only [stepSum, sumOn]
      split_ifs <;> omega

/-- ★ 錨の列 A・段 o の子の並びで、遠い字と低い列のあとの段 b+s の子のない節点（s ≤ 錨 + 1）。 -/
theorem GPF_farW_bot {A : List ℕ} {o b u s k0 : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (hs2 : 2 ≤ s) (hso : s ≤ o) (hsA : ∀ a ∈ A, s ≤ a + 1) (hk0 : 1 ≤ k0)
    (hk0A : ∀ a ∈ A, k0 ≤ a) (hk0o : k0 ≤ o) (hub : u ≤ b) {ws : List (ℕ × TrioSeq)}
    (hws : ∀ k, k0 ≤ k → OkWsk k b ws) {X : TrioSeq} (hX : ∀ k, k0 ≤ k → okWkF k u X) :
    GPF A o b (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++
      [((2, b + s, 0) : ℕ × ℕ × ℕ)]) := by
  have hlo : liftOff (fun _ => 0) A o = o := liftOff_zeroF A o
  have hFP := FarP_GpT_ge hA hA1 ho (f := fun _ => 0) hs2 (by rw [hlo]; exact hso)
  have hP : Fr (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) :=
    Fr_append (Fr_farW _ _ _) (Fr_fwW _ _ _ _)
  have hAk0 : ∀ a ∈ A, k0 ≤ liftVal (fun _ => 0) A a := fun a ha => by
    rw [liftVal_zeroF]; exact hk0A a ha
  have hs0 : ∀ b', b ≤ b' → OkWsk k0 b' (ws ++ [(u, X)]) := fun b' hb' =>
    OkWsk_snoc (le_trans hub hb') (hX k0 le_rfl) (OkWsk_mono hb' (hws k0 le_rfl))
  have eP : ∀ b', b ≤ b' → mlift (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) b (b' - b)
      = farW b' (b' + liftOff (fun _ => 0) A o + 1) (ws ++ [(u, X)]) := by
    intro b' hb'
    have := mlift_farW_basek (show b < b + o + 1 by omega) (b' - b) (ws ++ [(u, X)]) (hs0 b le_rfl).1
    rw [farW_snoc] at this
    rw [show b + (b' - b) = b' by omega, show b + o + 1 + (b' - b) = b' + o + 1 by omega] at this
    rw [hlo]; exact this
  have eR : ∀ (g : ℕ → ℕ) b', b ≤ b' →
      reliftX b' (fun _ => 0) g A (mlift (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) b (b' - b))
        = farW b' (b' + liftOff (addF (fun _ => 0) g) A o + 1) (ws ++ [(u, X)]) := by
    intro g b' hb'
    rw [eP b' hb']
    exact reliftX_farWk hA b' (fun _ => 0) g hAk0 _ (hs0 b' hb').1
  have hbot : BotGe (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X) (1 + 1) (b + s) := by
    unfold fwW
    exact BotGe_node (Fr_farW _ _ _) (by omega)
      (BotGe_top (Fr_FLW (Fr_mlift (hX k0 le_rfl).1 _ _)) _)
  refine ⟨?_, Fr_append hP (Fr_single (by omega) _ _)⟩
  refine hFP b _ 2 hP (by omega) hbot (fun g b' hb' => ?_) (fun g b' hb' τ L h1τ hτ hL hGL => ?_)
  · rw [eR g b' hb']
    exact GpT_farWskL hA hA1 ho (liftVal_ge_addF hAk0 g)
      (liftOff_ge_addF hA (by rw [hlo]; exact hk0o) g) (hs0 b' hb')
  · rw [eR g b' hb']
    have hro : reOff (fun _ => 0) g A s = s + stepSum 0 g A s := by
      unfold reOff; rw [reStep_zeroF]
    have hτ' : τ ≤ s - 1 + stepSum 0 g A s := by omega
    have hτA : ∀ a ∈ A, τ ≤ liftVal (addF (fun _ => 0) g) A a := fun a ha => by
      rw [liftVal_zero_add]
      have h1 := hsA a ha
      have h2 := stepSum_mono 0 g (show s ≤ a + 1 by omega) A
      omega
    have hτo : τ < liftOff (addF (fun _ => 0) g) A o := by
      rw [liftOff_addF hA, hlo]
      have h2 := stepSum_mono 0 g hso A
      have h3 := stepSum_le_sumOn g o A
      omega
    obtain ⟨k, hk⟩ : ∃ k, k = max τ k0 := ⟨_, rfl⟩
    have hk0k : k0 ≤ k := by rw [hk]; exact le_max_right _ _
    have hτk : τ ≤ k := by rw [hk]; exact le_max_left _ _
    have hk1 : 1 ≤ k := by omega
    have hAkG : ∀ a ∈ A, k ≤ liftVal (addF (fun _ => 0) g) A a := fun a ha => by
      rw [hk]
      refine max_le (hτA a ha) ?_
      rw [liftVal_zero_add]; have := hk0A a ha; omega
    have hkoG : k ≤ liftOff (addF (fun _ => 0) g) A o := by
      rw [hk]
      refine max_le (by omega) ?_
      rw [liftOff_addF hA, hlo]; omega
    have hGL' : GpT [] τ (addF (fun _ => 0) g) b' L := by
      simpa [GC, lowP_k hτA le_rfl, sumOn] using hGL
    have hGF : GPF [] τ b' L := ⟨GpT_congr (by simp) (fun a ha => by simp at ha) hGL', hL⟩
    have hX' := okWkF_node hk1 hτk (okWkF_lift hk1 (le_trans hub hb') (hX k hk0k)) hGF
    have hs := OkWsk_snoc le_rfl hX' (OkWsk_mono hb' (hws k hk0k))
    have e : farW b' (b' + liftOff (addF (fun _ => 0) g) A o + 1) (ws ++ [(u, X)]) ++
        shiftr01 (2 - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
        = farW b' (b' + liftOff (addF (fun _ => 0) g) A o + 1) (ws ++ [(b', mlift X u (b' - u) ++
            ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)]) := by
      rw [farW_snoc, farW_snoc, List.append_assoc]
      congr 1
      show fwW b' _ u X ++ _ = fwW b' _ b' _
      unfold fwW
      rw [Nat.sub_self, mlift_zero]
      simp [shiftr01]
    rw [e]
    exact GpT_farWskL hA hA1 ho hAkG hkoG hs

/-- ★ 語の述語（節点の段 s ≤ o は t の持ち上げで動かない）。 -/
theorem PVF_farW_bot {A : List ℕ} {o b u s k0 : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (hs2 : 2 ≤ s) (hso : s ≤ o) (hsA : ∀ a ∈ A, s ≤ a + 1) (hk0 : 1 ≤ k0)
    (hk0A : ∀ a ∈ A, k0 ≤ a) (hk0o : k0 ≤ o) (hub : u ≤ b) {ws : List (ℕ × TrioSeq)}
    (hws : ∀ k, k0 ≤ k → OkWsk k b ws) {X : TrioSeq} (hX : ∀ k, k0 ≤ k → okWkF k u X) :
    PVF A o b (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++
      [((2, b + s, 0) : ℕ × ℕ × ℕ)]) := by
  have hG := GPF_farW_bot hA hA1 ho hs2 hso hsA hk0 hk0A hk0o hub hws hX
  refine ⟨fun t => ?_, hG.2⟩
  rw [liftOff_zeroF A o]
  have hRu : RawWsk k0 b (ws ++ [(u, X)]) := (OkWsk_snoc hub (hX k0 le_rfl) (hws k0 le_rfl)).1
  have em : mlift (farW b (b + o + 1) ws ++ fwW b (b + o + 1) u X ++
        [((2, b + s, 0) : ℕ × ℕ × ℕ)]) (b + o) t
      = farW b (b + (o + t) + 1) ws ++ fwW b (b + (o + t) + 1) u X ++
        [((2, b + s, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_low _ _ (show ((2, b + s, 0) : ℕ × ℕ × ℕ).2.1 ≤ b + o by show b + s ≤ b + o; omega)]
    have := mlift_farW_highk (show b + k0 ≤ b + o by omega) (show b + o < b + o + 1 by omega) t
      (ws ++ [(u, X)]) hRu
    rw [farW_snoc, farW_snoc] at this
    rw [this, show b + o + 1 + t = b + (o + t) + 1 by omega]
  rw [em]
  exact (GPF_farW_bot (o := o + t) (fun a ha => by have := hA a ha; omega) hA1 (by omega) hs2
    (by omega) hsA hk0 hk0A (by omega) hub hws hX).1

end HaA
end TRIO
