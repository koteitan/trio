/-
KxH.lean: 上限つきの文脈の制限と R_child（GyF の CtxP_restrict / R_child の写し）。

    CtxPb G A c e R : SlotAx・congr・relift と、s + e ≤ liftVal f A c の FarP だけ
    CtxPb_restrict  : τ1 + e ≤ liftVal h0 A c なら、子の級の文脈（CtxP）になる
    R_childb        : 上限つきの族に、段 τ（τ + e ≤ liftVal h A c）の節点と子を置く

κ の族の FarP の eq（e = 1、ずらした族の low だけ）と lt（e = 0、ずらした族の low と eq）で使う。
-/
import KxG

namespace TRIO
namespace KxH

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK

/-- FarP を「s + e ≤ 錨 c の本当の段」に限った文脈の公理。 -/
def CtxPb (G : (ℕ → ℕ) → ℕ → ℕ → TrioSeq → Prop) (A : List ℕ) (c e : ℕ)
    (R : (ℕ → ℕ) → ℕ → TrioSeq → Prop) : Prop :=
  ∀ f, SlotAx (R f) ∧
    (∀ f' b X, (∀ a ∈ A, f a = f' a) → R f b X → R f' b X) ∧
    (∀ g b X, Fr X → R f b X → R (addF f g) b (reliftX b f g A X)) ∧
    (∀ s, 2 ≤ s → s + e ≤ liftVal f A c → FarP G R A f s)

theorem CtxPb_restrict {A : List ℕ} {c e : ℕ} {R : (ℕ → ℕ) → ℕ → TrioSeq → Prop}
    (hR : CtxPb (GC A) A c e R) (hc : ∀ a ∈ A, a ≤ c) {h0 : ℕ → ℕ} {τ1 : ℕ}
    (hbound : τ1 + e ≤ liftVal h0 A c) :
    CtxP (GC (lowP h0 A τ1)) (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1))
      (fun h' => R (mergeF (lowP h0 A τ1) h' h0)) := by
  intro h'
  refine ⟨(hR _).1, fun h'' b X hagree hX => ?_, fun g b X hXFr hX => ?_, fun s hs2 hs => ?_⟩
  · have e : mergeF (lowP h0 A τ1) h' h0 = mergeF (lowP h0 A τ1) h'' h0 := by
      funext a; unfold mergeF; split_ifs with ha
      · exact hagree a ha
      · rfl
    show R (mergeF (lowP h0 A τ1) h'' h0) b X
    rw [← e]; exact hX
  · have := (hR _).2.2.1 (maskF (lowP h0 A τ1) g) b X hXFr hX
    show R (mergeF (lowP h0 A τ1) (addF h' g) h0) b (reliftX b h' g (lowP h0 A τ1) X)
    rwa [mergeF_add, ← reliftX_merge (A := A) (h0 := h0) (τ1 := τ1) b h' h0 g X]
  · intro b P d hP hd hbot h1' h2'
    have hsM : s + e ≤ liftVal (mergeF (lowP h0 A τ1) h' h0) A c := by
      have hall : ∀ F : ℕ → ℕ, stepSum 0 F A (c + 1) = sumOn F A :=
        fun F => stepSum_all 0 (c + 1) F (fun x hx => by have := hc x hx; omega)
      have hsubP : ∀ F : ℕ → ℕ, stepSum 0 F (lowP h0 A τ1) (c + 1) = sumOn F (lowP h0 A τ1) :=
        fun F => stepSum_all 0 (c + 1) F (fun x hx => by have := hc x (mem_lowP_iff.mp hx).1; omega)
      have hsubU : ∀ F : ℕ → ℕ, stepSum 0 F (lowU h0 A τ1) (c + 1) = sumOn F (lowU h0 A τ1) :=
        fun F => stepSum_all 0 (c + 1) F (fun x hx => by have := hc x (mem_lowU_iff.mp hx).1; omega)
      have sM := stepSum_lowPU 0 (c + 1) (mergeF (lowP h0 A τ1) h' h0) h0 A τ1
      have s0 := stepSum_lowPU 0 (c + 1) h0 h0 A τ1
      rw [hall, hsubP, hsubU] at sM s0
      have ePM : sumOn (mergeF (lowP h0 A τ1) h' h0) (lowP h0 A τ1) = sumOn h' (lowP h0 A τ1) :=
        sumOn_congr (fun x hx => by unfold mergeF; rw [if_pos hx])
      have eUM : sumOn (mergeF (lowP h0 A τ1) h' h0) (lowU h0 A τ1) = sumOn h0 (lowU h0 A τ1) :=
        sumOn_congr (fun x hx => by
          unfold mergeF
          rw [if_neg (fun hm => (mem_lowU_iff.mp hx).2 (mem_lowP_iff.mp hm).2)])
      have hb := hbound
      unfold liftVal at hb ⊢
      rw [hall] at hb ⊢
      by_cases hne : lowP h0 A τ1 = []
      · have hlo : liftOff h' (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1)) = τ1 := by
          rw [hne]; simp [liftOff, stepSum, sumOn]
        have hs0 : sumOn h' (lowP h0 A τ1) = 0 := by rw [hne]; rfl
        have hs0' : sumOn h0 (lowP h0 A τ1) = 0 := by rw [hne]; rfl
        rw [hlo] at hs
        omega
      · have hlo : liftOff h' (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1))
            = τ1 - sumOn h0 (lowP h0 A τ1) + sumOn h' (lowP h0 A τ1) :=
          liftOff_eq_sumOn (fun x hx => (lowP_lt_o1 x hx).1)
        obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil _ hne
        have hsum := (lowP_lt_o1 x0 hx0).2
        rw [hlo] at hs
        omega
    refine (hR _).2.2.2 s hs2 hsM b P d hP hd hbot (fun G b' hb' => ?_)
      (fun G b' hb' τ L h1τ hτ hL hGL => ?_)
    · have e1 := h1' G b' hb'
      simp only at e1
      rw [mergeF_add, ← reliftX_merge (A := A) (h0 := h0) (τ1 := τ1) b' h' h0 G] at e1
      have e2 := (hR _).2.2.1 (upperF (lowP h0 A τ1) G) b' _ (Fr_reliftX (Fr_mlift hP _ _) _ _ _ _) e1
      rwa [reliftX_comp, addF_assoc, G_split] at e2
    · have hτ' : τ < reOff h' G (lowP h0 A τ1) s := by
        rw [← reOff_merge (A := A) (h0 := h0) (τ1 := τ1) h' G hs]; exact hτ
      have hGL' := GC_merge (A := A) (h0 := h0) (τ1 := τ1) h' G hs hτ' hGL
      have e1 := h2' G b' hb' τ L h1τ hτ' hL hGL'
      simp only at e1
      rw [mergeF_add, ← reliftX_merge (A := A) (h0 := h0) (τ1 := τ1) b' h' h0 G] at e1
      have hY : Fr (reliftX b' (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G) A
          (mlift P b (b' - b))) := Fr_reliftX (Fr_mlift hP _ _) _ _ _ _
      have hbotY : BotGe (reliftX b' (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G) A
          (mlift P b (b' - b))) d (b' + τ) := by
        have b1 := BotGe_slift hbot (stair_step b (b' - b))
        rw [← mlift_eq_slift, if_pos (by omega), show b + s + (b' - b) = b' + s by omega] at b1
        have b2 := BotGe_slift b1
          (reStair_stair b' (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G) A)
        rw [reStair_base] at b2
        have e3 : reOff (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G) A s
            = reOff h' G (lowP h0 A τ1) s := by
          rw [reOff_merge (A := A) (h0 := h0) (τ1 := τ1) h' _ hs]
          unfold reOff
          rw [reStep_congr 0 s (fun _ _ => rfl) (fun x hx => by unfold maskF; rw [if_pos hx])]
        rw [e3] at b2
        exact BotGe_mono b2 (by omega)
      have hU : Fr (reliftX b' (mergeF (lowP h0 A τ1) h' h0) (maskF (lowP h0 A τ1) G) A
          (mlift P b (b' - b)) ++ shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) :=
        Fr_append hY (Fr_shift_node _ _ _)
      have e2 := (hR _).2.2.1 (upperF (lowP h0 A τ1) G) b' _ hU e1
      rw [reliftX_upper_unit (A := A) (h0 := h0) (τ1 := τ1) h' G hs hτ' hL hd hbotY,
        reliftX_comp, addF_assoc, G_split] at e2
      exact e2

theorem R_childb {A : List ℕ} {c e : ℕ} {R : (ℕ → ℕ) → ℕ → TrioSeq → Prop}
    (hR : CtxPb (GC A) A c e R) (hc : ∀ a ∈ A, a ≤ c) {h : ℕ → ℕ} {τ b : ℕ} {X L : TrioSeq}
    (hX : Fr X) (hRX : R h b X) (hL : GC A h τ b L) (hτ : τ + e ≤ liftVal h A c) :
    R h b (X ++ ((1, b + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  have hR1 := CtxPb_restrict hR hc (h0 := h) (τ1 := τ) hτ
  unfold GC at hL
  have hn := GpT_elim0 hL hR1
  simp only [mergeF_self] at hn
  rw [liftOff_lowP] at hn
  have := hn b le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero] at this

end KxH
end TRIO
