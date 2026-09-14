/-
HcU.lean: 一般の列の、全ての埋め込みで良い接頭辞 PVE（遠い段の族の一般化の土台）。

    embW A k H g S o f b W := mlift (reliftX b H g A W) (b + liftOff (H+g) A k) (liftOff f (S ++ A) o − liftOff (H+g) A k)
      （内容の範囲は錨 A の再持ち上げ g で動かし、F の段 b + liftOff (H+g) A k + 1 を埋め込み先の F の段へ持ち上げる）
    PVE A k H b0 W := ∀ 埋め込み (g S o f)、埋め込み先の再持ち上げ g'、段 b ≥ b0、
      PVP (S ++ A) o (f+g') b (reliftX b f g' (S ++ A) (embW A k H g S o f b (W を b へ持ち上げた形)))

- 付け替え: PVE_lift（段）、PVE_relift（状態）、PVE_shift（上限 k → k+t、F の段の持ち上げ）、PVE_congr、PVE_PVP。
- 錨 o の挿入: EmbU_cons_top と embW_cons_top（塔の内側の級 (o :: S ++ A, o+1) は F の段を 1 上げた形）。
-/
import HcO

namespace TRIO
namespace HcU

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcJ HcK HcL HcM HcN HcO

/-! ## 埋め込み -/

noncomputable def embW (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ)
    (W : TrioSeq) : TrioSeq :=
  mlift (reliftX b H g A W) (b + liftOff (addF H g) A k)
    (liftOff f (S ++ A) o - liftOff (addF H g) A k)

def PVE (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (b0 : ℕ) (W : TrioSeq) : Prop :=
  ∀ (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f g' : ℕ → ℕ) (b : ℕ), EmbU A k H g S o f → b0 ≤ b →
    PVP (S ++ A) o (addF f g') b
      (reliftX b f g' (S ++ A) (embW A k H g S o f b (mlift W b0 (b - b0))))

theorem EmbU_KL {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) : liftOff (addF H g) A k ≤ liftOff f (S ++ A) o := by
  rw [liftOff_eq_reOff0]; exact hE.2.2.2.2.2.2

theorem Fr_embW {W : TrioSeq} (hW : Fr W) (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ)
    (f : ℕ → ℕ) (b : ℕ) : Fr (embW A k H g S o f b W) :=
  Fr_mlift (Fr_reliftX hW _ _ _ _) _ _

theorem embW_lift_base (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ)
    (b t : ℕ) (X : TrioSeq) :
    mlift (embW A k H g S o f b X) b t = embW A k H g S o f (b + t) (mlift X b t) := by
  unfold embW
  rw [mlift_commk, mlift_reliftX,
    show b + liftOff (addF H g) A k + t = b + t + liftOff (addF H g) A k by omega]

theorem EmbU_shift_o {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) (t : ℕ) : EmbU A k H g S (o + t) f := by
  obtain ⟨hf, hSA, hA, hA1, ho, hK, hKo⟩ := hE
  refine ⟨hf, hSA, fun a ha => by have := hA a ha; omega, hA1, by omega, hK, ?_⟩
  rw [liftOff_add_t hA]; omega

theorem embW_shift_o {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) (t b : ℕ) (X : TrioSeq) :
    embW A k H g S (o + t) f b X = mlift (embW A k H g S o f b X) (b + liftOff f (S ++ A) o) t := by
  have hKL := EmbU_KL hE
  unfold embW
  rw [liftOff_add_t hE.2.2.1]
  have e := mlift_mlift (reliftX b H g A X) (b + liftOff (addF H g) A k)
    (liftOff f (S ++ A) o - liftOff (addF H g) A k) t
  rw [show b + liftOff (addF H g) A k + (liftOff f (S ++ A) o - liftOff (addF H g) A k)
    = b + liftOff f (S ++ A) o by omega] at e
  rw [e, show liftOff f (S ++ A) o - liftOff (addF H g) A k + t
    = liftOff f (S ++ A) o + t - liftOff (addF H g) A k by omega]

theorem EmbU_cons_top {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) : EmbU A k H g (o :: S) (o + 1) (upF o 0 f) := by
  obtain ⟨hf, hSA, hA, hA1, ho, hK, hKo⟩ := hE
  have hAo' : ∀ a ∈ o :: (S ++ A), a < o + 1 := by
    intro a ha; simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · omega
    · have := hA a ha; omega
  have hA1' : ∀ a ∈ o :: (S ++ A), 1 ≤ a := by
    intro a ha; simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact ho
    · exact hA1 a ha
  have hHo : upF o 0 f o = 0 := by simp [upF]
  have hHA : ∀ a ∈ S ++ A, upF o 0 f a = f a := upF_low hA 0 f
  have e1 : liftOff (upF o 0 f) (o :: (S ++ A)) (o + 1) = liftOff f (S ++ A) o + 1 := by
    rw [sumOn_liftOff hAo', sumOn_liftOff hA]
    simp only [sumOn, hHo, sumOn_congr hHA]
    omega
  have eo : liftOff (upF o 0 f) (S ++ A) o = liftOff f (S ++ A) o := by
    rw [sumOn_liftOff hA, sumOn_liftOff hA, sumOn_congr hHA]
  refine ⟨fun a ha => ?_, fun s hs a ha => ?_, ?_, ?_, by omega, fun s hs => ?_, ?_⟩
  · rw [hHA a (List.mem_append_right _ ha)]; exact hf a ha
  · simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact hA a (List.mem_append_right _ ha)
    · exact hSA s hs a ha
  · rw [List.cons_append]; exact hAo'
  · rw [List.cons_append]; exact hA1'
  · simp only [List.mem_cons] at hs
    rw [List.cons_append]
    rcases hs with hs | hs
    · rw [hs, liftVal_cons_top hA, hHo, Nat.add_zero, eo]; exact hKo
    · rw [liftVal_cons_low hA (List.mem_append_left _ hs)]
      have e : liftVal (upF o 0 f) (S ++ A) s = liftVal f (S ++ A) s := by
        unfold liftVal; rw [stepSum_congr 0 (s + 1) hHA]
      rw [e]; exact hK s hs
  · rw [List.cons_append, e1]; omega

theorem liftOff_cons_top {B : List ℕ} {o : ℕ} (hA : ∀ a ∈ B, a < o) (f : ℕ → ℕ) :
    liftOff (upF o 0 f) (o :: B) (o + 1) = liftOff f B o + 1 := by
  have hAo' : ∀ a ∈ o :: B, a < o + 1 := by
    intro a ha; simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · omega
    · have := hA a ha; omega
  have hHo : upF o 0 f o = 0 := by simp [upF]
  have hHA : ∀ a ∈ B, upF o 0 f a = f a := upF_low hA 0 f
  rw [sumOn_liftOff hAo', sumOn_liftOff hA]
  simp only [sumOn, hHo, sumOn_congr hHA]
  omega

theorem embW_cons_top {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) (b : ℕ) (X : TrioSeq) :
    embW A k H g (o :: S) (o + 1) (upF o 0 f) b X
      = mlift (embW A k H g S o f b X) (b + liftOff f (S ++ A) o) 1 := by
  have hKL := EmbU_KL hE
  unfold embW
  rw [List.cons_append, liftOff_cons_top hE.2.2.1]
  have e := mlift_mlift (reliftX b H g A X) (b + liftOff (addF H g) A k)
    (liftOff f (S ++ A) o - liftOff (addF H g) A k) 1
  rw [show b + liftOff (addF H g) A k + (liftOff f (S ++ A) o - liftOff (addF H g) A k)
    = b + liftOff f (S ++ A) o by omega] at e
  rw [e, show liftOff f (S ++ A) o - liftOff (addF H g) A k + 1
    = liftOff f (S ++ A) o + 1 - liftOff (addF H g) A k by omega]

/-- 錨 o を挿入した級での再持ち上げ（錨 o の量 0）は、元の級での再持ち上げ。 -/
theorem reliftX_cons_top0 {B : List ℕ} {o : ℕ} (hA : ∀ a ∈ B, a < o) (b : ℕ) (f g' : ℕ → ℕ)
    (X : TrioSeq) : reliftX b (upF o 0 f) (upF o 0 g') (o :: B) X = reliftX b f g' B X := by
  have e := reliftX_cons_top hA b (upF o 0 f) g' (upF o 0 g') (upF_low hA 0 g') X
  have e0 : upF o 0 g' o = 0 := by simp [upF]
  rw [e0, mlift_zero] at e
  rw [e]
  exact reliftX_congr b (upF_low hA 0 f) (fun _ _ => rfl) X

theorem addF_upF0 (o : ℕ) (f g' : ℕ → ℕ) : addF (upF o 0 f) (upF o 0 g') = upF o 0 (addF f g') := by
  funext a; by_cases h : a = o <;> simp [addF, upF, h]

/-! ## 付け替え -/

theorem PVE_lift {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b0 : ℕ} {W : TrioSeq} (h : PVE A k H b0 W)
    {b1 : ℕ} (hb : b0 ≤ b1) : PVE A k H b1 (mlift W b0 (b1 - b0)) := by
  intro g S o f g' b hE hb1
  have e := mlift_mlift W b0 (b1 - b0) (b - b1)
  rw [show b0 + (b1 - b0) = b1 by omega, show b1 - b0 + (b - b1) = b - b0 by omega] at e
  rw [e]
  exact h g S o f g' b hE (le_trans hb hb1)

theorem PVE_relift {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b0 : ℕ} {W : TrioSeq} (h : PVE A k H b0 W)
    (G : ℕ → ℕ) : PVE A k (addF H G) b0 (reliftX b0 H G A W) := by
  intro g S o f g' b hE hb
  have hE' : EmbU A k H (addF G g) S o f := by
    unfold EmbU at hE ⊢; rw [← addF_assoc]; exact hE
  have := h (addF G g) S o f g' b hE' hb
  have e : embW A k (addF H G) g S o f b (mlift (reliftX b0 H G A W) b0 (b - b0))
      = embW A k H (addF G g) S o f b (mlift W b0 (b - b0)) := by
    unfold embW
    rw [mlift_reliftX, show b0 + (b - b0) = b by omega, reliftX_comp, addF_assoc]
  rw [e]; exact this

theorem PVE_shift {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) {H : ℕ → ℕ} {b0 : ℕ} {W : TrioSeq}
    (h : PVE A k H b0 W) (t : ℕ) : PVE A (k + t) H b0 (mlift W (b0 + liftOff H A k) t) := by
  intro g S o f g' b hE hb
  have hK : ∀ G : ℕ → ℕ, liftOff (addF H G) A (k + t) = liftOff (addF H G) A k + t :=
    fun G => liftOff_add_t hAk _ t
  have hle : reOff (fun _ => 0) (addF H g) A k ≤ reOff (fun _ => 0) (addF H g) A (k + t) := by
    rw [← liftOff_eq_reOff0, ← liftOff_eq_reOff0, hK]; omega
  have hE' : EmbU A k H g S o f :=
    ⟨hE.1, hE.2.1, hE.2.2.1, hE.2.2.2.1, hE.2.2.2.2.1,
      fun s hs => le_trans hle (hE.2.2.2.2.2.1 s hs), le_trans hle hE.2.2.2.2.2.2⟩
  have := h g S o f g' b hE' hb
  have hKo := EmbU_KL hE
  rw [hK] at hKo
  have e : embW A (k + t) H g S o f b (mlift (mlift W (b0 + liftOff H A k) t) b0 (b - b0))
      = embW A k H g S o f b (mlift W b0 (b - b0)) := by
    unfold embW
    rw [mlift_commk, show b0 + liftOff H A k + (b - b0) = b + liftOff H A k by omega,
      mlift_reliftX_high hAk, hK]
    have e2 := mlift_mlift (reliftX b H g A (mlift W b0 (b - b0))) (b + liftOff (addF H g) A k) t
      (liftOff f (S ++ A) o - (liftOff (addF H g) A k + t))
    rw [show b + liftOff (addF H g) A k + t = b + (liftOff (addF H g) A k + t) by omega] at e2
    rw [e2, show t + (liftOff f (S ++ A) o - (liftOff (addF H g) A k + t))
      = liftOff f (S ++ A) o - liftOff (addF H g) A k by omega]
  rw [e]; exact this

theorem PVE_congr {A : List ℕ} {k : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A, H a = H' a) {b0 : ℕ}
    {W : TrioSeq} (h : PVE A k H b0 W) : PVE A k H' b0 W := by
  intro g S o f g' b hE hb
  have := h g S o f g' b (EmbU_congr (fun a ha => (hH a ha).symm) hE) hb
  have e : embW A k H' g S o f b (mlift W b0 (b - b0)) = embW A k H g S o f b (mlift W b0 (b - b0)) := by
    unfold embW
    have el : liftOff (addF H' g) A k = liftOff (addF H g) A k := by
      rw [liftOff_eq_reOff0, liftOff_eq_reOff0, reOff_congrF (fun a ha => (hH a ha).symm) g k]
    rw [el, reliftX_congr b (fun a ha => (hH a ha).symm) (fun _ _ => rfl)]
  rw [e]; exact this

theorem PVE_PVP {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) (hA1 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k)
    {H : ℕ → ℕ} {b0 : ℕ} {W : TrioSeq} (h : PVE A k H b0 W) : PVP A k H b0 W := by
  have := h (fun _ => 0) [] k H (fun _ => 0) b0 (EmbU_triv hAk hA1 hk H) le_rfl
  simp only [embW, List.nil_append, addF_zero, reliftX_zero, Nat.sub_self, mlift_zero] at this
  exact this

end HcU
end TRIO
