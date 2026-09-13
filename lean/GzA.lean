/-
GzA.lean: 節点の位置に錨を挿入して持ち上げた形でも良い語 PVX。

    PVX A o f b W := ∀ S j F, S ⊆ [o, o+j) → F = f（A の上）→
      PVP (S ++ A) (o + j) F b (mlift W (b + liftOff f A o) (j + Σ_{s ∈ S} F s))

挿入した錨 S は、節点より上の持ち上げでできた空の区間にある。S の上の状態 F は任意
（S の錨の持ち上げは、空の区間の上を全部持ち上げるので、節点の持ち上げ Σ F に入る）。
-/
import GyK

namespace TRIO
namespace GzA

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK

/-! ## 連結の上の和 -/

theorem stepSum_append (b : ℕ) (f : ℕ → ℕ) (m : ℕ) (S A : List ℕ) :
    stepSum b f (S ++ A) m = stepSum b f S m + stepSum b f A m := by
  induction S with
  | nil => simp [stepSum]
  | cons s S ih => simp only [List.cons_append, stepSum, ih]; omega

theorem stepSum_none (b : ℕ) (f : ℕ → ℕ) (m : ℕ) :
    ∀ L : List ℕ, (∀ x ∈ L, m ≤ b + x) → stepSum b f L m = 0
  | [], _ => rfl
  | x :: L, h => by
      have hx := h x (by simp)
      simp only [stepSum, if_neg (show ¬ b + x < m by omega),
        stepSum_none b f m L (fun y hy => h y (by simp [hy]))]

theorem sumOn_append (f : ℕ → ℕ) (S A : List ℕ) : sumOn f (S ++ A) = sumOn f S + sumOn f A := by
  induction S with
  | nil => simp [sumOn]
  | cons s S ih => simp only [List.cons_append, sumOn, ih]; omega

theorem liftVal_ins {S A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hS : ∀ s ∈ S, o ≤ s)
    (F : ℕ → ℕ) {a : ℕ} (ha : a ∈ A) : liftVal F (S ++ A) a = liftVal F A a := by
  unfold liftVal
  rw [stepSum_append, stepSum_none 0 F _ S (fun s hs => by have := hS s hs; have := hA a ha; omega)]
  simp

theorem liftOff_ins {S A : List ℕ} {o j : ℕ} (hA : ∀ a ∈ A, a < o) (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j)
    (F : ℕ → ℕ) : liftOff F (S ++ A) (o + j) = liftOff F A o + j + sumOn F S := by
  unfold liftOff
  rw [stepSum_append, stepSum_all 0 (o + j) F (fun s hs => by have := (hS s hs).2; omega),
    stepSum_all 0 (o + j) F (fun a ha => by have := hA a ha; omega),
    stepSum_all 0 o F (fun a ha => by have := hA a ha; omega)]
  omega

theorem reStep_congr_all (b m : ℕ) {F f G g : ℕ → ℕ} {B A : List ℕ} :
    ∀ L : List ℕ, (∀ a ∈ L, liftVal F B a = liftVal f A a ∧ G a = g a) →
      reStep b F G B L m = reStep b f g A L m
  | [], _ => rfl
  | a :: L, h => by
      simp only [reStep]
      rw [(h a (by simp)).1, (h a (by simp)).2,
        reStep_congr_all b m L (fun x hx => h x (by simp [hx]))]

theorem reStep_append (b m : ℕ) (f g : ℕ → ℕ) (A0 S A : List ℕ) :
    reStep b f g A0 (S ++ A) m = reStep b f g A0 S m + reStep b f g A0 A m := by
  induction S with
  | nil => simp [reStep]
  | cons s S ih => simp only [List.cons_append, reStep, ih]; omega

theorem reStep_zeroG_on (b m : ℕ) (f g : ℕ → ℕ) (A0 : List ℕ) :
    ∀ L : List ℕ, (∀ x ∈ L, g x = 0) → reStep b f g A0 L m = 0
  | [], _ => rfl
  | x :: L, h => by
      simp only [reStep, h x (by simp), reStep_zeroG_on b m f g A0 L (fun y hy => h y (by simp [hy]))]
      simp

/-- S の錨を持ち上げない持ち上げは、S を除いた錨の列の持ち上げと同じ。 -/
theorem reliftX_ins {S A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hS : ∀ s ∈ S, o ≤ s)
    (b : ℕ) (F G : ℕ → ℕ) (hG : ∀ s ∈ S, G s = 0) (X : TrioSeq) :
    reliftX b F G (S ++ A) X = reliftX b F G A X := by
  unfold reliftX
  congr 1
  funext m
  unfold reStair
  rw [reStep_append, reStep_zeroG_on b m _ _ _ S hG,
    reStep_congr_all b m A (fun a ha => ⟨liftVal_ins hA hS F ha, rfl⟩)]
  simp

/-! ## 挿入で閉じた語 -/

def PVX (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ) (W : TrioSeq) : Prop :=
  ∀ S j F, (∀ s ∈ S, o ≤ s ∧ s < o + j) → (∀ a ∈ A, F a = f a) →
    PVP (S ++ A) (o + j) F b (mlift W (b + liftOff f A o) (j + sumOn F S))

theorem hA_ins {S A : List ℕ} {o j : ℕ} (hA : ∀ a ∈ A, a < o) (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) :
    ∀ a ∈ S ++ A, a < o + j := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact (hS a h).2
  · have := hA a h; omega

theorem hA1_ins {S A : List ℕ} {o j : ℕ} (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) : ∀ a ∈ S ++ A, 1 ≤ a := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · have := (hS a h).1; omega
  · exact hA1 a h

theorem liftOff_congrA {A : List ℕ} {o : ℕ} {F f : ℕ → ℕ} (hF : ∀ a ∈ A, F a = f a) :
    liftOff F A o = liftOff f A o := by
  unfold liftOff; rw [stepSum_congr 0 o hF]

theorem PVX_to_PVP {A : List ℕ} {o : ℕ} {f : ℕ → ℕ} {b : ℕ} {W : TrioSeq} (h : PVX A o f b W) :
    PVP A o f b W := by
  have := h [] 0 f (by simp) (fun _ _ => rfl)
  simpa [sumOn, mlift_zero] using this

/-- 挿入の合成。 -/
theorem PVX_refine {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {f : ℕ → ℕ} {b : ℕ} {W : TrioSeq}
    (h : PVX A o f b W) (S : List ℕ) (j : ℕ) (F : ℕ → ℕ) (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j)
    (hF : ∀ a ∈ A, F a = f a) :
    PVX (S ++ A) (o + j) F b (mlift W (b + liftOff f A o) (j + sumOn F S)) := by
  intro S' j' F' hS' hF'
  have hSA : ∀ s ∈ S, F' s = F s := fun s hs => hF' s (List.mem_append_left _ hs)
  have hAA : ∀ a ∈ A, F' a = f a := fun a ha => by
    rw [hF' a (List.mem_append_right _ ha)]; exact hF a ha
  have h1 := h (S' ++ S) (j + j') F' (by
    intro s hs
    rcases List.mem_append.mp hs with h2 | h2
    · have := hS' s h2; omega
    · have := hS s h2; omega) hAA
  rw [List.append_assoc, show o + (j + j') = o + j + j' by omega, sumOn_append,
    sumOn_congr hSA] at h1
  rw [liftOff_ins hA hS, liftOff_congrA hF,
    show b + (liftOff f A o + j + sumOn F S) = b + liftOff f A o + (j + sumOn F S) by omega,
    mlift_mlift, show j + sumOn F S + (j' + sumOn F' S') = j + j' + (sumOn F' S' + sumOn F S) by omega]
  exact h1

theorem PVX_shift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {f : ℕ → ℕ} {b : ℕ} {W : TrioSeq}
    (h : PVX A o f b W) (t : ℕ) : PVX A (o + t) f b (mlift W (b + liftOff f A o) t) := by
  have := PVX_refine hA h [] t f (by simp) (fun _ _ => rfl)
  simpa [sumOn] using this

theorem PVX_lift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {W : TrioSeq} (hW : Fr W) (h : PVX A o H b W) {b' : ℕ} (hb : b ≤ b') :
    PVX A o H b' (mlift W b (b' - b)) := by
  intro S j F hS hF
  have h1 := PVP_lift (hA_ins hA hS) (hA1_ins hA1 ho hS) (by omega) (Fr_mlift hW _ _) (h S j F hS hF) hb
  rw [mlift_commk, show b + liftOff H A o + (b' - b) = b' + liftOff H A o by omega] at h1
  exact h1

theorem PVX_congr {A : List ℕ} {o : ℕ} {H1 H2 : ℕ → ℕ}
    (hH : ∀ a ∈ A, H1 a = H2 a) {b : ℕ} {W : TrioSeq} (h : PVX A o H1 b W) : PVX A o H2 b W := by
  intro S j F hS hF
  rw [← liftOff_congrA hH]
  exact h S j F hS (fun a ha => by rw [hF a ha, hH a ha])

theorem PVX_relift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {H : ℕ → ℕ} {b : ℕ} {W : TrioSeq}
    (h : PVX A o H b W) (G : ℕ → ℕ) : PVX A o (addF H G) b (reliftX b H G A W) := by
  intro S j F hS hF
  classical
  have hS0 : ∀ s ∈ S, o ≤ s := fun s hs => (hS s hs).1
  have hSA : ∀ s ∈ S, s ∉ A := fun s hs ha => by have := hS0 s hs; have := hA s ha; omega
  obtain ⟨F0, hF0⟩ : ∃ F0 : ℕ → ℕ, F0 = fun a => if a ∈ A then H a else F a := ⟨_, rfl⟩
  obtain ⟨G0, hG0⟩ : ∃ G0 : ℕ → ℕ, G0 = fun a => if a ∈ A then G a else 0 := ⟨_, rfl⟩
  have hF0A : ∀ a ∈ A, F0 a = H a := fun a ha => by rw [hF0]; simp [ha]
  have hF0S : ∀ s ∈ S, F0 s = F s := fun s hs => by rw [hF0]; simp [hSA s hs]
  have hG0S : ∀ s ∈ S, G0 s = 0 := fun s hs => by rw [hG0]; simp [hSA s hs]
  have hG0A : ∀ a ∈ A, G0 a = G a := fun a ha => by rw [hG0]; simp [ha]
  have h1 := PVP_relift (hA_ins hA hS) (h S j F0 hS hF0A) G0
  rw [reliftX_ins hA hS0 b F0 G0 hG0S, sumOn_congr hF0S] at h1
  have e2 : reliftX b F0 G0 A (mlift W (b + liftOff H A o) (j + sumOn F S))
      = reliftX b H G A (mlift W (b + liftOff H A o) (j + sumOn F S)) := by
    unfold reliftX; congr 1; funext m; unfold reStair
    rw [reStep_congr b m hF0A hG0A]
  rw [e2, mlift_reliftX_high hA] at h1
  refine PVP_congr (hA_ins hA hS) (fun a ha => ?_) h1
  rcases List.mem_append.mp ha with h2 | h2
  · show addF F0 G0 a = F a
    unfold addF; rw [hF0S a h2, hG0S a h2]; simp
  · show addF F0 G0 a = F a
    unfold addF; rw [hF0A a h2, hG0A a h2, hF a h2]; rfl

theorem PVX_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (ho : 2 ≤ o) (f : ℕ → ℕ) (b : ℕ) :
    PVX A o f b [] := by
  intro S j F hS _
  rw [mlift_nil]
  exact PVP_nil (hA_ins hA hS) (by omega) _ b

theorem PVP_nil1 (f : ℕ → ℕ) (b : ℕ) : PVP [] 1 f b [] := by
  intro t
  rw [mlift_nil]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact GpT_nil1 _ b
  · exact GpT_nil (fun a ha => by simp at ha) (by omega) _ b

theorem PVX_nil1 (f : ℕ → ℕ) (b : ℕ) : PVX [] 1 f b [] := by
  intro S j F hS _
  rw [mlift_nil]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hS0 : S = [] := List.eq_nil_iff_forall_not_mem.mpr (fun s hs => by have := hS s hs; omega)
    subst hS0
    simpa using PVP_nil1 F b
  · exact PVP_nil (hA_ins (fun a ha => by simp at ha) hS) (by omega) _ b

end GzA
end TRIO
