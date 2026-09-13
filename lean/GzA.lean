/-
GzA.lean: 節点の位置に錨を挿入して持ち上げた形でも良い語 PVX。

    zeroOn S f a = if a ∈ S then 0 else f a
    PVX A o f b W := ∀ S j, S ⊆ [o, o+j) →
      PVP (S ++ A) (o + j) (zeroOn S f) b (mlift W (b + liftOff f A o) j)

挿入した錨 S は空の区間（節点の上の持ち上げでできた隙間）にあり、状態 0 で置く。
-/
import GyK

namespace TRIO
namespace GzA

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK

/-! ## 挿入した錨の状態 -/

def zeroOn (S : List ℕ) (f : ℕ → ℕ) : ℕ → ℕ := fun a => if a ∈ S then 0 else f a

theorem zeroOn_nil (f : ℕ → ℕ) : zeroOn [] f = f := by funext a; simp [zeroOn]

theorem zeroOn_append (S' S : List ℕ) (f : ℕ → ℕ) :
    zeroOn (S' ++ S) f = zeroOn S' (zeroOn S f) := by
  funext a; unfold zeroOn
  by_cases h1 : a ∈ S' <;> by_cases h2 : a ∈ S <;> simp [h1, h2]

theorem addF_zeroOn (S : List ℕ) (f g : ℕ → ℕ) :
    addF (zeroOn S f) (zeroOn S g) = zeroOn S (addF f g) := by
  funext a; unfold zeroOn addF
  by_cases h : a ∈ S <;> simp [h]

theorem zeroOn_low {S A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hS : ∀ s ∈ S, o ≤ s)
    (f : ℕ → ℕ) : ∀ a ∈ A, zeroOn S f a = f a := by
  intro a ha
  have hn : a ∉ S := fun h => by have := hS a h; have := hA a ha; omega
  simp [zeroOn, hn]

/-! ## 連結の上の和 -/

theorem stepSum_append (b : ℕ) (f : ℕ → ℕ) (m : ℕ) (S A : List ℕ) :
    stepSum b f (S ++ A) m = stepSum b f S m + stepSum b f A m := by
  induction S with
  | nil => simp [stepSum]
  | cons s S ih => simp only [List.cons_append, stepSum, ih]; omega

theorem stepSum_zeroOn (b : ℕ) (f : ℕ → ℕ) (m : ℕ) (S : List ℕ) :
    ∀ L : List ℕ, (∀ x ∈ L, x ∈ S) → stepSum b (zeroOn S f) L m = 0
  | [], _ => rfl
  | x :: L, h => by
      have hx : x ∈ S := h x (by simp)
      simp only [stepSum, zeroOn, if_pos hx, stepSum_zeroOn b f m S L (fun y hy => h y (by simp [hy]))]
      simp

theorem liftVal_ins {S A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hS : ∀ s ∈ S, o ≤ s)
    (f : ℕ → ℕ) {a : ℕ} (ha : a ∈ A) : liftVal (zeroOn S f) (S ++ A) a = liftVal f A a := by
  unfold liftVal
  rw [stepSum_append, stepSum_zeroOn 0 f _ S S (fun _ h => h),
    stepSum_congr 0 _ (zeroOn_low hA hS f)]
  simp

theorem liftOff_ins {S A : List ℕ} {o j : ℕ} (hA : ∀ a ∈ A, a < o) (hS : ∀ s ∈ S, o ≤ s)
    (f : ℕ → ℕ) : liftOff (zeroOn S f) (S ++ A) (o + j) = liftOff f A o + j := by
  unfold liftOff
  rw [stepSum_append, stepSum_zeroOn 0 f _ S S (fun _ h => h),
    stepSum_congr 0 _ (zeroOn_low hA hS f),
    stepSum_all 0 (o + j) f (fun a ha => by have := hA a ha; omega),
    stepSum_all 0 o f (fun a ha => by have := hA a ha; omega)]
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

theorem reliftX_ins {S A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hS : ∀ s ∈ S, o ≤ s)
    (b : ℕ) (f g : ℕ → ℕ) (X : TrioSeq) :
    reliftX b (zeroOn S f) (zeroOn S g) (S ++ A) X = reliftX b f g A X := by
  unfold reliftX
  congr 1
  funext m
  unfold reStair
  rw [reStep_append, reStep_zeroG_on b m _ _ _ S (fun x hx => by simp [zeroOn, hx]),
    reStep_congr_all b m A (fun a ha => ⟨liftVal_ins hA hS f ha, zeroOn_low hA hS g a ha⟩)]
  simp

/-! ## 挿入で閉じた語 -/

def PVX (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ) (W : TrioSeq) : Prop :=
  ∀ S j, (∀ s ∈ S, o ≤ s ∧ s < o + j) →
    PVP (S ++ A) (o + j) (zeroOn S f) b (mlift W (b + liftOff f A o) j)

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

theorem PVX_to_PVP {A : List ℕ} {o : ℕ} {f : ℕ → ℕ} {b : ℕ} {W : TrioSeq} (h : PVX A o f b W) :
    PVP A o f b W := by
  have := h [] 0 (by simp)
  simpa [zeroOn_nil, mlift_zero] using this

/-- 挿入の合成。 -/
theorem PVX_refine {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {f : ℕ → ℕ} {b : ℕ} {W : TrioSeq}
    (h : PVX A o f b W) (S : List ℕ) (j : ℕ) (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) :
    PVX (S ++ A) (o + j) (zeroOn S f) b (mlift W (b + liftOff f A o) j) := by
  intro S' j' hS'
  have h1 := h (S' ++ S) (j + j') (by
    intro s hs
    rcases List.mem_append.mp hs with h2 | h2
    · have := hS' s h2; omega
    · have := hS s h2; omega)
  rw [List.append_assoc, zeroOn_append, show o + (j + j') = o + j + j' by omega] at h1
  rw [liftOff_ins hA (fun s hs => (hS s hs).1), show b + (liftOff f A o + j) = b + liftOff f A o + j by omega,
    mlift_mlift]
  exact h1

theorem PVX_shift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {f : ℕ → ℕ} {b : ℕ} {W : TrioSeq}
    (h : PVX A o f b W) (t : ℕ) : PVX A (o + t) f b (mlift W (b + liftOff f A o) t) := by
  have := PVX_refine hA h [] t (by simp)
  simpa [zeroOn_nil] using this

theorem PVX_lift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {W : TrioSeq} (hW : Fr W) (h : PVX A o H b W) {b' : ℕ} (hb : b ≤ b') :
    PVX A o H b' (mlift W b (b' - b)) := by
  intro S j hS
  have h1 := PVP_lift (hA_ins hA hS) (hA1_ins hA1 ho hS) (by omega) (Fr_mlift hW _ _) (h S j hS) hb
  rw [mlift_commk, show b + liftOff H A o + (b' - b) = b' + liftOff H A o by omega] at h1
  exact h1

theorem PVX_congr {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {H1 H2 : ℕ → ℕ}
    (hH : ∀ a ∈ A, H1 a = H2 a) {b : ℕ} {W : TrioSeq} (h : PVX A o H1 b W) : PVX A o H2 b W := by
  intro S j hS
  have e : liftOff H1 A o = liftOff H2 A o := by unfold liftOff; rw [stepSum_congr 0 o hH]
  rw [← e]
  refine PVP_congr (hA_ins hA hS) (fun a ha => ?_) (h S j hS)
  rcases List.mem_append.mp ha with h2 | h2
  · simp [zeroOn, h2]
  · rw [zeroOn_low hA (fun s hs => (hS s hs).1) H1 a h2, zeroOn_low hA (fun s hs => (hS s hs).1) H2 a h2]
    exact hH a h2

theorem PVX_relift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {H : ℕ → ℕ} {b : ℕ} {W : TrioSeq}
    (h : PVX A o H b W) (G : ℕ → ℕ) : PVX A o (addF H G) b (reliftX b H G A W) := by
  intro S j hS
  have hS0 : ∀ s ∈ S, o ≤ s := fun s hs => (hS s hs).1
  have h1 := PVP_relift (hA_ins hA hS) (h S j hS) (zeroOn S G)
  rw [addF_zeroOn, reliftX_ins hA hS0, mlift_reliftX_high hA] at h1
  exact h1

theorem PVX_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (ho : 2 ≤ o) (f : ℕ → ℕ) (b : ℕ) :
    PVX A o f b [] := by
  intro S j hS
  rw [mlift_nil]
  exact PVP_nil (hA_ins hA hS) (by omega) _ b

theorem PVP_nil1 (f : ℕ → ℕ) (b : ℕ) : PVP [] 1 f b [] := by
  intro t
  rw [mlift_nil]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact GpT_nil1 _ b
  · exact GpT_nil (fun a ha => by simp at ha) (by omega) _ b

theorem PVX_nil1 (f : ℕ → ℕ) (b : ℕ) : PVX [] 1 f b [] := by
  intro S j hS
  rw [mlift_nil]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hS0 : S = [] := List.eq_nil_iff_forall_not_mem.mpr (fun s hs => by have := hS s hs; omega)
    subst hS0
    simpa [zeroOn_nil] using PVP_nil1 f b
  · exact PVP_nil (hA_ins (fun a ha => by simp at ha) hS) (by omega) _ b

end GzA
end TRIO
