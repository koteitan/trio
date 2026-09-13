/-
KxA.lean: κ の世界で良い語 PVK（notes 追記509。GzA の PVX の mlift を klift にしたもの）。

    PVK A o f b W := ∀ S j F K, S ⊆ [o, o+j) → F = f（A の上）→
      PVP (S ++ A) (o + j) F b (klift W (b + liftOff f A o) (j + Σ_{s ∈ S} F s) K)
-/
import KlF
import GzA

namespace TRIO
namespace KxA

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA KlA KlB KlE

def PVK (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ) (W : TrioSeq) : Prop :=
  ∀ S j F K, (∀ s ∈ S, o ≤ s ∧ s < o + j) → (∀ a ∈ A, F a = f a) →
    PVP (S ++ A) (o + j) F b (klift W (b + liftOff f A o) (j + sumOn F S) K)

theorem PVK_to_PVP {A : List ℕ} {o : ℕ} {f : ℕ → ℕ} {b : ℕ} {W : TrioSeq} (h : PVK A o f b W) :
    PVP A o f b W := by
  have := h [] 0 f (fun _ => 0) (by simp) (fun _ _ => rfl)
  simpa [sumOn, klift_zero_j] using this

/-- 世界の合成（KlF.klift_comp）。 -/
theorem PVK_refine {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {f : ℕ → ℕ} {b : ℕ} {W : TrioSeq}
    (h : PVK A o f b W) (S : List ℕ) (j : ℕ) (F : ℕ → ℕ) (K : ℕ → ℕ)
    (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) (hF : ∀ a ∈ A, F a = f a) :
    PVK (S ++ A) (o + j) F b (klift W (b + liftOff f A o) (j + sumOn F S) K) := by
  intro S' j' F' K' hS' hF'
  have hSA : ∀ s ∈ S, F' s = F s := fun s hs => hF' s (List.mem_append_left _ hs)
  have hAA : ∀ a ∈ A, F' a = f a := fun a ha => by
    rw [hF' a (List.mem_append_right _ ha)]; exact hF a ha
  have h1 := h (S' ++ S) (j + j') F' (KlF.compK (j + sumOn F S) (j' + sumOn F' S') K K') (by
    intro s hs
    rcases List.mem_append.mp hs with h2 | h2
    · have := hS' s h2; omega
    · have := hS s h2; omega) hAA
  rw [List.append_assoc, show o + (j + j') = o + j + j' by omega, sumOn_append,
    sumOn_congr hSA] at h1
  rw [liftOff_ins hA hS, liftOff_congrA hF,
    show b + (liftOff f A o + j + sumOn F S) = b + liftOff f A o + (j + sumOn F S) by omega,
    KlF.klift_comp,
    show j + sumOn F S + (j' + sumOn F' S') = j + j' + (sumOn F' S' + sumOn F S) by omega]
  exact h1

theorem PVK_lift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {H : ℕ → ℕ} {b : ℕ} {W : TrioSeq} (hW : Fr W) (h : PVK A o H b W) {b' : ℕ} (hb : b ≤ b') :
    PVK A o H b' (mlift W b (b' - b)) := by
  intro S j F K hS hF
  have h1 := PVP_lift (hA_ins hA hS) (hA1_ins hA1 ho hS) (by omega) (Fr_klift hW _ _ _)
    (h S j F K hS hF) hb
  have hk1 : 1 ≤ liftOff H A o := by unfold liftOff; omega
  rw [KlD.klift_mlift_low (show b < b + liftOff H A o by omega),
    show b + liftOff H A o + (b' - b) = b' + liftOff H A o by omega] at h1
  exact h1

theorem PVK_congr {A : List ℕ} {o : ℕ} {H1 H2 : ℕ → ℕ}
    (hH : ∀ a ∈ A, H1 a = H2 a) {b : ℕ} {W : TrioSeq} (h : PVK A o H1 b W) : PVK A o H2 b W := by
  intro S j F K hS hF
  rw [← liftOff_congrA hH]
  exact h S j F K hS (fun a ha => by rw [hF a ha, hH a ha])

theorem PVK_relift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {H : ℕ → ℕ} {b : ℕ} {W : TrioSeq}
    (h : PVK A o H b W) (G : ℕ → ℕ) : PVK A o (addF H G) b (reliftX b H G A W) := by
  intro S j F K hS hF
  classical
  have hS0 : ∀ s ∈ S, o ≤ s := fun s hs => (hS s hs).1
  have hSA : ∀ s ∈ S, s ∉ A := fun s hs ha => by have := hS0 s hs; have := hA s ha; omega
  obtain ⟨F0, hF0⟩ : ∃ F0 : ℕ → ℕ, F0 = fun a => if a ∈ A then H a else F a := ⟨_, rfl⟩
  obtain ⟨G0, hG0⟩ : ∃ G0 : ℕ → ℕ, G0 = fun a => if a ∈ A then G a else 0 := ⟨_, rfl⟩
  have hF0A : ∀ a ∈ A, F0 a = H a := fun a ha => by rw [hF0]; simp [ha]
  have hF0S : ∀ s ∈ S, F0 s = F s := fun s hs => by rw [hF0]; simp [hSA s hs]
  have hG0S : ∀ s ∈ S, G0 s = 0 := fun s hs => by rw [hG0]; simp [hSA s hs]
  have hG0A : ∀ a ∈ A, G0 a = G a := fun a ha => by rw [hG0]; simp [ha]
  have h1 := PVP_relift (hA_ins hA hS) (h S j F0 K hS hF0A) G0
  rw [reliftX_ins hA hS0 b F0 G0 hG0S, sumOn_congr hF0S] at h1
  have e2 : reliftX b F0 G0 A (klift W (b + liftOff H A o) (j + sumOn F S) K)
      = reliftX b H G A (klift W (b + liftOff H A o) (j + sumOn F S) K) := by
    unfold reliftX; congr 1; funext m; unfold reStair
    rw [reStep_congr b m hF0A hG0A]
  have e3 : reliftX b H G A (klift W (b + liftOff H A o) (j + sumOn F S) K)
      = klift (reliftX b H G A W) (b + liftOff (addF H G) A o) (j + sumOn F S) K := by
    rw [KlD.klift_reliftX (fun a ha => liftVal_lt_liftOff hA ha), reStair_base]
    have := reOff_above hA H G 0
    simp only [Nat.add_zero] at this
    rw [this]
  rw [e2, e3] at h1
  refine PVP_congr (hA_ins hA hS) (fun a ha => ?_) h1
  rcases List.mem_append.mp ha with h2 | h2
  · show addF F0 G0 a = F a
    unfold addF; rw [hF0S a h2, hG0S a h2]; simp
  · show addF F0 G0 a = F a
    unfold addF; rw [hF0A a h2, hG0A a h2, hF a h2]; rfl

theorem PVK_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (ho : 2 ≤ o) (f : ℕ → ℕ) (b : ℕ) :
    PVK A o f b [] := by
  intro S j F K hS _
  rw [klift_nil]
  exact PVP_nil (hA_ins hA hS) (by omega) _ b

theorem PVK_nil1 (f : ℕ → ℕ) (b : ℕ) : PVK [] 1 f b [] := by
  intro S j F K hS _
  rw [klift_nil]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hS0 : S = [] := List.eq_nil_iff_forall_not_mem.mpr (fun s hs => by have := hS s hs; omega)
    subst hS0
    simpa using PVP_nil1 F b
  · exact PVP_nil (hA_ins (fun a ha => by simp at ha) hS) (by omega) _ b

end KxA
end TRIO
