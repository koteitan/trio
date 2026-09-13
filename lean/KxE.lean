/-
KxE.lean: κ の族の FarP の準備。

    BotGe_klift      : klift は入れ子の底の条件を保つ
    reliftX_split    : 錨の列 S ++ A の状態の持ち上げを、A の部分と S の部分に分ける
    band_reStair     : S の部分の階段は、閾値 v 以下で動かず、v + J 以上で Σ_S G だけ上がる（KlH.klift_slift_band の仮定）
    mlift_klift_top  : klift のあとの閾値 v + J のマスクリフトは 1 回の klift
-/
import KxD
import KlH

namespace TRIO
namespace KxE

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzB KxA KxB KxC KxD KlA KlB KlE KlG KlH

theorem BotGe_klift {P : TrioSeq} {d v : ℕ} (hbot : BotGe P d v) (o j : ℕ) (K : ℕ → ℕ) :
    BotGe (klift P o j K) d v := by
  intro c y hc hy hr
  rw [klift_length] at hy
  have hr' : Relation.ReflTransGen (nextrel0 (P ++ [c])) y P.length := by
    have h0 : ∀ i, entry (klift P o j K ++ [c]) 0 i = entry (P ++ [c]) 0 i := by
      intro i
      rcases Nat.lt_or_ge i P.length with hi | hi
      · rw [Small.entry_append_left (by rw [klift_length]; exact hi), Small.entry_append_left hi,
          entry0_klift]
      · obtain ⟨q, rfl⟩ : ∃ q, i = P.length + q := ⟨i - P.length, by omega⟩
        have e1 : entry (klift P o j K ++ [c]) 0 (P.length + q) = entry [c] 0 q := by
          have := entry_append_right (klift P o j K) [c] 0 q
          rwa [klift_length] at this
        rw [e1, entry_append_right]
    have := (rtg0_congr0 (by simp) h0).1 hr
    rwa [klift_length] at this
  have hyv := hbot c y hc hy hr'
  rw [entry1_klift hy]
  omega

theorem reliftX_split {S A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hS : ∀ s ∈ S, o ≤ s)
    (b : ℕ) (F G : ℕ → ℕ) (X : TrioSeq) :
    reliftX b F G (S ++ A) X
      = reliftX b (addF F (maskF A G)) (upperF A G) (S ++ A) (reliftX b F (maskF A G) A X) := by
  classical
  have hm : ∀ s ∈ S, maskF A G s = 0 := fun s hs => by
    unfold maskF; rw [if_neg (fun ha => by have := hS s hs; have := hA s ha; omega)]
  rw [← reliftX_ins hA hS b F (maskF A G) hm X, reliftX_comp, G_split]

theorem stepSum_le_sumOn (b m : ℕ) (f : ℕ → ℕ) : ∀ L : List ℕ, stepSum b f L m ≤ sumOn f L
  | [] => le_rfl
  | a :: L => by
      have := stepSum_le_sumOn b m f L
      simp only [stepSum, sumOn]
      split_ifs <;> omega

theorem reStep_none {b m : ℕ} {f g : ℕ → ℕ} {A0 : List ℕ} :
    ∀ L : List ℕ, (∀ a ∈ L, m ≤ b + liftVal f A0 a) → reStep b f g A0 L m = 0
  | [], _ => rfl
  | a :: L, h => by
      have ha := h a (by simp)
      simp only [reStep]
      rw [if_neg (by omega), reStep_none L (fun x hx => h x (by simp [hx]))]

theorem reStep_every {b m : ℕ} {f g : ℕ → ℕ} {A0 : List ℕ} :
    ∀ L : List ℕ, (∀ a ∈ L, b + liftVal f A0 a < m) → reStep b f g A0 L m = sumOn g L
  | [], _ => rfl
  | a :: L, h => by
      have ha := h a (by simp)
      simp only [reStep, sumOn]
      rw [if_pos ha, reStep_every L (fun x hx => h x (by simp [hx]))]

theorem liftVal_ins_S {S A : List ℕ} {o j : ℕ} (hA : ∀ a ∈ A, a < o)
    (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) (F : ℕ → ℕ) {s : ℕ} (hs : s ∈ S) :
    liftOff F A o ≤ liftVal F (S ++ A) s ∧ liftVal F (S ++ A) s < liftOff F A o + j + sumOn F S := by
  have h1 := hS s hs
  unfold liftVal
  rw [stepSum_append, stepSum_all 0 (s + 1) F (A := A) (fun a ha => by have := hA a ha; omega),
    sumOn_liftOff hA]
  have := stepSum_le_sumOn 0 (s + 1) F S
  omega

/-- ★ 挿入した錨 S の部分の階段は帯 [v, v + J) の中にしか段差がない。 -/
theorem band_reStair {S A : List ℕ} {o j : ℕ} (hA : ∀ a ∈ A, a < o)
    (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) (b : ℕ) (F G : ℕ → ℕ) (hG : ∀ a ∈ A, G a = 0) :
    (∀ m, m ≤ b + liftOff F A o → reStair b F G (S ++ A) m = m) ∧
    (∀ m, b + liftOff F A o + (j + sumOn F S) ≤ m →
      reStair b F G (S ++ A) m - m = sumOn G S) := by
  have hAz : ∀ m, reStep b F G (S ++ A) A m = 0 := fun m => reStep_zeroG_on b m F G (S ++ A) A hG
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · unfold reStair
    rw [reStep_append, hAz,
      reStep_none S (fun s hs => by have := (liftVal_ins_S hA hS F hs).1; omega)]
    try simp
  · unfold reStair
    rw [reStep_append, hAz,
      reStep_every S (fun s hs => by have := (liftVal_ins_S hA hS F hs).2; omega)]
    omega

theorem mlift_klift_top (X : TrioSeq) (v J t : ℕ) (K : ℕ → ℕ) :
    mlift (klift X v J K) (v + J) t = klift X v (J + t) (KlF.compK J t K (fun _ => 0)) := by
  rw [← KlC.klift_zero_eq_mlift, KlF.klift_comp]

end KxE
end TRIO
