/-
HeA.lean: 一般の列（F の段より上の列を含む）の埋め込みの像 embW の合成（F のタイの子を一般の列にする設計の土台、追記576）。

    embW A k H g S o f b W = mlift (reliftX b H g A W) (b + liftOff (H+g) A k) (liftOff f (S ++ A) o − liftOff (H+g) A k)
- embW_eq_slift: embW は階段 embStair の slift。
- embW_comp: 埋め込み e のあとに e2 を重ねた像は、合成した埋め込み (g+g2, S2 ++ S, o2, f2) の像。
  F の段以下は錨 A の再持ち上げの合成（reStair_ins_low / reStair_comp）、F の段より上は F の段からの差を保つ（reOff_above）。
-/
import HcU

namespace TRIO
namespace HeA

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcM HcU

/-! ## 階段 -/

theorem reStair_mono' (b : ℕ) (f g : ℕ → ℕ) (A : List ℕ) {m n : ℕ} (h : m ≤ n) :
    reStair b f g A m ≤ reStair b f g A n := by
  have h1 := (reStair_stair b f g A).step m n h
  have h2 := (reStair_stair b f g A).ge m
  have h3 := (reStair_stair b f g A).ge n
  omega

theorem reStair_above {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (b : ℕ) (f g : ℕ → ℕ) {m : ℕ}
    (hm : b + liftOff f A o ≤ m) : reStair b f g A m = m + sumOn g A := by
  obtain ⟨t, rfl⟩ : ∃ t, m = b + (liftOff f A o + t) := ⟨m - (b + liftOff f A o), by omega⟩
  rw [reStair_base, reOff_above hA, liftOff_addF hA]
  omega

theorem reStair_at_top {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (b : ℕ) (f g : ℕ → ℕ) :
    reStair b f g A (b + liftOff f A o) = b + liftOff (addF f g) A o := by
  rw [reStair_above hA b f g le_rfl, liftOff_addF hA]; omega

noncomputable def embStair (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ)
    (b : ℕ) : ℕ → ℕ :=
  fun m => reStair b H g A m + (if b + liftOff (addF H g) A k < reStair b H g A m
    then liftOff f (S ++ A) o - liftOff (addF H g) A k else 0)

theorem embStair_stair (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ) :
    Stair (embStair A k H g S o f b) := by
  show Stair (fun m => (fun x => x + (if b + liftOff (addF H g) A k < x
    then liftOff f (S ++ A) o - liftOff (addF H g) A k else 0)) (reStair b H g A m))
  exact stair_comp (reStair_stair b H g A) (stair_step _ _)

theorem embW_eq_slift (A : List ℕ) (k : ℕ) (H g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ)
    (W : TrioSeq) : embW A k H g S o f b W = slift W (embStair A k H g S o f b) := by
  unfold embW reliftX
  rw [mlift_eq_slift, slift_slift (reStair_stair b H g A) (stair_step _ _)]
  rfl

/-! ## 合成 -/

/-- ★ 埋め込みの像の合成。 -/
theorem embW_comp {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ}
    {f : ℕ → ℕ} (hE : EmbU A k H g S o f) {g2 : ℕ → ℕ} {S2 : List ℕ} {o2 : ℕ} {f2 : ℕ → ℕ}
    (hE2 : EmbU (S ++ A) o f g2 S2 o2 f2) (b : ℕ) (W : TrioSeq) :
    embW (S ++ A) o f g2 S2 o2 f2 b (embW A k H g S o f b W)
      = embW A k H (addF g g2) (S2 ++ S) o2 f2 b W := by
  rw [embW_eq_slift, embW_eq_slift, embW_eq_slift,
    slift_slift (embStair_stair _ _ _ _ _ _ _ _) (embStair_stair _ _ _ _ _ _ _ _)]
  congr 1
  funext m
  obtain ⟨hf, hSA, hA, hA1, ho, hK, hKo⟩ := hE
  obtain ⟨hf2, hSA2, hA2, hA12, ho2, hK2, hKo2⟩ := hE2
  obtain ⟨-, -, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g2
  rw [← liftOff_eq_reOff0] at hK hKo hKoG hKo2
  have hKg : liftOff (addF H g) A k = liftOff H A k + sumOn g A := liftOff_addF hAk H g
  have hKgg2 : liftOff (addF H (addF g g2)) A k = liftOff (addF H g) A k + sumOn g2 A := by
    rw [← addF_assoc]; exact liftOff_addF hAk (addF H g) g2
  have hKfg2 : liftOff (addF f g2) (S ++ A) o = liftOff f (S ++ A) o + sumOn g2 (S ++ A) :=
    liftOff_addF hA f g2
  show embStair (S ++ A) o f g2 S2 o2 f2 b (embStair A k H g S o f b m)
    = embStair A k H (addF g g2) (S2 ++ S) o2 f2 b m
  unfold embStair
  rw [List.append_assoc]
  rcases Nat.lt_or_ge (b + liftOff H A k) m with hm | hm
  · -- F の段より上
    have hx : reStair b H g A m = m + sumOn g A := reStair_above hAk b H g (by omega)
    have h1 : b + liftOff (addF H g) A k < reStair b H g A m := by rw [hx]; omega
    simp only [if_pos h1]
    have hv : b + liftOff f (S ++ A) o ≤ reStair b H g A m +
        (liftOff f (S ++ A) o - liftOff (addF H g) A k) := by rw [hx]; omega
    have hc : reStair b H (addF g g2) A m = m + sumOn g A + sumOn g2 A := by
      rw [← reStair_comp, hx, reStair_above hAk b (addF H g) g2 (by omega)]
    have h2 : b + liftOff (addF f g2) (S ++ A) o < reStair b f g2 (S ++ A)
        (reStair b H g A m + (liftOff f (S ++ A) o - liftOff (addF H g) A k)) := by
      rw [reStair_above hA b f g2 hv, hx]; omega
    have h3 : b + liftOff (addF H (addF g g2)) A k < reStair b H (addF g g2) A m := by
      rw [hc]; omega
    simp only [if_pos h2, if_pos h3]
    rw [reStair_above hA b f g2 hv, hx, hc]
    omega
  · -- F の段以下
    have hx : reStair b H g A m ≤ b + liftOff (addF H g) A k := by
      have := reStair_mono' b H g A hm; rwa [reStair_at_top hAk] at this
    have h1 : ¬ (b + liftOff (addF H g) A k < reStair b H g A m) := by omega
    simp only [if_neg h1, Nat.add_zero]
    have hins : reStair b f g2 (S ++ A) (reStair b H g A m)
        = reStair b (addF H g) g2 A (reStair b H g A m) :=
      reStair_ins_low hSA hf b g2 hK hx
    simp only [hins, reStair_comp]
    have hy : reStair b H (addF g g2) A m ≤ b + liftOff (addF H (addF g g2)) A k := by
      have := reStair_mono' b H (addF g g2) A hm; rwa [reStair_at_top hAk] at this
    have h2 : ¬ (b + liftOff (addF f g2) (S ++ A) o < reStair b H (addF g g2) A m) := by omega
    have h3 : ¬ (b + liftOff (addF H (addF g g2)) A k < reStair b H (addF g g2) A m) := by omega
    simp only [if_neg h2, if_neg h3]

end HeA
end TRIO
