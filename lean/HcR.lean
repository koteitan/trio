/-
HcR.lean: F のタイの子の並びの最後に、高い塊（段 u+τ の節点を含む）を置く生成器の部品。

    okRN A0 o u X := Fr X ∧ RN A0 o 0 u X
    GoodChuX_snocN: GoodChuX Lds → GoodLow u us → okRN X → GoodChuX (Lds ++ [us ++ [some X]])
-/
import HcP

namespace TRIO
namespace HcR

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcJ HcK HcL HcM HcN HcO HcP

def okRN (A0 : List ℕ) (o u : ℕ) (X : TrioSeq) : Prop := Fr X ∧ RN A0 o (fun _ => 0) u X

theorem okRN_nil {A0 : List ℕ} {o : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) (hAo : ∀ a ∈ A0, a < o)
    (u : ℕ) : okRN A0 o u [] := ⟨Fr_nil, RN_nil hA01 ho hAo _ _⟩

theorem okRN_load {A0 : List ℕ} {o u : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) {X : TrioSeq}
    (h : okRN A0 o u X) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    okRN A0 o u (X ++ shiftr01 1 0 Z) :=
  ⟨Fr_append h.1 (Fr_shift1 Z), slot_load (RN_ax hA01 ho _) h.1 h.2 Z hZ hb⟩

theorem okRN_node {A0 : List ℕ} {o u τ : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o)
    (hAo : ∀ a ∈ A0, a < o) (hτ : τ ≤ o) {X L : TrioSeq} (A' : List ℕ)
    (hA' : A0.filter (fun a => decide (a < τ)) = A') (h : okRN A0 o u X) (hL : GPF A' τ u L) :
    okRN A0 o u (X ++ ((1, u + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  refine ⟨Fr_append h.1 (Fr_node _ _),
    RN_node hA01 ho hAo h.1 h.2 ?_ (by rw [liftOff_zeroF]; exact hτ)⟩
  rw [GC_zeroF, hA']; exact hL.1

theorem okRN_tie {A0 : List ℕ} {o u : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) {X : TrioSeq}
    (h : okRN A0 o u X) {D : TrioSeq} (hD : GF 1 u D) :
    okRN A0 o u (X ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) := by
  have := ((Gof_one_iff u D).mp hD.1) (RN A0 o (fun _ => 0)) (RN_ax hA01 ho _) u le_rfl X h.1 h.2
  rw [Nat.sub_self, mlift_zero] at this
  exact ⟨Fr_append h.1 (Fr_node _ _), this⟩

/-- ★ F のタイの子の並び（低い並び us のあとに高い塊 X）を足す。 -/
theorem GoodChuX_snocN {A0 : List ℕ} {o u : ℕ} {Lds : List (List (Option TrioSeq))}
    (hL : GoodChuX A0 o (fun _ => 0) u Lds) {us : List (Option TrioSeq)} (hus : GoodLow u us)
    {X : TrioSeq} (hX : okRN A0 o u X) : GoodChuX A0 o (fun _ => 0) u (Lds ++ [us ++ [some X]]) := by
  have := (RN_okW hX.2).2.2 u le_rfl us hus Lds hL
  rwa [Nat.sub_self, mlift_zero] at this

end HcR
end TRIO
