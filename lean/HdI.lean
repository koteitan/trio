/-
HdI.lean: 木の単位の F のタイの子の並びの最後に、高い塊（段 u+τ の節点を含む）を置く生成器の部品（HcR の写し）。

    okRNt A0 o u X := Fr X ∧ RNt A0 o 0 u X
    GoodChtX_snocN: GoodChtX Lds → GoodLowT u us → okRNt X → GoodChtX (Lds ++ [us ++ [UT.ch X]])
-/
import HdH

namespace TRIO
namespace HdI

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH

def okRNt (A0 : List ℕ) (o u : ℕ) (X : TrioSeq) : Prop := Fr X ∧ RNt A0 o (fun _ => 0) u X

theorem okRNt_nil {A0 : List ℕ} {o : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) (hAo : ∀ a ∈ A0, a < o)
    (u : ℕ) : okRNt A0 o u [] := ⟨Fr_nil, RNt_nil hA01 ho hAo _ _⟩

theorem okRNt_load {A0 : List ℕ} {o u : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) {X : TrioSeq}
    (h : okRNt A0 o u X) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    okRNt A0 o u (X ++ shiftr01 1 0 Z) :=
  ⟨Fr_append h.1 (Fr_shift1 Z), slot_load (RNt_ax hA01 ho _) h.1 h.2 Z hZ hb⟩

theorem okRNt_node {A0 : List ℕ} {o u τ : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o)
    (hAo : ∀ a ∈ A0, a < o) (hτ : τ ≤ o) {X L : TrioSeq} (A' : List ℕ)
    (hA' : A0.filter (fun a => decide (a < τ)) = A') (h : okRNt A0 o u X) (hL : GPF A' τ u L) :
    okRNt A0 o u (X ++ ((1, u + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  refine ⟨Fr_append h.1 (Fr_node _ _),
    RNt_node hA01 ho hAo h.1 h.2 ?_ (by rw [liftOff_zeroF]; exact hτ)⟩
  rw [GC_zeroF, hA']; exact hL.1

theorem okRNt_tie {A0 : List ℕ} {o u : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) {X : TrioSeq}
    (h : okRNt A0 o u X) {D : TrioSeq} (hD : GF 1 u D) :
    okRNt A0 o u (X ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) := by
  have := ((Gof_one_iff u D).mp hD.1) (RNt A0 o (fun _ => 0)) (RNt_ax hA01 ho _) u le_rfl X h.1 h.2
  rw [Nat.sub_self, mlift_zero] at this
  exact ⟨Fr_append h.1 (Fr_node _ _), this⟩

/-- ★ F のタイの子の並び（低い並び us のあとに高い塊 X）を足す。 -/
theorem GoodChtX_snocN {A0 : List ℕ} {o u : ℕ} {Lds : List (List UT)}
    (hL : GoodChtX A0 o (fun _ => 0) u Lds) {us : List UT} (hus : GoodLowT u us)
    {X : TrioSeq} (hX : okRNt A0 o u X) : GoodChtX A0 o (fun _ => 0) u (Lds ++ [us ++ [UT.ch X]]) := by
  have := (RNt_okW hX.2).2.2 u le_rfl us hus Lds hL
  rwa [Nat.sub_self, mlift_zero] at this

end HdI
end TRIO
