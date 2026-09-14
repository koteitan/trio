/-
HaV.lean: F の語のあとに、中身が荷と子つきのタイ（段 1）の遠い語の並び（節点の子の並び、語の述語）。

- okWFkF_tie: 中身の族 okWFk 1 に子つきのタイを足す（GTs の nslot、HaS.okWFk_ax）。
- PVF_farWF: Pf r ++ farW b r ws（中身は okWFk 1）は PVF（HaR.farWFk_PVP、HaS.FarCFk_of）。
-/
import HaS

namespace TRIO
namespace HaV

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaI HaR HaS

theorem okWFkF_tie {u : ℕ} {X : TrioSeq} (h : okWFkF 1 u X) {D : TrioSeq} (hD : GF 1 u D) :
    okWFkF 1 u (X ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) := by
  have := ((Gof_one_iff u D).mp hD.1) (okWFk 1) (okWFk_ax le_rfl) u le_rfl X h.1 h.2
  rw [Nat.sub_self, mlift_zero] at this
  exact ⟨Fr_append h.1 (Fr_node _ _), this⟩

def OkWsFk (b : ℕ) (ws : List (ℕ × TrioSeq)) : Prop :=
  RawWsk 1 b ws ∧ ∀ w ∈ ws, okWFk 1 w.1 w.2

theorem OkWsFk_nil (b : ℕ) : OkWsFk b [] := ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

theorem OkWsFk_cons {b u : ℕ} (hub : u ≤ b) {X : TrioSeq} (h : okWFkF 1 u X)
    {ws : List (ℕ × TrioSeq)} (hs : OkWsFk b ws) : OkWsFk b ((u, X) :: ws) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨hub, h.1, h.2.1, h.2.2.1⟩
    · exact hs.1 w hw
  · rcases List.mem_cons.mp hw with rfl | hw
    · exact h.2
    · exact hs.2 w hw

/-- ★ F の語のあとに、中身が okWFk 1 の遠い語の並び。 -/
theorem PVF_farWF {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (b : ℕ) (ws : List (ℕ × TrioSeq)) (h : OkWsFk b ws) :
    PVF A o b (Pf (b + o + 1) ++ farW b (b + o + 1) ws) := by
  have := farWFk_PVP (FarCFk_of 1 b ws h.2) hA hA1 ho (fun _ => 0)
    (fun a ha => by rw [liftVal_zeroF]; exact hA1 a ha) (by rw [liftOff_zeroF]; exact ho) b le_rfl h.1
  rw [liftOff_zeroF] at this
  exact ⟨this, Fr_PWF _ _ _⟩

end HaV
end TRIO
