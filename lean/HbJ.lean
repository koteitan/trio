/-
HbJ.lean: F のタイの本数つきの遠い語の生成器の部品（HaG の写し）。

- okRAn A0 o n u X := Fr X ∧ RAn A0 o 0 n u X。
  荷（slot_load）、段 u+τ（1 ≤ τ ≤ o）の節点（RAn_node）、子つきの単位のタイ（GTs の nslot）。
- PVF_farWAn: 遠い語の並び（語ごとに F のタイの本数を持つ）は節点の子の並び（語の述語）。
-/
import HaG
import HbI

namespace TRIO
namespace HbJ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF HaG HbD HbE HbF HbG HbH HbI

/-! ## 中身 -/

def okRAn (A0 : List ℕ) (o n u : ℕ) (X : TrioSeq) : Prop := Fr X ∧ RAn A0 o (fun _ => 0) n u X

theorem okRAn_nil {A0 : List ℕ} {o : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) (n u : ℕ) :
    okRAn A0 o n u [] :=
  ⟨Fr_nil, RAn_nil (GTWAn_nil n A0 o hA01 ho) _ u⟩

theorem okRAn_load {A0 : List ℕ} {o n u : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) {X : TrioSeq}
    (h : okRAn A0 o n u X) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    okRAn A0 o n u (X ++ shiftr01 1 0 Z) :=
  ⟨Fr_append h.1 (Fr_shift1 Z), slot_load (RAn_ax hA01 ho _ n) h.1 h.2 Z hZ hb⟩

theorem okRAn_node {A0 : List ℕ} {o n u τ : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o)
    (hAo : ∀ a ∈ A0, a < o) (hτ : τ ≤ o) {X L : TrioSeq} (A' : List ℕ)
    (hA' : A0.filter (fun a => decide (a < τ)) = A') (h : okRAn A0 o n u X) (hL : GPF A' τ u L) :
    okRAn A0 o n u (X ++ ((1, u + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  refine ⟨Fr_append h.1 (Fr_node _ _),
    RAn_node hA01 ho hAo h.1 h.2 ?_ (by rw [liftOff_zeroF]; exact hτ)⟩
  rw [GC_zeroF, hA']; exact hL.1

theorem okRAn_tie {A0 : List ℕ} {o n u : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) {X : TrioSeq}
    (h : okRAn A0 o n u X) {D : TrioSeq} (hD : GF 1 u D) :
    okRAn A0 o n u (X ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) := by
  have := ((Gof_one_iff u D).mp hD.1) (RAn A0 o (fun _ => 0) n) (RAn_ax hA01 ho _ n) u le_rfl X
    h.1 h.2
  rw [Nat.sub_self, mlift_zero] at this
  exact ⟨Fr_append h.1 (Fr_node _ _), this⟩

/-! ## 並び -/

def OkWsAn (A0 : List ℕ) (o b : ℕ) (ws : List (ℕ × ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, w.2.1 ≤ b ∧ okRAn A0 o w.1 w.2.1 w.2.2

theorem OkWsAn_nil (A0 : List ℕ) (o b : ℕ) : OkWsAn A0 o b [] := fun _ h => by simp at h

theorem OkWsAn_cons {A0 : List ℕ} {o b n u : ℕ} (hub : u ≤ b) {X : TrioSeq} (h : okRAn A0 o n u X)
    {ws : List (ℕ × ℕ × TrioSeq)} (hs : OkWsAn A0 o b ws) : OkWsAn A0 o b ((n, u, X) :: ws) := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact ⟨hub, h⟩
  · exact hs w hw

theorem RawWsAn_of_OkWsAn {A0 : List ℕ} {o b : ℕ} {ws : List (ℕ × ℕ × TrioSeq)}
    (h : OkWsAn A0 o b ws) : RawWsAn A0 o (fun _ => 0) b ws := fun w hw => by
  have hok := RAn_okWA (h w hw).2.2
  exact ⟨(h w hw).1, (h w hw).2.1, hok.1, hok.2.1⟩

theorem FarCAn_ofA {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} (b0 : ℕ) :
    ∀ ws : List (ℕ × ℕ × TrioSeq), (∀ w ∈ ws, okWAn A0 k0 H w.1 w.2.1 w.2.2) →
      FarCAn A0 k0 H b0 ws := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil => intro _; exact FarCAn_nil A0 k0 H b0
  | append_singleton ws w ih =>
      intro hok
      have hw := hok w (List.mem_append_right _ (List.mem_singleton_self _))
      exact hw.2.2 b0 ws (ih (fun w' h' => hok w' (List.mem_append_left _ h')))

theorem FarCAn_of_OkWsAn {A0 : List ℕ} {o b : ℕ} {ws : List (ℕ × ℕ × TrioSeq)}
    (h : OkWsAn A0 o b ws) (b0 : ℕ) : FarCAn A0 o (fun _ => 0) b0 ws :=
  FarCAn_ofA b0 ws (fun w hw => RAn_okWA (h w hw).2.2)

/-- ★ 遠い語の並び（語ごとに F のタイの本数と錨つきの中身）は節点の子の並び。 -/
theorem PVF_farWAn {A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ A0, a < o) (hA1 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) (b : ℕ) (ws : List (ℕ × ℕ × TrioSeq)) (h : OkWsAn A0 o b ws) :
    PVF A0 o b (farWn b (b + o + 1) ws) := by
  have := farWAn_PVP (FarCAn_of_OkWsAn h b) (fun _ => 0) (S := []) (o := o) (f := fun _ => 0)
    (fun a _ => by simp [addF]) le_rfl (RawWsAn_of_OkWsAn h) (by simp) (by simpa using hA)
    (by simpa using hA1) ho (by simp) (by rw [reOff_zz]; simp [liftOff_zeroF])
  simp only [List.nil_append, liftOff_zeroF, relWsn_zero] at this
  exact ⟨this, Fr_farWn _ _ _⟩

end HbJ
end TRIO
