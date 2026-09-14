/-
HcG.lean: 子を中身と同じ形にした遠い語の生成器の部品（HbJ の写し）。

- 子: okCh v D := Fr D ∧ ChOK v D。okCh_nil（空の F のタイ）、okCh_load（荷）、okCh_tie（子つきの単位のタイ）。
  子の並び: GoodLc_nil（潰れ）、GoodLc_snoc。
- 中身: okRAc A0 o u X := Fr X ∧ RAc A0 o 0 u X。nil / load / node / tie。
- 並び: OkWsAc、FarCAc_of_OkWsAc、PVF_farWAc（語ごとに F のタイの子の並びと錨つきの中身）。
-/
import HaG
import HcF

namespace TRIO
namespace HcG

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcB HcC HcD HcE HcF

/-! ## 子 -/

theorem ChOK_nil (v : ℕ) : ChOK v [] := by
  refine ⟨fun h => absurd rfl h, LowC_nil _, fun u _ Lds hL => ?_⟩
  rw [mlift_nil]
  exact GoodLc_Fsucc hL

def okCh (v : ℕ) (D : TrioSeq) : Prop := Fr D ∧ ChOK v D

theorem okCh_nil (v : ℕ) : okCh v [] := ⟨Fr_nil, ChOK_nil v⟩

theorem okCh_load {v : ℕ} {D : TrioSeq} (h : okCh v D) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * v))
    (hb : based Z) : okCh v (D ++ shiftr01 1 0 Z) :=
  ⟨Fr_append h.1 (Fr_shift1 Z), slot_load ChOK_ax h.1 h.2 Z hZ hb⟩

theorem okCh_tie {v : ℕ} {D : TrioSeq} (h : okCh v D) {E : TrioSeq} (hE : GF 1 v E) :
    okCh v (D ++ ((1, v + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 E) := by
  have := ((Gof_one_iff v E).mp hE.1) ChOK ChOK_ax v le_rfl D h.1 h.2
  rw [Nat.sub_self, mlift_zero] at this
  exact ⟨Fr_append h.1 (Fr_node _ _), this⟩

theorem GoodLc_nil (v : ℕ) : GoodLc v [] :=
  ⟨fun _ h => by simp at h, fun _ _ _ _ _ _ _ hC => farWAc_collapse hC⟩

theorem GoodLc_snoc {v : ℕ} {Lds : List TrioSeq} (hL : GoodLc v Lds) {D : TrioSeq} (hD : okCh v D) :
    GoodLc v (Lds ++ [D]) := by
  have := hD.2.2.2 v le_rfl Lds hL
  rwa [Nat.sub_self, mlift_zero] at this

/-! ## 中身 -/

def okRAc (A0 : List ℕ) (o u : ℕ) (X : TrioSeq) : Prop := Fr X ∧ RAc A0 o (fun _ => 0) u X

theorem okRAc_nil (A0 : List ℕ) (o u : ℕ) : okRAc A0 o u [] := ⟨Fr_nil, RAc_nil _ _ _ _⟩

theorem okRAc_load {A0 : List ℕ} {o u : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) {X : TrioSeq}
    (h : okRAc A0 o u X) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    okRAc A0 o u (X ++ shiftr01 1 0 Z) :=
  ⟨Fr_append h.1 (Fr_shift1 Z), slot_load (RAc_ax hA01 ho _) h.1 h.2 Z hZ hb⟩

theorem okRAc_node {A0 : List ℕ} {o u τ : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o)
    (hAo : ∀ a ∈ A0, a < o) (hτ : τ ≤ o) {X L : TrioSeq} (A' : List ℕ)
    (hA' : A0.filter (fun a => decide (a < τ)) = A') (h : okRAc A0 o u X) (hL : GPF A' τ u L) :
    okRAc A0 o u (X ++ ((1, u + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  refine ⟨Fr_append h.1 (Fr_node _ _),
    RAc_node hA01 ho hAo h.1 h.2 ?_ (by rw [liftOff_zeroF]; exact hτ)⟩
  rw [GC_zeroF, hA']; exact hL.1

theorem okRAc_tie {A0 : List ℕ} {o u : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) {X : TrioSeq}
    (h : okRAc A0 o u X) {D : TrioSeq} (hD : GF 1 u D) :
    okRAc A0 o u (X ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) := by
  have := ((Gof_one_iff u D).mp hD.1) (RAc A0 o (fun _ => 0)) (RAc_ax hA01 ho _) u le_rfl X h.1 h.2
  rw [Nat.sub_self, mlift_zero] at this
  exact ⟨Fr_append h.1 (Fr_node _ _), this⟩

/-! ## 並び -/

def OkWsAc (A0 : List ℕ) (o b : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, w.2.1 ≤ b ∧ GoodLc w.2.1 w.1 ∧ okRAc A0 o w.2.1 w.2.2

theorem OkWsAc_nil (A0 : List ℕ) (o b : ℕ) : OkWsAc A0 o b [] := fun _ h => by simp at h

theorem OkWsAc_cons {A0 : List ℕ} {o b u : ℕ} (hub : u ≤ b) {Lds : List TrioSeq} (hL : GoodLc u Lds)
    {X : TrioSeq} (h : okRAc A0 o u X) {ws : List (List TrioSeq × ℕ × TrioSeq)} (hs : OkWsAc A0 o b ws) :
    OkWsAc A0 o b ((Lds, u, X) :: ws) := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact ⟨hub, hL, h⟩
  · exact hs w hw

theorem RawWsAc_of_OkWsAc {A0 : List ℕ} {o b : ℕ} (ho : 1 ≤ o) {ws : List (List TrioSeq × ℕ × TrioSeq)}
    (h : OkWsAc A0 o b ws) : RawWsAc A0 o (fun _ => 0) b ws := fun w hw => by
  have hok := RAc_okWA (h w hw).2.2.2
  have hKge : o ≤ reOff (fun _ => 0) (fun _ => 0) A0 o := by unfold reOff; omega
  exact ⟨(h w hw).1, fun D hD => ⟨((h w hw).2.1.1 D hD).1,
      LowC_mono (show w.2.1 + 1 ≤ w.2.1 + reOff (fun _ => 0) (fun _ => 0) A0 o by omega)
        ((h w hw).2.1.1 D hD).2⟩,
    (h w hw).2.2.1, hok.1, hok.2.1⟩

theorem FarCAc_of_OkWsAc {A0 : List ℕ} {o b : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) :
    ∀ ws : List (List TrioSeq × ℕ × TrioSeq), OkWsAc A0 o b ws →
      ∀ b0, FarCAc A0 o (fun _ => 0) b0 ws := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil => intro _ b0; exact FarCAc_nil _ _ _ b0
  | append_singleton ws w ih =>
      intro h b0
      have hw := h w (List.mem_append_right _ (List.mem_singleton_self _))
      have hok := RAc_okWA hw.2.2.2
      have hG := GoodLc_GoodCh hw.2.1 hA01 ho (fun _ => 0)
      have := hok.2.2 w.2.1 le_rfl w.1 hG b0 ws
        (ih (fun w' h' => h w' (List.mem_append_left _ h')) b0)
      rwa [Nat.sub_self, mlift_zero] at this

/-- ★ 遠い語の並び（語ごとに F のタイの子の並びと錨つきの中身）は節点の子の並び。 -/
theorem PVF_farWAc {A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ A0, a < o) (hA1 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) (b : ℕ) (ws : List (List TrioSeq × ℕ × TrioSeq)) (h : OkWsAc A0 o b ws) :
    PVF A0 o b (farWc b (b + o + 1) ws) := by
  have := farWAc_PVP (FarCAc_of_OkWsAc hA1 ho ws h b) (fun _ => 0) (S := []) (o := o)
    (f := fun _ => 0) (fun a _ => by simp [addF]) le_rfl (RawWsAc_of_OkWsAc ho h) (by simp)
    (by simpa using hA) (by simpa using hA1) ho (by simp)
    (by rw [HaG.reOff_zz]; simp [liftOff_zeroF])
  simp only [List.nil_append, liftOff_zeroF, relWsc_zero] at this
  exact ⟨this, Fr_farWc _ _ _⟩

end HcG
end TRIO
