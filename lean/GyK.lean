/-
GyK.lean: 生成器のための組み立て規則（状態 0、Fr つき）。

    GPF A o b E := GpT A o 0 b E ∧ Fr E          （節点の子の並び）
    PVF A o b W := PVP A o 0 b W ∧ Fr W          （節点の下の語）
    RLF A o b Y := RLC A o 0 b Y ∧ Fr Y          （節点の下の字の中身）
-/
import GyJ

namespace TRIO
namespace GyK

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ

/-! ## 状態 0 -/

theorem stepSum_zeroF' (b m : ℕ) : ∀ L : List ℕ, stepSum b (fun _ => 0) L m = 0
  | [] => rfl
  | x :: L => by simp [stepSum, stepSum_zeroF' b m L]

theorem liftVal_zeroF (A : List ℕ) (a : ℕ) : liftVal (fun _ => 0) A a = a := by
  unfold liftVal; simp [stepSum_zeroF']

theorem liftOff_zeroF (A : List ℕ) (o : ℕ) : liftOff (fun _ => 0) A o = o := by
  unfold liftOff; simp [stepSum_zeroF']

theorem sumOn_zeroF : ∀ L : List ℕ, sumOn (fun _ => 0) L = 0
  | [] => rfl
  | x :: L => by simp [sumOn, sumOn_zeroF L]

theorem lowP_zeroF (A : List ℕ) (τ : ℕ) :
    lowP (fun _ => 0) A τ = A.filter (fun a => decide (a < τ)) := by
  unfold lowP; simp only [liftVal_zeroF]

theorem GC_zeroF (A : List ℕ) (τ b : ℕ) (L : TrioSeq) :
    GC A (fun _ => 0) τ b L = GpT (A.filter (fun a => decide (a < τ))) τ (fun _ => 0) b L := by
  unfold GC; rw [lowP_zeroF, sumOn_zeroF, Nat.sub_zero]

/-! ## タイの子（錨なし、行 1 の差 1） -/

theorem GpT_nil1 (f : ℕ → ℕ) (b : ℕ) : GpT [] 1 f b [] := by
  refine GpT_intro (fun a ha => by simp at ha) (fun R hR g => ?_)
  have e1 : liftOff (addF f g) [] 1 = 1 := by simp [liftOff, stepSum]
  have e2 : reliftX b f g [] [] = [] := by unfold reliftX; exact slift_nil _
  rw [e1, e2]
  exact GTs_nil b (R (addF f g)) (hR (addF f g)).1

theorem GTs_of_GpT {f : ℕ → ℕ} {u : ℕ} {D : TrioSeq} (h : GpT [] 1 f u D) : GTs u D := by
  intro ok hok
  have hid : ∀ (b : ℕ) (f' g : ℕ → ℕ) (X : TrioSeq), reliftX b f' g [] X = X := by
    intro b f' g X
    unfold reliftX
    have : reStair b f' g [] = fun m => m := by funext m; simp [reStair, reStep]
    rw [this]; exact slift_id X
  have hR : CtxP (GC []) [] 1 (fun _ => ok) := fun f' =>
    ⟨hok, fun _ _ _ _ hX => hX, fun g b X _ hX => by rw [hid]; exact hX,
     fun s hs2 hs => absurd hs (by simp [liftOff, stepSum]; omega)⟩
  have := GpT_elim0 h hR
  simpa [liftOff, stepSum] using this

/-! ## 節点の子の並び -/

def GPF (A : List ℕ) (o b : ℕ) (E : TrioSeq) : Prop := GpT A o (fun _ => 0) b E ∧ Fr E

theorem GF_of_GPF {u : ℕ} {D : TrioSeq} (h : GPF [] 1 u D) : GF 1 u D :=
  ⟨(Gof_one_iff u D).mpr (GTs_of_GpT h.1), h.2⟩

theorem GPF_nil1 (b : ℕ) : GPF [] 1 b [] := ⟨GpT_nil1 _ b, Fr_nil⟩

theorem GPF_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (ho : 2 ≤ o) (b : ℕ) :
    GPF A o b [] := ⟨GpT_nil hA ho _ b, Fr_nil⟩

theorem GPF_load {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {b : ℕ} {K Z : TrioSeq} (h : GPF A o b K) (hZ : Z ∈ Wg (2 * b)) (hb : based Z) :
    GPF A o b (K ++ shiftr01 1 0 Z) :=
  ⟨GpT_load hA hA1 ho h.2 h.1 hZ hb, Fr_append h.2 (Fr_shift1 Z)⟩

theorem GPF_node {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {b τ : ℕ} {C L : TrioSeq} (A' : List ℕ) (hA' : A.filter (fun a => decide (a < τ)) = A')
    (h : GPF A o b C) (hL : GPF A' τ b L) :
    GPF A o b (C ++ ((1, b + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  refine ⟨GpT_node hA hA1 ho h.2 hL.2 h.1 ?_, Fr_append h.2 (Fr_node _ _)⟩
  rw [GC_zeroF, hA']; exact hL.1

/-! ## 節点の下の語 -/

def PVF (A : List ℕ) (o b : ℕ) (W : TrioSeq) : Prop := PVP A o (fun _ => 0) b W ∧ Fr W

theorem GPF_of_PVF {A : List ℕ} {o b : ℕ} {W : TrioSeq} (h : PVF A o b W) : GPF A o b W :=
  ⟨PVP_to_GpT h.1, h.2⟩

theorem PVF_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (ho : 2 ≤ o) (b : ℕ) :
    PVF A o b [] := ⟨PVP_nil hA ho _ b, Fr_nil⟩

theorem PVF_nil1 (b : ℕ) : PVF [] 1 b [] := by
  refine ⟨fun t => ?_, Fr_nil⟩
  rw [mlift_nil]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact GpT_nil1 _ b
  · exact GpT_nil (fun a ha => by simp at ha) (by omega) _ b

/-! ## 節点の下の字の中身 -/

def RLF (A : List ℕ) (o b : ℕ) (Y : TrioSeq) : Prop := RLC A o (fun _ => 0) b Y ∧ Fr Y

theorem PVF_snoc {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {b : ℕ} {W Y : TrioSeq}
    (h : PVF A o b W) (hY : RLF A o b Y) :
    PVF A o b (W ++ ((1, b + o + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y) := by
  have hL := hY.1 (fun _ => 0) b le_rfl
  have e : addF (fun _ => 0) (fun _ => 0) = (fun _ => (0 : ℕ)) := by funext a; simp [addF]
  rw [e, Nat.sub_self, mlift_zero, reliftX_zero] at hL
  have hL2 := hL W h.2 h.1
  simp only [Nat.add_zero, liftOff_zeroF] at hL2
  exact ⟨hL2, Fr_append h.2 (Fr_letter _ _)⟩

theorem RLF_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (b : ℕ) : RLF A o b [] := ⟨RLC_nil hA hA1 ho _ b, Fr_nil⟩

theorem RLF_load {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {b : ℕ} {K Z : TrioSeq} (h : RLF A o b K) (hZ : Z ∈ Wg (2 * b)) (hb : based Z) :
    RLF A o b (K ++ shiftr01 1 0 Z) :=
  ⟨slot_load (RLC_ax hA hA1 ho _) h.2 h.1 Z hZ hb, Fr_append h.2 (Fr_shift1 Z)⟩

/-- 字の中身の節点（行 1 の差 τ ≤ o+1）と、その子の並び。τ = o+1 が F。 -/
theorem RLF_child {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {b τ : ℕ} {K L : TrioSeq} (A' : List ℕ) (hA' : (o :: A).filter (fun a => decide (a < τ)) = A')
    (hτ : τ ≤ o + 1) (h : RLF A o b K) (hL : GPF A' τ b L) :
    RLF A o b (K ++ ((1, b + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  have hAo' : ∀ a ∈ o :: A, a < o + 1 := by
    intro a ha; simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · omega
    · have := hA a ha; omega
  have hGC : GC (o :: A) (fun _ => 0) τ b L := by rw [GC_zeroF, hA']; exact hL.1
  refine ⟨R_child (CtxP_RLC hA hA1 ho) hAo' h.2 h.1 hGC (by rw [liftOff_zeroF]; exact hτ),
    Fr_append h.2 (Fr_node _ _)⟩

end GyK
end TRIO
