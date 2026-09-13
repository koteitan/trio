/-
GzM.lean: 遠い字のあとの中身を「低い列 Y（段 c で与える）」にした遠い語（GzH の単位の一般化、追記539）。

    LowC v Y      := Y の全ての列が、Y の中の行 0 の祖先（自分を含む）に行 1 ≤ v の列を持つ
    fwW b r c Y   := (1,r,1) :: ((1,r,1) :: mlift Y c (b − c))↑1
    farW b r ws   := ws.flatMap (fun w => fwW b r w.1 w.2)
    RawW b w      := w.1 ≤ b ∧ Fr w.2 ∧ Hd w.2 ∧ LowC (w.1 + 1) w.2

低い列は、節点の段以上の持ち上げ（閾値 ≥ b+1）でも再持ち上げでも動かず、段 b の持ち上げでは段と一緒に動く。
-/
import GzI

namespace TRIO
namespace GzM

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI

/-! ## 低い列 -/

def LowC (v : ℕ) (Y : TrioSeq) : Prop :=
  ∀ i, i < Y.length → ∃ k, Relation.ReflTransGen (nextrel0 Y) k i ∧ entry Y 1 k ≤ v

theorem LowC_mono {v w : ℕ} (h : v ≤ w) {Y : TrioSeq} (hY : LowC v Y) : LowC w Y :=
  fun i hi => by
    obtain ⟨k, hk, hle⟩ := hY i hi
    exact ⟨k, hk, le_trans hle h⟩

theorem LowC_mlift {c : ℕ} {Y : TrioSeq} (hY : LowC (c + 1) Y) (t : ℕ) :
    LowC (c + 1 + t) (mlift Y c t) := by
  intro i hi
  rw [mlift_length] at hi
  obtain ⟨k, hk, hle⟩ := hY i hi
  have hkY : k < Y.length := lt_of_le_of_lt (rtg0_le hk) hi
  refine ⟨k, ?_, ?_⟩
  · rw [mlift_eq_slift]; exact rtg0_slift'.mpr hk
  · rw [entry1_mlift hkY]; split_ifs <;> omega

/-! ## 語 -/

noncomputable def fwW (b r c : ℕ) (Y : TrioSeq) : TrioSeq :=
  ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: mlift Y c (b - c))

theorem Fr_fwW (b r c : ℕ) (Y : TrioSeq) : Fr (fwW b r c Y) := Fr_letter _ _

theorem Hd_fwW (b r c : ℕ) (Y : TrioSeq) : Hd (fwW b r c Y) := Hd_letter _ _

theorem Fr_FLW {r : ℕ} {Y : TrioSeq} (hY : Fr Y) : Fr (((1, r, 1) : ℕ × ℕ × ℕ) :: Y) := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · show 1 ≤ 1; omega
  · exact hY y hy

theorem mlift_fwW_high {b v r c : ℕ} (hv : b + 1 ≤ v) (hvr : v < r) (hcb : c ≤ b) {Y : TrioSeq}
    (hY : Fr Y) (hL : LowC (c + 1) Y) (t : ℕ) : mlift (fwW b r c Y) v t = fwW b (r + t) c Y := by
  unfold fwW
  rw [mlift_letter hvr (Fr_FLW (Fr_mlift hY c (b - c))) t]
  have hL' : LowC v (mlift Y c (b - c)) := LowC_mono (by omega) (LowC_mlift hL (b - c))
  have e := mlift_append_low (A := [((1, r, 1) : ℕ × ℕ × ℕ)]) hL' t
  simp only [List.singleton_append] at e
  rw [e, mlift_one hvr]
  rfl

theorem mlift_fwW_base {b r c : ℕ} (hbr : b < r) (hcb : c ≤ b) {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y)
    (t : ℕ) : mlift (fwW b r c Y) b t = fwW (b + t) (r + t) c Y := by
  unfold fwW
  rw [mlift_letter hbr (Fr_FLW (Fr_mlift hY c (b - c))) t]
  have e := mlift_app (W := [((1, r, 1) : ℕ × ℕ × ℕ)]) (U := mlift Y c (b - c))
    (Fr_single le_rfl _ _) (Hd_mlift hH c (b - c)) b t
  simp only [List.singleton_append] at e
  rw [e, mlift_one hbr]
  have e2 := mlift_mlift Y c (b - c) t
  rw [show c + (b - c) = b by omega] at e2
  rw [e2, show b - c + t = b + t - c by omega]
  rfl

theorem reliftX_fwW {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (b : ℕ) (f g : ℕ → ℕ) {c : ℕ} (hcb : c ≤ b) {Y : TrioSeq} (hY : Fr Y) (hL : LowC (c + 1) Y) :
    reliftX b f g A (fwW b (b + liftOff f A o + 1) c Y)
      = fwW b (b + liftOff (addF f g) A o + 1) c Y := by
  unfold fwW
  rw [show b + liftOff f A o + 1 = b + (liftOff f A o + 1) by omega,
    reliftX_node (Fr_FLW (Fr_mlift hY c (b - c))) b (liftOff f A o + 1) 1 f g A]
  have hlow : lowP f A (liftOff f A o + 1) = A :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  rw [hlow, reOff_above hA f g 1]
  have hL' : LowC (b + 1) (mlift Y c (b - c)) := by
    have := LowC_mlift hL (b - c)
    rwa [show c + 1 + (b - c) = b + 1 by omega] at this
  have e : reliftX b f g A ([((1, b + (liftOff f A o + 1), 1) : ℕ × ℕ × ℕ)] ++ mlift Y c (b - c))
      = reliftX b f g A [((1, b + (liftOff f A o + 1), 1) : ℕ × ℕ × ℕ)] ++ mlift Y c (b - c) := by
    unfold reliftX
    exact slift_append_low hL' (fun m hm => reStair_tie b f g hA1 hm)
  simp only [List.singleton_append] at e
  rw [e]
  have e1 : reliftX b f g A [((1, b + (liftOff f A o + 1), 1) : ℕ × ℕ × ℕ)]
      = [((1, b + (liftOff (addF f g) A o + 1), 1) : ℕ × ℕ × ℕ)] := by
    have := reliftX_node (V := []) Fr_nil b (liftOff f A o + 1) 1 f g A
    rw [hlow, reOff_above hA f g 1] at this
    simpa [shiftr01, reliftX, slift_nil] using this
  rw [e1]
  simp only [List.singleton_append, ← Nat.add_assoc]

/-! ## 並び -/

noncomputable def farW (b r : ℕ) (ws : List (ℕ × TrioSeq)) : TrioSeq := ws.flatMap (fun w => fwW b r w.1 w.2)

def RawW (b : ℕ) (w : ℕ × TrioSeq) : Prop := w.1 ≤ b ∧ Fr w.2 ∧ Hd w.2 ∧ LowC (w.1 + 1) w.2

def RawWs (b : ℕ) (ws : List (ℕ × TrioSeq)) : Prop := ∀ w ∈ ws, RawW b w

theorem RawW_mono {b b' : ℕ} (h : b ≤ b') {w : ℕ × TrioSeq} (hw : RawW b w) : RawW b' w :=
  ⟨le_trans hw.1 h, hw.2.1, hw.2.2.1, hw.2.2.2⟩

theorem RawWs_mono {b b' : ℕ} (h : b ≤ b') {ws : List (ℕ × TrioSeq)} (hR : RawWs b ws) :
    RawWs b' ws := fun w hw => RawW_mono h (hR w hw)

theorem RawWs_tail {b : ℕ} {w : ℕ × TrioSeq} {ws : List (ℕ × TrioSeq)} (hR : RawWs b (w :: ws)) :
    RawWs b ws := fun w' h => hR w' (List.mem_cons_of_mem _ h)

theorem farW_cons (b r : ℕ) (w : ℕ × TrioSeq) (ws : List (ℕ × TrioSeq)) :
    farW b r (w :: ws) = fwW b r w.1 w.2 ++ farW b r ws := by simp [farW]

theorem farW_snoc (b r : ℕ) (ws : List (ℕ × TrioSeq)) (w : ℕ × TrioSeq) :
    farW b r (ws ++ [w]) = farW b r ws ++ fwW b r w.1 w.2 := by simp [farW, List.flatMap_append]

theorem Fr_farW (b r : ℕ) (ws : List (ℕ × TrioSeq)) : Fr (farW b r ws) := by
  intro y hy
  simp only [farW, List.mem_flatMap] at hy
  obtain ⟨w, -, hy⟩ := hy
  exact Fr_fwW b r w.1 w.2 y hy

theorem Hd_farW (b r : ℕ) : ∀ ws : List (ℕ × TrioSeq), Hd (farW b r ws)
  | [] => fun h => absurd rfl h
  | w :: ws => fun _ => by rw [farW_cons]; rfl

theorem mlift_farW_high {b v r : ℕ} (hv : b + 1 ≤ v) (hvr : v < r) (t : ℕ) :
    ∀ ws, RawWs b ws → mlift (farW b r ws) v t = farW b (r + t) ws
  | [] => fun _ => by simp [farW, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farW_cons, farW_cons, mlift_app (Fr_fwW b r _ _) (Hd_farW b r ws),
        mlift_fwW_high hv hvr hw.1 hw.2.1 hw.2.2.2 t, mlift_farW_high hv hvr t ws (RawWs_tail hR)]

theorem mlift_farW_base {b r : ℕ} (hbr : b < r) (t : ℕ) :
    ∀ ws, RawWs b ws → mlift (farW b r ws) b t = farW (b + t) (r + t) ws
  | [] => fun _ => by simp [farW, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farW_cons, farW_cons, mlift_app (Fr_fwW b r _ _) (Hd_farW b r ws),
        mlift_fwW_base hbr hw.1 hw.2.1 hw.2.2.1 t, mlift_farW_base hbr t ws (RawWs_tail hR)]

theorem reliftX_farW {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (b : ℕ) (f g : ℕ → ℕ) : ∀ ws, RawWs b ws →
    reliftX b f g A (farW b (b + liftOff f A o + 1) ws)
      = farW b (b + liftOff (addF f g) A o + 1) ws
  | [] => fun _ => by simp [farW, reliftX, slift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farW_cons, farW_cons, reliftX_app (Fr_fwW _ _ _ _) (Hd_farW _ _ ws),
        reliftX_fwW hA hA1 b f g hw.1 hw.2.1 hw.2.2.2, reliftX_farW hA hA1 b f g ws (RawWs_tail hR)]

end GzM
end TRIO
