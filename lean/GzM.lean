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

/-! ## 全ての錨の列で GpT -/

def FarCW (b0 : ℕ) (ws : List (ℕ × TrioSeq)) : Prop :=
  ∀ (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), b0 ≤ b → RawWs b ws → (∀ a ∈ A, a < o) →
    (∀ a ∈ A, 1 ≤ a) → 1 ≤ o → GpT A o f b (farW b (b + liftOff f A o + 1) ws)

theorem FarCW_nil (b0 : ℕ) : FarCW b0 [] := by
  intro A o f b _ _ hA hA1 ho
  rw [show farW b (b + liftOff f A o + 1) [] = [] from rfl]
  rcases Nat.lt_or_ge o 2 with h | h
  · have ho1 : o = 1 := by omega
    subst ho1
    have hA0 : A = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => by have := hA a ha; have := hA1 a ha; omega)
    subst hA0
    exact GpT_nil1 f b
  · exact GpT_nil hA h f b

theorem farW_PVP {b0 : ℕ} {ws : List (ℕ × TrioSeq)} (hC : FarCW b0 ws) {A : List ℕ}
    {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o) (f : ℕ → ℕ) (b : ℕ)
    (hb : b0 ≤ b) (hR : RawWs b ws) : PVP A o f b (farW b (b + liftOff f A o + 1) ws) := by
  intro t
  have hk : o ≤ liftOff f A o := by unfold liftOff; omega
  rw [mlift_farW_high (show b + 1 ≤ b + liftOff f A o by omega)
    (show b + liftOff f A o < b + liftOff f A o + 1 by omega) t ws hR]
  have := hC A (o + t) f b hb hR (fun a ha => by have := hA a ha; omega) hA1 (by omega)
  rwa [liftOff_add_t hA, show b + (liftOff f A o + t) + 1 = b + liftOff f A o + 1 + t by omega]
    at this

/-! ## 潰れの塔 -/

noncomputable def towW (b : ℕ) (ws : List (ℕ × TrioSeq)) : ℕ → ℕ → TrioSeq
  | r, 0 => farW b r ws ++ [((1, r, 1) : ℕ × ℕ × ℕ)]
  | r, m + 1 => farW b r ws ++ ((1, r, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towW b ws (r + 1) m))

theorem towW_GpT {b0 : ℕ} {ws : List (ℕ × TrioSeq)} (hC : FarCW b0 ws) :
    ∀ (m : ℕ) (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), b0 ≤ b → RawWs b ws →
    (∀ a ∈ A, a < o) → (∀ a ∈ A, 1 ≤ a) → 1 ≤ o →
    GpT A o f b (towW b ws (b + liftOff f A o + 1) m)
  | 0, A, o, f, b, hb, hR, hA, hA1, ho => by
      rw [towW]
      exact PVP_to_GpT (PVP_snocz hA hA1 ho (Fr_farW _ _ ws) (farW_PVP hC hA hA1 ho f b hb hR))
  | m + 1, A, o, f, b, hb, hR, hA, hA1, ho => by
      have hAo' : ∀ a ∈ o :: A, a < o + 1 := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · omega
        · have := hA a ha; omega
      have hA1' : ∀ a ∈ o :: A, 1 ≤ a := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact ho
        · exact hA1 a ha
      obtain ⟨H, hH⟩ : ∃ H : ℕ → ℕ, H = upF o 0 f := ⟨_, rfl⟩
      have hHo : H o = 0 := by rw [hH]; simp [upF]
      have hHA : ∀ a ∈ A, H a = f a := by rw [hH]; exact upF_low hA 0 f
      have e1 : liftOff H (o :: A) (o + 1) = liftOff f A o + 1 := by
        rw [sumOn_liftOff hAo', sumOn_liftOff hA]
        simp only [sumOn, hHo, sumOn_congr hHA]
        omega
      have hL := towW_GpT hC m (o :: A) (o + 1) H b hb hR hAo' hA1' (by omega)
      rw [e1, show b + (liftOff f A o + 1) + 1 = b + liftOff f A o + 1 + 1 by omega] at hL
      have hGC : GC (o :: A) H (liftOff f A o + 1) b
          (towW b ws (b + liftOff f A o + 1 + 1) m) := by
        rw [← e1, GC_slot hAo']; exact hL
      have hRL := R_child (CtxP_RLC hA hA1 ho) hAo' Fr_nil (RLC_nil hA hA1 ho H b) hGC
        (le_of_eq e1.symm)
      have h1 := hRL (fun _ => 0) b le_rfl
      rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero, hHo, Nat.add_zero,
        List.nil_append] at h1
      have hLC := LC1_congr hA hHA h1
      have := hLC _ (Fr_farW _ _ ws) (farW_PVP hC hA hA1 ho f b hb hR)
      rw [show b + (liftOff f A o + 1) = b + liftOff f A o + 1 by omega] at this
      rw [towW]
      exact PVP_to_GpT this

theorem farW_P (b c : ℕ) (ws : List (ℕ × TrioSeq)) :
    Fr (farW b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ∧
    coneV ((farW b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) c
      (farW b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]).length := by
  refine ⟨Fr_append (Fr_farW _ _ ws) (Fr_single le_rfl _ _), ?_⟩
  have hbot : BotGe (farW b (c + 1) ws ++ ((1, c + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 [])
      (0 + 1 + 1) (c + 1) :=
    BotGe_node (Fr_farW _ _ ws) le_rfl (BotGe_top Fr_nil (c + 1))
  simp only [shiftr01, List.map_nil] at hbot
  exact coneV_of_BotGe hbot (by omega)

theorem mlift_PW {b c : ℕ} (hbc : b + 1 ≤ c) {ws : List (ℕ × TrioSeq)}
    (hR : RawWs b ws) (j : ℕ) :
    mlift (farW b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j
      = farW b (c + 1 + j) ws ++ [((1, c + 1 + j, 1) : ℕ × ℕ × ℕ)] := by
  rw [mlift_app (Fr_farW _ _ ws) (fun _ => rfl), mlift_farW_high hbc (by omega) j ws hR,
    mlift_one (show c < c + 1 by omega)]

theorem farW_flat {b : ℕ} {ws : List (ℕ × TrioSeq)} (hR : RawWs b ws) :
    ∀ m c, b + 1 ≤ c → (List.range (m + 1)).flatMap (fun j =>
      shiftr01 (j * 2) 0 (((0, c + j, 0) : ℕ × ℕ × ℕ) ::
        mlift (farW b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j))
      = ((0, c, 0) : ℕ × ℕ × ℕ) :: towW b ws (c + 1) m
  | 0, c, hc => by simp [mlift_PW hc hR, towW]
  | m + 1, c, hc => by
      rw [flatMap_range_cons _ (m + 1)]
      have e : ∀ j, shiftr01 ((j + 1) * 2) 0 (((0, c + (j + 1), 0) : ℕ × ℕ × ℕ) ::
          mlift (farW b (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c (j + 1))
          = shiftr01 2 0 (shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (farW b (c + 1 + 1) ws ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)) := by
        intro j
        rw [mlift_PW hc hR, mlift_PW (c := c + 1) (by omega) hR, shift_shift,
          show c + (j + 1) = c + 1 + j by omega, show c + 1 + (j + 1) = c + 1 + 1 + j by omega,
          show (j + 1) * 2 = j * 2 + 2 by omega]
      simp only [e]
      rw [← shift_flatMap 2 (fun j => shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (farW b (c + 1 + 1) ws ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)),
        farW_flat hR m (c + 1) (by omega)]
      have eT : shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towW b ws (c + 1 + 1) m))
          = shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towW b ws (c + 1 + 1) m) := by
        rw [show shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towW b ws (c + 1 + 1) m)
            = shiftr01 (1 + 1) 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towW b ws (c + 1 + 1) m) from rfl,
          ← shift_shift]
        rfl
      rw [towW, eT]
      simp [mlift_PW hc hR]

/-- ★ 標準の並びの後ろの遠い語（中身が遠い字だけ）の潰れ。 -/
theorem farW_collapse {b0 c0 : ℕ} {ws : List (ℕ × TrioSeq)} (hC : FarCW b0 ws) :
    FarCW b0 (ws ++ [(c0, [])]) := by
  intro A o f b hb hR hA hA1 ho
  have hR0 : RawWs b ws := fun w h => hR w (List.mem_append_left _ h)
  refine GpT_intro hA (fun R hR' g => ?_)
  rw [reliftX_farW hA hA1 b f g _ hR]
  obtain ⟨F, hF⟩ : ∃ F, F = addF f g := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = liftOff F A o := ⟨_, rfl⟩
  rw [← hF, ← hk]
  have hk1 : o ≤ k := by rw [hk]; unfold liftOff; omega
  intro u' hu X hX hRX
  rw [mlift_farW_base (show b < b + k + 1 by omega) (u' - b) _ hR,
    show b + k + 1 + (u' - b) = u' + k + 1 by omega, show b + (u' - b) = u' by omega, farW_snoc]
  have hRu : RawWs u' ws := RawWs_mono hu hR0
  obtain ⟨c, hc⟩ : ∃ c, c = u' + k := ⟨_, rfl⟩
  rw [← hc]
  have hbc : u' + 1 ≤ c := by rw [hc]; omega
  obtain ⟨hP, hcone⟩ := farW_P u' c ws
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq, U0 = ((0, c, 0) : ℕ × ℕ × ℕ) ::
      ((farW u' (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) :=
    ⟨_, rfl⟩
  have eU : ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (farW u' (c + 1) ws ++ fwW u' (c + 1) c0 [])
      = shiftr01 1 0 U0 := by
    rw [hU0]; simp [shiftr01, fwW, mlift_nil]
  rw [eU]
  have hlen : 2 ≤ U0.length := by rw [hU0]; simp
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom hP (show 1 ≤ 2 by omega) hcone
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h | h
    · exfalso
      have hl : U0.length - 1 = (((0, c, 0) : ℕ × ℕ × ℕ) ::
          (farW u' (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])).length + 0 := by
        rw [hU0]; simp
      rw [hl] at h
      unfold lev at h
      rw [hU0, show ((0, c, 0) : ℕ × ℕ × ℕ) :: ((farW u' (c + 1) ws ++
          [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)])
        = (((0, c, 0) : ℕ × ℕ × ℕ) :: (farW u' (c + 1) ws ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])) ++
          [((2, c + 1, 1) : ℕ × ℕ × ℕ)] by simp,
        entry_append_right, entry_append_right] at h
      simp [entry] at h
    · exact h
  refine (hR' F).1.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
    (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp), hU0]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] U0 1 m hlen hpV
  simp only [List.nil_append] at eO
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [eO, hU0, oper_zcone hP (show 1 ≤ 2 by omega) hcone (m' + 1), farW_flat hRu m' c hbc]
  have eS : shiftr01 1 0 (((0, c, 0) : ℕ × ℕ × ℕ) :: towW u' ws (c + 1) m')
      = ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towW u' ws (c + 1) m') := by
    simp [shiftr01]
  rw [eS]
  have hD := towW_GpT hC m' A o F u' (by omega) hRu hA hA1 ho
  rw [← hk, ← hc] at hD
  have h := GpT_elim0 hD hR'
  rw [← hk] at h
  have := h u' le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero, ← hc] at this

end GzM
end TRIO
