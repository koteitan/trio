/-
GzH.lean: 節点の下の「遠い字と単位の語」の並び（全ての錨の列と状態で GpT）。

    fwU b r us = (1,r,1) :: ((1,r,1) :: unitsC b us)↑1     （字、中身 = 遠い字 ++ 単位）
    farU b r uss = uss.flatMap (fwU b r)
    単位 = 荷（行 1 ≤ b の Wg の元）か、行 1 が b+1 の子のないタイ（GxL.unitC b）

単位は、節点の段以上の持ち上げ（mlift の閾値 ≥ b+1）でも再持ち上げ（reStair）でも動かない。
よって並びの形は (A, o, f, b) に対して b + liftOff f A o + 1 だけで決まり、GzF と同じ帰納が回る。
-/
import GzF

namespace TRIO
namespace GzH

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF

/-! ## 単位 -/

theorem RawU_mono {b b' : ℕ} (h : b ≤ b') {us : List (Option TrioSeq)} (hR : RawU b us) :
    RawU b' us :=
  fun Z hZ => ⟨Wg_mono (by omega) (hR Z hZ).1, (hR Z hZ).2⟩

def RawUs (b : ℕ) (uss : List (List (Option TrioSeq))) : Prop := ∀ us ∈ uss, RawU b us

theorem RawUs_mono {b b' : ℕ} (h : b ≤ b') {uss : List (List (Option TrioSeq))} (hR : RawUs b uss) :
    RawUs b' uss :=
  fun us hus => RawU_mono h (hR us hus)

theorem RawUs_tail {b : ℕ} {us : List (Option TrioSeq)} {uss : List (List (Option TrioSeq))}
    (hR : RawUs b (us :: uss)) : RawUs b uss :=
  fun us' h => hR us' (List.mem_cons_of_mem _ h)

theorem mlift_units_high {b v : ℕ} (hv : b + 1 ≤ v) (X : TrioSeq) :
    ∀ us : List (Option TrioSeq), RawU b us → ∀ t,
      mlift (X ++ unitsC b us) v t = mlift X v t ++ unitsC b us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ t; simp [unitsC]
  | append_singleton us o ih =>
      intro hR t
      have ih' := ih (RawU_prefix hR) t
      rw [unitsC_snoc, ← List.append_assoc]
      cases o with
      | none =>
          simp only [unitC]
          rw [mlift_snoc_low _ _ (show ((1, b + 1, 0) : ℕ × ℕ × ℕ).2.1 ≤ v from hv), ih',
            List.append_assoc]
      | some Z =>
          simp only [unitC]
          have hZ := hR Z (by simp)
          rw [mlift_append_low (low_of_Wg hZ.1 1 (show b ≤ v by omega)) t, ih', List.append_assoc]

theorem mlift_units_base {b : ℕ} {X : TrioSeq} (hX : Fr X) :
    ∀ us : List (Option TrioSeq), RawU b us → ∀ t,
      mlift (X ++ unitsC b us) b t = mlift X b t ++ unitsC (b + t) us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ t; simp [unitsC]
  | append_singleton us o ih =>
      intro hR t
      have ih' := ih (RawU_prefix hR) t
      rw [unitsC_snoc, unitsC_snoc, ← List.append_assoc]
      cases o with
      | none =>
          simp only [unitC]
          have hK : ∀ y ∈ X ++ unitsC b us, 1 ≤ y.1 := Fr_append hX (unitsC_ge b us)
          rw [mlift_snoc_cone _ _ (coneV_top hK b) t, ih']
          have e : ((((1, b + 1, 0) : ℕ × ℕ × ℕ).1, ((1, b + 1, 0) : ℕ × ℕ × ℕ).2.1 + t,
              ((1, b + 1, 0) : ℕ × ℕ × ℕ).2.2) : ℕ × ℕ × ℕ) = ((1, b + t + 1, 0) : ℕ × ℕ × ℕ) := by
            show ((1, b + 1 + t, 0) : ℕ × ℕ × ℕ) = _
            rw [show b + 1 + t = b + t + 1 by omega]
          rw [e, List.append_assoc]
      | some Z =>
          simp only [unitC]
          have hZ := hR Z (by simp)
          rw [mlift_append_low (low_of_Wg hZ.1 1 le_rfl) t, ih', List.append_assoc]

theorem reliftX_units {b : ℕ} (f g : ℕ → ℕ) {A : List ℕ} (hA1 : ∀ a ∈ A, 1 ≤ a) (X : TrioSeq) :
    ∀ us : List (Option TrioSeq), RawU b us →
      reliftX b f g A (X ++ unitsC b us) = reliftX b f g A X ++ unitsC b us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _; simp [unitsC]
  | append_singleton us o ih =>
      intro hR
      have ih' := ih (RawU_prefix hR)
      rw [unitsC_snoc, ← List.append_assoc]
      unfold reliftX at ih' ⊢
      cases o with
      | none =>
          simp only [unitC]
          rw [slift_snoc_fix _ _ (fun m hm => reStair_tie b f g hA1 hm), ih', List.append_assoc]
      | some Z =>
          simp only [unitC]
          have hZ := hR Z (by simp)
          rw [slift_append_low (low_of_Wg hZ.1 1 le_rfl) (fun m hm => reStair_low b f g A hm), ih',
            List.append_assoc]

/-! ## 語 -/

def fwU (b r : ℕ) (us : List (Option TrioSeq)) : TrioSeq :=
  ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, r, 1) : ℕ × ℕ × ℕ) :: unitsC b us)

theorem Fr_FLunits (b r : ℕ) (us : List (Option TrioSeq)) :
    Fr (((1, r, 1) : ℕ × ℕ × ℕ) :: unitsC b us) := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · show 1 ≤ 1; omega
  · exact unitsC_ge b us y hy

theorem Fr_fwU (b r : ℕ) (us : List (Option TrioSeq)) : Fr (fwU b r us) := Fr_letter _ _

theorem Hd_fwU (b r : ℕ) (us : List (Option TrioSeq)) : Hd (fwU b r us) := Hd_letter _ _

theorem mlift_one {v r : ℕ} (hvr : v < r) (t : ℕ) :
    mlift [((1, r, 1) : ℕ × ℕ × ℕ)] v t = [((1, r + t, 1) : ℕ × ℕ × ℕ)] := by
  have := mlift_letter hvr (V := []) Fr_nil t
  simpa [shiftr01, mlift_nil] using this

theorem mlift_fwU_high {b v r : ℕ} (hv : b + 1 ≤ v) (hvr : v < r) {us : List (Option TrioSeq)}
    (hR : RawU b us) (t : ℕ) : mlift (fwU b r us) v t = fwU b (r + t) us := by
  unfold fwU
  rw [mlift_letter hvr (Fr_FLunits b r us) t]
  have e := mlift_units_high hv [((1, r, 1) : ℕ × ℕ × ℕ)] us hR t
  simp only [List.singleton_append] at e
  rw [e, mlift_one hvr]
  rfl

theorem mlift_fwU_base {b r : ℕ} (hbr : b < r) {us : List (Option TrioSeq)} (hR : RawU b us)
    (t : ℕ) : mlift (fwU b r us) b t = fwU (b + t) (r + t) us := by
  unfold fwU
  rw [mlift_letter hbr (Fr_FLunits b r us) t]
  have e := mlift_units_base (b := b) (X := [((1, r, 1) : ℕ × ℕ × ℕ)])
    (Fr_single le_rfl _ _) us hR t
  simp only [List.singleton_append] at e
  rw [e, mlift_one hbr]
  rfl

theorem reliftX_fwU {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (b : ℕ) (f g : ℕ → ℕ) {us : List (Option TrioSeq)} (hR : RawU b us) :
    reliftX b f g A (fwU b (b + liftOff f A o + 1) us)
      = fwU b (b + liftOff (addF f g) A o + 1) us := by
  unfold fwU
  rw [show b + liftOff f A o + 1 = b + (liftOff f A o + 1) by omega,
    reliftX_node (Fr_FLunits b _ us) b (liftOff f A o + 1) 1 f g A]
  have hlow : lowP f A (liftOff f A o + 1) = A :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  rw [hlow, reOff_above hA f g 1]
  have e := reliftX_units f g hA1 [((1, b + (liftOff f A o + 1), 1) : ℕ × ℕ × ℕ)] us hR
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

def farU (b r : ℕ) (uss : List (List (Option TrioSeq))) : TrioSeq := uss.flatMap (fwU b r)

theorem farU_cons (b r : ℕ) (us : List (Option TrioSeq)) (uss : List (List (Option TrioSeq))) :
    farU b r (us :: uss) = fwU b r us ++ farU b r uss := by simp [farU]

theorem farU_snoc (b r : ℕ) (uss : List (List (Option TrioSeq))) (us : List (Option TrioSeq)) :
    farU b r (uss ++ [us]) = farU b r uss ++ fwU b r us := by simp [farU, List.flatMap_append]

theorem Fr_farU (b r : ℕ) (uss : List (List (Option TrioSeq))) : Fr (farU b r uss) := by
  intro y hy
  simp only [farU, List.mem_flatMap] at hy
  obtain ⟨us, -, hy⟩ := hy
  exact Fr_fwU b r us y hy

theorem Hd_farU (b r : ℕ) : ∀ uss : List (List (Option TrioSeq)), Hd (farU b r uss)
  | [] => fun h => absurd rfl h
  | us :: uss => fun _ => by rw [farU_cons]; rfl

theorem mlift_farU_high {b v r : ℕ} (hv : b + 1 ≤ v) (hvr : v < r) (t : ℕ) :
    ∀ uss, RawUs b uss → mlift (farU b r uss) v t = farU b (r + t) uss
  | [] => fun _ => by simp [farU, mlift_nil]
  | us :: uss => fun hR => by
      rw [farU_cons, farU_cons, mlift_app (Fr_fwU b r us) (Hd_farU b r uss),
        mlift_fwU_high hv hvr (hR us (by simp)) t, mlift_farU_high hv hvr t uss (RawUs_tail hR)]

theorem mlift_farU_base {b r : ℕ} (hbr : b < r) (t : ℕ) :
    ∀ uss, RawUs b uss → mlift (farU b r uss) b t = farU (b + t) (r + t) uss
  | [] => fun _ => by simp [farU, mlift_nil]
  | us :: uss => fun hR => by
      rw [farU_cons, farU_cons, mlift_app (Fr_fwU b r us) (Hd_farU b r uss),
        mlift_fwU_base hbr (hR us (by simp)) t, mlift_farU_base hbr t uss (RawUs_tail hR)]

theorem reliftX_farU {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (b : ℕ) (f g : ℕ → ℕ) : ∀ uss, RawUs b uss →
    reliftX b f g A (farU b (b + liftOff f A o + 1) uss)
      = farU b (b + liftOff (addF f g) A o + 1) uss
  | [] => fun _ => by simp [farU, reliftX, slift_nil]
  | us :: uss => fun hR => by
      rw [farU_cons, farU_cons, reliftX_app (Fr_fwU _ _ _) (Hd_farU _ _ uss),
        reliftX_fwU hA hA1 b f g (hR us (by simp)), reliftX_farU hA hA1 b f g uss (RawUs_tail hR)]

/-! ## 全ての錨の列で GpT -/

def FarCU (b0 : ℕ) (uss : List (List (Option TrioSeq))) : Prop :=
  ∀ (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), b0 ≤ b → RawUs b uss → (∀ a ∈ A, a < o) →
    (∀ a ∈ A, 1 ≤ a) → 1 ≤ o → GpT A o f b (farU b (b + liftOff f A o + 1) uss)

theorem FarCU_nil (b0 : ℕ) : FarCU b0 [] := by
  intro A o f b _ _ hA hA1 ho
  rw [show farU b (b + liftOff f A o + 1) [] = [] from rfl]
  rcases Nat.lt_or_ge o 2 with h | h
  · have ho1 : o = 1 := by omega
    subst ho1
    have hA0 : A = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => by have := hA a ha; have := hA1 a ha; omega)
    subst hA0
    exact GpT_nil1 f b
  · exact GpT_nil hA h f b

theorem farU_PVP {b0 : ℕ} {uss : List (List (Option TrioSeq))} (hC : FarCU b0 uss) {A : List ℕ}
    {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o) (f : ℕ → ℕ) (b : ℕ)
    (hb : b0 ≤ b) (hR : RawUs b uss) : PVP A o f b (farU b (b + liftOff f A o + 1) uss) := by
  intro t
  have hk : o ≤ liftOff f A o := by unfold liftOff; omega
  rw [mlift_farU_high (show b + 1 ≤ b + liftOff f A o by omega)
    (show b + liftOff f A o < b + liftOff f A o + 1 by omega) t uss hR]
  have := hC A (o + t) f b hb hR (fun a ha => by have := hA a ha; omega) hA1 (by omega)
  rwa [liftOff_add_t hA, show b + (liftOff f A o + t) + 1 = b + liftOff f A o + 1 + t by omega]
    at this

/-! ## 潰れの塔 -/

def towU (b : ℕ) (uss : List (List (Option TrioSeq))) : ℕ → ℕ → TrioSeq
  | r, 0 => farU b r uss ++ [((1, r, 1) : ℕ × ℕ × ℕ)]
  | r, m + 1 => farU b r uss ++ ((1, r, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towU b uss (r + 1) m))

theorem towU_GpT {b0 : ℕ} {uss : List (List (Option TrioSeq))} (hC : FarCU b0 uss) :
    ∀ (m : ℕ) (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), b0 ≤ b → RawUs b uss →
    (∀ a ∈ A, a < o) → (∀ a ∈ A, 1 ≤ a) → 1 ≤ o →
    GpT A o f b (towU b uss (b + liftOff f A o + 1) m)
  | 0, A, o, f, b, hb, hR, hA, hA1, ho => by
      rw [towU]
      exact PVP_to_GpT (PVP_snocz hA hA1 ho (Fr_farU _ _ uss) (farU_PVP hC hA hA1 ho f b hb hR))
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
      have hL := towU_GpT hC m (o :: A) (o + 1) H b hb hR hAo' hA1' (by omega)
      rw [e1, show b + (liftOff f A o + 1) + 1 = b + liftOff f A o + 1 + 1 by omega] at hL
      have hGC : GC (o :: A) H (liftOff f A o + 1) b
          (towU b uss (b + liftOff f A o + 1 + 1) m) := by
        rw [← e1, GC_slot hAo']; exact hL
      have hRL := R_child (CtxP_RLC hA hA1 ho) hAo' Fr_nil (RLC_nil hA hA1 ho H b) hGC
        (le_of_eq e1.symm)
      have h1 := hRL (fun _ => 0) b le_rfl
      rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero, hHo, Nat.add_zero,
        List.nil_append] at h1
      have hLC := LC1_congr hA hHA h1
      have := hLC _ (Fr_farU _ _ uss) (farU_PVP hC hA hA1 ho f b hb hR)
      rw [show b + (liftOff f A o + 1) = b + liftOff f A o + 1 by omega] at this
      rw [towU]
      exact PVP_to_GpT this

theorem farU_P (b c : ℕ) (uss : List (List (Option TrioSeq))) :
    Fr (farU b (c + 1) uss ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ∧
    coneV ((farU b (c + 1) uss ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) c
      (farU b (c + 1) uss ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]).length := by
  refine ⟨Fr_append (Fr_farU _ _ uss) (Fr_single le_rfl _ _), ?_⟩
  have hbot : BotGe (farU b (c + 1) uss ++ ((1, c + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 [])
      (0 + 1 + 1) (c + 1) :=
    BotGe_node (Fr_farU _ _ uss) le_rfl (BotGe_top Fr_nil (c + 1))
  simp only [shiftr01, List.map_nil] at hbot
  exact coneV_of_BotGe hbot (by omega)

theorem mlift_PU {b c : ℕ} (hbc : b + 1 ≤ c) {uss : List (List (Option TrioSeq))}
    (hR : RawUs b uss) (j : ℕ) :
    mlift (farU b (c + 1) uss ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j
      = farU b (c + 1 + j) uss ++ [((1, c + 1 + j, 1) : ℕ × ℕ × ℕ)] := by
  rw [mlift_app (Fr_farU _ _ uss) (fun _ => rfl), mlift_farU_high hbc (by omega) j uss hR,
    mlift_one (show c < c + 1 by omega)]

theorem farU_flat {b : ℕ} {uss : List (List (Option TrioSeq))} (hR : RawUs b uss) :
    ∀ m c, b + 1 ≤ c → (List.range (m + 1)).flatMap (fun j =>
      shiftr01 (j * 2) 0 (((0, c + j, 0) : ℕ × ℕ × ℕ) ::
        mlift (farU b (c + 1) uss ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j))
      = ((0, c, 0) : ℕ × ℕ × ℕ) :: towU b uss (c + 1) m
  | 0, c, hc => by simp [mlift_PU hc hR, towU]
  | m + 1, c, hc => by
      rw [flatMap_range_cons _ (m + 1)]
      have e : ∀ j, shiftr01 ((j + 1) * 2) 0 (((0, c + (j + 1), 0) : ℕ × ℕ × ℕ) ::
          mlift (farU b (c + 1) uss ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c (j + 1))
          = shiftr01 2 0 (shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (farU b (c + 1 + 1) uss ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)) := by
        intro j
        rw [mlift_PU hc hR, mlift_PU (c := c + 1) (by omega) hR, shift_shift,
          show c + (j + 1) = c + 1 + j by omega, show c + 1 + (j + 1) = c + 1 + 1 + j by omega,
          show (j + 1) * 2 = j * 2 + 2 by omega]
      simp only [e]
      rw [← shift_flatMap 2 (fun j => shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (farU b (c + 1 + 1) uss ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)),
        farU_flat hR m (c + 1) (by omega)]
      have eT : shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towU b uss (c + 1 + 1) m))
          = shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towU b uss (c + 1 + 1) m) := by
        rw [show shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towU b uss (c + 1 + 1) m)
            = shiftr01 (1 + 1) 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towU b uss (c + 1 + 1) m) from rfl,
          ← shift_shift]
        rfl
      rw [towU, eT]
      simp [mlift_PU hc hR]

/-- ★ 標準の並びの後ろの遠い語（中身が遠い字だけ）の潰れ。 -/
theorem farU_collapse {b0 : ℕ} {uss : List (List (Option TrioSeq))} (hC : FarCU b0 uss) :
    FarCU b0 (uss ++ [[]]) := by
  intro A o f b hb hR hA hA1 ho
  have hR0 : RawUs b uss := fun us h => hR us (List.mem_append_left _ h)
  refine GpT_intro hA (fun R hR' g => ?_)
  rw [reliftX_farU hA hA1 b f g _ hR]
  obtain ⟨F, hF⟩ : ∃ F, F = addF f g := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = liftOff F A o := ⟨_, rfl⟩
  rw [← hF, ← hk]
  have hk1 : o ≤ k := by rw [hk]; unfold liftOff; omega
  intro u' hu X hX hRX
  rw [mlift_farU_base (show b < b + k + 1 by omega) (u' - b) _ hR,
    show b + k + 1 + (u' - b) = u' + k + 1 by omega, show b + (u' - b) = u' by omega, farU_snoc]
  have hRu : RawUs u' uss := RawUs_mono hu hR0
  obtain ⟨c, hc⟩ : ∃ c, c = u' + k := ⟨_, rfl⟩
  rw [← hc]
  have hbc : u' + 1 ≤ c := by rw [hc]; omega
  obtain ⟨hP, hcone⟩ := farU_P u' c uss
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq, U0 = ((0, c, 0) : ℕ × ℕ × ℕ) ::
      ((farU u' (c + 1) uss ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) :=
    ⟨_, rfl⟩
  have eU : ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (farU u' (c + 1) uss ++ fwU u' (c + 1) [])
      = shiftr01 1 0 U0 := by
    rw [hU0]; simp [shiftr01, fwU, unitsC]
  rw [eU]
  have hlen : 2 ≤ U0.length := by rw [hU0]; simp
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom hP (show 1 ≤ 2 by omega) hcone
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h | h
    · exfalso
      have hl : U0.length - 1 = (((0, c, 0) : ℕ × ℕ × ℕ) ::
          (farU u' (c + 1) uss ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])).length + 0 := by
        rw [hU0]; simp
      rw [hl] at h
      unfold lev at h
      rw [hU0, show ((0, c, 0) : ℕ × ℕ × ℕ) :: ((farU u' (c + 1) uss ++
          [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)])
        = (((0, c, 0) : ℕ × ℕ × ℕ) :: (farU u' (c + 1) uss ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])) ++
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
  rw [eO, hU0, oper_zcone hP (show 1 ≤ 2 by omega) hcone (m' + 1), farU_flat hRu m' c hbc]
  have eS : shiftr01 1 0 (((0, c, 0) : ℕ × ℕ × ℕ) :: towU u' uss (c + 1) m')
      = ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towU u' uss (c + 1) m') := by
    simp [shiftr01]
  rw [eS]
  have hD := towU_GpT hC m' A o F u' (by omega) hRu hA hA1 ho
  rw [← hk, ← hc] at hD
  have h := GpT_elim0 hD hR'
  rw [← hk] at h
  have := h u' le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero, ← hc] at this

end GzH
end TRIO
