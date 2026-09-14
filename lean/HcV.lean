/-
HcV.lean: 一般の接頭辞 PVE の潰れの塔と、遠い字だけの語を足す規則 PVE_collapse（HcJ の一般化）。

    towG X c 0     = X ++ [(1, c+1, 1)]
    towG X c (m+1) = X ++ (1, c+1, 1) :: ((1, c+1, 0) :: (towG (X↑1) (c+1) m)↑1)↑1      （X↑1 = mlift X c 1）
    towE_GpT: PVE W → 埋め込み先で towG は GpT（塔の内側は錨 o を挿入した埋め込み、HcJ.towWu_GpT の写し）
    PVE_collapse: PVE W → PVE (W ++ [(1, r, 1), (2, r, 1)])   （r = b0 + liftOff H A k + 1、HcJ.farWAu_collapse の写し）
-/
import HcU

namespace TRIO
namespace HcV

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcI HcJ HcK HcL HcM HcN HcO HcU

/-! ## 塔 -/

noncomputable def towG (X : TrioSeq) (c : ℕ) : ℕ → TrioSeq
  | 0 => X ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]
  | m + 1 => X ++ ((1, c + 1, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towG (mlift X c 1) (c + 1) m))

theorem Fr_towG {X : TrioSeq} (hX : Fr X) : ∀ m c, Fr (towG X c m)
  | 0, c => by rw [towG]; exact Fr_append hX (GzF.Fr_single le_rfl _ _)
  | m + 1, c => by rw [towG]; exact Fr_append hX (Fr_letter _ _)

/-- ★ 一般の接頭辞の潰れの塔は、埋め込み先の級で GpT。 -/
theorem towE_GpT {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b0 : ℕ} {W : TrioSeq} (hW : Fr W)
    (hP : PVE A k H b0 W) : ∀ (m : ℕ) (g : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f g' : ℕ → ℕ) (b : ℕ),
    EmbU A k H g S o f → b0 ≤ b →
    GpT (S ++ A) o (addF f g') b
      (towG (reliftX b f g' (S ++ A) (embW A k H g S o f b (mlift W b0 (b - b0))))
        (b + liftOff (addF f g') (S ++ A) o) m)
  | 0, g, S, o, f, g', b, hE, hb => by
      rw [towG]
      exact PVP_to_GpT (PVP_snocz hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1
        (Fr_reliftX (Fr_embW (Fr_mlift hW _ _) _ _ _ _ _ _ _ _) _ _ _ _) (hP g S o f g' b hE hb))
  | m + 1, g, S, o, f, g', b, hE, hb => by
      have hA := hE.2.2.1
      have hA1 := hE.2.2.2.1
      have ho := hE.2.2.2.2.1
      have hAo' : ∀ a ∈ o :: (S ++ A), a < o + 1 := by
        intro a ha; simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · omega
        · have := hA a ha; omega
      have hL := towE_GpT hW hP m g (o :: S) (o + 1) (upF o 0 f) (upF o 0 g') b (EmbU_cons_top hE) hb
      rw [addF_upF0, List.cons_append, reliftX_cons_top0 hA, embW_cons_top hE,
        mlift_reliftX_high hA, liftOff_cons_top hA,
        show b + (liftOff (addF f g') (S ++ A) o + 1) = b + liftOff (addF f g') (S ++ A) o + 1 by omega]
        at hL
      have hGC : GC (o :: (S ++ A)) (upF o 0 (addF f g')) (liftOff (addF f g') (S ++ A) o + 1) b
          (towG (mlift (reliftX b f g' (S ++ A) (embW A k H g S o f b (mlift W b0 (b - b0))))
            (b + liftOff (addF f g') (S ++ A) o) 1) (b + liftOff (addF f g') (S ++ A) o + 1) m) := by
        rw [← liftOff_cons_top hA (addF f g'), GC_slot hAo']; exact hL
      have hRL := R_child (CtxP_RLC hA hA1 ho) hAo' Fr_nil
        (RLC_nil hA hA1 ho (upF o 0 (addF f g')) b) hGC (le_of_eq (liftOff_cons_top hA (addF f g')).symm)
      have h1 := hRL (fun _ => 0) b le_rfl
      rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero,
        show upF o 0 (addF f g') o = 0 by simp [upF], Nat.add_zero, List.nil_append] at h1
      have hLC := LC1_congr hA (upF_low hA 0 (addF f g')) h1
      have := hLC _ (Fr_reliftX (Fr_embW (Fr_mlift hW _ _) _ _ _ _ _ _ _ _) _ _ _ _)
        (hP g S o f g' b hE hb)
      rw [show b + (liftOff (addF f g') (S ++ A) o + 1) = b + liftOff (addF f g') (S ++ A) o + 1 by omega]
        at this
      rw [towG]
      exact PVP_to_GpT this

theorem mlift_snoc_letter {X : TrioSeq} (hX : Fr X) (c j : ℕ) :
    mlift (X ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j = mlift X c j ++ [((1, c + 1 + j, 1) : ℕ × ℕ × ℕ)] := by
  rw [mlift_app hX (fun _ => rfl), mlift_one (show c < c + 1 by omega)]

theorem towG_flat : ∀ (m : ℕ) (X : TrioSeq) (c : ℕ), Fr X → (List.range (m + 1)).flatMap (fun j =>
      shiftr01 (j * 2) 0 (((0, c + j, 0) : ℕ × ℕ × ℕ) :: mlift (X ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j))
      = ((0, c, 0) : ℕ × ℕ × ℕ) :: towG X c m
  | 0, X, c, hX => by simp [mlift_zero, towG]
  | m + 1, X, c, hX => by
      rw [GzF.flatMap_range_cons _ (m + 1)]
      have e : ∀ j, shiftr01 ((j + 1) * 2) 0 (((0, c + (j + 1), 0) : ℕ × ℕ × ℕ) ::
          mlift (X ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c (j + 1))
          = shiftr01 2 0 (shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (mlift X c 1 ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)) := by
        intro j
        rw [mlift_snoc_letter hX, mlift_snoc_letter (Fr_mlift hX _ _), mlift_mlift, GzF.shift_shift,
          show c + (j + 1) = c + 1 + j by omega, show c + 1 + (j + 1) = c + 1 + 1 + j by omega,
          show (j + 1) * 2 = j * 2 + 2 by omega, show 1 + j = j + 1 by omega]
      simp only [e]
      rw [← GzF.shift_flatMap 2 (fun j => shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (mlift X c 1 ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)),
        towG_flat m (mlift X c 1) (c + 1) (Fr_mlift hX _ _)]
      have eT : shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towG (mlift X c 1) (c + 1) m))
          = shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towG (mlift X c 1) (c + 1) m) := by
        rw [show shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towG (mlift X c 1) (c + 1) m)
            = shiftr01 (1 + 1) 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towG (mlift X c 1) (c + 1) m) from rfl,
          ← GzF.shift_shift]
        rfl
      rw [show towG X c (m + 1) = X ++ ((1, c + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0
          (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towG (mlift X c 1) (c + 1) m)) from rfl, eT]
      simp [mlift_zero]

theorem letter_P {Y : TrioSeq} (hY : Fr Y) (c : ℕ) :
    Fr (Y ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ∧
    coneV ((Y ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) c
      (Y ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]).length := by
  refine ⟨Fr_append hY (GzF.Fr_single le_rfl _ _), ?_⟩
  have hbot : BotGe (Y ++ ((1, c + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 []) (0 + 1 + 1) (c + 1) :=
    BotGe_node hY le_rfl (BotGe_top Fr_nil _)
  have := coneV_of_BotGe (z := 1) hbot (show c < c + 1 by omega)
  simpa [shiftr01] using this

/-! ## 遠い字だけの語 -/

theorem col_eq (r : ℕ) : ([((1, r, 1) : ℕ × ℕ × ℕ), ((2, r, 1) : ℕ × ℕ × ℕ)] : TrioSeq)
    = ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 [((1, r, 1) : ℕ × ℕ × ℕ)] := by simp [shiftr01]

theorem mlift_col {W : TrioSeq} (hW : Fr W) {v r : ℕ} (hvr : v < r) (t : ℕ) :
    mlift (W ++ [((1, r, 1) : ℕ × ℕ × ℕ), ((2, r, 1) : ℕ × ℕ × ℕ)]) v t
      = mlift W v t ++ [((1, r + t, 1) : ℕ × ℕ × ℕ), ((2, r + t, 1) : ℕ × ℕ × ℕ)] := by
  rw [col_eq, col_eq, mlift_letterU hW (GzF.Fr_single le_rfl _ _) hvr, mlift_one hvr]

theorem reliftX_col {W : TrioSeq} (hW : Fr W) {B : List ℕ} {o : ℕ} (hB : ∀ a ∈ B, a < o) (b : ℕ)
    (f g : ℕ → ℕ) :
    reliftX b f g B (W ++ [((1, b + liftOff f B o + 1, 1) : ℕ × ℕ × ℕ),
        ((2, b + liftOff f B o + 1, 1) : ℕ × ℕ × ℕ)])
      = reliftX b f g B W ++ [((1, b + liftOff (addF f g) B o + 1, 1) : ℕ × ℕ × ℕ),
          ((2, b + liftOff (addF f g) B o + 1, 1) : ℕ × ℕ × ℕ)] := by
  have hlow : lowP f B (liftOff f B o + 1) = B :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hB ha; omega)
  rw [col_eq, col_eq, reliftX_app hW (Hd_letter _ _),
    show b + liftOff f B o + 1 = b + (liftOff f B o + 1) by omega,
    reliftX_node (GzF.Fr_single le_rfl _ _) b (liftOff f B o + 1) 1 f g B, hlow,
    reliftX_one b (liftOff f B o + 1) 1 f g B, reOff_above hB f g 1]
  simp only [← Nat.add_assoc]

theorem embW_col {W : TrioSeq} (hW : Fr W) {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k)
    {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ} (hE : EmbU A k H g S o f) (b : ℕ) :
    embW A k H g S o f b (W ++ [((1, b + liftOff H A k + 1, 1) : ℕ × ℕ × ℕ),
        ((2, b + liftOff H A k + 1, 1) : ℕ × ℕ × ℕ)])
      = embW A k H g S o f b W ++ [((1, b + liftOff f (S ++ A) o + 1, 1) : ℕ × ℕ × ℕ),
          ((2, b + liftOff f (S ++ A) o + 1, 1) : ℕ × ℕ × ℕ)] := by
  have hKL := EmbU_KL hE
  unfold embW
  rw [reliftX_col hW hAk b H g, mlift_col (Fr_reliftX hW _ _ _ _)
    (show b + liftOff (addF H g) A k < b + liftOff (addF H g) A k + 1 by omega),
    show b + liftOff (addF H g) A k + 1 + (liftOff f (S ++ A) o - liftOff (addF H g) A k)
      = b + liftOff f (S ++ A) o + 1 by omega]

/-- 埋め込み先の級で、接頭辞のあとに遠い字だけの語。 -/
theorem collapse_core {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b0 : ℕ} {W : TrioSeq} (hW : Fr W)
    (hP : PVE A k H b0 W) {g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f g' : ℕ → ℕ} {b : ℕ}
    (hE : EmbU A k H g S o f) (hb : b0 ≤ b) :
    GpT (S ++ A) o (addF f g') b
      (reliftX b f g' (S ++ A) (embW A k H g S o f b (mlift W b0 (b - b0))) ++
        [((1, b + liftOff (addF f g') (S ++ A) o + 1, 1) : ℕ × ℕ × ℕ),
          ((2, b + liftOff (addF f g') (S ++ A) o + 1, 1) : ℕ × ℕ × ℕ)]) := by
  have hA := hE.2.2.1
  have hFrY : ∀ (G : ℕ → ℕ) (u : ℕ),
      Fr (reliftX u f G (S ++ A) (embW A k H g S o f u (mlift W b0 (u - b0)))) :=
    fun G u => Fr_reliftX (Fr_embW (Fr_mlift hW _ _) _ _ _ _ _ _ _ _) _ _ _ _
  refine GpT_intro hA (fun R hR' g'' => ?_)
  rw [reliftX_col (hFrY g' b) hA b (addF f g') g'', reliftX_comp, addF_assoc]
  obtain ⟨kk, hkk⟩ : ∃ kk, kk = liftOff (addF f (addF g' g'')) (S ++ A) o := ⟨_, rfl⟩
  rw [← hkk]
  intro u' hu X hX hRX
  rw [mlift_col (hFrY _ b) (show b < b + kk + 1 by omega) (u' - b),
    show b + kk + 1 + (u' - b) = u' + kk + 1 by omega]
  have eY : mlift (reliftX b f (addF g' g'') (S ++ A) (embW A k H g S o f b (mlift W b0 (b - b0))))
        b (u' - b)
      = reliftX u' f (addF g' g'') (S ++ A) (embW A k H g S o f u' (mlift W b0 (u' - b0))) := by
    rw [mlift_reliftX, show b + (u' - b) = u' by omega, embW_lift_base, show b + (u' - b) = u' by omega]
    have e := mlift_mlift W b0 (b - b0) (u' - b)
    rw [show b0 + (b - b0) = b by omega, show b - b0 + (u' - b) = u' - b0 by omega] at e
    rw [e]
  rw [eY]
  obtain ⟨Y3, hY3⟩ : ∃ Y3, Y3 = reliftX u' f (addF g' g'') (S ++ A)
      (embW A k H g S o f u' (mlift W b0 (u' - b0))) := ⟨_, rfl⟩
  rw [← hY3]
  have hFrY3 : Fr Y3 := by rw [hY3]; exact hFrY _ _
  obtain ⟨c, hc⟩ : ∃ c, c = u' + kk := ⟨_, rfl⟩
  rw [show u' + kk + 1 = c + 1 by omega]
  obtain ⟨hPr, hcone⟩ := letter_P hFrY3 c
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq, U0 = ((0, c, 0) : ℕ × ℕ × ℕ) ::
      ((Y3 ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) := ⟨_, rfl⟩
  have eU : ((1, u' + kk, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (Y3 ++
      [((1, c + 1, 1) : ℕ × ℕ × ℕ), ((2, c + 1, 1) : ℕ × ℕ × ℕ)]) = shiftr01 1 0 U0 := by
    rw [hU0, ← hc]; simp [shiftr01]
  rw [eU]
  have hlen : 2 ≤ U0.length := by
    rw [hU0]; simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]
    omega
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom hPr (show 1 ≤ 2 by omega) hcone
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h' | h'
    · exfalso
      have hl : U0.length - 1 = (((0, c, 0) : ℕ × ℕ × ℕ) ::
          (Y3 ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])).length + 0 := by
        rw [hU0]
        simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]
        omega
      rw [hl] at h'
      unfold lev at h'
      rw [hU0, show ((0, c, 0) : ℕ × ℕ × ℕ) :: ((Y3 ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++
          [((2, c + 1, 1) : ℕ × ℕ × ℕ)])
        = (((0, c, 0) : ℕ × ℕ × ℕ) :: (Y3 ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])) ++
          [((2, c + 1, 1) : ℕ × ℕ × ℕ)] by simp,
        entry_append_right, entry_append_right] at h'
      simp [entry] at h'
    · exact h'
  refine (hR' (addF f (addF g' g''))).1.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
    (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp only [List.length_cons]; omega), hU0]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] U0 1 m hlen hpV
  simp only [List.nil_append] at eO
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [eO, hU0, oper_zcone hPr (show 1 ≤ 2 by omega) hcone (m' + 1), towG_flat m' Y3 c hFrY3]
  have eS : shiftr01 1 0 (((0, c, 0) : ℕ × ℕ × ℕ) :: towG Y3 c m')
      = ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towG Y3 c m') := by
    simp [shiftr01]
  rw [eS]
  have hD := towE_GpT hW hP m' g S o f (addF g' g'') u' hE (by omega)
  rw [← hkk, ← hY3, ← hc] at hD
  have h' := GpT_elim0 hD hR'
  rw [← hkk] at h'
  have := h' u' le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero, ← hc] at this

/-- ★ PVE の接頭辞のあとに遠い字だけの語を足す。 -/
theorem PVE_collapse {A : List ℕ} {k : ℕ} (hAk : ∀ a ∈ A, a < k) {H : ℕ → ℕ} {b0 : ℕ} {W : TrioSeq}
    (hW : Fr W) (hP : PVE A k H b0 W) :
    PVE A k H b0 (W ++ [((1, b0 + liftOff H A k + 1, 1) : ℕ × ℕ × ℕ),
      ((2, b0 + liftOff H A k + 1, 1) : ℕ × ℕ × ℕ)]) := by
  intro g S o f g' b hE hb t
  have hA := hE.2.2.1
  rw [mlift_col hW (show b0 < b0 + liftOff H A k + 1 by omega),
    show b0 + liftOff H A k + 1 + (b - b0) = b + liftOff H A k + 1 by omega,
    embW_col (Fr_mlift hW _ _) hAk hE b,
    reliftX_col (Fr_embW (Fr_mlift hW _ _) _ _ _ _ _ _ _ _) hA b f g',
    mlift_col (Fr_reliftX (Fr_embW (Fr_mlift hW _ _) _ _ _ _ _ _ _ _) _ _ _ _)
      (show b + liftOff (addF f g') (S ++ A) o < b + liftOff (addF f g') (S ++ A) o + 1 by omega),
    ← mlift_reliftX_high hA, ← embW_shift_o hE t b,
    show b + liftOff (addF f g') (S ++ A) o + 1 + t = b + liftOff (addF f g') (S ++ A) (o + t) + 1 by
      rw [liftOff_add_t hA]; omega]
  exact collapse_core hW hP (EmbU_shift_o hE t) hb

end HcV
end TRIO
