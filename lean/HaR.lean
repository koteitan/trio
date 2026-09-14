/-
HaR.lean: F の語で始まる遠い語の族（最上段の潰れの塔の各段は「F の語のあとに中身つきの遠い語」）。

    FarCFk k b0 ws := ∀ A o f b, 条件（GzU.FarCWk と同じ）→ GpT A o f b (Pf r ++ farW b r ws)   （r = b + liftOff f A o + 1）

GzU.FarCWk の写し。F の語 Pf は字と同じ行 1 で、持ち上げ・再持ち上げで字と一緒に動く（HaI）。
-/
import HaI

namespace TRIO
namespace HaR

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF HaG HaI

def FarCFk (k b0 : ℕ) (ws : List (ℕ × TrioSeq)) : Prop :=
  ∀ (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), b0 ≤ b → RawWsk k b ws → (∀ a ∈ A, a < o) →
    (∀ a ∈ A, 1 ≤ a) → 1 ≤ o → (∀ a ∈ A, k ≤ liftVal f A a) → k ≤ liftOff f A o →
    GpT A o f b (Pf (b + liftOff f A o + 1) ++ farW b (b + liftOff f A o + 1) ws)

theorem FarCFk_nil (k b0 : ℕ) : FarCFk k b0 [] := by
  intro A o f b _ _ hA hA1 ho _ _
  have := GpT_Pf hA hA1 ho f b
  simpa [farW] using this

theorem Fr_PWF (b r : ℕ) (ws : List (ℕ × TrioSeq)) : Fr (Pf r ++ farW b r ws) :=
  Fr_append (Fr_Pf r) (Fr_farW b r ws)

theorem mlift_PWF_high {k b v r : ℕ} (hv : b + k ≤ v) (hvr : v < r) (t : ℕ)
    {ws : List (ℕ × TrioSeq)} (hR : RawWsk k b ws) :
    mlift (Pf r ++ farW b r ws) v t = Pf (r + t) ++ farW b (r + t) ws := by
  rw [mlift_app (Fr_Pf r) (Hd_farW b r ws), mlift_Pf hvr t, mlift_farW_highk hv hvr t ws hR]

theorem mlift_PWF_base {k b r : ℕ} (hbr : b < r) (t : ℕ) {ws : List (ℕ × TrioSeq)}
    (hR : RawWsk k b ws) :
    mlift (Pf r ++ farW b r ws) b t = Pf (r + t) ++ farW (b + t) (r + t) ws := by
  rw [mlift_app (Fr_Pf r) (Hd_farW b r ws), mlift_Pf hbr t, mlift_farW_basek hbr t ws hR]

theorem reliftX_PWF {A : List ℕ} {o k : ℕ} (hA : ∀ a ∈ A, a < o) (b : ℕ) (f g : ℕ → ℕ)
    (hAk : ∀ a ∈ A, k ≤ liftVal f A a) {ws : List (ℕ × TrioSeq)} (hR : RawWsk k b ws) :
    reliftX b f g A (Pf (b + liftOff f A o + 1) ++ farW b (b + liftOff f A o + 1) ws)
      = Pf (b + liftOff (addF f g) A o + 1) ++ farW b (b + liftOff (addF f g) A o + 1) ws := by
  rw [reliftX_app (Fr_Pf _) (Hd_farW _ _ _), reliftX_Pf hA b f g, reliftX_farWk hA b f g hAk ws hR]

theorem farWFk_PVP {k b0 : ℕ} {ws : List (ℕ × TrioSeq)} (hC : FarCFk k b0 ws) {A : List ℕ}
    {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o) (f : ℕ → ℕ)
    (hAk : ∀ a ∈ A, k ≤ liftVal f A a) (hko : k ≤ liftOff f A o) (b : ℕ) (hb : b0 ≤ b)
    (hR : RawWsk k b ws) :
    PVP A o f b (Pf (b + liftOff f A o + 1) ++ farW b (b + liftOff f A o + 1) ws) := by
  intro t
  rw [mlift_PWF_high (show b + k ≤ b + liftOff f A o by omega)
    (show b + liftOff f A o < b + liftOff f A o + 1 by omega) t hR]
  have := hC A (o + t) f b hb hR (fun a ha => by have := hA a ha; omega) hA1 (by omega) hAk
    (by rw [liftOff_add_t hA]; omega)
  rwa [liftOff_add_t hA, show b + (liftOff f A o + t) + 1 = b + liftOff f A o + 1 + t by omega]
    at this

/-! ## 潰れの塔 -/

noncomputable def towWF (b : ℕ) (ws : List (ℕ × TrioSeq)) (r : ℕ) : ℕ → TrioSeq
  | 0 => (Pf r ++ farW b r ws) ++ [((1, r, 1) : ℕ × ℕ × ℕ)]
  | m + 1 => (Pf r ++ farW b r ws) ++ ((1, r, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towWF b ws (r + 1) m))

theorem Fr_towWF (b : ℕ) (ws : List (ℕ × TrioSeq)) : ∀ m r, Fr (towWF b ws r m)
  | 0, r => by rw [towWF]; exact Fr_append (Fr_PWF _ _ ws) (GzF.Fr_single le_rfl _ _)
  | m + 1, r => by rw [towWF]; exact Fr_append (Fr_PWF _ _ ws) (Fr_letter _ _)

theorem towWFk_GpT {k b0 : ℕ} {ws : List (ℕ × TrioSeq)} (hC : FarCFk k b0 ws) :
    ∀ (m : ℕ) (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ), b0 ≤ b → RawWsk k b ws →
    (∀ a ∈ A, a < o) → (∀ a ∈ A, 1 ≤ a) → 1 ≤ o → (∀ a ∈ A, k ≤ liftVal f A a) →
    k ≤ liftOff f A o → GpT A o f b (towWF b ws (b + liftOff f A o + 1) m)
  | 0, A, o, f, b, hb, hR, hA, hA1, ho, hAk, hko => by
      rw [towWF]
      exact PVP_to_GpT (PVP_snocz hA hA1 ho (Fr_PWF _ _ ws)
        (farWFk_PVP hC hA hA1 ho f hAk hko b hb hR))
  | m + 1, A, o, f, b, hb, hR, hA, hA1, ho, hAk, hko => by
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
      have eo : liftOff H A o = liftOff f A o := by
        rw [sumOn_liftOff hA, sumOn_liftOff hA, sumOn_congr hHA]
      have hAk' : ∀ a ∈ o :: A, k ≤ liftVal H (o :: A) a := by
        intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with ha | ha
        · rw [ha, liftVal_cons_top hA, hHo, Nat.add_zero, eo]; exact hko
        · rw [liftVal_cons_low hA ha]
          have e : liftVal H A a = liftVal f A a := by
            unfold liftVal; rw [stepSum_congr 0 (a + 1) hHA]
          rw [e]; exact hAk a ha
      have hL := towWFk_GpT hC m (o :: A) (o + 1) H b hb hR hAo' hA1' (by omega) hAk'
        (by rw [e1]; omega)
      rw [e1, show b + (liftOff f A o + 1) + 1 = b + liftOff f A o + 1 + 1 by omega] at hL
      have hGC : GC (o :: A) H (liftOff f A o + 1) b
          (towWF b ws (b + liftOff f A o + 1 + 1) m) := by
        rw [← e1, GC_slot hAo']; exact hL
      have hRL := R_child (CtxP_RLC hA hA1 ho) hAo' Fr_nil (RLC_nil hA hA1 ho H b) hGC
        (le_of_eq e1.symm)
      have h1 := hRL (fun _ => 0) b le_rfl
      rw [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero, hHo, Nat.add_zero,
        List.nil_append] at h1
      have hLC := LC1_congr hA hHA h1
      have := hLC _ (Fr_PWF _ _ ws) (farWFk_PVP hC hA hA1 ho f hAk hko b hb hR)
      rw [show b + (liftOff f A o + 1) = b + liftOff f A o + 1 by omega] at this
      rw [towWF]
      exact PVP_to_GpT this

theorem mlift_PWFt {k b c : ℕ} (hbc : b + k ≤ c) {ws : List (ℕ × TrioSeq)}
    (hR : RawWsk k b ws) (j : ℕ) :
    mlift ((Pf (c + 1) ++ farW b (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j
      = (Pf (c + 1 + j) ++ farW b (c + 1 + j) ws) ++ [((1, c + 1 + j, 1) : ℕ × ℕ × ℕ)] := by
  rw [mlift_app (Fr_PWF _ _ ws) (fun _ => rfl), mlift_PWF_high hbc (by omega) j hR,
    mlift_one (show c < c + 1 by omega)]

theorem farWFk_flat {k b : ℕ} {ws : List (ℕ × TrioSeq)} (hR : RawWsk k b ws) :
    ∀ m c, b + k ≤ c → (List.range (m + 1)).flatMap (fun j =>
      shiftr01 (j * 2) 0 (((0, c + j, 0) : ℕ × ℕ × ℕ) ::
        mlift ((Pf (c + 1) ++ farW b (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j))
      = ((0, c, 0) : ℕ × ℕ × ℕ) :: towWF b ws (c + 1) m
  | 0, c, hc => by simp [mlift_zero, towWF]
  | m + 1, c, hc => by
      rw [GzF.flatMap_range_cons _ (m + 1)]
      have e : ∀ j, shiftr01 ((j + 1) * 2) 0 (((0, c + (j + 1), 0) : ℕ × ℕ × ℕ) ::
          mlift ((Pf (c + 1) ++ farW b (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c (j + 1))
          = shiftr01 2 0 (shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift ((Pf (c + 1 + 1) ++ farW b (c + 1 + 1) ws) ++
              [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)) := by
        intro j
        rw [mlift_PWFt hc hR, mlift_PWFt (c := c + 1) (by omega) hR, GzF.shift_shift,
          show c + (j + 1) = c + 1 + j by omega, show c + 1 + (j + 1) = c + 1 + 1 + j by omega,
          show (j + 1) * 2 = j * 2 + 2 by omega]
      simp only [e]
      rw [← GzF.shift_flatMap 2 (fun j => shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift ((Pf (c + 1 + 1) ++ farW b (c + 1 + 1) ws) ++
              [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)),
        farWFk_flat hR m (c + 1) (by omega)]
      have eT : shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towWF b ws (c + 1 + 1) m))
          = shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towWF b ws (c + 1 + 1) m) := by
        rw [show shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towWF b ws (c + 1 + 1) m)
            = shiftr01 (1 + 1) 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towWF b ws (c + 1 + 1) m) from rfl,
          ← GzF.shift_shift]
        rfl
      rw [show towWF b ws (c + 1) (m + 1) = (Pf (c + 1) ++ farW b (c + 1) ws) ++
          ((1, c + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (towWF b ws (c + 1 + 1) m)) from rfl, eT]
      simp [mlift_zero]

theorem farWF_P (b c : ℕ) (ws : List (ℕ × TrioSeq)) :
    Fr ((Pf (c + 1) ++ farW b (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ∧
    coneV (((Pf (c + 1) ++ farW b (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++
      [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) c
      ((Pf (c + 1) ++ farW b (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]).length := by
  refine ⟨Fr_append (Fr_PWF _ _ ws) (GzF.Fr_single le_rfl _ _), ?_⟩
  have hbot : BotGe ((Pf (c + 1) ++ farW b (c + 1) ws) ++ ((1, c + 1, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 []) (0 + 1 + 1) (c + 1) :=
    BotGe_node (Fr_PWF _ _ ws) le_rfl (BotGe_top Fr_nil _)
  have := coneV_of_BotGe (z := 1) hbot (show c < c + 1 by omega)
  simpa [shiftr01] using this

/-- ★ F の語で始まる遠い語の並びの潰れ（中身なしの遠い語を足す）。 -/
theorem farWFk_collapse {k b0 c0 : ℕ} {ws : List (ℕ × TrioSeq)} (hC : FarCFk k b0 ws) :
    FarCFk k b0 (ws ++ [(c0, [])]) := by
  intro A o f b hb hR hA hA1 ho hAk hko
  have hR0 : RawWsk k b ws := fun w h => hR w (List.mem_append_left _ h)
  refine GpT_intro hA (fun R hR' g => ?_)
  rw [reliftX_PWF hA b f g hAk hR]
  obtain ⟨F, hF⟩ : ∃ F, F = addF f g := ⟨_, rfl⟩
  have hAkF : ∀ a ∈ A, k ≤ liftVal F A a := by rw [hF]; exact liftVal_ge_addF hAk g
  have hkoF : k ≤ liftOff F A o := by rw [hF]; exact liftOff_ge_addF hA hko g
  obtain ⟨kk, hkk⟩ : ∃ kk, kk = liftOff F A o := ⟨_, rfl⟩
  rw [← hF, ← hkk]
  have hk1 : o ≤ kk := by rw [hkk]; unfold liftOff; omega
  have hkkk : k ≤ kk := by rw [hkk]; exact hkoF
  intro u' hu X hX hRX
  rw [mlift_PWF_base (show b < b + kk + 1 by omega) (u' - b) hR,
    show b + kk + 1 + (u' - b) = u' + kk + 1 by omega, show b + (u' - b) = u' by omega, farW_snoc]
  have hRu : RawWsk k u' ws := RawWsk_mono hu hR0
  obtain ⟨c, hc⟩ : ∃ c, c = u' + kk := ⟨_, rfl⟩
  rw [← hc]
  have hbc : u' + k ≤ c := by rw [hc]; omega
  obtain ⟨hP, hcone⟩ := farWF_P u' c ws
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq, U0 = ((0, c, 0) : ℕ × ℕ × ℕ) ::
      (((Pf (c + 1) ++ farW u' (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++
        [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) := ⟨_, rfl⟩
  have eU : ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (Pf (c + 1) ++ (farW u' (c + 1) ws ++
      fwW u' (c + 1) c0 [])) = shiftr01 1 0 U0 := by
    rw [hU0]; simp [shiftr01, fwW, mlift_nil]
  rw [eU]
  have hlen : 2 ≤ U0.length := by
    rw [hU0]; simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]; omega
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom hP (show 1 ≤ 2 by omega) hcone
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h | h
    · exfalso
      have hl : U0.length - 1 = (((0, c, 0) : ℕ × ℕ × ℕ) ::
          ((Pf (c + 1) ++ farW u' (c + 1) ws) ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)])).length + 0 := by
        rw [hU0]; simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]; omega
      rw [hl] at h
      unfold lev at h
      rw [hU0, show ((0, c, 0) : ℕ × ℕ × ℕ) :: (((Pf (c + 1) ++ farW u' (c + 1) ws) ++
          [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)])
        = (((0, c, 0) : ℕ × ℕ × ℕ) :: ((Pf (c + 1) ++ farW u' (c + 1) ws) ++
          [((1, c + 1, 1) : ℕ × ℕ × ℕ)])) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)] by simp,
        entry_append_right, entry_append_right] at h
      simp [entry] at h
    · exact h
  refine (hR' F).1.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
    (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp only [List.length_cons]; omega), hU0]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] U0 1 m hlen hpV
  simp only [List.nil_append] at eO
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [eO, hU0, oper_zcone hP (show 1 ≤ 2 by omega) hcone (m' + 1), farWFk_flat hRu m' c hbc]
  have eS : shiftr01 1 0 (((0, c, 0) : ℕ × ℕ × ℕ) :: towWF u' ws (c + 1) m')
      = ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towWF u' ws (c + 1) m') := by
    simp [shiftr01]
  rw [eS]
  have hD := towWFk_GpT hC m' A o F u' (by omega) hRu hA hA1 ho hAkF hkoF
  rw [← hkk, ← hc] at hD
  have h := GpT_elim0 hD hR'
  rw [← hkk] at h
  have := h u' le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero, ← hc] at this

end HaR
end TRIO
