/-
GyG.lean: 節点の下の語（GpT の世界）。子の並びの末尾の空の字 GpT_snocz_core と、語の述語 PVP。

    PVP A o f b W := ∀ t, GpT A (o + t) f b (mlift W (b + liftOff f A o) t)
-/
import GyF

namespace TRIO
namespace GyG

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF

/-! ## 節点より上の値の計算 -/

theorem sumOn_addF (f g : ℕ → ℕ) : ∀ L : List ℕ, sumOn (addF f g) L = sumOn f L + sumOn g L
  | [] => rfl
  | x :: L => by simp only [sumOn, addF, sumOn_addF f g L]; omega

theorem liftOff_addF {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (f g : ℕ → ℕ) :
    liftOff (addF f g) A o = liftOff f A o + sumOn g A := by
  rw [sumOn_liftOff hA, sumOn_liftOff hA, sumOn_addF]; omega

theorem liftOff_add_t {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (f : ℕ → ℕ) (t : ℕ) :
    liftOff f A (o + t) = liftOff f A o + t := by
  rw [sumOn_liftOff (fun a ha => by have := hA a ha; omega), sumOn_liftOff hA]; omega

theorem reOff_above {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (f g : ℕ → ℕ) (t : ℕ) :
    reOff f g A (liftOff f A o + t) = liftOff (addF f g) A o + t := by
  unfold reOff
  rw [reStep_lowP, lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega),
    liftOff_addF hA]
  omega

theorem mlift_reliftX_high {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (b : ℕ) (f g : ℕ → ℕ)
    (t : ℕ) (W : TrioSeq) :
    reliftX b f g A (mlift W (b + liftOff f A o) t)
      = mlift (reliftX b f g A W) (b + liftOff (addF f g) A o) t := by
  unfold reliftX
  rw [mlift_eq_slift, mlift_eq_slift, slift_slift (stair_step _ t) (reStair_stair b f g A),
    slift_slift (reStair_stair b f g A) (stair_step _ t)]
  congr 1
  funext m
  have hall : ∀ m', liftOff f A o ≤ m' → reStep 0 f g A A m' = sumOn g A := by
    intro m' hm'
    rw [reStep_lowP, lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)]
  have hk := liftOff_addF hA f g
  unfold reStair
  by_cases h : b + liftOff f A o < m
  · obtain ⟨m', rfl⟩ : ∃ m', m = b + m' := ⟨m - b, by omega⟩
    rw [if_pos h, show b + m' + t = b + (m' + t) by omega, reStep_base, reStep_base,
      hall (m' + t) (by omega), hall m' (by omega),
      if_pos (show b + liftOff (addF f g) A o < b + m' + sumOn g A by omega)]
    omega
  · rw [if_neg h, Nat.add_zero]
    have hmono : reStep b f g A A m ≤ reStep b f g A A (b + liftOff f A o) :=
      reStep_mono b f g A (by omega) A
    rw [reStep_base, hall _ le_rfl] at hmono
    rw [if_neg (by omega)]
    omega

theorem amin_snoc_top {W : TrioSeq} (hW : Fr W) (r z : ℕ) :
    amin (W ++ [((1, r, z) : ℕ × ℕ × ℕ)]) W.length = r :=
  amin_snoc_bottom (BotGe_top hW r)

theorem reliftX_snoc_letter {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {W : TrioSeq} (hW : Fr W)
    (b : ℕ) (f g : ℕ → ℕ) :
    reliftX b f g A (W ++ [((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ)])
      = reliftX b f g A W ++ [((1, b + liftOff (addF f g) A o + 1, 1) : ℕ × ℕ × ℕ)] := by
  unfold reliftX
  rw [slift_snoc, amin_snoc_top hW]
  have e : reStair b f g A (b + liftOff f A o + 1) = b + liftOff (addF f g) A o + 1 := by
    rw [show b + liftOff f A o + 1 = b + (liftOff f A o + 1) by omega, reStair_base, reOff_above hA]
    omega
  rw [e]
  have hk : liftOff f A o ≤ liftOff (addF f g) A o := by rw [liftOff_addF hA]; omega
  congr 1
  simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
  omega

theorem GC_high {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {F : ℕ → ℕ} {τ : ℕ}
    (hτ : liftOff F A o ≤ τ) (b : ℕ) (L : TrioSeq) :
    GC A F τ b L = GpT A (o + (τ - liftOff F A o)) F b L := by
  unfold GC
  have hl : lowP F A τ = A := lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := F) hA ha; omega)
  rw [hl]
  have hs := sumOn_liftOff (f := F) hA
  congr
  omega

/-! ## 子の並びの末尾の空の字 -/

theorem GpT_snocz_core {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) {f : ℕ → ℕ} {b : ℕ} {W : TrioSeq} (hW : Fr W)
    (hPV : ∀ t, GpT A (o + t) f b (mlift W (b + liftOff f A o) t)) :
    GpT A o f b (W ++ [((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ)]) := by
  refine GpT_intro hA (fun R hR g => ?_)
  rw [reliftX_snoc_letter hA hW b f g]
  have hW1 : Fr (reliftX b f g A W) := Fr_reliftX hW _ _ _ _
  have hPV1 : ∀ t, GpT A (o + t) (addF f g) b
      (mlift (reliftX b f g A W) (b + liftOff (addF f g) A o) t) := by
    intro t
    have := GpT_lift (fun a ha => by have := hA a ha; omega) (hPV t) g
    rwa [mlift_reliftX_high hA] at this
  obtain ⟨F, hF⟩ : ∃ F, F = addF f g := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = liftOff F A o := ⟨_, rfl⟩
  rw [← hF] at hPV1 ⊢
  rw [← hk] at hPV1 ⊢
  intro u' hu X hX hRX
  obtain ⟨d, hd⟩ : ∃ d, d = u' - b := ⟨_, rfl⟩
  rw [← hd]
  obtain ⟨V, hV⟩ : ∃ V : ℕ → TrioSeq,
      V = fun τ => mlift (mlift (reliftX b f g A W) b d) (u' + k) (τ - k) := ⟨_, rfl⟩
  have hVFr : ∀ τ, Fr (V τ) := fun τ => by rw [hV]; exact Fr_mlift (Fr_mlift hW1 _ _) _ _
  have hk1 : 1 ≤ k := by rw [hk]; unfold liftOff; omega
  have hBase : ∀ τ, k ≤ τ → GpT A (o + (τ - k)) F u' (V τ) := by
    intro τ hτ
    have h0 := hPV1 (τ - k)
    have h1 := (GpT_ax (fun a ha => by have := hA a ha; omega) hA1 (by omega) F).lift b _
      (Fr_mlift hW1 _ _) h0 u' hu
    rw [← hd, mlift_commk, show b + k + d = u' + k by omega] at h1
    rw [hV]; exact h1
  have eStep : ∀ τ, k ≤ τ → mlift (V τ) (u' + τ) 1 = V (τ + 1) := by
    intro τ hτ
    rw [hV]
    have := mlift_mlift (mlift (reliftX b f g A W) b d) (u' + k) (τ - k) 1
    rw [show u' + k + (τ - k) = u' + τ by omega, show τ - k + 1 = τ + 1 - k by omega] at this
    exact this
  have claim : ∀ m τ, k ≤ τ →
      GpT A (o + (τ - k)) F u' (V τ ++ shiftr01 1 0 ((((0, u' + τ + 1, 0) : ℕ × ℕ × ℕ) ::
        (V (τ + 1) ++ [((1, u' + τ + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m⟧)) := by
    intro m
    induction m with
    | zero =>
        intro τ hτ
        rw [oper_zcone (hVFr (τ + 1)) le_rfl (coneV_top1 (hVFr (τ + 1)) (by omega)) 0]
        simp only [List.range_zero, List.flatMap_nil, shiftr01, List.map_nil, List.append_nil]
        exact hBase τ hτ
    | succ m ih =>
        intro τ hτ
        rw [oper_zcone_succ (hVFr (τ + 1)) le_rfl (coneV_top1 (hVFr (τ + 1)) (by omega)) m,
          show u' + τ + 1 = u' + (τ + 1) by omega, eStep (τ + 1) (by omega)]
        have eS : shiftr01 1 0 (((0, u' + (τ + 1), 0) : ℕ × ℕ × ℕ) ::
            (V (τ + 1) ++ shiftr01 1 0 ((((0, u' + (τ + 1) + 1, 0) : ℕ × ℕ × ℕ) ::
              (V (τ + 1 + 1) ++ [((1, u' + (τ + 1) + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m⟧)))
            = ((1, u' + (τ + 1), 0) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (V (τ + 1) ++ shiftr01 1 0 ((((0, u' + (τ + 1) + 1, 0) : ℕ × ℕ × ℕ) ::
                (V (τ + 1 + 1) ++ [((1, u' + (τ + 1) + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m⟧)) := by
          simp [shiftr01]
        rw [eS]
        have hih := ih (τ + 1) (by omega)
        have hFrL : Fr (V (τ + 1) ++ shiftr01 1 0 ((((0, u' + (τ + 1) + 1, 0) : ℕ × ℕ × ℕ) ::
            (V (τ + 1 + 1) ++ [((1, u' + (τ + 1) + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m⟧)) :=
          Fr_append (hVFr _) (Fr_shift1 _)
        have hkτ : liftOff F A (o + (τ - k)) ≤ τ + 1 := by
          rw [liftOff_add_t hA, ← hk]; omega
        have hGL : GC A F (τ + 1) u' (V (τ + 1) ++ shiftr01 1 0 ((((0, u' + (τ + 1) + 1, 0) :
            ℕ × ℕ × ℕ) :: (V (τ + 1 + 1) ++ [((1, u' + (τ + 1) + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m⟧)) := by
          rw [GC_high (fun a ha => by have := hA a ha; omega) hkτ, liftOff_add_t hA, ← hk,
            show o + (τ - k) + (τ + 1 - (k + (τ - k))) = o + (τ + 1 - k) by omega]
          exact hih
        exact GpT_node (fun a ha => by have := hA a ha; omega) hA1 (by omega) (hVFr τ) hFrL
          (hBase τ hτ) hGL
  have hcA := coneV_top1 hW1 (show b < b + k + 1 by omega)
  rw [mlift_snoc_cone (reliftX b f g A W) _ hcA d]
  have eL1 : ((((1, b + k + 1, 1) : ℕ × ℕ × ℕ).1, ((1, b + k + 1, 1) : ℕ × ℕ × ℕ).2.1 + d,
      ((1, b + k + 1, 1) : ℕ × ℕ × ℕ).2.2) : ℕ × ℕ × ℕ) = ((1, u' + k + 1, 1) : ℕ × ℕ × ℕ) := by
    show ((1, b + k + 1 + d, 1) : ℕ × ℕ × ℕ) = _
    rw [show b + k + 1 + d = u' + k + 1 by omega]
  have eV0 : mlift (reliftX b f g A W) b d = V k := by rw [hV]; simp [mlift_zero]
  rw [eL1, eV0]
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq,
      U0 = ((0, u' + k, 0) : ℕ × ℕ × ℕ) :: (V k ++ [((1, u' + k + 1, 1) : ℕ × ℕ × ℕ)]) := ⟨_, rfl⟩
  have eU : ((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (V k ++ [((1, u' + k + 1, 1) : ℕ × ℕ × ℕ)])
      = shiftr01 1 0 U0 := by rw [hU0]; simp [shiftr01]
  rw [eU]
  have hlen : 2 ≤ U0.length := by rw [hU0]; simp
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom (hVFr k) le_rfl
      (coneV_top1 (hVFr k) (show u' + k < u' + k + 1 by omega))
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h | h
    · exfalso
      have hl : U0.length - 1 = (((0, u' + k, 0) : ℕ × ℕ × ℕ) :: V k).length + 0 := by
        rw [hU0]; simp
      rw [hl] at h
      unfold lev at h
      rw [hU0, show ((0, u' + k, 0) : ℕ × ℕ × ℕ) :: (V k ++ [((1, u' + k + 1, 1) : ℕ × ℕ × ℕ)])
        = (((0, u' + k, 0) : ℕ × ℕ × ℕ) :: V k) ++ [((1, u' + k + 1, 1) : ℕ × ℕ × ℕ)] by simp,
        entry_append_right, entry_append_right] at h
      simp [entry] at h
    · exact h
  refine (hR F).1.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
    (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp), hU0]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] U0 1 m hlen hpV
  simp only [List.nil_append] at eO
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [eO, hU0, oper_zcone_succ (hVFr k) le_rfl (coneV_top1 (hVFr k) (by omega)) m', eStep k le_rfl]
  have eS : shiftr01 1 0 (((0, u' + k, 0) : ℕ × ℕ × ℕ) ::
      (V k ++ shiftr01 1 0 ((((0, u' + k + 1, 0) : ℕ × ℕ × ℕ) ::
        (V (k + 1) ++ [((1, u' + k + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m'⟧)))
      = ((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (V k ++ shiftr01 1 0 ((((0, u' + k + 1, 0) : ℕ × ℕ × ℕ) ::
          (V (k + 1) ++ [((1, u' + k + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦m'⟧)) := by
    simp [shiftr01]
  rw [eS]
  have hc := claim m' k le_rfl
  rw [Nat.sub_self, Nat.add_zero] at hc
  have h := GpT_elim0 hc hR
  rw [← hk] at h
  have := h u' le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero] at this

/-! ## 節点の下の語 -/

def PVP (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) (b : ℕ) (W : TrioSeq) : Prop :=
  ∀ t, GpT A (o + t) f b (mlift W (b + liftOff f A o) t)

theorem PVP_to_GpT {A : List ℕ} {o : ℕ} {f : ℕ → ℕ} {b : ℕ} {W : TrioSeq} (h : PVP A o f b W) :
    GpT A o f b W := by
  have := h 0; rwa [Nat.add_zero, mlift_zero] at this

theorem PVP_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (ho : 2 ≤ o) (f : ℕ → ℕ) (b : ℕ) :
    PVP A o f b [] := by
  intro t; rw [mlift_nil]; exact GpT_nil (fun a ha => by have := hA a ha; omega) (by omega) f b

theorem PVP_snocz {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {f : ℕ → ℕ} {b : ℕ} {W : TrioSeq} (hW : Fr W) (h : PVP A o f b W) :
    PVP A o f b (W ++ [((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ)]) := by
  intro t
  have hcA := coneV_top1 hW (show b + liftOff f A o < b + liftOff f A o + 1 by omega)
  rw [mlift_snoc_cone W _ hcA t]
  have eL : ((((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ).1,
      ((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ).2.1 + t,
      ((1, b + liftOff f A o + 1, 1) : ℕ × ℕ × ℕ).2.2) : ℕ × ℕ × ℕ)
      = ((1, b + liftOff f A (o + t) + 1, 1) : ℕ × ℕ × ℕ) := by
    show ((1, b + liftOff f A o + 1 + t, 1) : ℕ × ℕ × ℕ) = _
    rw [liftOff_add_t hA, show b + liftOff f A o + 1 + t = b + (liftOff f A o + t) + 1 by omega]
  rw [eL]
  refine GpT_snocz_core (fun a ha => by have := hA a ha; omega) hA1 (by omega) (Fr_mlift hW _ _)
    (fun t' => ?_)
  have := h (t + t')
  rw [show o + (t + t') = o + t + t' by omega] at this
  have e := mlift_mlift W (b + liftOff f A o) t t'
  rw [liftOff_add_t hA, show b + (liftOff f A o + t) = b + liftOff f A o + t by omega, e]
  exact this

end GyG
end TRIO
