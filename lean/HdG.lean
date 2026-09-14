/-
HdG.lean: 木の単位の子の位置の節点の族 NXt の状態の層 RNt と文脈の公理（HcL の写し）。

    RNt A k H b X := ∀ g b', b ≤ b' → NXt A k (H+g) b' (reliftX b' H g A (mlift X b (b' − b)))

- FarP の場: 塊の底の節点は、埋め込み先の級で FarP_GpT_ge（行 0 の深さ d+2）。h2 の子の節点は、
  再持ち上げした族 H+g+g' の NXt に、低い子の並び（族によらない）と GoodChtX の埋め込みを渡す。
- RNt_node: 子の級 GC A H τ の並びを持つ節点を置く（GyF.R_child）。
-/
import HdF

namespace TRIO
namespace HdG

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcE HcF HcI HcM HdA HdB HdC HdD HdE HdF

/-! ## 補題 -/

theorem EmbU_self {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (hAk : ∀ a ∈ A, a < k)
    (H g : ℕ → ℕ) : EmbU A k H g [] k (addF H g) := by
  refine ⟨fun a _ => rfl, by simp, by simpa using hAk, by simpa using hA01, hk1, by simp, ?_⟩
  simp only [List.nil_append, liftOff_eq_reOff0]; exact le_rfl

theorem EmbU_shift {A : List ℕ} {k : ℕ} {H g : ℕ → ℕ} {S : List ℕ} {o : ℕ} {f : ℕ → ℕ}
    (hE : EmbU A k H g S o f) : EmbU A k (addF H g) (fun _ => 0) S o f := by
  unfold EmbU at hE ⊢
  rw [addF_zero]
  exact hE

theorem mapt_zero (c : ℕ) (H : ℕ → ℕ) (A : List ℕ) (Lds : List (List UT)) :
    Lds.map (relTs A H (fun _ => 0) c) = Lds := by
  have e : relTs A H (fun _ => 0) c = id := funext (fun us => relTs_zero A H c us)
  simp [e]

theorem fwH_child_app (b r : ℕ) (H0 C P N : TrioSeq) {d : ℕ} (hd : 1 ≤ d) :
    fwH b r H0 b (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (C ++ (P ++ shiftr01 (d - 1) 0 N)))
      = fwH b r H0 b (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (C ++ P)) ++ shiftr01 (d + 1) 0 N := by
  unfold fwH
  simp only [Nat.sub_self, mlift_zero]
  have e : shiftr01 1 0 (shiftr01 1 0 (shiftr01 (d - 1) 0 N)) = shiftr01 (d + 1) 0 N := by
    simp only [GzF.shift_shift]; congr 1; omega
  rw [← e]
  simp only [shiftr01, List.map_append, List.map_cons, List.cons_append, List.append_assoc]

theorem EmbU_congr {A : List ℕ} {k : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A, H a = H' a) {g : ℕ → ℕ}
    {S : List ℕ} {o : ℕ} {f : ℕ → ℕ} (hE : EmbU A k H g S o f) : EmbU A k H' g S o f := by
  obtain ⟨hf, hSA, hA, hA1, ho, hK, hKo⟩ := hE
  have eK := reOff_congrF hH g k
  refine ⟨fun a ha => by rw [hf a ha]; simp [addF, hH a ha], hSA, hA, hA1, ho, fun s hs => ?_, ?_⟩
  · rw [← eK]; exact hK s hs
  · rw [← eK]; exact hKo

theorem GoodChtX_congr {A : List ℕ} {k : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A, H a = H' a) {u : ℕ}
    {Lds : List (List UT)} (h : GoodChtX A k H u Lds) : GoodChtX A k H' u Lds := by
  refine ⟨fun us hus => by rw [← reOff_congrH hH]; exact h.1 us hus,
    fun g S o f b hE hub ws hC hR => ?_⟩
  have e : relTs A H' g u = relTs A H g u :=
    funext (fun us => relTs_congr (fun a ha => (hH a ha).symm) g u us)
  rw [e]
  exact h.2 g S o f b (EmbU_congr (fun a ha => (hH a ha).symm) hE) hub ws hC hR

theorem NXt_congr {A : List ℕ} {k : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A, H a = H' a) {c : ℕ}
    {X : TrioSeq} (h : NXt A k H c X) : NXt A k H' c X :=
  ⟨h.1, by rw [← reOff_congrH hH]; exact h.2.1, fun c' hc' us hus Lds hL =>
    GoodChtX_congr hH (h.2.2 c' hc' us hus Lds (GoodChtX_congr (fun a ha => (hH a ha).symm) hL))⟩

theorem NXt_nil {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (hAk : ∀ a ∈ A, a < k)
    (H : ℕ → ℕ) (c : ℕ) : NXt A k H c [] := by
  refine ⟨fun h => absurd rfl h, LowC_nil _, fun c' hc' us hus Lds hL => ?_⟩
  refine NXt_snoc_of hA01 hk1 hL hus hc' Fr_nil (fun h => absurd rfl h) (LowC_nil _)
    (fun g S o f b hE hub ws hC hR => ?_)
  have := (GoodChtX_snoc_low hL hus hA01 hk1 hAk).2 g S o f b hE hub ws hC hR
  rw [farWt_snoc, List.map_append, List.map_singleton, mapt_tie_inv hA01 hus.1 H g, FTLt_snoc] at this
  dsimp only at this
  have e : reliftX b H g A (mlift ([] : TrioSeq) c (b - c)) = [] := by
    rw [mlift_nil]; unfold reliftX; exact slift_nil _
  rw [e, List.append_nil]
  simpa [fwH, mlift_nil, mlift_zero] using this

/-! ## 状態の層 -/

def RNt (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (b : ℕ) (X : TrioSeq) : Prop :=
  ∀ g b', b ≤ b' → NXt A k (addF H g) b' (reliftX b' H g A (mlift X b (b' - b)))

theorem RNt_lift {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b : ℕ} {X : TrioSeq}
    (h : RNt A k H b X) (g : ℕ → ℕ) : RNt A k (addF H g) b (reliftX b H g A X) := by
  intro g' b' hb'
  rw [mlift_reliftX, show b + (b' - b) = b' by omega, reliftX_comp, addF_assoc]
  exact h (addF g g') b' hb'

theorem RNt_congr {A : List ℕ} {k : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A, H a = H' a)
    {b : ℕ} {X : TrioSeq} (h : RNt A k H b X) : RNt A k H' b X := by
  intro g b' hb'
  have e : reliftX b' H' g A (mlift X b (b' - b)) = reliftX b' H g A (mlift X b (b' - b)) :=
    reliftX_congr b' (fun a ha => (hH a ha).symm) (fun _ _ => rfl) _
  rw [e]
  exact NXt_congr (fun a ha => by simp [addF, hH a ha]) (h g b' hb')

theorem RNt_nil {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (hAk : ∀ a ∈ A, a < k)
    (H : ℕ → ℕ) (b : ℕ) : RNt A k H b [] := by
  intro g b' _
  rw [mlift_nil]
  have e : reliftX b' H g A [] = [] := by unfold reliftX; exact slift_nil _
  rw [e]
  exact NXt_nil hA01 hk1 hAk _ _

theorem RNt_okW {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b : ℕ} {X : TrioSeq}
    (h : RNt A k H b X) : NXt A k H b X := by
  have := h (fun _ => 0) b le_rfl
  rwa [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero] at this

/-- ★ 状態の層の差し込み口の公理。 -/
theorem RNt_ax {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (H : ℕ → ℕ) :
    SlotAx (RNt A k H) where
  lift := by
    intro u W hW h u1 hu1 g b' hb'
    have e := mlift_mlift W u (u1 - u) (b' - u1)
    rw [show u + (u1 - u) = u1 by omega, show u1 - u + (b' - u1) = b' - u by omega] at e
    rw [e]
    exact h g b' (le_trans hu1 hb')
  oper := by
    intro u W U hW hU hH hlen hp hIH g b' hb'
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    rw [mlift_app hW hH u (b' - u), reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _)]
    refine (NXt_ax hA01 hk1 (addF H g)).oper b' _ _
      (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
      (Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) (by rw [reliftX_length, mlift_length]; exact hlen)
      ?_ (fun m hm => ?_)
    · unfold reliftX
      rw [slift_length, srow_slift (reStair_stair _ _ _ _) (by rw [mlift_length]; omega),
        hasParent_slift (reStair_stair _ _ _ _)]
      exact (hasParent_mlift_iff u (b' - u) hUne).mpr hp
    · have h1 := hIH m hm g b' hb'
      rw [mlift_app hW (Hd_oper hH hUne hm),
        reliftX_app (Fr_mlift hW _ _) (Hd_mlift (Hd_oper hH hUne hm) _ _)] at h1
      unfold reliftX at h1 ⊢
      rwa [← mlift_oper', slift_oper (reStair_stair _ _ _ _)] at h1
  orph := by
    intro u W U h j hW hU hH hj1 hj hnp hz g b' hb'
    have hfix : ∀ m, m ≤ j → reStair b' H g A m = m :=
      fun m hm => reStair_low b' H g _ (by omega)
    have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u := hj
    have eU : reliftX b' H g A (mlift U u (b' - u)) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]
        = slift (mlift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) (reStair b' H g A) := by
      unfold reliftX; rw [mlift_snoc_low U _ hc, slift_snoc_fix _ _ hfix]
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _)]
    have eU2 : reliftX b' H g A (mlift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) u (b' - u))
        = reliftX b' H g A (mlift U u (b' - u)) ++ [((h, j, 0) : ℕ × ℕ × ℕ)] := by
      rw [eU]; rfl
    rw [eU2]
    refine (NXt_ax hA01 hk1 (addF H g)).orph b' _ _ h j
      (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (by rw [eU]; exact Fr_slift (Fr_mlift hU _ _) _)
      (by rw [eU]; exact Hd_slift (Hd_mlift hH _ _) _) hj1 (le_trans hj hb') ?_
      (fun z hz' hbz => ?_)
    · intro hh; apply hnp
      rw [eU, reliftX_length, mlift_length, hasParent_slift (reStair_stair _ _ _ _),
        mlift_eq_slift, hasParent_slift (stair_step _ _)] at hh
      exact hh
    · have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
      have h1 := hz z hz' hbz g b' hb'
      have hHz := Hd_append_shift hH hbz
      rw [mlift_app hW hHz, mlift_append_low (low_of_Wg hzW h (show j ≤ u by omega))] at h1
      have hH2 : Hd (mlift U u (b' - u) ++ shiftr01 h 0 z) := by
        have := Hd_mlift hHz u (b' - u)
        rwa [mlift_append_low (low_of_Wg hzW h (show j ≤ u by omega))] at this
      rw [reliftX_app (Fr_mlift hW _ _) hH2] at h1
      unfold reliftX at h1 ⊢
      rwa [slift_append_low (low_of_Wg hzW h (show j ≤ b' by omega))
        (fun m hm => reStair_low b' H g _ hm)] at h1
  tie := by
    intro u W U x hW hU hH hc hload g b' hb'
    have eT : mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)
        = mlift U u (b' - u) ++ [((x, b' + 1, 0) : ℕ × ℕ × ℕ)] := by
      rw [mlift_snoc_cone U _ hc]
      show _ ++ [((x, u + 1 + (b' - u), 0) : ℕ × ℕ × ℕ)] = _
      rw [show u + 1 + (b' - u) = b' + 1 by omega]
    have hfix : ∀ m, m ≤ b' + 1 → reStair b' H g A m = m :=
      fun m hm => reStair_tie b' H g hA01 hm
    have eU : reliftX b' H g A (mlift U u (b' - u)) ++ [((x, b' + 1, 0) : ℕ × ℕ × ℕ)]
        = reliftX b' H g A (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) := by
      rw [eT]; unfold reliftX; rw [slift_snoc_fix _ _ hfix]
    have hHU : Hd U := by
      intro hne
      have := hH (by simp)
      rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), ← eU]
    refine (NXt_ax hA01 hk1 (addF H g)).tie b' _ _ x
      (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (by rw [eU]; exact Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
      (by rw [eU]; exact Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) ?_ (fun b'' hb'' Z hZ hbZ => ?_)
    · rw [eU, reliftX_length, mlift_length]
      unfold reliftX
      rw [coneV_iff_amin, amin_slift (reStair_stair _ _ _ _) (by simp)]
      have h0 : coneV (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) (u + (b' - u))
          U.length := coneV_mlift (by simp) hc (b' - u)
      rw [show u + (b' - u) = b' by omega, coneV_iff_amin] at h0
      have h1 := (reStair_stair b' H g A).ge
        (amin (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) U.length)
      omega
    · have h1 := hload b'' (le_trans hb' hb'') Z hZ hbZ g b'' le_rfl
      rw [Nat.sub_self, mlift_zero] at h1
      have e1 : reliftX b'' H g A (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z)
          = reliftX b'' H g A (mlift (W ++ U) u (b'' - u)) ++ shiftr01 x 0 Z := by
        unfold reliftX
        exact slift_append_low (low_of_Wg hZ x le_rfl) (fun m hm => reStair_low b'' H g _ hm)
      have e2 : reliftX b'' H g A (mlift (W ++ U) u (b'' - u))
          = mlift (reliftX b' H g A (mlift W u (b' - u)) ++
              reliftX b' H g A (mlift U u (b' - u))) b' (b'' - b') := by
        rw [← reliftX_app (Fr_mlift hW _ _) (Hd_mlift hHU _ _), ← mlift_app hW hHU, mlift_reliftX,
          show b' + (b'' - b') = b'' by omega]
        have e := mlift_mlift (W ++ U) u (b' - u) (b'' - b')
        rw [show u + (b' - u) = b' by omega, show b' - u + (b'' - b') = b'' - u by omega] at e
        rw [e]
      rw [e1, e2] at h1
      exact h1
  flat := by
    intro u W hW h g b' hb'
    rw [mlift_snoc_flat W 1 u (b' - u) hW]
    have e : reliftX b' H g A (mlift W u (b' - u) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
        = reliftX b' H g A (mlift W u (b' - u)) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
      unfold reliftX
      refine slift_snoc_fix _ _ (fun m hm => ?_)
      have hm0 : m = 0 := by simpa using hm
      subst hm0; exact (reStair_stair _ _ _ _).zero
    rw [e]
    exact (NXt_ax hA01 hk1 (addF H g)).flat b' _ (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
      (h g b' hb')

/-! ## FarP の場 -/

/-- 子の段が塊の段 b1 と同じ場合。 -/
theorem FarP_RNt_core {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (hAk : ∀ a ∈ A, a < k)
    {P1 : TrioSeq} {b1 s1 d : ℕ} {H1 : ℕ → ℕ} (hP1Fr : Fr P1) (hd : 1 ≤ d)
    (hbotP1 : BotGe P1 d (b1 + s1)) (hs12 : 2 ≤ s1) (hsK : s1 ≤ reOff (fun _ => 0) H1 A k)
    (hP1ok : NXt A k H1 b1 P1) (hHd : Hd (P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)]))
    (h2' : ∀ (g2 : ℕ → ℕ) b', b1 ≤ b' → ∀ τ L, 1 ≤ τ → τ < reOff H1 g2 A s1 → Fr L →
      GC A (addF H1 g2) τ b' L →
      NXt A k (addF H1 g2) b' (reliftX b' H1 g2 A (mlift P1 b1 (b' - b1)) ++
        shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)))
    (us : List UT) (hus : GoodLowT b1 us)
    (Lds : List (List UT)) (hL : GoodChtX A k H1 b1 Lds) :
    GoodChtX A k H1 b1 (Lds ++ [us ++ [UT.ch (P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)])]]) := by
  have hKge : k ≤ reOff (fun _ => 0) H1 A k := by unfold reOff; omega
  have e00 : mlift (P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)]) b1 (b1 - b1)
      = P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)] := by rw [Nat.sub_self, mlift_zero]
  rw [← e00]
  refine NXt_snoc_of hA01 hk1 hL hus le_rfl (Fr_append hP1Fr (GzF.Fr_single hd _ _)) hHd
    (LowC_snoc hP1ok.2.1 _ (by show b1 + s1 ≤ b1 + reOff (fun _ => 0) H1 A k; omega))
    (fun g S o f bb hE hub ws hC hR => ?_)
  have hA := hE.2.2.1
  have hA1 := hE.2.2.2.1
  have ho := hE.2.2.2.2.1
  have hSA := hE.2.1
  have hf := hE.1
  have hK := hE.2.2.2.2.2.1
  have hKo := hE.2.2.2.2.2.2
  have e0 : ∀ c (K G : ℕ → ℕ) (B : List ℕ), reliftX c K G B ([] : TrioSeq) = [] := fun c K G B => by
    unfold reliftX; exact slift_nil _
  obtain ⟨r, hr⟩ : ∃ r, r = bb + liftOff f (S ++ A) o + 1 := ⟨_, rfl⟩
  have hbotQ : BotGe (mlift P1 b1 (bb - b1)) d (bb + s1) := by
    have := BotGe_slift hbotP1 (stair_step b1 (bb - b1))
    rw [← mlift_eq_slift, if_pos (by omega), show b1 + s1 + (bb - b1) = bb + s1 by omega] at this
    exact this
  have eL1 : mlift (P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)]) b1 (bb - b1)
      = mlift P1 b1 (bb - b1) ++ [((d, bb + s1, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_bottom hbotP1, if_pos (by omega), show b1 + s1 + (bb - b1) = bb + s1 by omega]
  rw [eL1, reliftX_snoc_bottom hd bb hbotQ H1 g A, ← hr]
  obtain ⟨P3, hP3⟩ : ∃ P3, P3 = reliftX bb H1 g A (mlift P1 b1 (bb - b1)) := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = reOff H1 g A s1 := ⟨_, rfl⟩
  rw [← hP3, ← hs']
  have hs2ge : s1 ≤ s' := by rw [hs']; unfold reOff; omega
  have hs2K : s' ≤ reOff (fun _ => 0) (addF H1 g) A k := by
    rw [hs', ← reOff_zero_comp H1 g A k]; exact reOff_mono H1 g A hsK
  have hso : s' ≤ liftOff f (S ++ A) o := le_trans hs2K hKo
  have hFP := FarP_GpT_ge hA hA1 ho (f := f) (show 2 ≤ s' by omega) hso
  have eF : fwH bb r (FTLt bb r b1 (Lds.map (relTs A H1 g b1))) bb
        (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT bb r b1 us ++ (P3 ++ [((d, bb + s', 0) : ℕ × ℕ × ℕ)])))
      = fwH bb r (FTLt bb r b1 (Lds.map (relTs A H1 g b1))) bb
          (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT bb r b1 us ++ P3)) ++
        [((d + 2, bb + s', 0) : ℕ × ℕ × ℕ)] := by
    unfold fwH; simp only [Nat.sub_self, mlift_zero]; simp [shiftr01]
  rw [eF, ← List.append_assoc]
  have hP3F : Fr P3 := by rw [hP3]; exact Fr_reliftX (Fr_mlift hP1Fr _ _) _ _ _ _
  have hQF : Fr (farWt bb r ws ++ fwH bb r (FTLt bb r b1
      (Lds.map (relTs A H1 g b1))) bb
      (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT bb r b1 us ++ P3))) :=
    Fr_append (Fr_farWt _ _ _) (Fr_fwH _ _ _ _ _)
  have hbotP3 : BotGe P3 d (bb + s') := by
    have := BotGe_slift hbotQ (reStair_stair bb H1 g A)
    change BotGe (reliftX bb H1 g A (mlift P1 b1 (bb - b1))) d _ at this
    rwa [reStair_base, ← hP3, ← hs'] at this
  have hbotC : BotGe (chT bb r b1 us ++ P3) d (bb + s') := by
    rcases P1 with _ | ⟨x, P1t⟩
    · have hd1 : d = 1 := by have := hHd (by simp); simpa [entry] using this
      subst hd1
      exact BotGe_one (Fr_append (Fr_chT _ hus.1) hP3F) _
    · refine BotGe_append_left (Fr_chT _ hus.1)
        (by rw [hP3]; exact Hd_reliftX (Hd_mlift hP1ok.1 _ _) _ _ _ _) ?_ hbotP3
      intro h0
      have := congrArg List.length h0
      rw [hP3] at this
      simp [mlift_length, reliftX_length] at this
  have hbotQQ : BotGe (farWt bb r ws ++ fwH bb r (FTLt bb r b1
      (Lds.map (relTs A H1 g b1))) bb
      (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT bb r b1 us ++ P3))) (d + 2) (bb + s') := by
    unfold fwH
    simp only [Nat.sub_self, mlift_zero]
    exact BotGe_node (Fr_farWt _ _ _) (by omega) (BotGe_node (Fr_FTLt _ _ _ _) (by omega) hbotC)
  have hW1R : ∀ us' ∈ Lds ++ [us ++ [UT.ch (mlift P1 b1 (b1 - b1))]],
      RawTs (b1 + reOff (fun _ => 0) H1 A k) us' := by
    intro us' hus'
    rcases List.mem_append.mp hus' with hus' | hus'
    · exact hL.1 us' hus'
    · rw [List.mem_singleton] at hus'; rw [hus']
      rw [Nat.sub_self, mlift_zero]
      exact RawTs_snoc.mpr ⟨RawTs_mono' (by omega) hus.1, RawT_ch hP1Fr hP1ok.1 hP1ok.2.1⟩
  have eQ : farWt bb r ws ++ fwH bb r (FTLt bb r b1
      (Lds.map (relTs A H1 g b1))) bb
      (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT bb r b1 us ++ P3))
      = farWt bb r (ws ++ [((Lds ++ [us ++ [UT.ch (mlift P1 b1 (b1 - b1))]]).map
          (relTs A H1 g b1), b1, [])]) := by
    rw [farWt_lastX hA01 H1 g le_rfl hub ws Lds hus.1 P1, hP3]
  have hRn : RawWsAt (S ++ A) o f bb (ws ++ [((Lds ++ [us ++ [UT.ch (mlift P1 b1 (b1 - b1))]]).map
      (relTs A H1 g b1), b1, [])]) :=
    RawWsAt_snoc hR ⟨hub, RawLdt_emb hE hW1R, Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
  have eP : ∀ (g' : ℕ → ℕ) b', bb ≤ b' →
      reliftX b' f g' (S ++ A) (mlift (farWt bb r ws ++ fwH bb r (FTLt bb r b1
        (Lds.map (relTs A H1 g b1))) bb
        (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT bb r b1 us ++ P3))) bb (b' - bb))
      = farWt b' (b' + liftOff (addF f g') (S ++ A) o + 1) (relWst (S ++ A) f g' ws) ++
        fwH b' (b' + liftOff (addF f g') (S ++ A) o + 1)
          (FTLt b' (b' + liftOff (addF f g') (S ++ A) o + 1) b1
            (Lds.map (relTs A H1 (addF g g') b1))) b'
          (((1, b' + liftOff (addF f g') (S ++ A) o + 1, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (chT b' (b' + liftOff (addF f g') (S ++ A) o + 1) b1 us ++
              reliftX b' H1 (addF g g') A (mlift P1 b1 (b' - b1)))) := by
    intro g' b' hb'
    rw [eQ, hr, mlift_farWt_self hRn hb', reliftX_farWt_self hA b' g' (RawWsAt_mono hb' hRn),
      relWst_snoc, e0, EmbU_relLdt hE b1 g' hW1R,
      farWt_lastX hA01 H1 (addF g g') le_rfl (by omega) _ Lds hus.1 P1]
  have hRw : ∀ w ∈ ws, (∀ us ∈ w.1, RawTs (w.2.1 + reOff (fun _ => 0) f (S ++ A) o) us) ∧
      Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) f (S ++ A) o) w.2.2 :=
    fun w hw => (hR w hw).2
  refine hFP bb _ (d + 2) hQF (by omega) hbotQQ (fun g' b' hb' => ?_)
    (fun g' b' hb' τ L h1τ hτ hL' hGL => ?_)
  · -- h1
    rw [eP g' b' hb']
    exact NXt_snoc_elim (hP1ok.2.2 b1 le_rfl us hus Lds hL) hA01 hus.1 le_rfl (addF g g') S o
      (addF f g') b' (EmbU_relift hE g') (by omega) _ (FarCAt_mono hb' (FarCAt_relift hC hRw g'))
      (RawWsAt_relWst (RawWsAt_mono hb' hR) g')
  · -- h2
    rw [eP g' b' hb']
    obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
    have hτ1 : τ < reOff H1 (addF g g') A s1 := by
      have e1 : reOff f g' (S ++ A) s' = reOff (addF H1 g) g' A s' :=
        reOff_ins_low hSA hf g' hK hs2K
      rw [e1, hs', reOff_comp] at hτ
      exact hτ
    have hτK : τ ≤ reOff (fun _ => 0) (addF H1 (addF g g')) A k := by
      have := reOff_mono H1 (addF g g') A hsK
      rw [reOff_zero_comp] at this
      omega
    have hGL' : GC A (addF H1 (addF g g')) τ b' L :=
      GC_ins_low hSA hfG (fun s'' hs'' => le_trans hτK (hKG s'' hs'')) hGL
    have hY := h2' (addF g g') b' (by omega) τ L h1τ hτ1 hL' hGL'
    have hL2 : GoodChtX A k (addF H1 (addF g g')) b1
        (Lds.map (relTs A H1 (addF g g') b1)) :=
      GoodChtX_emb hL (EmbU_self hA01 hk1 hAk H1 (addF g g'))
    have hL3 := GoodChtX_lift hL2 (show b1 ≤ b' by omega)
    have hus3 := GoodLowT_lift hus (show b1 ≤ b' by omega)
    have hE3 : EmbU A k (addF H1 (addF g g')) (fun _ => 0) S o (addF f g') :=
      EmbU_shift (EmbU_relift hE g')
    have := NXt_snoc_elim (hY.2.2 b' le_rfl _ hus3 _ hL3) hA01 hus3.1 le_rfl (fun _ => 0) S o
      (addF f g') b' hE3 le_rfl _ (FarCAt_mono hb' (FarCAt_relift hC hRw g'))
      (RawWsAt_relWst (RawWsAt_mono hb' hR) g')
    rw [reliftX_zero, Nat.sub_self, mlift_zero, mapt_zero, FTLt_rebase (show b1 ≤ b' by omega) le_rfl,
      chT_rebase (show b1 ≤ b' by omega) le_rfl, fwH_child_app _ _ _ _ _ _ hd] at this
    rw [show d + 2 - 1 = d + 1 by omega, List.append_assoc]
    exact this

theorem FarP_RNt {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (hAk : ∀ a ∈ A, a < k)
    {H : ℕ → ℕ} {s : ℕ} (hs2 : 2 ≤ s) (hs : s ≤ liftOff H A k) :
    FarP (GC A) (fun H' => RNt A k H') A H s := by
  intro b P d hP hd hbot h1 h2 g1 b1 hb1
  have hbotb : BotGe (mlift P b (b1 - b)) d (b1 + s) := by
    have := BotGe_slift hbot (stair_step b (b1 - b))
    rw [← mlift_eq_slift, if_pos (by omega), show b + s + (b1 - b) = b1 + s by omega] at this
    exact this
  have eB1 : mlift (P ++ [((d, b + s, 0) : ℕ × ℕ × ℕ)]) b (b1 - b)
      = mlift P b (b1 - b) ++ [((d, b1 + s, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_bottom hbot, if_pos (by omega), show b + s + (b1 - b) = b1 + s by omega]
  rw [eB1, reliftX_snoc_bottom hd b1 hbotb H g1 A]
  obtain ⟨P1, hP1⟩ : ∃ P1, P1 = reliftX b1 H g1 A (mlift P b (b1 - b)) := ⟨_, rfl⟩
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = reOff H g1 A s := ⟨_, rfl⟩
  obtain ⟨H1, hH1⟩ : ∃ H1, H1 = addF H g1 := ⟨_, rfl⟩
  rw [← hP1, ← hs1, ← hH1]
  have hP1Fr : Fr P1 := by rw [hP1]; exact Fr_reliftX (Fr_mlift hP _ _) _ _ _ _
  have hbotP1 : BotGe P1 d (b1 + s1) := by
    have := BotGe_slift hbotb (reStair_stair b1 H g1 A)
    change BotGe (reliftX b1 H g1 A (mlift P b (b1 - b))) d _ at this
    rwa [reStair_base, ← hP1, ← hs1] at this
  have hP1ok : NXt A k H1 b1 P1 := by
    have := RNt_okW (h1 g1 b1 hb1); rwa [← hP1, ← hH1] at this
  have hs1ge : s ≤ s1 := by rw [hs1]; unfold reOff; omega
  have hsK : s1 ≤ reOff (fun _ => 0) H1 A k := by
    rw [hs1, hH1, ← reOff_zero_comp H g1 A k]
    exact reOff_mono H g1 A (by rw [← liftOff_eq_reOff0]; exact hs)
  have h2' : ∀ (g2 : ℕ → ℕ) b', b1 ≤ b' → ∀ τ L, 1 ≤ τ → τ < reOff H1 g2 A s1 → Fr L →
      GC A (addF H1 g2) τ b' L →
      NXt A k (addF H1 g2) b' (reliftX b' H1 g2 A (mlift P1 b1 (b' - b1)) ++
        shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) := by
    intro g2 b' hb' τ L h1τ hτ hL hGL
    have eH : addF H1 g2 = addF H (addF g1 g2) := by rw [hH1, addF_assoc]
    have hτ' : τ < reOff H (addF g1 g2) A s := by
      rw [← reOff_comp, ← hs1, ← hH1]; exact hτ
    rw [eH] at hGL ⊢
    have := RNt_okW (h2 (addF g1 g2) b' (by omega) τ L h1τ hτ' hL hGL)
    have eP : reliftX b' H1 g2 A (mlift P1 b1 (b' - b1))
        = reliftX b' H (addF g1 g2) A (mlift P b (b' - b)) := by
      rw [hP1, mlift_reliftX, show b1 + (b' - b1) = b' by omega, hH1, reliftX_comp]
      have e := mlift_mlift P b (b1 - b) (b' - b1)
      rw [show b + (b1 - b) = b1 by omega, show b1 - b + (b' - b1) = b' - b by omega] at e
      rw [e]
    rw [eP]; exact this
  have hHd : Hd (P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)]) := by
    have hGC1 : GC A (addF H1 (fun _ => 0)) 1 b1 [] := by
      unfold GC; rw [lowP_one hA01]; simpa [sumOn] using GpT_nil1 (addF H1 (fun _ => 0)) b1
    have hH := (h2' (fun _ => 0) b1 le_rfl 1 [] le_rfl
      (by unfold reOff; rw [reStep_zeroG]; omega) Fr_nil hGC1).1
    rw [Nat.sub_self, mlift_zero, reliftX_zero] at hH
    intro _
    have h0 := hH (by simp [shiftr01])
    rcases P1 with _ | ⟨x, P1⟩
    · simp [shiftr01, entry] at h0 ⊢; omega
    · exact h0
  refine ⟨hHd, LowC_snoc hP1ok.2.1 _ (by show b1 + s1 ≤ b1 + reOff (fun _ => 0) H1 A k; omega),
    fun c' hc' us hus Lds hL => ?_⟩
  have eM : mlift (P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)]) b1 (c' - b1)
      = mlift P1 b1 (c' - b1) ++ [((d, c' + s1, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_bottom hbotP1, if_pos (by omega), show b1 + s1 + (c' - b1) = c' + s1 by omega]
  rw [eM]
  refine FarP_RNt_core hA01 hk1 hAk (Fr_mlift hP1Fr _ _) hd ?_ (by omega) hsK
    ((NXt_ax hA01 hk1 H1).lift b1 P1 hP1Fr hP1ok c' hc') ?_ ?_ us hus Lds hL
  · have := BotGe_slift hbotP1 (stair_step b1 (c' - b1))
    rw [← mlift_eq_slift, if_pos (by omega), show b1 + s1 + (c' - b1) = c' + s1 by omega] at this
    exact this
  · rw [← eM]; exact Hd_mlift hHd _ _
  · intro g2 b' hb' τ L h1τ hτ hL' hGL
    have := h2' g2 b' (by omega) τ L h1τ hτ hL' hGL
    have e := mlift_mlift P1 b1 (c' - b1) (b' - c')
    rw [show b1 + (c' - b1) = c' by omega, show c' - b1 + (b' - c') = b' - b1 by omega] at e
    rw [e]; exact this

/-- ★ RNt は錨の列 A・上限 k の文脈の族。 -/
theorem RNt_ctx {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (hAk : ∀ a ∈ A, a < k) :
    CtxP (GC A) A k (fun H => RNt A k H) := fun H =>
  ⟨RNt_ax hA01 hk1 H, fun _ _ _ hH h => RNt_congr hH h, fun g _ _ _ h => RNt_lift h g,
    fun _ hs2 hs => FarP_RNt hA01 hk1 hAk hs2 hs⟩

/-- ★ 子の位置の塊に、子の級 GC A H τ の並びを持つ節点を置く。 -/
theorem RNt_node {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (hAk : ∀ a ∈ A, a < k)
    {H : ℕ → ℕ} {u τ : ℕ} {X L : TrioSeq} (hX : Fr X)
    (h : RNt A k H u X) (hL : GC A H τ u L) (hτ : τ ≤ liftOff H A k) :
    RNt A k H u (X ++ ((1, u + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
  R_child (R := fun H => RNt A k H) (RNt_ctx hA01 hk1 hAk) hAk hX h hL hτ

end HdG
end TRIO
