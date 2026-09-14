/-
HeF.lean: 道の集合 P の低い塊の族の状態の層 RNs P と文脈の公理（HdO の写し、段つきの道）。

    RNs P A k H b X := ∀ g b', b ≤ b' → NXs P A k (H+g) b' (reliftX b' H g A (mlift X b (b' − b)))
- 道の成分の節点は行 1 が r + l ≥ r なので、底の祖先の行 1 ≥ v（BotGe_chTQ / BotGe_path）。
- FarP の場の証明は HdO と同じ（PSOK の emb / lift / raw を使う）。
-/
import HeE

namespace TRIO
namespace HeF

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcE HcF HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HeB HeC HeD HeE

/-! ## 補題 -/

theorem Gd_congrH {P : PS} {A : List ℕ} {k : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A, H a = H' a) {c : ℕ}
    {x : List UT} (h : Gd P A k H c x) : Gd P A k H' c x := by
  refine ⟨by rw [← reOff_congrH hH]; exact h.1, fun G S o f hE u hcu Lds hL Q hQ => ?_⟩
  have e : imgT A H' G c u x = imgT A H G c u x := by
    unfold imgT; exact relTs_congr (fun a ha => (hH a ha).symm) G u _
  rw [e]
  exact h.2 G S o f (EmbU_congr (fun a ha => (hH a ha).symm) hE) u hcu Lds hL Q hQ

theorem NXs_congr {P : PS} {A : List ℕ} {k : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A, H a = H' a) {c : ℕ}
    {X : TrioSeq} (h : NXs P A k H c X) : NXs P A k H' c X :=
  ⟨h.1, by rw [← reOff_congrH hH]; exact h.2.1, fun c' hc' us hus =>
    Gd_congrH hH (h.2.2 c' hc' us (Gd_congrH (fun a ha => (hH a ha).symm) hus))⟩

theorem NXs_nil {P : PS} {A : List ℕ} {k : ℕ} (H : ℕ → ℕ) (c : ℕ) : NXs P A k H c [] := by
  refine ⟨fun h => absurd rfl h, LowC_nil _, fun c' hc' us hus => ?_⟩
  refine NXs_snoc_of hus hc' Fr_nil (fun h => absurd rfl h) (LowC_nil _)
    (fun G S o f hE u hcu Lds hL Q hQ b hub ws hC hR => ?_)
  have := hus.2 G S o f hE u hcu Lds hL Q hQ b hub ws hC hR
  rw [farWt_botT] at this
  have e : reliftX b H G A (mlift ([] : TrioSeq) c (b - c)) = [] := by
    rw [mlift_nil]; unfold reliftX; exact slift_nil _
  rw [e, List.append_nil]
  exact this

theorem BotGe_chTQ {b r u : ℕ} {V : TrioSeq} {d v : ℕ} (hvr : v ≤ r) (hV : BotGe V d v) :
    ∀ Q : Path, (∀ p ∈ Q, ∃ K, RawTs K p.1) →
      BotGe (chTQ b r u Q ++ shiftr01 Q.length 0 V) (d + Q.length) v
  | [], _ => by simpa [chTQ, shiftr01] using hV
  | (us, l) :: q, hQ => by
      obtain ⟨K, hK⟩ := hQ (us, l) (by simp)
      have ih := BotGe_chTQ (b := b) (u := u) hvr hV q (fun p' h' => hQ p' (by simp [h']))
      have e : chTQ b r u ((us, l) :: q) ++ shiftr01 ((us, l) :: q).length 0 V
          = chT b r u us ++ ((1, r + l, 0) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (chTQ b r u q ++ shiftr01 q.length 0 V) := by
        simp only [chTQ, List.length_cons, shiftr01_append0, shiftr01_add0, List.append_assoc,
          List.cons_append]
      rw [e, show d + ((us, l) :: q).length = d + q.length + 1 by simp; omega]
      exact BotGe_node (Fr_chT _ hK) (show v ≤ r + l by omega) ih

/-- 道の下の塊の底の節点の祖先は、行 1 が r の道の頭か、塊の中。 -/
theorem BotGe_path {b r u : ℕ} (ws : List (List (List UT) × ℕ × TrioSeq)) (Lds : List (List UT)) (Q : Path)
    (hQ : ∀ p ∈ Q, ∃ K, RawTs K p.1) {V : TrioSeq} {d v : ℕ} (hvr : v ≤ r) (hV : BotGe V d v) :
    BotGe (farWt b r ws ++ (fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++
      shiftr01 (Q.length + 2) 0 V)) (d + (Q.length + 2)) v := by
  have h1 := BotGe_chTQ (b := b) (u := u) hvr hV Q hQ
  have h2 := BotGe_node (Fr_FTLt b r u Lds) hvr h1 (z := 0)
  have h3 := BotGe_node (X := []) Fr_nil hvr h2 (z := 1)
  have e : fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++ shiftr01 (Q.length + 2) 0 V
      = [] ++ ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FTLt b r u Lds ++ ((1, r, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (chTQ b r u Q ++ shiftr01 Q.length 0 V)) := by
    have e0 : shiftr01 Q.length 0 (chT b r u []) = [] := by simp [chT, shiftr01]
    simp [fwH, mlift_nil, FTLt_snoc, chT_plugQ, chT, shiftr01, Function.comp_def, Nat.add_assoc]
  rw [e, show d + (Q.length + 2) = d + Q.length + 1 + 1 by omega]
  refine BotGe_append_left (Fr_farWt _ _ _) (by rw [← e]; exact Hd_app_ne (Hd_fwH _ _ _ _ _) (by simp [fwH]))
    (by simp) h3

/-! ## 状態の層 -/

def RNs (P : PS) (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (b : ℕ) (X : TrioSeq) : Prop :=
  ∀ g b', b ≤ b' → NXs P A k (addF H g) b' (reliftX b' H g A (mlift X b (b' - b)))

theorem RNs_lift {P : PS} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b : ℕ} {X : TrioSeq}
    (h : RNs P A k H b X) (g : ℕ → ℕ) : RNs P A k (addF H g) b (reliftX b H g A X) := by
  intro g' b' hb'
  rw [mlift_reliftX, show b + (b' - b) = b' by omega, reliftX_comp, addF_assoc]
  exact h (addF g g') b' hb'

theorem RNs_congr {P : PS} {A : List ℕ} {k : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A, H a = H' a)
    {b : ℕ} {X : TrioSeq} (h : RNs P A k H b X) : RNs P A k H' b X := by
  intro g b' hb'
  have e : reliftX b' H' g A (mlift X b (b' - b)) = reliftX b' H g A (mlift X b (b' - b)) :=
    reliftX_congr b' (fun a ha => (hH a ha).symm) (fun _ _ => rfl) _
  rw [e]
  exact NXs_congr (fun a ha => by simp [addF, hH a ha]) (h g b' hb')

theorem RNs_nil {P : PS} {A : List ℕ} {k : ℕ} (H : ℕ → ℕ) (b : ℕ) : RNs P A k H b [] := by
  intro g b' _
  rw [mlift_nil]
  have e : reliftX b' H g A [] = [] := by unfold reliftX; exact slift_nil _
  rw [e]
  exact NXs_nil _ _

theorem RNs_okW {P : PS} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {b : ℕ} {X : TrioSeq}
    (h : RNs P A k H b X) : NXs P A k H b X := by
  have := h (fun _ => 0) b le_rfl
  rwa [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero] at this

/-- ★ 状態の層の差し込み口の公理。 -/
theorem RNs_ax {P : PS} (hP : PSOK P) (hD : HeC.PSDec P) {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (H : ℕ → ℕ) :
    SlotAx (RNs P A k H) where
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
    refine (NXs_ax hP hD hA01 hk1 (addF H g)).oper b' _ _
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
    refine (NXs_ax hP hD hA01 hk1 (addF H g)).orph b' _ _ h j
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
    refine (NXs_ax hP hD hA01 hk1 (addF H g)).tie b' _ _ x
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
    exact (NXs_ax hP hD hA01 hk1 (addF H g)).flat b' _ (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
      (h g b' hb')

/-! ## FarP の場 -/

/-- 子の段が塊の段 b1 と同じ場合。 -/
theorem FarP_RNs_core {P : PS} (hP : PSOK P) (hD : HeC.PSDec P) {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k)
    (hAk : ∀ a ∈ A, a < k)
    {P1 : TrioSeq} {b1 s1 d : ℕ} {H1 : ℕ → ℕ} (hP1Fr : Fr P1) (hd : 1 ≤ d)
    (hbotP1 : BotGe P1 d (b1 + s1)) (hs12 : 2 ≤ s1) (hsK : s1 ≤ reOff (fun _ => 0) H1 A k)
    (hP1ok : NXs P A k H1 b1 P1) (hHd : Hd (P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)]))
    (h2' : ∀ (g2 : ℕ → ℕ) b', b1 ≤ b' → ∀ τ L, 1 ≤ τ → τ < reOff H1 g2 A s1 → Fr L →
      GC A (addF H1 g2) τ b' L →
      NXs P A k (addF H1 g2) b' (reliftX b' H1 g2 A (mlift P1 b1 (b' - b1)) ++
        shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)))
    (us : List UT) (hus : Gd P A k H1 b1 us) :
    Gd P A k H1 b1 (us ++ [UT.ch (P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)])]) := by
  have hKge : k ≤ reOff (fun _ => 0) H1 A k := by unfold reOff; omega
  have e00 : mlift (P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)]) b1 (b1 - b1)
      = P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)] := by rw [Nat.sub_self, mlift_zero]
  rw [← e00]
  have hP1T : Gd P A k H1 b1 (us ++ [UT.ch P1]) := by
    have := hP1ok.2.2 b1 le_rfl us hus
    rwa [Nat.sub_self, mlift_zero] at this
  refine NXs_snoc_of hus le_rfl (Fr_append hP1Fr (GzF.Fr_single hd _ _)) hHd
    (LowC_snoc hP1ok.2.1 _ (by show b1 + s1 ≤ b1 + reOff (fun _ => 0) H1 A k; omega))
    (fun G S o f hE u hcu Lds hL Q hQ bb hub ws hC hR => ?_)
  have hA := hE.2.2.1
  have hA1 := hE.2.2.2.1
  have ho := hE.2.2.2.2.1
  have hSA := hE.2.1
  have hf := hE.1
  have hK := hE.2.2.2.2.2.1
  have hKo := hE.2.2.2.2.2.2
  obtain ⟨r, hr⟩ : ∃ r, r = bb + liftOff f (S ++ A) o + 1 := ⟨_, rfl⟩
  have hbotQ : BotGe (mlift P1 b1 (bb - b1)) d (bb + s1) := by
    have := BotGe_slift hbotP1 (stair_step b1 (bb - b1))
    rw [← mlift_eq_slift, if_pos (by omega), show b1 + s1 + (bb - b1) = bb + s1 by omega] at this
    exact this
  have eL1 : mlift (P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)]) b1 (bb - b1)
      = mlift P1 b1 (bb - b1) ++ [((d, bb + s1, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_bottom hbotP1, if_pos (by omega), show b1 + s1 + (bb - b1) = bb + s1 by omega]
  rw [eL1, reliftX_snoc_bottom hd bb hbotQ H1 G A, ← hr]
  obtain ⟨P3, hP3⟩ : ∃ P3, P3 = reliftX bb H1 G A (mlift P1 b1 (bb - b1)) := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = reOff H1 G A s1 := ⟨_, rfl⟩
  rw [← hP3, ← hs']
  have hs2ge : s1 ≤ s' := by rw [hs']; unfold reOff; omega
  have hs2K : s' ≤ reOff (fun _ => 0) (addF H1 G) A k := by
    rw [hs', ← reOff_zero_comp H1 G A k]; exact reOff_mono H1 G A hsK
  have hso : s' ≤ liftOff f (S ++ A) o := le_trans hs2K hKo
  have hFP := FarP_GpT_ge hA hA1 ho (f := f) (show 2 ≤ s' by omega) hso
  have hRaw := RawTs_imgT hE hcu hus.1
  obtain ⟨V0, hV0⟩ : ∃ V0, V0 = chT bb r u (imgT A H1 G b1 u us) := ⟨_, rfl⟩
  rw [← hV0]
  have eF : farWt bb r ws ++ (fwH bb r (FTLt bb r u (Lds ++ [plugQ Q []])) u [] ++
        shiftr01 (Q.length + 2) 0 (V0 ++ (P3 ++ [((d, bb + s', 0) : ℕ × ℕ × ℕ)])))
      = (farWt bb r ws ++ (fwH bb r (FTLt bb r u (Lds ++ [plugQ Q []])) u [] ++
          shiftr01 (Q.length + 2) 0 (V0 ++ P3))) ++ [((d + (Q.length + 2), bb + s', 0) : ℕ × ℕ × ℕ)] := by
    simp [shiftr01, Nat.add_comm]
  rw [eF]
  have hP3F : Fr P3 := by rw [hP3]; exact Fr_reliftX (Fr_mlift hP1Fr _ _) _ _ _ _
  have hV0F : Fr V0 := by rw [hV0]; exact Fr_chT _ hRaw
  have hQF : Fr (farWt bb r ws ++ (fwH bb r (FTLt bb r u (Lds ++ [plugQ Q []])) u [] ++
      shiftr01 (Q.length + 2) 0 (V0 ++ P3))) :=
    Fr_append (Fr_farWt _ _ _) (Fr_append (Fr_fwH _ _ _ _ _) (Fr_shiftr (Fr_append hV0F hP3F) _))
  have hbotP3 : BotGe P3 d (bb + s') := by
    have := BotGe_slift hbotQ (reStair_stair bb H1 G A)
    change BotGe (reliftX bb H1 G A (mlift P1 b1 (bb - b1))) d _ at this
    rwa [reStair_base, ← hP3, ← hs'] at this
  have hbotC : BotGe (V0 ++ P3) d (bb + s') := by
    rcases P1 with _ | ⟨x, P1t⟩
    · have hd1 : d = 1 := by have := hHd (by simp); simpa [entry] using this
      subst hd1
      exact BotGe_one (Fr_append hV0F hP3F) _
    · refine BotGe_append_left hV0F
        (by rw [hP3]; exact Hd_reliftX (Hd_mlift hP1ok.1 _ _) _ _ _ _) ?_ hbotP3
      intro h0
      have := congrArg List.length h0
      rw [hP3] at this
      simp [mlift_length, reliftX_length] at this
  have hbotQQ := BotGe_path (b := bb) (r := r) (u := u) ws Lds Q
    (fun p' h' => ⟨_, hP.raw _ _ _ _ _ hQ p' h'⟩) (show bb + s' ≤ r by omega) hbotC
  -- 最後の語を木の単位で書く
  have hTraw : RawTs (u + reOff (fun _ => 0) f (S ++ A) o) (imgT A H1 G b1 u (us ++ [UT.ch P1])) :=
    RawTs_imgT hE hcu hP1T.1
  have eQ : farWt bb r ws ++ (fwH bb r (FTLt bb r u (Lds ++ [plugQ Q []])) u [] ++
        shiftr01 (Q.length + 2) 0 (V0 ++ P3))
      = farWt bb r (ws ++ [(Lds ++ [plugQ Q (imgT A H1 G b1 u (us ++ [UT.ch P1]))], u, [])]) := by
    rw [farWt_botT, hV0, hP3]
    have := chT_imgT_ch (A := A) H1 G (b := bb) (r := r) (le_refl b1) hcu hub us P1
    rw [Nat.sub_self, mlift_zero] at this
    rw [this]
  have hW1R : ∀ us' ∈ Lds ++ [plugQ Q (imgT A H1 G b1 u (us ++ [UT.ch P1]))],
      RawTs (u + reOff (fun _ => 0) f (S ++ A) o) us' := by
    intro us' hus'
    rcases List.mem_append.mp hus' with hus' | hus'
    · exact hL.1 us' hus'
    · simp at hus'; subst hus'; exact RawTs_plugQ Q _ (hP.raw _ _ _ _ _ hQ) hTraw
  have hRn : RawWsAt (S ++ A) o f bb
      (ws ++ [(Lds ++ [plugQ Q (imgT A H1 G b1 u (us ++ [UT.ch P1]))], u, [])]) :=
    RawWsAt_snoc hR ⟨hub, hW1R, Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
  have hRw : ∀ w ∈ ws, (∀ us ∈ w.1, RawTs (w.2.1 + reOff (fun _ => 0) f (S ++ A) o) us) ∧
      Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) f (S ++ A) o) w.2.2 :=
    fun w hw => (hR w hw).2
  have e0 : ∀ c (K G' : ℕ → ℕ) (B : List ℕ), reliftX c K G' B ([] : TrioSeq) = [] := fun c K G' B => by
    unfold reliftX; exact slift_nil _
  have eP : ∀ (g' : ℕ → ℕ) b', bb ≤ b' →
      reliftX b' f g' (S ++ A) (mlift (farWt bb r ws ++ (fwH bb r (FTLt bb r u (Lds ++ [plugQ Q []])) u [] ++
        shiftr01 (Q.length + 2) 0 (V0 ++ P3))) bb (b' - bb))
      = farWt b' (b' + liftOff (addF f g') (S ++ A) o + 1) (relWst (S ++ A) f g' ws ++
          [(Lds.map (relTs (S ++ A) f g' u) ++
            [plugQ (mapQ (relTs (S ++ A) f g' u) Q) (imgT A H1 (addF G g') b1 u (us ++ [UT.ch P1]))], u, [])]) := by
    intro g' b' hb'
    have eI : relTs (S ++ A) f g' u (imgT A H1 G b1 u (us ++ [UT.ch P1]))
        = imgT A H1 (addF G g') b1 u (us ++ [UT.ch P1]) := by
      have := imgT_comp hE g' hcu le_rfl hP1T.1
      rwa [show imgT (S ++ A) f g' u u (imgT A H1 G b1 u (us ++ [UT.ch P1]))
          = relTs (S ++ A) f g' u (imgT A H1 G b1 u (us ++ [UT.ch P1])) by
        unfold imgT; rw [Nat.sub_self, mlTs_zero]] at this
    rw [eQ, hr, mlift_farWt_self hRn hb', reliftX_farWt_self hA b' g' (RawWsAt_mono hb' hRn),
      relWst_snoc, e0, List.map_append, List.map_singleton, relTs_plugQ, eI]
  refine hFP bb _ (d + (Q.length + 2)) hQF (by omega) hbotQQ (fun g' b' hb' => ?_)
    (fun g' b' hb' τ L h1τ hτ hL' hGL => ?_)
  · -- h1
    rw [eP g' b' hb']
    have hE' := EmbU_relift hE g'
    have hEs := EmbU_self hA1 ho hA f g'
    have := hP1T.2 (addF G g') S o (addF f g') hE' u hcu (Lds.map (relTs (S ++ A) f g' u))
      (GoodChtX_emb hL hEs) (mapQ (relTs (S ++ A) f g' u) Q) (hP.emb _ _ _ _ _ hQ _ _ _ _ hEs) b' (by omega)
      (relWst (S ++ A) f g' ws) (FarCAt_mono hb' (FarCAt_relift hC hRw g'))
      (RawWsAt_relWst (RawWsAt_mono hb' hR) g')
    exact this
  · -- h2
    rw [eP g' b' hb']
    obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
    have hτ1 : τ < reOff H1 (addF G g') A s1 := by
      have e1 : reOff f g' (S ++ A) s' = reOff (addF H1 G) g' A s' :=
        reOff_ins_low hSA hf g' hK hs2K
      rw [e1, hs', reOff_comp] at hτ
      exact hτ
    have hτK : τ ≤ reOff (fun _ => 0) (addF H1 (addF G g')) A k := by
      have := reOff_mono H1 (addF G g') A hsK
      rw [reOff_zero_comp] at this
      omega
    have hGL' : GC A (addF H1 (addF G g')) τ b' L :=
      GC_ins_low hSA hfG (fun s'' hs'' => le_trans hτK (hKG s'' hs'')) hGL
    have hY := h2' (addF G g') b' (by omega) τ L h1τ hτ1 hL' hGL'
    have hub' : u ≤ b' := by omega
    have hEs := EmbU_self hA1 ho hA f g'
    have hL3 := GoodChtX_lift (GoodChtX_emb hL hEs) hub'
    have hQ3 := hP.lift _ _ _ _ _ (hP.emb _ _ _ _ _ hQ _ _ _ _ hEs) b' hub'
    have hus3 : Gd P A k (addF H1 (addF G g')) b' (mlTs b1 (b' - b1) (relTs A H1 (addF G g') b1 us)) :=
      Gd_lift (Gd_emb hus (EmbU_self hA01 hk1 hAk H1 (addF G g'))) (show b1 ≤ b' by omega)
    have hE3 : EmbU A k (addF H1 (addF G g')) (fun _ => 0) S o (addF f g') :=
      EmbU_shift (EmbU_relift hE g')
    have := NXs_snoc_elim (hY.2.2 b' le_rfl _ hus3) le_rfl (fun _ => 0) S o (addF f g') hE3 b' le_rfl _
      hL3 _ hQ3 b' le_rfl (relWst (S ++ A) f g' ws) (FarCAt_mono hb' (FarCAt_relift hC hRw g'))
      (RawWsAt_relWst (RawWsAt_mono hb' hR) g')
    have eL3 : (Lds.map (relTs (S ++ A) f g' u)).map (mlTs u (b' - u)) ++
        [plugQ (mapQ (mlTs u (b' - u)) (mapQ (relTs (S ++ A) f g' u) Q)) []]
        = (Lds.map (relTs (S ++ A) f g' u) ++ [plugQ (mapQ (relTs (S ++ A) f g' u) Q) []]).map
            (mlTs u (b' - u)) := by
      simp [mlTs_plugQ, mlTs]
    have eus3 : mlTs b1 (b' - b1) (relTs A H1 (addF G g') b1 us)
        = mlTs u (b' - u) (imgT A H1 (addF G g') b1 u us) := by
      unfold imgT
      rw [← relTs_mlTs A H1 (addF G g') hub', mlTs_comp hcu hub',
        relTs_mlTs A H1 (addF G g') (show b1 ≤ b' by omega)]
    rw [imgT_zero, reliftX_zero, Nat.sub_self, mlift_zero, mapQ_length, mapQ_length, eL3,
      FTLt_rebase hub' le_rfl, fwH_nil_c _ _ _ b' u, eus3, chT_rebase hub' le_rfl] at this
    have eC := chT_imgT_ch (A := A) H1 (addF G g') (b := b')
      (r := b' + liftOff (addF f g') (S ++ A) o + 1) (le_refl b1) hcu hub' us P1
    rw [Nat.sub_self, mlift_zero] at eC
    rw [farWt_botT, eC, mapQ_length]
    have e5 : shiftr01 (d + (Q.length + 2) - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
        = shiftr01 (Q.length + 2) 0 (shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) := by
      rw [shiftr01_add0]; congr 1; omega
    rw [e5]
    simp only [List.append_assoc, shiftr01_append0] at this ⊢
    exact this

theorem FarP_RNs {Ps : PS} (hPs : PSOK Ps) (hD : HeC.PSDec Ps) {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (hAk : ∀ a ∈ A, a < k)
    {H : ℕ → ℕ} {s0 : ℕ} (hs2 : 2 ≤ s0) (hs : s0 ≤ liftOff H A k) :
    FarP (GC A) (fun H' => RNs Ps A k H') A H s0 := by
  intro b P d hP hd hbot h1 h2 g1 b1 hb1
  have hbotb : BotGe (mlift P b (b1 - b)) d (b1 + s0) := by
    have := BotGe_slift hbot (stair_step b (b1 - b))
    rw [← mlift_eq_slift, if_pos (by omega), show b + s0 + (b1 - b) = b1 + s0 by omega] at this
    exact this
  have eB1 : mlift (P ++ [((d, b + s0, 0) : ℕ × ℕ × ℕ)]) b (b1 - b)
      = mlift P b (b1 - b) ++ [((d, b1 + s0, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_bottom hbot, if_pos (by omega), show b + s0 + (b1 - b) = b1 + s0 by omega]
  rw [eB1, reliftX_snoc_bottom hd b1 hbotb H g1 A]
  obtain ⟨P1, hP1⟩ : ∃ P1, P1 = reliftX b1 H g1 A (mlift P b (b1 - b)) := ⟨_, rfl⟩
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = reOff H g1 A s0 := ⟨_, rfl⟩
  obtain ⟨H1, hH1⟩ : ∃ H1, H1 = addF H g1 := ⟨_, rfl⟩
  rw [← hP1, ← hs1, ← hH1]
  have hP1Fr : Fr P1 := by rw [hP1]; exact Fr_reliftX (Fr_mlift hP _ _) _ _ _ _
  have hbotP1 : BotGe P1 d (b1 + s1) := by
    have := BotGe_slift hbotb (reStair_stair b1 H g1 A)
    change BotGe (reliftX b1 H g1 A (mlift P b (b1 - b))) d _ at this
    rwa [reStair_base, ← hP1, ← hs1] at this
  have hP1ok : NXs Ps A k H1 b1 P1 := by
    have := RNs_okW (h1 g1 b1 hb1); rwa [← hP1, ← hH1] at this
  have hs1ge : s0 ≤ s1 := by rw [hs1]; unfold reOff; omega
  have hsK : s1 ≤ reOff (fun _ => 0) H1 A k := by
    rw [hs1, hH1, ← reOff_zero_comp H g1 A k]
    exact reOff_mono H g1 A (by rw [← liftOff_eq_reOff0]; exact hs)
  have h2' : ∀ (g2 : ℕ → ℕ) b', b1 ≤ b' → ∀ τ L, 1 ≤ τ → τ < reOff H1 g2 A s1 → Fr L →
      GC A (addF H1 g2) τ b' L →
      NXs Ps A k (addF H1 g2) b' (reliftX b' H1 g2 A (mlift P1 b1 (b' - b1)) ++
        shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) := by
    intro g2 b' hb' τ L h1τ hτ hL hGL
    have eH : addF H1 g2 = addF H (addF g1 g2) := by rw [hH1, addF_assoc]
    have hτ' : τ < reOff H (addF g1 g2) A s0 := by
      rw [← reOff_comp, ← hs1, ← hH1]; exact hτ
    rw [eH] at hGL ⊢
    have := RNs_okW (h2 (addF g1 g2) b' (by omega) τ L h1τ hτ' hL hGL)
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
    fun c' hc' us hus => ?_⟩
  have eM : mlift (P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)]) b1 (c' - b1)
      = mlift P1 b1 (c' - b1) ++ [((d, c' + s1, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_bottom hbotP1, if_pos (by omega), show b1 + s1 + (c' - b1) = c' + s1 by omega]
  rw [eM]
  refine FarP_RNs_core hPs hD hA01 hk1 hAk (Fr_mlift hP1Fr _ _) hd ?_ (by omega) hsK
    ((NXs_ax hPs hD hA01 hk1 H1).lift b1 P1 hP1Fr hP1ok c' hc') ?_ ?_ us hus
  · have := BotGe_slift hbotP1 (stair_step b1 (c' - b1))
    rw [← mlift_eq_slift, if_pos (by omega), show b1 + s1 + (c' - b1) = c' + s1 by omega] at this
    exact this
  · rw [← eM]; exact Hd_mlift hHd _ _
  · intro g2 b' hb' τ L h1τ hτ hL' hGL
    have := h2' g2 b' (by omega) τ L h1τ hτ hL' hGL
    have e := mlift_mlift P1 b1 (c' - b1) (b' - c')
    rw [show b1 + (c' - b1) = c' by omega, show c' - b1 + (b' - c') = b' - b1 by omega] at e
    rw [e]; exact this

/-- ★ RNs は錨の列 A・上限 k の文脈の族。 -/
theorem RNs_ctx {P : PS} (hP : PSOK P) (hD : HeC.PSDec P) {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (hAk : ∀ a ∈ A, a < k) :
    CtxP (GC A) A k (fun H => RNs P A k H) := fun H =>
  ⟨RNs_ax hP hD hA01 hk1 H, fun _ _ _ hH h => RNs_congr hH h, fun g _ _ _ h => RNs_lift h g,
    fun _ hs2 hs => FarP_RNs hP hD hA01 hk1 hAk hs2 hs⟩

/-- ★ 子の位置の塊に、子の級 GC A H τ の並びを持つ節点を置く。 -/
theorem RNs_node {P : PS} (hP : PSOK P) (hD : HeC.PSDec P) {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk1 : 1 ≤ k) (hAk : ∀ a ∈ A, a < k)
    {H : ℕ → ℕ} {u τ : ℕ} {X L : TrioSeq} (hX : Fr X)
    (h : RNs P A k H u X) (hL : GC A H τ u L) (hτ : τ ≤ liftOff H A k) :
    RNs P A k H u (X ++ ((1, u + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
  R_child (R := fun H => RNs P A k H) (RNs_ctx hP hD hA01 hk1 hAk) hAk hX h hL hτ

end HeF
end TRIO
