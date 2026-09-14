/-
HaE.lean: 錨つきの中身の遠い語の族（notes 追記546）の第 3 部: 状態の層を持つ文脈の族 RA。

    RA A0 k0 H b X := ∀ g b', b ≤ b' → okWA A0 k0 (addF H g) b' (reliftX b' H g A0 (mlift X b (b' - b)))

状態の取り替え（RA_congr）、再持ち上げ（RA_lift）、差し込み口の公理（RA_ax、GyI.RLC_ax の写しで okWA_ax の場を呼ぶ）。
-/
import HaD

namespace TRIO
namespace HaE

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD

/-! ## 状態の取り替え -/

theorem reOff_congrH {H H' : ℕ → ℕ} {A0 : List ℕ} (hH : ∀ a ∈ A0, H a = H' a) (m : ℕ) :
    reOff (fun _ => 0) H A0 m = reOff (fun _ => 0) H' A0 m := by
  unfold reOff
  rw [reStep_congr 0 m (fun _ _ => rfl) hH]

theorem reOff_congrF {H H' : ℕ → ℕ} {A0 : List ℕ} (hH : ∀ a ∈ A0, H a = H' a) (g : ℕ → ℕ)
    (m : ℕ) : reOff (fun _ => 0) (addF H g) A0 m = reOff (fun _ => 0) (addF H' g) A0 m :=
  reOff_congrH (fun a ha => by simp [addF, hH a ha]) m

theorem relWs_congr {H H' : ℕ → ℕ} {A0 : List ℕ} (hH : ∀ a ∈ A0, H a = H' a) (g : ℕ → ℕ)
    (ws : List (ℕ × TrioSeq)) : relWs A0 H g ws = relWs A0 H' g ws := by
  unfold relWs
  exact List.map_congr_left (fun w _ => by rw [reliftX_congr w.1 hH (fun _ _ => rfl) w.2])

theorem FarCA_congr {A0 : List ℕ} {k0 : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A0, H a = H' a) {b0 : ℕ}
    {ws : List (ℕ × TrioSeq)} (hC : FarCA A0 k0 H b0 ws) : FarCA A0 k0 H' b0 ws := by
  intro g S o f b hf hb hR hSA hA hA1 ho hK hKo
  have hHg : ∀ a ∈ A0, addF H g a = addF H' g a := fun a ha => by simp [addF, hH a ha]
  have hf' : ∀ a ∈ A0, f a = addF H g a := fun a ha => by rw [hHg a ha]; exact hf a ha
  have hR' : RawWsA A0 k0 H b ws := fun w hw => by
    have := hR w hw
    exact ⟨this.1, this.2.1, this.2.2.1, by rw [reOff_congrH hH]; exact this.2.2.2⟩
  have eK := reOff_congrF hH g k0
  have := hC g S o f b hf' hb hR' hSA hA hA1 ho (by rw [eK]; exact hK) (by rw [eK]; exact hKo)
  rwa [relWs_congr hH] at this

theorem okWA_congr {A0 : List ℕ} {k0 : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A0, H a = H' a) {u : ℕ}
    {X : TrioSeq} (h : okWA A0 k0 H u X) : okWA A0 k0 H' u X := by
  refine ⟨h.1, by rw [← reOff_congrH hH]; exact h.2.1, fun b0 ws hC => ?_⟩
  exact FarCA_congr hH (h.2.2 b0 ws (FarCA_congr (fun a ha => (hH a ha).symm) hC))

/-! ## 並びの再持ち上げ -/

theorem relWs_comp (A0 : List ℕ) (H g g' : ℕ → ℕ) (ws : List (ℕ × TrioSeq)) :
    relWs A0 (addF H g) g' (relWs A0 H g ws) = relWs A0 H (addF g g') ws := by
  simp [relWs, reliftX_comp]

theorem FarCA_relift {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b0 : ℕ} {ws : List (ℕ × TrioSeq)}
    (hC : FarCA A0 k0 H b0 ws)
    (hRw : ∀ w ∈ ws, Fr w.2 ∧ Hd w.2 ∧ LowC (w.1 + reOff (fun _ => 0) H A0 k0) w.2)
    (g2 : ℕ → ℕ) : FarCA A0 k0 (addF H g2) b0 (relWs A0 H g2 ws) := by
  intro g S o f b hf hb hR hSA hA hA1 ho hK hKo
  have eH : addF (addF H g2) g = addF H (addF g2 g) := by funext a; simp [addF]; omega
  rw [eH] at hf hK hKo
  have hR0 : RawWsA A0 k0 H b ws := fun w hw => by
    have h1 := hR (w.1, reliftX w.1 H g2 A0 w.2) (List.mem_map.mpr ⟨w, hw, rfl⟩)
    exact ⟨h1.1, (hRw w hw).1, (hRw w hw).2.1, (hRw w hw).2.2⟩
  have := hC (addF g2 g) S o f b hf hb hR0 hSA hA hA1 ho hK hKo
  rw [relWs_comp]
  exact this

/-! ## 状態の層を持つ族 -/

def RA (A0 : List ℕ) (k0 : ℕ) (H : ℕ → ℕ) (b : ℕ) (X : TrioSeq) : Prop :=
  ∀ g b', b ≤ b' → okWA A0 k0 (addF H g) b' (reliftX b' H g A0 (mlift X b (b' - b)))

theorem RA_lift {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ} {X : TrioSeq}
    (h : RA A0 k0 H b X) (g : ℕ → ℕ) : RA A0 k0 (addF H g) b (reliftX b H g A0 X) := by
  intro g' b' hb'
  rw [mlift_reliftX, show b + (b' - b) = b' by omega, reliftX_comp, addF_assoc]
  exact h (addF g g') b' hb'

theorem RA_congr {A0 : List ℕ} {k0 : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A0, H a = H' a) {b : ℕ}
    {X : TrioSeq} (h : RA A0 k0 H b X) : RA A0 k0 H' b X := by
  intro g b' hb'
  have e : reliftX b' H' g A0 (mlift X b (b' - b)) = reliftX b' H g A0 (mlift X b (b' - b)) :=
    reliftX_congr b' (fun a ha => (hH a ha).symm) (fun _ _ => rfl) _
  rw [e]
  exact okWA_congr (fun a ha => by simp [addF, hH a ha]) (h g b' hb')

theorem RA_nil (A0 : List ℕ) (k0 : ℕ) (H : ℕ → ℕ) (b : ℕ) : RA A0 k0 H b [] := by
  intro g b' _
  rw [mlift_nil]
  have e : reliftX b' H g A0 [] = [] := by unfold reliftX; exact slift_nil _
  rw [e]
  exact ⟨fun h => absurd rfl h, LowC_nil _, fun b0 => GTWA_nil A0 k0 _ b0 b'⟩

theorem RA_okWA {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ} {X : TrioSeq} (h : RA A0 k0 H b X) :
    okWA A0 k0 H b X := by
  have := h (fun _ => 0) b le_rfl
  rwa [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero] at this

/-- ★ 状態の層を持つ族の差し込み口の公理。 -/
theorem RA_ax {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0) (H : ℕ → ℕ) :
    SlotAx (RA A0 k0 H) where
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
    refine (okWA_ax hA01 hk1 (addF H g)).oper b' _ _
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
    have hfix : ∀ m, m ≤ j → reStair b' H g A0 m = m :=
      fun m hm => reStair_low b' H g _ (by omega)
    have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u := hj
    have eU : reliftX b' H g A0 (mlift U u (b' - u)) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]
        = slift (mlift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) (reStair b' H g A0) := by
      unfold reliftX; rw [mlift_snoc_low U _ hc, slift_snoc_fix _ _ hfix]
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _)]
    have eU2 : reliftX b' H g A0 (mlift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) u (b' - u))
        = reliftX b' H g A0 (mlift U u (b' - u)) ++ [((h, j, 0) : ℕ × ℕ × ℕ)] := by
      rw [eU]; rfl
    rw [eU2]
    refine (okWA_ax hA01 hk1 (addF H g)).orph b' _ _ h j
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
    have hfix : ∀ m, m ≤ b' + 1 → reStair b' H g A0 m = m :=
      fun m hm => reStair_tie b' H g hA01 hm
    have eU : reliftX b' H g A0 (mlift U u (b' - u)) ++ [((x, b' + 1, 0) : ℕ × ℕ × ℕ)]
        = reliftX b' H g A0 (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) := by
      rw [eT]; unfold reliftX; rw [slift_snoc_fix _ _ hfix]
    have hHU : Hd U := by
      intro hne
      have := hH (by simp)
      rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
    rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), ← eU]
    refine (okWA_ax hA01 hk1 (addF H g)).tie b' _ _ x
      (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _) (by rw [eU]; exact Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
      (by rw [eU]; exact Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) ?_ (fun b'' hb'' Z hZ hbZ => ?_)
    · rw [eU, reliftX_length, mlift_length]
      unfold reliftX
      rw [coneV_iff_amin, amin_slift (reStair_stair _ _ _ _) (by simp)]
      have h0 : coneV (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) (u + (b' - u))
          U.length := coneV_mlift (by simp) hc (b' - u)
      rw [show u + (b' - u) = b' by omega, coneV_iff_amin] at h0
      have h1 := (reStair_stair b' H g A0).ge
        (amin (mlift (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u (b' - u)) U.length)
      omega
    · have h1 := hload b'' (le_trans hb' hb'') Z hZ hbZ g b'' le_rfl
      rw [Nat.sub_self, mlift_zero] at h1
      have e1 : reliftX b'' H g A0 (mlift (W ++ U) u (b'' - u) ++ shiftr01 x 0 Z)
          = reliftX b'' H g A0 (mlift (W ++ U) u (b'' - u)) ++ shiftr01 x 0 Z := by
        unfold reliftX
        exact slift_append_low (low_of_Wg hZ x le_rfl) (fun m hm => reStair_low b'' H g _ hm)
      have e2 : reliftX b'' H g A0 (mlift (W ++ U) u (b'' - u))
          = mlift (reliftX b' H g A0 (mlift W u (b' - u)) ++
              reliftX b' H g A0 (mlift U u (b' - u))) b' (b'' - b') := by
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
    have e : reliftX b' H g A0 (mlift W u (b' - u) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
        = reliftX b' H g A0 (mlift W u (b' - u)) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
      unfold reliftX
      refine slift_snoc_fix _ _ (fun m hm => ?_)
      have hm0 : m = 0 := by simpa using hm
      subst hm0; exact (reStair_stair _ _ _ _).zero
    rw [e]
    exact (okWA_ax hA01 hk1 (addF H g)).flat b' _ (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
      (h g b' hb')

end HaE
end TRIO
