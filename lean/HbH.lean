/-
HbH.lean: F のタイの本数つきの錨つきの中身の遠い語の族の第 3 部: 状態の層を持つ文脈の族 RAn（HaE・HaF・HaY の写し）。

    RAn A0 k0 H n b X := ∀ g b', b ≤ b' → okWAn A0 k0 (addF H g) n b' (reliftX b' H g A0 (mlift X b (b' - b)))

RAn は錨の列 A0・上限 k0 の文脈の族（CtxP）。空の中身（RAn_nil）だけは本数 n の空の語の規則を仮定に取る。
-/
import HaF
import HbG

namespace TRIO
namespace HbH

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF HbD HbE HbF HbG

/-! ## 状態の取り替えと再持ち上げ -/

theorem FarCAn_congr {A0 : List ℕ} {k0 : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A0, H a = H' a) {b0 : ℕ}
    {ws : List (ℕ × ℕ × TrioSeq)} (hC : FarCAn A0 k0 H b0 ws) : FarCAn A0 k0 H' b0 ws := by
  intro g S o f b hf hb hR hSA hA hA1 ho hK hKo
  have hHg : ∀ a ∈ A0, addF H g a = addF H' g a := fun a ha => by simp [addF, hH a ha]
  have hf' : ∀ a ∈ A0, f a = addF H g a := fun a ha => by rw [hHg a ha]; exact hf a ha
  have hR' : RawWsAn A0 k0 H b ws := fun w hw => by
    have := hR w hw
    exact ⟨this.1, this.2.1, this.2.2.1, by rw [reOff_congrH hH]; exact this.2.2.2⟩
  have eK := reOff_congrF hH g k0
  have := hC g S o f b hf' hb hR' hSA hA hA1 ho (by rw [eK]; exact hK) (by rw [eK]; exact hKo)
  rwa [relWsn_congr hH] at this

theorem okWAn_congr {A0 : List ℕ} {k0 : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A0, H a = H' a) {n u : ℕ}
    {X : TrioSeq} (h : okWAn A0 k0 H n u X) : okWAn A0 k0 H' n u X := by
  refine ⟨h.1, by rw [← reOff_congrH hH]; exact h.2.1, fun b0 ws hC => ?_⟩
  exact FarCAn_congr hH (h.2.2 b0 ws (FarCAn_congr (fun a ha => (hH a ha).symm) hC))

theorem FarCAn_relift {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b0 : ℕ} {ws : List (ℕ × ℕ × TrioSeq)}
    (hC : FarCAn A0 k0 H b0 ws)
    (hRw : ∀ w ∈ ws, Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) H A0 k0) w.2.2)
    (g2 : ℕ → ℕ) : FarCAn A0 k0 (addF H g2) b0 (relWsn A0 H g2 ws) := by
  intro g S o f b hf hb hR hSA hA hA1 ho hK hKo
  have eH : addF (addF H g2) g = addF H (addF g2 g) := by funext a; simp [addF]; omega
  rw [eH] at hf hK hKo
  have hR0 : RawWsAn A0 k0 H b ws := fun w hw => by
    have h1 := hR (w.1, w.2.1, reliftX w.2.1 H g2 A0 w.2.2) (List.mem_map.mpr ⟨w, hw, rfl⟩)
    exact ⟨h1.1, (hRw w hw).1, (hRw w hw).2.1, (hRw w hw).2.2⟩
  have := hC (addF g2 g) S o f b hf hb hR0 hSA hA hA1 ho hK hKo
  rw [relWsn_comp]
  exact this

/-! ## 状態の層を持つ族 -/

def RAn (A0 : List ℕ) (k0 : ℕ) (H : ℕ → ℕ) (n b : ℕ) (X : TrioSeq) : Prop :=
  ∀ g b', b ≤ b' → okWAn A0 k0 (addF H g) n b' (reliftX b' H g A0 (mlift X b (b' - b)))

theorem RAn_lift {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {n b : ℕ} {X : TrioSeq}
    (h : RAn A0 k0 H n b X) (g : ℕ → ℕ) : RAn A0 k0 (addF H g) n b (reliftX b H g A0 X) := by
  intro g' b' hb'
  rw [mlift_reliftX, show b + (b' - b) = b' by omega, reliftX_comp, addF_assoc]
  exact h (addF g g') b' hb'

theorem RAn_congr {A0 : List ℕ} {k0 : ℕ} {H H' : ℕ → ℕ} (hH : ∀ a ∈ A0, H a = H' a) {n b : ℕ}
    {X : TrioSeq} (h : RAn A0 k0 H n b X) : RAn A0 k0 H' n b X := by
  intro g b' hb'
  have e : reliftX b' H' g A0 (mlift X b (b' - b)) = reliftX b' H g A0 (mlift X b (b' - b)) :=
    reliftX_congr b' (fun a ha => (hH a ha).symm) (fun _ _ => rfl) _
  rw [e]
  exact okWAn_congr (fun a ha => by simp [addF, hH a ha]) (h g b' hb')

theorem RAn_nil {A0 : List ℕ} {k0 : ℕ} {n : ℕ}
    (hnil : ∀ (H' : ℕ → ℕ) (b0 c0 : ℕ), GTWAn A0 k0 H' b0 n c0 []) (H : ℕ → ℕ) (b : ℕ) :
    RAn A0 k0 H n b [] := by
  intro g b' _
  rw [mlift_nil]
  have e : reliftX b' H g A0 [] = [] := by unfold reliftX; exact slift_nil _
  rw [e]
  exact ⟨fun h => absurd rfl h, LowC_nil _, fun b0 => hnil _ b0 b'⟩

theorem RAn_okWA {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {n b : ℕ} {X : TrioSeq}
    (h : RAn A0 k0 H n b X) : okWAn A0 k0 H n b X := by
  have := h (fun _ => 0) b le_rfl
  rwa [addF_zero, Nat.sub_self, mlift_zero, reliftX_zero] at this

/-- ★ 状態の層を持つ族の差し込み口の公理。 -/
theorem RAn_ax {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0) (H : ℕ → ℕ)
    (n : ℕ) : SlotAx (RAn A0 k0 H n) where
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
    refine (okWAn_ax hA01 hk1 (addF H g) n).oper b' _ _
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
    refine (okWAn_ax hA01 hk1 (addF H g) n).orph b' _ _ h j
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
    refine (okWAn_ax hA01 hk1 (addF H g) n).tie b' _ _ x
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
    exact (okWAn_ax hA01 hk1 (addF H g) n).flat b' _ (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
      (h g b' hb')

/-! ## FarP の場 -/

theorem BotGe_FT {M : TrioSeq} {d v r : ℕ} (hvr : v ≤ r) (hbot : BotGe M d v) :
    ∀ n, BotGe (FT r n ++ M) d v := by
  have key : ∀ n, BotGe (List.replicate n ((1, r, 0) : ℕ × ℕ × ℕ) ++ M) d v := by
    intro n
    induction n with
    | zero => simpa using hbot
    | succ n ih =>
        rw [List.replicate_succ, List.cons_append]
        exact BotGe_cons hvr ih
  intro n
  rw [FT, List.cons_append]
  exact BotGe_cons hvr (key n)

theorem FarP_RAn {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) {H : ℕ → ℕ} {n s : ℕ}
    (hs2 : 2 ≤ s) (hs : s ≤ liftOff H A0 k0) : FarP (GC A0) (fun H' => RAn A0 k0 H' n) A0 H s := by
  intro b P d hP hd hbot h1 h2 g1 b1 hb1
  have hbotb : BotGe (mlift P b (b1 - b)) d (b1 + s) := by
    have := BotGe_slift hbot (stair_step b (b1 - b))
    rw [← mlift_eq_slift, if_pos (by omega), show b + s + (b1 - b) = b1 + s by omega] at this
    exact this
  have eB1 : mlift (P ++ [((d, b + s, 0) : ℕ × ℕ × ℕ)]) b (b1 - b)
      = mlift P b (b1 - b) ++ [((d, b1 + s, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_bottom hbot, if_pos (by omega), show b + s + (b1 - b) = b1 + s by omega]
  rw [eB1, reliftX_snoc_bottom hd b1 hbotb H g1 A0]
  obtain ⟨P1, hP1⟩ : ∃ P1, P1 = reliftX b1 H g1 A0 (mlift P b (b1 - b)) := ⟨_, rfl⟩
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = reOff H g1 A0 s := ⟨_, rfl⟩
  obtain ⟨H1, hH1⟩ : ∃ H1, H1 = addF H g1 := ⟨_, rfl⟩
  rw [← hP1, ← hs1, ← hH1]
  have hP1Fr : Fr P1 := by rw [hP1]; exact Fr_reliftX (Fr_mlift hP _ _) _ _ _ _
  have hbotP1 : BotGe P1 d (b1 + s1) := by
    have := BotGe_slift hbotb (reStair_stair b1 H g1 A0)
    change BotGe (reliftX b1 H g1 A0 (mlift P b (b1 - b))) d _ at this
    rwa [reStair_base, ← hP1, ← hs1] at this
  have hP1ok : okWAn A0 k0 H1 n b1 P1 := by
    have := RAn_okWA (h1 g1 b1 hb1); rwa [← hP1, ← hH1] at this
  have hs1ge : s ≤ s1 := by rw [hs1]; unfold reOff; omega
  have hsK : s1 ≤ reOff (fun _ => 0) H1 A0 k0 := by
    rw [hs1, hH1, ← reOff_zero_comp H g1 A0 k0]
    exact reOff_mono H g1 A0 (by rw [← liftOff_eq_reOff0]; exact hs)
  have h2' : ∀ (g2 : ℕ → ℕ) b', b1 ≤ b' → ∀ τ L, 1 ≤ τ → τ < reOff H1 g2 A0 s1 → Fr L →
      GC A0 (addF H1 g2) τ b' L →
      okWAn A0 k0 (addF H1 g2) n b' (reliftX b' H1 g2 A0 (mlift P1 b1 (b' - b1)) ++
        shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) := by
    intro g2 b' hb' τ L h1τ hτ hL hGL
    have eH : addF H1 g2 = addF H (addF g1 g2) := by rw [hH1, addF_assoc]
    have hτ' : τ < reOff H (addF g1 g2) A0 s := by
      rw [← reOff_comp, ← hs1, ← hH1]; exact hτ
    rw [eH] at hGL ⊢
    have := RAn_okWA (h2 (addF g1 g2) b' (by omega) τ L h1τ hτ' hL hGL)
    have eP : reliftX b' H1 g2 A0 (mlift P1 b1 (b' - b1))
        = reliftX b' H (addF g1 g2) A0 (mlift P b (b' - b)) := by
      rw [hP1, mlift_reliftX, show b1 + (b' - b1) = b' by omega, hH1, reliftX_comp]
      have e := mlift_mlift P b (b1 - b) (b' - b1)
      rw [show b + (b1 - b) = b1 by omega, show b1 - b + (b' - b1) = b' - b by omega] at e
      rw [e]
    rw [eP]; exact this
  refine ⟨?_, LowC_snoc hP1ok.2.1 _ (by show b1 + s1 ≤ b1 + reOff (fun _ => 0) H1 A0 k0; omega),
    fun b0 ws hC g S o f bb hf hb hR hSA hA hA1 ho hK hKo => ?_⟩
  · -- 先頭
    have hGC1 : GC A0 (addF H1 (fun _ => 0)) 1 b1 [] := by
      unfold GC; rw [lowP_one hA01]; simpa [sumOn] using GpT_nil1 (addF H1 (fun _ => 0)) b1
    have hH := (h2' (fun _ => 0) b1 le_rfl 1 [] le_rfl
      (by unfold reOff; rw [reStep_zeroG]; omega) Fr_nil hGC1).1
    rw [Nat.sub_self, mlift_zero, reliftX_zero] at hH
    intro _
    have h0 := hH (by simp [shiftr01])
    rcases P1 with _ | ⟨x, P1⟩
    · simp [shiftr01, entry] at h0 ⊢; omega
    · exact h0
  · -- 遠い語の中
    have hw : RawWAn A0 k0 H1 bb (n, b1, P1 ++ [((d, b1 + s1, 0) : ℕ × ℕ × ℕ)]) :=
      hR _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hR0 : RawWsAn A0 k0 H1 bb ws := fun w' h' => hR w' (List.mem_append_left _ h')
    have hb1bb : b1 ≤ bb := hw.1
    have hbotP3 : BotGe (reliftX b1 H1 g A0 P1) d (b1 + reOff H1 g A0 s1) := by
      have := BotGe_slift hbotP1 (reStair_stair b1 H1 g A0)
      change BotGe (reliftX b1 H1 g A0 P1) d _ at this
      rwa [reStair_base] at this
    have hs2ge : s1 ≤ reOff H1 g A0 s1 := by unfold reOff; omega
    have hs2K : reOff H1 g A0 s1 ≤ reOff (fun _ => 0) (addF H1 g) A0 k0 := by
      rw [← reOff_zero_comp H1 g A0 k0]; exact reOff_mono H1 g A0 hsK
    simp only [relWsn_snoc, farWn_snoc]
    rw [reliftX_snoc_bottom hd b1 hbotP1 H1 g A0]
    have hbotP3u : BotGe (mlift (reliftX b1 H1 g A0 P1) b1 (bb - b1)) d (bb + reOff H1 g A0 s1) := by
      have := BotGe_slift hbotP3 (stair_step b1 (bb - b1))
      rw [← mlift_eq_slift] at this
      rwa [if_pos (by omega), show b1 + reOff H1 g A0 s1 + (bb - b1) = bb + reOff H1 g A0 s1 by omega]
        at this
    have eL : mlift (reliftX b1 H1 g A0 P1 ++ [((d, b1 + reOff H1 g A0 s1, 0) : ℕ × ℕ × ℕ)]) b1 (bb - b1)
        = mlift (reliftX b1 H1 g A0 P1) b1 (bb - b1) ++
          [((d, bb + reOff H1 g A0 s1, 0) : ℕ × ℕ × ℕ)] := by
      rw [mlift_snoc_cone _ _ (coneV_of_BotGe hbotP3 (by omega))]
      show _ ++ [((d, b1 + reOff H1 g A0 s1 + (bb - b1), 0) : ℕ × ℕ × ℕ)] = _
      rw [show b1 + reOff H1 g A0 s1 + (bb - b1) = bb + reOff H1 g A0 s1 by omega]
    obtain ⟨r, hr⟩ : ∃ r, r = bb + liftOff f (S ++ A0) o + 1 := ⟨_, rfl⟩
    rw [← hr]
    have eF : fwWn bb r n b1 (reliftX b1 H1 g A0 P1 ++ [((d, b1 + reOff H1 g A0 s1, 0) : ℕ × ℕ × ℕ)])
        = fwWn bb r n b1 (reliftX b1 H1 g A0 P1) ++
          [((d + 1, bb + reOff H1 g A0 s1, 0) : ℕ × ℕ × ℕ)] := by
      unfold fwWn; rw [eL]; simp [shiftr01]
    rw [eF, ← List.append_assoc]
    have hso : reOff H1 g A0 s1 ≤ liftOff f (S ++ A0) o := le_trans hs2K hKo
    have hFP := FarP_GpT_ge hA hA1 ho (f := f) (show 2 ≤ reOff H1 g A0 s1 by omega) hso
    have hQF : Fr (farWn bb r (relWsn A0 H1 g ws) ++ fwWn bb r n b1 (reliftX b1 H1 g A0 P1)) :=
      Fr_append (Fr_farWn _ _ _) (Fr_fwWn _ _ _ _ _)
    have hRP : ∀ b', bb ≤ b' → RawWsAn A0 k0 H1 b' (ws ++ [(n, b1, P1)]) := fun b' hb' =>
      RawWsAn_snoc (RawWsAn_mono hb' hR0) ⟨show b1 ≤ b' by omega, hP1Fr, hP1ok.1, hP1ok.2.1⟩
    have hC1 : FarCAn A0 k0 H1 b0 (ws ++ [(n, b1, P1)]) := hP1ok.2.2 b0 ws hC
    have eP : ∀ b', bb ≤ b' →
        mlift (farWn bb r (relWsn A0 H1 g ws) ++ fwWn bb r n b1 (reliftX b1 H1 g A0 P1)) bb (b' - bb)
          = farWn b' (b' + liftOff f (S ++ A0) o + 1) (relWsn A0 H1 g (ws ++ [(n, b1, P1)])) := by
      intro b' hb'
      have hRk := RawWskn_relWsn (hRP bb le_rfl) g
      rw [relWsn_snoc] at hRk
      have := mlift_farWn_basek (show bb < r by omega) (b' - bb) _ hRk
      rw [farWn_snoc] at this
      rw [show bb + (b' - bb) = b' by omega,
        show r + (b' - bb) = b' + liftOff f (S ++ A0) o + 1 by omega] at this
      rw [relWsn_snoc]
      exact this
    refine hFP bb _ (d + 1) hQF (by omega) ?_ (fun g' b' hb' => ?_)
      (fun g' b' hb' τ L h1τ hτ hL hGL => ?_)
    · unfold fwWn
      exact BotGe_node (Fr_farWn _ _ _) (by omega) (BotGe_FT (by omega) hbotP3u n)
    · -- h1
      obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
      rw [eP b' hb', reliftX_farWnA hA hSA b' hf g' hK _ (hRP b' hb')]
      exact hC1 (addF g g') S o (addF f g') b' hfG (by omega) (hRP b' hb') hSA hA hA1 ho hKG hKoG
    · -- h2
      obtain ⟨hfG, hKG, hKoG⟩ := FarCA_conds_lift hSA hA hf hK hKo g'
      rw [eP b' hb', reliftX_farWnA hA hSA b' hf g' hK _ (hRP b' hb'), relWsn_snoc]
      have hτ1 : τ < reOff H1 (addF g g') A0 s1 := by
        have e1 : reOff f g' (S ++ A0) (reOff H1 g A0 s1)
            = reOff (addF H1 g) g' A0 (reOff H1 g A0 s1) :=
          reOff_ins_low hSA hf g' hK hs2K
        rw [e1, reOff_comp] at hτ
        exact hτ
      have hτK : τ ≤ reOff (fun _ => 0) (addF H1 (addF g g')) A0 k0 := by
        have := reOff_mono H1 (addF g g') A0 hsK
        rw [reOff_zero_comp] at this
        omega
      have hGL' : GC A0 (addF H1 (addF g g')) τ b' L :=
        GC_ins_low hSA hfG (fun s' hs' => le_trans hτK (hKG s' hs')) hGL
      have hY := h2' (addF g g') b' (by omega) τ L h1τ hτ1 hL hGL'
      have hRw : ∀ w ∈ ws, Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) H1 A0 k0) w.2.2 :=
        fun w hw => (hR0 w hw).2
      have hC3 := FarCAn_relift hC hRw (addF g g')
      have hFrY : Fr (reliftX b' H1 (addF g g') A0 (mlift P1 b1 (b' - b1)) ++
          shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) :=
        Fr_append (Fr_reliftX (Fr_mlift hP1Fr _ _) _ _ _ _) (Fr_shift_node _ _ _)
      have hR3 := RawWsAn_snoc (RawWsAn_relWsn (RawWsAn_mono (show bb ≤ b' by omega) hR0) (addF g g'))
        (show RawWAn A0 k0 (addF H1 (addF g g')) b' (n, b', reliftX b' H1 (addF g g') A0
          (mlift P1 b1 (b' - b1)) ++ shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 L)) from ⟨le_rfl, hFrY, hY.1, hY.2.1⟩)
      have e0 : ∀ a ∈ A0, addF f g' a = addF (addF H1 (addF g g')) (fun _ => 0) a := fun a ha => by
        rw [addF_zero]; exact hfG a ha
      have := hY.2.2 b0 _ hC3 (fun _ => 0) S o (addF f g') b' e0 (by omega) hR3 hSA hA hA1 ho
        (by rw [addF_zero]; exact hKG) (by rw [addF_zero]; exact hKoG)
      rw [relWsn_zero, farWn_snoc] at this
      dsimp only at this
      have eY : fwWn b' (b' + liftOff (addF f g') (S ++ A0) o + 1) n b'
            (reliftX b' H1 (addF g g') A0 (mlift P1 b1 (b' - b1)) ++
              shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L))
          = fwWn b' (b' + liftOff (addF f g') (S ++ A0) o + 1) n b1 (reliftX b1 H1 (addF g g') A0 P1) ++
            shiftr01 d 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
        unfold fwWn
        rw [Nat.sub_self, mlift_zero, mlift_reliftX, show b1 + (b' - b1) = b' by omega,
          show shiftr01 d 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)
            = shiftr01 1 0 (shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L)) by
            rw [GzF.shift_shift, show d - 1 + 1 = d by omega]]
        simp only [shiftr01_append0, List.cons_append, List.append_assoc]
      rw [eY] at this
      rw [farWn_snoc, List.append_assoc, show d + 1 - 1 = d by omega]
      exact this

/-- ★ RAn は錨の列 A0・上限 k0 の文脈の族。 -/
theorem RAn_ctx {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0) (n : ℕ) :
    CtxP (GC A0) A0 k0 (fun H => RAn A0 k0 H n) := fun H =>
  ⟨RAn_ax hA01 hk1 H n, fun _ _ _ hH h => RAn_congr hH h, fun g _ _ _ h => RAn_lift h g,
    fun _ hs2 hs => FarP_RAn hA01 hs2 hs⟩

/-- ★ 本数 n の語の錨つきの中身に、子の級 GC A0 H τ の並びを持つ節点を置く。 -/
theorem RAn_node {A0 : List ℕ} {k0 : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (hk1 : 1 ≤ k0)
    (hAk : ∀ a ∈ A0, a < k0) {n : ℕ} {H : ℕ → ℕ} {u τ : ℕ} {X L : TrioSeq} (hX : Fr X)
    (h : RAn A0 k0 H n u X) (hL : GC A0 H τ u L) (hτ : τ ≤ liftOff H A0 k0) :
    RAn A0 k0 H n u (X ++ ((1, u + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
  R_child (R := fun H => RAn A0 k0 H n) (RAn_ctx hA01 hk1 n) hAk hX h hL hτ

end HbH
end TRIO
