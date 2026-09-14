/-
HdH.lean: 木の単位の F のタイの子の F の位置のタイの規則 GoodLowT_none と、生成器の部品。

- GoodLowT_none: GoodLowT c us → GoodLowT c (us ++ [UT.tie 0 []])。F の位置のタイ (3, r, 0) は FarP_GpT_lt
  （s = liftOff + 1）。h1 は us の語、h2 の子の節点は埋め込み先の族で HcO.RNt_node と NXt を使って置く。
- 低い塊の族 ChLowT c X := LowC (c+1) X ∧ ∀ 族, NXt（HcN.NXt_ax から差し込み口の公理）。GoodLowT_some。
- 生成器: okLow（塊）、okRAt（中身）、OkWsAt、FarCAt_of_OkWsAt、PVF_farWAt。
-/
import HaG
import HdG

namespace TRIO
namespace HdH

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcE HcF HcI HcM HdA HdB HdC HdD HdE HdF HdG

/-! ## 最後の語の形 -/

theorem farWt_lastE {A : List ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (H g : ℕ → ℕ) {b r c' : ℕ}
    (ws : List (List (List UT) × ℕ × TrioSeq))
    (Lds : List (List UT)) {us : List UT} (hus : RawTs (c' + 1) us) :
    farWt b r (ws ++ [((Lds ++ [us]).map (relTs A H g c'), c', [])])
      = farWt b r ws ++ fwH b r (FTLt b r c' (Lds.map (relTs A H g c'))) b
          (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r c' us)) := by
  rw [farWt_snoc]
  dsimp only
  rw [List.map_append, List.map_singleton, mapt_tie_inv hA01 hus H g, FTLt_snoc]
  simp only [fwH, mlift_nil, Nat.sub_self, mlift_zero, List.append_nil]

theorem farWt_lastN {A : List ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (H g : ℕ → ℕ) {b r c' : ℕ}
    (ws : List (List (List UT) × ℕ × TrioSeq))
    (Lds : List (List UT)) {us : List UT} (hus : RawTs (c' + 1) us) :
    farWt b r (ws ++ [((Lds ++ [us ++ [(UT.tie 0 [])]]).map
        (relTs A H g c'),
        c', [])])
      = (farWt b r ws ++ fwH b r (FTLt b r c' (Lds.map (relTs A H g c'))) b
          (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r c' us))) ++ [((3, r, 0) : ℕ × ℕ × ℕ)] := by
  have hus' : RawTs (c' + 1) (us ++ [UT.tie 0 []]) := RawTs_snoc.mpr ⟨hus, by simp [RawT, RawTs]⟩
  rw [farWt_lastE hA01 H g ws Lds hus', chT_snoc]
  simp [fwH, unitT, chT, shiftr01, mlift_nil, mlift_zero]

theorem fwH_child_app1 (b r : ℕ) (H0 C N : TrioSeq) :
    fwH b r H0 b (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (C ++ N))
      = fwH b r H0 b (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 C) ++ shiftr01 2 0 N := by
  unfold fwH
  simp only [Nat.sub_self, mlift_zero]
  have e : shiftr01 1 0 (shiftr01 1 0 N) = shiftr01 2 0 N := by rw [GzF.shift_shift]
  rw [← e]
  simp only [shiftr01, List.map_append, List.map_cons, List.cons_append, List.append_assoc]

/-! ## F の位置のタイ -/

/-- ★ F のタイの子の並びの最後に F の位置のタイを足す規則。 -/
theorem GoodLowT_none {c : ℕ} {us : List UT} (h : GoodLowT c us) :
    GoodLowT c (us ++ [UT.tie 0 []]) := by
  have hraw : RawTs (c + 1) (us ++ [UT.tie 0 []]) := RawTs_snoc.mpr ⟨h.1, by simp [RawT, RawTs]⟩
  refine ⟨hraw, fun A k hA01 hk hAk H u hcu Lds hL => ?_⟩
  have e1 : mlTs c (u - c) (us ++ [UT.tie 0 []]) = mlTs c (u - c) us ++ [UT.tie 0 []] := by
    rw [mlTs_append]; simp [mlTs, mlT]
  rw [e1]
  obtain ⟨us', hus'def⟩ : ∃ us', us' = mlTs c (u - c) us := ⟨_, rfl⟩
  rw [← hus'def]
  have hus' : GoodLowT u us' := by rw [hus'def]; exact GoodLowT_lift h hcu
  have hG1 : GoodChtX A k H u (Lds ++ [us']) := by
    rw [hus'def]; exact h.2 A k hA01 hk hAk H u hcu Lds hL
  have hKge : k ≤ reOff (fun _ => 0) H A k := by unfold reOff; omega
  have hW1R : ∀ us2 ∈ Lds ++ [us'], RawTs (u + reOff (fun _ => 0) H A k) us2 := by
    intro us2 hus2
    rcases List.mem_append.mp hus2 with hus2 | hus2
    · exact hL.1 us2 hus2
    · rw [List.mem_singleton] at hus2; rw [hus2]
      exact RawTs_mono' (by omega) hus'.1
  have hraw2 : ∀ us2 ∈ Lds ++ [us' ++ [(UT.tie 0 [])]],
      RawTs (u + reOff (fun _ => 0) H A k) us2 := by
    intro us2 hus2
    rcases List.mem_append.mp hus2 with hus2 | hus2
    · exact hL.1 us2 hus2
    · rw [List.mem_singleton] at hus2; rw [hus2]
      exact RawTs_snoc.mpr ⟨RawTs_mono' (by omega) hus'.1, by simp [RawT, RawTs]⟩
  refine ⟨hraw2, fun g S o f b hE hub ws hC hR => ?_⟩
  have hA := hE.2.2.1
  have hA1 := hE.2.2.2.1
  have ho := hE.2.2.2.2.1
  have e0 : ∀ c (K G : ℕ → ℕ) (B : List ℕ), reliftX c K G B ([] : TrioSeq) = [] := fun c K G B => by
    unfold reliftX; exact slift_nil _
  rw [farWt_lastN hA01 H g ws Lds hus'.1]
  obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f (S ++ A) o + 1 := ⟨_, rfl⟩
  rw [← hr]
  have hRn : RawWsAt (S ++ A) o f b
      (ws ++ [((Lds ++ [us']).map (relTs A H g u), u, [])]) :=
    RawWsAt_snoc hR ⟨hub, RawLdt_emb hE hW1R, Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
  have eP0 : farWt b r ws ++ fwH b r (FTLt b r u (Lds.map (relTs A H g u))) b
        (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r u us'))
      = farWt b r (ws ++ [((Lds ++ [us']).map (relTs A H g u), u, [])]) := by
    rw [farWt_lastE hA01 H g ws Lds hus'.1]
  have eR : ∀ (g' : ℕ → ℕ) b', b ≤ b' →
      reliftX b' f g' (S ++ A) (mlift (farWt b r ws ++ fwH b r (FTLt b r u
        (Lds.map (relTs A H g u))) b
        (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r u us'))) b (b' - b))
      = farWt b' (b' + liftOff (addF f g') (S ++ A) o + 1)
          (relWst (S ++ A) f g' ws ++
            [((Lds ++ [us']).map (relTs A H (addF g g') u), u, [])]) := by
    intro g' b' hb'
    rw [eP0, hr, mlift_farWt_self hRn hb', reliftX_farWt_self hA b' g' (RawWsAt_mono hb' hRn),
      relWst_snoc, e0, EmbU_relLdt hE u g' hW1R]
  have hFP := FarP_GpT_lt (A := S ++ A) (o := o) hA ho (f := f) (s := liftOff f (S ++ A) o + 1)
    (by omega)
  have hP : Fr (farWt b r ws ++ fwH b r (FTLt b r u
      (Lds.map (relTs A H g u))) b
      (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r u us'))) :=
    Fr_append (Fr_farWt _ _ _) (Fr_fwH _ _ _ _ _)
  have hbot : BotGe (farWt b r ws ++ fwH b r (FTLt b r u
      (Lds.map (relTs A H g u))) b
      (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r u us'))) 3 (b + (liftOff f (S ++ A) o + 1)) := by
    unfold fwH
    simp only [Nat.sub_self, mlift_zero]
    exact BotGe_node (Fr_farWt _ _ _) (by omega)
      (BotGe_node (Fr_FTLt _ _ _ _) (by omega) (BotGe_one (Fr_chT _ hus'.1) _))
  suffices hG2 : GpT (S ++ A) o f b ((farWt b r ws ++ fwH b r (FTLt b r u
      (Lds.map (relTs A H g u))) b
      (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r u us'))) ++
      [((3, b + (liftOff f (S ++ A) o + 1), 0) : ℕ × ℕ × ℕ)]) by
    rwa [show b + (liftOff f (S ++ A) o + 1) = r by omega] at hG2
  have hRw : ∀ w ∈ ws, (∀ us ∈ w.1, RawTs (w.2.1 + reOff (fun _ => 0) f (S ++ A) o) us) ∧
      Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) f (S ++ A) o) w.2.2 :=
    fun w hw => (hR w hw).2
  refine hFP b _ 3 hP (by omega) hbot (fun g' b' hb' => ?_)
    (fun g' b' hb' τ L h1τ hτ hL' hGL => ?_)
  · -- h1: us の語
    rw [eR g' b' hb']
    exact hG1.2 (addF g g') S o (addF f g') b' (EmbU_relift hE g') (by omega) _
      (FarCAt_mono hb' (FarCAt_relift hC hRw g')) (RawWsAt_relWst (RawWsAt_mono hb' hR) g')
  · -- h2: 埋め込み先の族で子の節点を置く
    rw [eR g' b' hb', farWt_lastE hA01 H (addF g g') _ Lds hus'.1]
    have hτo : τ ≤ liftOff (addF f g') (S ++ A) o := by
      have := reOff_above hA f g' 1
      rw [this] at hτ
      omega
    have hRN : RNt (S ++ A) o (addF f g') b' ([] ++ ((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) :=
      RNt_node hA1 ho hA Fr_nil (RNt_nil hA1 ho hA _ _) hGL hτo
    have hNX := RNt_okW hRN
    have hLA := GoodChtX_lift (GoodChtX_emb hL (EmbU_relift hE g')) (show u ≤ b' by omega)
    have husB := GoodLowT_lift hus' (show u ≤ b' by omega)
    have := NXt_snoc_elim (hNX.2.2 b' le_rfl _ husB _ hLA) hA1 husB.1 le_rfl (fun _ => 0) [] o
      (addF f g') b' (EmbU_triv hA hA1 ho _) le_rfl _ (FarCAt_mono hb' (FarCAt_relift hC hRw g'))
      (RawWsAt_relWst (RawWsAt_mono hb' hR) g')
    simp only [List.nil_append] at this
    rw [reliftX_zero, Nat.sub_self, mlift_zero, mapt_zero, FTLt_rebase (show u ≤ b' by omega) le_rfl,
      chT_rebase (show u ≤ b' by omega) le_rfl] at this
    rw [show 3 - 1 = 2 by rfl, List.append_assoc, ← fwH_child_app1]
    exact this

/-! ## 低い塊 -/

def ChLowT (c : ℕ) (X : TrioSeq) : Prop :=
  LowC (c + 1) X ∧ ∀ (A : List ℕ) (k : ℕ), (∀ a ∈ A, 1 ≤ a) → 1 ≤ k → (∀ a ∈ A, a < k) →
    ∀ H : ℕ → ℕ, NXt A k H c X

/-- ★ 低い塊の族の差し込み口の公理。 -/
theorem ChLowT_ax : SlotAx ChLowT where
  lift := by
    intro c W hW h c1 hc1
    exact ⟨LowC_v1_lift hc1 h.1, fun A k h1 h2 h3 H =>
      (NXt_ax h1 h2 H).lift c W hW (h.2 A k h1 h2 h3 H) c1 hc1⟩
  oper := by
    intro c W U hW hU hH hlen hp hIH
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    have hI1 := hIH 1 le_rfl
    have hU1 : U⟦1⟧ = U.dropLast := oper_one_eq_dropLast (by omega)
    have hLow : LowC (c + 1) (W ++ U) := by
      have hI1' := hI1.1
      rw [hU1] at hI1'
      obtain ⟨q, hq, -⟩ := hp
      have hqlt : q < U.length - 1 := nextR_index_lt hq
      have hrt := rtg_nextrel0_lift W U (rtg0_of_nextR' hq)
      have hsplit : W ++ U = (W ++ U.dropLast) ++ [U.getLast hUne] := by
        rw [List.append_assoc, List.dropLast_append_getLast hUne]
      rw [hsplit] at hrt ⊢
      have hlenD : (W ++ U.dropLast).length = W.length + (U.length - 1) := by
        rw [List.length_append, List.length_dropLast]
      rw [← hlenD] at hrt
      exact LowC_snoc_anc hI1' (by rw [hlenD]; omega) hrt
    exact ⟨hLow, fun A k h1 h2 h3 H =>
      (NXt_ax h1 h2 H).oper c W U hW hU hH hlen hp (fun m hm => (hIH m hm).2 A k h1 h2 h3 H)⟩
  orph := by
    intro c W U h j hW hU hH hj1 hj hnp hz
    have hz0 := hz [] (Wg_nil _) based_nil
    have e0 : W ++ (U ++ shiftr01 h 0 []) = W ++ U := by simp [shiftr01]
    rw [e0] at hz0
    refine ⟨?_, fun A k h1 h2 h3 H =>
      (NXt_ax h1 h2 H).orph c W U h j hW hU hH hj1 hj hnp (fun z hz' hbz => (hz z hz' hbz).2 A k h1 h2 h3 H)⟩
    rw [← List.append_assoc]
    exact LowC_snoc hz0.1 _ (by show j ≤ c + 1; omega)
  tie := by
    intro c W U x hW hU hH hc hload
    have h0 := hload c le_rfl [] (Wg_nil _) based_nil
    have e0 : mlift (W ++ U) c (c - c) ++ shiftr01 x 0 [] = W ++ U := by
      simp [shiftr01, mlift_zero]
    rw [e0] at h0
    refine ⟨?_, fun A k h1 h2 h3 H =>
      (NXt_ax h1 h2 H).tie c W U x hW hU hH hc
        (fun c'' hc'' Z hZ hbZ => (hload c'' hc'' Z hZ hbZ).2 A k h1 h2 h3 H)⟩
    rw [← List.append_assoc]
    exact LowC_snoc h0.1 _ (by show c + 1 ≤ c + 1; omega)
  flat := by
    intro c W hW h
    exact ⟨LowC_snoc h.1 _ (by show 0 ≤ c + 1; omega), fun A k h1 h2 h3 H =>
      (NXt_ax h1 h2 H).flat c W hW (h.2 A k h1 h2 h3 H)⟩

def okLow (c : ℕ) (X : TrioSeq) : Prop := Fr X ∧ ChLowT c X

theorem okLow_nil (c : ℕ) : okLow c [] :=
  ⟨Fr_nil, LowC_nil _, fun _ _ h1 h2 h3 H => NXt_nil h1 h2 h3 H c⟩

theorem okLow_load {c : ℕ} {X : TrioSeq} (h : okLow c X) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * c))
    (hb : based Z) : okLow c (X ++ shiftr01 1 0 Z) :=
  ⟨Fr_append h.1 (Fr_shift1 Z), slot_load ChLowT_ax h.1 h.2 Z hZ hb⟩

theorem okLow_tie {c : ℕ} {X : TrioSeq} (h : okLow c X) {E : TrioSeq} (hE : GF 1 c E) :
    okLow c (X ++ ((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 E) := by
  have := ((Gof_one_iff c E).mp hE.1) ChLowT ChLowT_ax c le_rfl X h.1 h.2
  rw [Nat.sub_self, mlift_zero] at this
  exact ⟨Fr_append h.1 (Fr_node _ _), this⟩

/-- ★ F のタイの子の並びの最後に低い塊を足す規則。 -/
theorem GoodLowT_some {c : ℕ} {us : List UT} (hus : GoodLowT c us) {X : TrioSeq}
    (hX : okLow c X) : GoodLowT c (us ++ [UT.ch X]) := by
  refine ⟨RawTs_snoc.mpr ⟨hus.1, RawT_ch hX.1 (hX.2.2 [] 1 (by simp) le_rfl (by simp) (fun _ => 0)).1 hX.2.1⟩,
    fun A k hA01 hk hAk H u hcu Lds hL => ?_⟩
  have := (hX.2.2 A k hA01 hk hAk H).2.2 u hcu _ (GoodLowT_lift hus hcu) Lds hL
  rw [mlTs_append]
  simp only [mlTs, mlT]
  exact this

/-- 子の並びに F のタイ（子の並び us）を足す。 -/
theorem GoodChtX_snocU {A0 : List ℕ} {o u : ℕ} (hAo : ∀ a ∈ A0, a < o) (hA01 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) {Lds : List (List UT)} (hL : GoodChtX A0 o (fun _ => 0) u Lds)
    {us : List UT} (hus : GoodLowT u us) : GoodChtX A0 o (fun _ => 0) u (Lds ++ [us]) :=
  GoodChtX_snoc_low hL hus hA01 ho hAo

/-! ## 中身 -/

def okRAt (A0 : List ℕ) (o u : ℕ) (X : TrioSeq) : Prop := Fr X ∧ RAt A0 o (fun _ => 0) u X

theorem okRAt_nil (A0 : List ℕ) (o u : ℕ) : okRAt A0 o u [] := ⟨Fr_nil, RAt_nil _ _ _ _⟩

theorem okRAt_load {A0 : List ℕ} {o u : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) {X : TrioSeq}
    (h : okRAt A0 o u X) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    okRAt A0 o u (X ++ shiftr01 1 0 Z) :=
  ⟨Fr_append h.1 (Fr_shift1 Z), slot_load (RAt_ax hA01 ho _) h.1 h.2 Z hZ hb⟩

theorem okRAt_node {A0 : List ℕ} {o u τ : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o)
    (hAo : ∀ a ∈ A0, a < o) (hτ : τ ≤ o) {X L : TrioSeq} (A' : List ℕ)
    (hA' : A0.filter (fun a => decide (a < τ)) = A') (h : okRAt A0 o u X) (hL : GPF A' τ u L) :
    okRAt A0 o u (X ++ ((1, u + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L) := by
  refine ⟨Fr_append h.1 (Fr_node _ _),
    RAt_node hA01 ho hAo h.1 h.2 ?_ (by rw [liftOff_zeroF]; exact hτ)⟩
  rw [GC_zeroF, hA']; exact hL.1

theorem okRAt_tie {A0 : List ℕ} {o u : ℕ} (hA01 : ∀ a ∈ A0, 1 ≤ a) (ho : 1 ≤ o) {X : TrioSeq}
    (h : okRAt A0 o u X) {D : TrioSeq} (hD : GF 1 u D) :
    okRAt A0 o u (X ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) := by
  have := ((Gof_one_iff u D).mp hD.1) (RAt A0 o (fun _ => 0)) (RAt_ax hA01 ho _) u le_rfl X h.1 h.2
  rw [Nat.sub_self, mlift_zero] at this
  exact ⟨Fr_append h.1 (Fr_node _ _), this⟩

/-! ## 並び -/

def OkWsAt (A0 : List ℕ) (o b : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, w.2.1 ≤ b ∧ GoodChtX A0 o (fun _ => 0) w.2.1 w.1 ∧ okRAt A0 o w.2.1 w.2.2

theorem OkWsAt_nil (A0 : List ℕ) (o b : ℕ) : OkWsAt A0 o b [] := fun _ h => by simp at h

theorem OkWsAt_cons {A0 : List ℕ} {o b u : ℕ} (hub : u ≤ b) {Lds : List (List UT)}
    (hL : GoodChtX A0 o (fun _ => 0) u Lds) {X : TrioSeq} (h : okRAt A0 o u X)
    {ws : List (List (List UT) × ℕ × TrioSeq)} (hs : OkWsAt A0 o b ws) :
    OkWsAt A0 o b ((Lds, u, X) :: ws) := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact ⟨hub, hL, h⟩
  · exact hs w hw

theorem RawWsAt_of_OkWsAt {A0 : List ℕ} {o b : ℕ}
    {ws : List (List (List UT) × ℕ × TrioSeq)}
    (h : OkWsAt A0 o b ws) : RawWsAt A0 o (fun _ => 0) b ws := fun w hw => by
  have hok := RAt_okWA (h w hw).2.2.2
  exact ⟨(h w hw).1, (h w hw).2.1.1, (h w hw).2.2.1, hok.1, hok.2.1⟩

theorem FarCAt_of_OkWsAt {A0 : List ℕ} {o b : ℕ} (hAo : ∀ a ∈ A0, a < o) (hA01 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) :
    ∀ ws : List (List (List UT) × ℕ × TrioSeq), OkWsAt A0 o b ws →
      ∀ b0, FarCAt A0 o (fun _ => 0) b0 ws := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil => intro _ b0; exact FarCAt_nil _ _ _ b0
  | append_singleton ws w ih =>
      intro h b0
      have hw := h w (List.mem_append_right _ (List.mem_singleton_self _))
      have hok := RAt_okWA hw.2.2.2
      have hG : GoodCht A0 o (fun _ => 0) w.2.1 w.1 := by
        have := GoodChtX_GoodCht hw.2.1 (EmbU_triv hAo hA01 ho (fun _ => 0))
        rw [mapt_zero] at this
        exact this
      have := hok.2.2 w.2.1 le_rfl w.1 hG b0 ws (ih (fun w' h' => h w' (List.mem_append_left _ h')) b0)
      rwa [Nat.sub_self, mlift_zero] at this

/-- ★ 遠い語の並び（F のタイの子に F の位置のタイを含む）は節点の子の並び。 -/
theorem PVF_farWAt {A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ A0, a < o) (hA1 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) (b : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq))
    (h : OkWsAt A0 o b ws) : PVF A0 o b (farWt b (b + o + 1) ws) := by
  have := farWAt_PVP (FarCAt_of_OkWsAt hA hA1 ho ws h b) (fun _ => 0) (S := []) (o := o)
    (f := fun _ => 0) (fun a _ => by simp [addF]) le_rfl (RawWsAt_of_OkWsAt h) (by simp)
    (by simpa using hA) (by simpa using hA1) ho (by simp)
    (by rw [HaG.reOff_zz]; simp [liftOff_zeroF])
  simp only [List.nil_append, liftOff_zeroF, relWst_zero] at this
  exact ⟨this, Fr_farWt _ _ _⟩

end HdH
end TRIO
