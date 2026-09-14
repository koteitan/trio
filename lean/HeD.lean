/-
HeD.lean: 道の集合 P の子の並びの最後の低い塊の族 NXs P と、その差し込み口の lift / oper / orph（HdM の写し、段つきの道）。

    NXs P A k H c X := Hd X ∧ LowC ∧ ∀ c' ≥ c, ∀ us, Gd P c' us → Gd P c' (us ++ [ch (X を c' へ)])
- 道の成分 (us, l) の節点は行 1 が r + l ≥ r（PathCone_chTQ）。
-/
import HeC

namespace TRIO
namespace HeD

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HbS HcA HcE HcF HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HeB HeC

/-! ## 道の錐 -/

theorem shift_ge {V : TrioSeq} (hV : Fr V) (m : ℕ) : ∀ c ∈ shiftr01 m 0 V, m + 1 ≤ c.1 := by
  intro c hc
  simp only [shiftr01, List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  have := hV p hp
  dsimp only; omega

theorem PathCone_letter {u d r : ℕ} (hur : u < r) {Z : TrioSeq} (h : PathCone u d Z) :
    PathCone u (d + 1) (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Z) := by
  intro y hy hvis hd
  rcases y with _ | y
  · exact hur
  · have hy' : y < Z.length := by simp only [List.length_cons, shiftr01_length] at hy; omega
    rw [entry_cons, entry0_shiftr01 hy'] at hd
    rw [entry_cons, entry1_shiftr01]
    refine h y hy' (fun k hk1 hk2 => ?_) (by omega)
    have := hvis (k + 1) (by omega) (by simp only [List.length_cons, shiftr01_length]; omega)
    rw [entry_cons, entry_cons, entry0_shiftr01 hy', entry0_shiftr01 hk2] at this
    omega

theorem PathCone_tieSnoc {u m r : ℕ} (hur : u < r) {Y V : TrioSeq} (h : PathCone u m Y)
    (hV : ∀ c ∈ V, m + 1 ≤ c.1) :
    PathCone u (m + 1) (Y ++ V ++ [((m + 1, r, 0) : ℕ × ℕ × ℕ)]) := by
  intro y hy hvis hd
  have e1 : ∀ i, i < Y.length → entry (Y ++ V ++ [((m + 1, r, 0) : ℕ × ℕ × ℕ)]) 0 i = entry Y 0 i :=
    fun i hi => by rw [Small.entry_append_left (by simp; omega), Small.entry_append_left hi]
  have eL : entry (Y ++ V ++ [((m + 1, r, 0) : ℕ × ℕ × ℕ)]) 0 (Y ++ V).length = m + 1 := by
    rw [show (Y ++ V).length = (Y ++ V).length + 0 from rfl, entry_append_right]; rfl
  rcases Nat.lt_or_ge y (Y ++ V).length with hlt | hge
  · have hlast := hvis (Y ++ V).length hlt (by simp)
    rw [eL] at hlast
    rcases Nat.lt_or_ge y Y.length with hlt2 | hge2
    · rw [Small.entry_append_left (by simp; omega), Small.entry_append_left hlt2]
      refine h y hlt2 (fun k hk1 hk2 => ?_) ?_
      · have := hvis k hk1 (by simp; omega)
        rwa [e1 y hlt2, e1 k hk2] at this
      · rw [e1 y hlt2] at hlast; omega
    · exfalso
      obtain ⟨w, rfl⟩ : ∃ w, y = Y.length + w := ⟨y - Y.length, by omega⟩
      rw [Small.entry_append_left hlt, entry_append_right] at hlast
      have hw : w < V.length := by simp at hlt; omega
      have := getD_row0_ge hV hw
      omega
  · have hy' : y = (Y ++ V).length := by simp at hy hge ⊢; omega
    subst hy'
    rw [show (Y ++ V).length = (Y ++ V).length + 0 from rfl, entry_append_right]
    exact hur

theorem shift_chTQ_cons (b r u m : ℕ) (us : List UT) (l : ℕ) (q : Path) :
    shiftr01 m 0 (chTQ b r u ((us, l) :: q))
      = shiftr01 m 0 (chT b r u us) ++ [((m + 1, r + l, 0) : ℕ × ℕ × ℕ)] ++
        shiftr01 (m + 1) 0 (chTQ b r u q) := by
  simp only [chTQ, shiftr01_append0, List.append_assoc]
  congr 1
  simp only [shiftr01, List.map_cons, List.singleton_append, List.map_map, Function.comp_def]
  refine congrArg₂ _ (by simp [Nat.add_comm]) ?_
  apply List.map_congr_left
  intro p _
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> omega

theorem PathCone_chTQ {b r : ℕ} (hbr : b < r) (bb u K : ℕ) :
    ∀ (Q : Path) (m : ℕ) (Y : TrioSeq), (∀ p ∈ Q, RawTs K p.1) → PathCone b m Y →
      PathCone b (m + Q.length) (Y ++ shiftr01 m 0 (chTQ bb r u Q))
  | [], m, Y, _, h => by simpa [chTQ, shiftr01] using h
  | (us, l) :: q, m, Y, hQ, h => by
      rw [shift_chTQ_cons, ← List.append_assoc, ← List.append_assoc]
      have h1 := PathCone_tieSnoc (show b < r + l by omega) h (V := shiftr01 m 0 (chT bb r u us))
        (shift_ge (Fr_chT _ (hQ (us, l) (by simp))) m)
      have := PathCone_chTQ hbr bb u K q (m + 1) _ (fun p' h' => hQ p' (by simp [h'])) h1
      rwa [show m + 1 + q.length = m + ((us, l) :: q).length by simp; omega] at this

theorem fwQ_eq (bb r u : ℕ) (Lds : List (List UT)) (Q : Path) :
    fwH bb r (FTLt bb r u (Lds ++ [plugQ Q []])) u []
      = ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 ([] ++ FTLt bb r u Lds ++ [((0 + 1, r, 0) : ℕ × ℕ × ℕ)] ++
          shiftr01 1 0 (chTQ bb r u Q)) := by
  simp only [fwH, mlift_nil, List.append_nil, FTLt_snoc, chT_plugQ, List.nil_append, Nat.zero_add]
  have e : shiftr01 Q.length 0 (chT bb r u []) = [] := by simp [chT, shiftr01]
  rw [e, List.append_nil]
  simp

theorem PathCone_fwQ {b r : ℕ} (hbr : b < r) (bb u K : ℕ) (Lds : List (List UT)) (Q : Path)
    (hQ : ∀ p ∈ Q, RawTs K p.1) :
    PathCone b (Q.length + 2) (fwH bb r (FTLt bb r u (Lds ++ [plugQ Q []])) u []) := by
  rw [fwQ_eq]
  have h0 : PathCone b 0 ([] : TrioSeq) := fun y hy => by simp at hy
  have h1 := PathCone_tieSnoc hbr h0 (V := FTLt bb r u Lds) (fun c hc => Fr_FTLt _ _ _ _ c hc)
  have h2 := PathCone_chTQ hbr bb u K Q (0 + 1) _ hQ h1
  have h3 := PathCone_letter hbr h2
  rwa [show 0 + 1 + Q.length + 1 = Q.length + 2 by omega] at h3

/-! ## 最後の語の形 -/

theorem farWt_botT (b r u : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq))
    (Lds : List (List UT)) (Q : Path) (T : List UT) :
    farWt b r (ws ++ [(Lds ++ [plugQ Q T], u, [])])
      = farWt b r ws ++ (fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++
          shiftr01 (Q.length + 2) 0 (chT b r u T)) := by
  have h1 := farWt_plugQ b r u ws Lds Q T
  have h0 := farWt_plugQ b r u ws Lds Q []
  have e : shiftr01 (Q.length + 2) 0 (chT b r u []) = [] := by simp [chT, shiftr01]
  rw [e, List.append_nil] at h0
  rw [h1, ← h0, farWt_snoc, List.append_assoc]

theorem bot_assoc (P Y V W U : TrioSeq) (d : ℕ) :
    P ++ (Y ++ shiftr01 d 0 (V ++ (W ++ U))) = P ++ ((Y ++ shiftr01 d 0 (V ++ W)) ++ shiftr01 d 0 U) := by
  simp only [List.append_assoc, shiftr01_append0]

theorem botY_facts {b r : ℕ} (hbr : b < r) (u K : ℕ) (Lds : List (List UT)) (Q : Path)
    (hQ : ∀ p ∈ Q, RawTs K p.1) {V : TrioSeq} (hV : Fr V) :
    Fr (fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++ shiftr01 (Q.length + 2) 0 V) ∧
    Hd (fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++ shiftr01 (Q.length + 2) 0 V) ∧
    (fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++ shiftr01 (Q.length + 2) 0 V) ≠ [] ∧
    PathCone b (Q.length + 2) (fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++
      shiftr01 (Q.length + 2) 0 V) := by
  have hne : fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ≠ [] := by simp [fwH]
  refine ⟨Fr_append (Fr_fwH _ _ _ _ _) (Fr_shiftr hV _), Hd_app_ne (Hd_fwH _ _ _ _ _) hne,
    by simp [fwH], PathCone_append (shift_ge hV _) (PathCone_fwQ hbr b u K Lds Q hQ)⟩

theorem chT_imgT_ch {A : List ℕ} (H G : ℕ → ℕ) {b r c c' u : ℕ} (hcc : c ≤ c') (hcu : c' ≤ u)
    (hub : u ≤ b) (us : List UT) (X : TrioSeq) :
    chT b r u (imgT A H G c' u (us ++ [UT.ch (mlift X c (c' - c))]))
      = chT b r u (imgT A H G c' u us) ++ reliftX b H G A (mlift X c (b - c)) := by
  rw [imgT_append, imgT_ch, chT_append]
  simp only [chT, unitT, List.append_nil]
  rw [mlift_comp_vub hcc hcu, mlift_reliftX, show u + (b - u) = b by omega,
    mlift_comp_vub (le_trans hcc hcu) hub]

/-! ## 低い塊の族 -/

def NXs (P : PS) (A : List ℕ) (k : ℕ) (H : ℕ → ℕ) (c : ℕ) (X : TrioSeq) : Prop :=
  Hd X ∧ LowC (c + reOff (fun _ => 0) H A k) X ∧
    ∀ c', c ≤ c' → ∀ us, Gd P A k H c' us → Gd P A k H c' (us ++ [UT.ch (mlift X c (c' - c))])

theorem NXs_snoc_of {P : PS} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c' : ℕ} {us : List UT}
    (hus : Gd P A k H c' us) {c : ℕ} (hcc : c ≤ c') {X : TrioSeq}
    (hXF : Fr X) (hXH : Hd X) (hXL : LowC (c + reOff (fun _ => 0) H A k) X)
    (hstep : ∀ (G : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ), EmbU A k H G S o f → ∀ u, c' ≤ u →
      ∀ Lds, GoodChtX (S ++ A) o f u Lds → ∀ Q, P (S ++ A) o f u Q → ∀ b, u ≤ b →
        ∀ ws, FarCAt (S ++ A) o f b ws → RawWsAt (S ++ A) o f b ws →
          GpT (S ++ A) o f b (farWt b (b + liftOff f (S ++ A) o + 1) ws ++
            (fwH b (b + liftOff f (S ++ A) o + 1)
              (FTLt b (b + liftOff f (S ++ A) o + 1) u (Lds ++ [plugQ Q []])) u [] ++
              shiftr01 (Q.length + 2) 0 (chT b (b + liftOff f (S ++ A) o + 1) u (imgT A H G c' u us) ++
                reliftX b H G A (mlift X c (b - c)))))) :
    Gd P A k H c' (us ++ [UT.ch (mlift X c (c' - c))]) := by
  refine ⟨RawTs_snoc.mpr ⟨hus.1, RawT_ch (Fr_mlift hXF _ _) (Hd_mlift hXH _ _) (LowC_lift_shift hcc hXL)⟩,
    fun G S o f hE u hcu Lds hL Q hQ => ?_⟩
  intro b hub ws hC hR
  rw [farWt_botT, chT_imgT_ch H G hcc hcu hub]
  exact hstep G S o f hE u hcu Lds hL Q hQ b hub ws hC hR

theorem NXs_snoc_elim {P : PS} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c' : ℕ} {us : List UT} {c : ℕ}
    {X : TrioSeq} (h : Gd P A k H c' (us ++ [UT.ch (mlift X c (c' - c))])) (hcc : c ≤ c')
    (G : ℕ → ℕ) (S : List ℕ) (o : ℕ) (f : ℕ → ℕ) (hE : EmbU A k H G S o f) (u : ℕ) (hcu : c' ≤ u)
    (Lds : List (List UT)) (hL : GoodChtX (S ++ A) o f u Lds) (Q : Path)
    (hQ : P (S ++ A) o f u Q) (b : ℕ) (hub : u ≤ b) (ws : List (List (List UT) × ℕ × TrioSeq))
    (hC : FarCAt (S ++ A) o f b ws) (hR : RawWsAt (S ++ A) o f b ws) :
    GpT (S ++ A) o f b (farWt b (b + liftOff f (S ++ A) o + 1) ws ++
      (fwH b (b + liftOff f (S ++ A) o + 1)
        (FTLt b (b + liftOff f (S ++ A) o + 1) u (Lds ++ [plugQ Q []])) u [] ++
        shiftr01 (Q.length + 2) 0 (chT b (b + liftOff f (S ++ A) o + 1) u (imgT A H G c' u us) ++
          reliftX b H G A (mlift X c (b - c))))) := by
  have := h.2 G S o f hE u hcu Lds hL Q hQ b hub ws hC hR
  rwa [farWt_botT, chT_imgT_ch H G hcc hcu hub] at this

theorem NXs_lift {P : PS} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} (c : ℕ) (W : TrioSeq)
    (h : NXs P A k H c W) (c1 : ℕ) (hc1 : c ≤ c1) : NXs P A k H c1 (mlift W c (c1 - c)) := by
  refine ⟨Hd_mlift h.1 c (c1 - c), LowC_lift_shift hc1 h.2.1, fun c' hc' us hus => ?_⟩
  have e := mlift_mlift W c (c1 - c) (c' - c1)
  rw [show c + (c1 - c) = c1 by omega, show c1 - c + (c' - c1) = c' - c by omega] at e
  rw [e]
  exact h.2.2 c' (le_trans hc1 hc') us hus

theorem NXs_oper {P : PS} (hP : PSOK P) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} (c : ℕ) (W U : TrioSeq)
    (hW : Fr W) (hU : Fr U) (hH : Hd U) (hlen : 2 ≤ U.length)
    (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → NXs P A k H c (W ++ U⟦m⟧)) : NXs P A k H c (W ++ U) := by
  have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  have hI1 := hIH 1 le_rfl
  have hU1 : U⟦1⟧ = U.dropLast := oper_one_eq_dropLast (by omega)
  have hLow : LowC (c + reOff (fun _ => 0) H A k) (W ++ U) := by
    have hI1' := hI1.2.1
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
  refine ⟨Hd_append_of hH hI1.1, hLow, fun c' hcc us hus => ?_⟩
  refine NXs_snoc_of hus hcc (Fr_append hW hU) (Hd_append_of hH hI1.1) hLow
    (fun G S o f hE u hcu Lds hL Q hQ b hub ws hC hR => ?_)
  have hA := hE.2.2.1
  have hA1 := hE.2.2.2.1
  have ho := hE.2.2.2.2.1
  have hbr : b < b + liftOff f (S ++ A) o + 1 := by omega
  have hV : Fr (chT b (b + liftOff f (S ++ A) o + 1) u (imgT A H G c' u us) ++
      reliftX b H G A (mlift W c (b - c))) :=
    Fr_append (Fr_chT _ (RawTs_imgT hE hcu hus.1)) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
  obtain ⟨hYF, hYH, hYne, -⟩ := botY_facts hbr u _ Lds Q (hP.raw _ _ _ _ _ hQ) hV
  rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), bot_assoc]
  refine tstep_oper hA hA1 ho f (Fr_farWt _ _ _) hYF hYH hYne (Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
    (by rw [reliftX_length, mlift_length]; exact hlen) ?_ (fun m hm => ?_)
  · unfold reliftX
    rw [slift_length, srow_slift (reStair_stair _ _ _ _) (by rw [mlift_length]; omega),
      hasParent_slift (reStair_stair _ _ _ _)]
    exact (hasParent_mlift_iff c (b - c) hUne).mpr hp
  · have := NXs_snoc_elim ((hIH m hm).2.2 c' hcc us hus) hcc G S o f hE u hcu Lds hL Q hQ b hub ws hC hR
    rw [mlift_app hW (Hd_oper hH hUne hm),
      reliftX_app (Fr_mlift hW _ _) (Hd_mlift (Hd_oper hH hUne hm) _ _), bot_assoc] at this
    unfold reliftX at this ⊢
    rwa [← mlift_oper', slift_oper (reStair_stair _ _ _ _)] at this

theorem NXs_orph {P : PS} (hP : PSOK P) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} (c : ℕ) (W U : TrioSeq) (h j : ℕ)
    (hW : Fr W) (hU : Fr (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
    (hj1 : 1 ≤ j) (hj : j ≤ c) (hnp : ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z → NXs P A k H c (W ++ (U ++ shiftr01 h 0 z))) :
    NXs P A k H c (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
  have hz0 := hz [] (Wg_nil _) based_nil
  have e0 : W ++ (U ++ shiftr01 h 0 []) = W ++ U := by simp [shiftr01]
  rw [e0] at hz0
  have hLow : LowC (c + reOff (fun _ => 0) H A k) (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
    rw [← List.append_assoc]
    exact LowC_snoc hz0.2.1 _ (by show j ≤ c + reOff (fun _ => 0) H A k; omega)
  refine ⟨Hd_append_of hH hz0.1, hLow, fun c' hcc us hus => ?_⟩
  refine NXs_snoc_of hus hcc (Fr_append hW hU) (Hd_append_of hH hz0.1) hLow
    (fun G S o f hE u hcu Lds hL Q hQ b hub ws hC hR => ?_)
  have hA := hE.2.2.1
  have hA1 := hE.2.2.2.1
  have ho := hE.2.2.2.2.1
  have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ c := hj
  have hfix : ∀ m, m ≤ j → reStair b H G A m = m := fun m hm => reStair_low b H G A (by omega)
  have eU : reliftX b H G A (mlift (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) c (b - c))
      = reliftX b H G A (mlift U c (b - c)) ++ [((h, j, 0) : ℕ × ℕ × ℕ)] := by
    unfold reliftX; rw [mlift_snoc_low U _ hc, slift_snoc_fix _ _ hfix]
  have hbr : b < b + liftOff f (S ++ A) o + 1 := by omega
  have hV : Fr (chT b (b + liftOff f (S ++ A) o + 1) u (imgT A H G c' u us) ++
      reliftX b H G A (mlift W c (b - c))) :=
    Fr_append (Fr_chT _ (RawTs_imgT hE hcu hus.1)) (Fr_reliftX (Fr_mlift hW _ _) _ _ _ _)
  obtain ⟨hYF, hYH, hYne, hPC⟩ := botY_facts hbr u _ Lds Q (hP.raw _ _ _ _ _ hQ) hV
  rw [mlift_app hW hH, reliftX_app (Fr_mlift hW _ _) (Hd_mlift hH _ _), eU, bot_assoc]
  refine tstep_orph hA hA1 ho f (Fr_farWt _ _ _) hYF hYH hYne hPC
    (by rw [← eU]; exact Fr_reliftX (Fr_mlift hU _ _) _ _ _ _)
    (by rw [← eU]; exact Hd_reliftX (Hd_mlift hH _ _) _ _ _ _) hj1 (by omega) ?_
    (fun z hz' hbz => ?_)
  · intro hh
    apply hnp
    rw [← eU, reliftX_length, mlift_length] at hh
    unfold reliftX at hh
    rw [hasParent_slift (reStair_stair _ _ _ _), mlift_eq_slift,
      hasParent_slift (stair_step _ _)] at hh
    exact hh
  · have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
    have hHz : Hd (U ++ shiftr01 h 0 z) := Hd_append_shift hH hbz
    have hzz := hz z hz' hbz
    have hlowz := low_of_Wg hzW h (show j ≤ c by omega)
    have := NXs_snoc_elim (hzz.2.2 c' hcc us hus) hcc G S o f hE u hcu Lds hL Q hQ b hub ws hC hR
    rw [mlift_app hW hHz, mlift_append_low hlowz] at this
    have hH2 : Hd (mlift U c (b - c) ++ shiftr01 h 0 z) := by
      have := Hd_mlift hHz c (b - c)
      rwa [mlift_append_low hlowz] at this
    rw [reliftX_app (Fr_mlift hW _ _) hH2] at this
    have e1 : reliftX b H G A (mlift U c (b - c) ++ shiftr01 h 0 z)
        = reliftX b H G A (mlift U c (b - c)) ++ shiftr01 h 0 z := by
      unfold reliftX
      exact slift_append_low (low_of_Wg hzW h (show j ≤ b by omega))
        (fun m hm => reStair_low b H G _ hm)
    rw [e1] at this
    simp only [List.append_assoc, shiftr01_append0] at this ⊢
    exact this

end HeD
end TRIO
