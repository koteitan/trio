/-
HdP.lean: 高さ t の空のタイの規則 GT_tieE、全ての高さの空の並び GT_nil、低い塊の族 ChLowS と、低い木の単位の並びの良さ GT_all。

- GT_tieE: GT t us → GT t (us ++ [tie []])。タイ (|Q|+3, r, 0) は FarP_GpT_lt（s = liftOff + 1）。
  h1 は us の語、h2 の子の節点は埋め込み先の級の RNs t（RNs_node）の塊として道の同じ位置に置く。
- GT_nil (t+1) = GT_of_jump と GT_tieE。
- GT_allL: 低い木（塊は ChLowS）の並びは全ての高さ・級で GT。
-/
import HdO

namespace TRIO
namespace HdP

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HcA HcE HcF HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdL HdM HdN HdO

/-! ## 空のタイ -/

/-- ★ 高さ t の並びの最後に空のタイを足す規則。 -/
theorem GT_tieE {t : ℕ} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} {us : List UT}
    (h : GT t A k H c us) : GT t A k H c (us ++ [UT.tie 0 []]) := by
  refine ⟨RawTs_snoc.mpr ⟨h.1, by simp [RawT, RawTs]⟩, fun G S o f hE u hcu Lds hL Q hQ => ?_⟩
  intro b hub ws hC hR
  have hA := hE.2.2.1
  have hA1 := hE.2.2.2.1
  have ho := hE.2.2.2.2.1
  obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f (S ++ A) o + 1 := ⟨_, rfl⟩
  rw [imgT_append, imgT_tie, imgT_nil, ← hr, farWt_botT]
  have hRaw := RawTs_imgT hE hcu h.1
  obtain ⟨V0, hV0⟩ : ∃ V0, V0 = chT b r u (imgT A H G c u us) := ⟨_, rfl⟩
  have hV0F : Fr V0 := by rw [hV0]; exact Fr_chT _ hRaw
  have eT : chT b r u (imgT A H G c u us ++ [UT.tie 0 []]) = V0 ++ [((1, r, 0) : ℕ × ℕ × ℕ)] := by
    rw [hV0]; simp [chT_append, chT, unitT, shiftr01]
  have eW : farWt b r ws ++ (fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++
        shiftr01 (Q.length + 2) 0 (V0 ++ [((1, r, 0) : ℕ × ℕ × ℕ)]))
      = (farWt b r ws ++ (fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++
          shiftr01 (Q.length + 2) 0 V0)) ++
        [((Q.length + 3, b + (liftOff f (S ++ A) o + 1), 0) : ℕ × ℕ × ℕ)] := by
    rw [shiftr01_append0]
    have e1 : shiftr01 (Q.length + 2) 0 [((1, r, 0) : ℕ × ℕ × ℕ)]
        = [((Q.length + 3, b + (liftOff f (S ++ A) o + 1), 0) : ℕ × ℕ × ℕ)] := by
      simp only [shiftr01, List.map_cons, List.map_nil]
      congr 1
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> omega
    rw [e1]
    simp only [List.append_assoc]
  rw [eT, eW]
  have hPF : Fr (farWt b r ws ++ (fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++
      shiftr01 (Q.length + 2) 0 V0)) :=
    Fr_append (Fr_farWt _ _ _) (Fr_append (Fr_fwH _ _ _ _ _) (Fr_shiftr hV0F _))
  have hbot : BotGe (farWt b r ws ++ (fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++
      shiftr01 (Q.length + 2) 0 V0)) (Q.length + 3) (b + (liftOff f (S ++ A) o + 1)) := by
    have := BotGe_path (b := b) (r := r) (u := u) ws Lds Q (fun us' h' => ⟨_, PG_raw hQ us' h'⟩)
      (show b + (liftOff f (S ++ A) o + 1) ≤ r by omega) (BotGe_one hV0F (b + (liftOff f (S ++ A) o + 1)))
    rwa [show 1 + (Q.length + 2) = Q.length + 3 by omega] at this
  have hRn : RawWsAt (S ++ A) o f b (ws ++ [(Lds ++ [plugQ Q (imgT A H G c u us)], u, [])]) := by
    refine RawWsAt_snoc hR ⟨hub, fun us' h' => ?_, Fr_nil, fun h => absurd rfl h, LowC_nil _⟩
    rcases List.mem_append.mp h' with h' | h'
    · exact hL.1 us' h'
    · simp at h'; subst h'; exact RawTs_plugQ Q _ (PG_raw hQ) hRaw
  have eQ : farWt b r ws ++ (fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++
      shiftr01 (Q.length + 2) 0 V0) = farWt b r (ws ++ [(Lds ++ [plugQ Q (imgT A H G c u us)], u, [])]) := by
    rw [farWt_botT, hV0]
  have hRw : ∀ w ∈ ws, (∀ us ∈ w.1, RawTs (w.2.1 + reOff (fun _ => 0) f (S ++ A) o) us) ∧
      Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) f (S ++ A) o) w.2.2 :=
    fun w hw => (hR w hw).2
  have e0 : ∀ c' (K G' : ℕ → ℕ) (B : List ℕ), reliftX c' K G' B ([] : TrioSeq) = [] := fun c' K G' B => by
    unfold reliftX; exact slift_nil _
  have eP : ∀ (g' : ℕ → ℕ) b', b ≤ b' →
      reliftX b' f g' (S ++ A) (mlift (farWt b r ws ++ (fwH b r (FTLt b r u (Lds ++ [plugQ Q []])) u [] ++
        shiftr01 (Q.length + 2) 0 V0)) b (b' - b))
      = farWt b' (b' + liftOff (addF f g') (S ++ A) o + 1) (relWst (S ++ A) f g' ws ++
          [(Lds.map (relTs (S ++ A) f g' u) ++
            [plugQ (Q.map (relTs (S ++ A) f g' u)) (imgT A H (addF G g') c u us)], u, [])]) := by
    intro g' b' hb'
    have eI : relTs (S ++ A) f g' u (imgT A H G c u us) = imgT A H (addF G g') c u us := by
      have := imgT_comp hE g' hcu le_rfl h.1
      rwa [show imgT (S ++ A) f g' u u (imgT A H G c u us) = relTs (S ++ A) f g' u (imgT A H G c u us) by
        unfold imgT; rw [Nat.sub_self, mlTs_zero]] at this
    rw [eQ, hr, mlift_farWt_self hRn hb', reliftX_farWt_self hA b' g' (RawWsAt_mono hb' hRn),
      relWst_snoc, e0, List.map_append, List.map_singleton, relTs_plugQ, eI]
  have hFP := FarP_GpT_lt (A := S ++ A) (o := o) hA ho (f := f) (s := liftOff f (S ++ A) o + 1) (by omega)
  refine hFP b _ (Q.length + 3) hPF (by omega) hbot (fun g' b' hb' => ?_)
    (fun g' b' hb' τ L h1τ hτ hL' hGL => ?_)
  · -- h1: us の語
    rw [eP g' b' hb']
    have hEs := EmbU_self hA1 ho hA f g'
    exact h.2 (addF G g') S o (addF f g') (EmbU_relift hE g') u hcu _ (GoodChtX_emb hL hEs) _
      (PG_emb hQ hEs) b' (by omega) _ (FarCAt_mono hb' (FarCAt_relift hC hRw g'))
      (RawWsAt_relWst (RawWsAt_mono hb' hR) g')
  · -- h2: 埋め込み先の級の RNs の塊
    rw [eP g' b' hb']
    have hτo : τ ≤ liftOff (addF f g') (S ++ A) o := by
      have := reOff_above hA f g' 1
      rw [this] at hτ
      omega
    have hub' : u ≤ b' := by omega
    have hRN := RNs_node (s := t) hA1 ho hA Fr_nil (RNs_nil _ _) hGL hτo
    have hNX := RNs_okW hRN
    have hEs := EmbU_self hA1 ho hA f g'
    have hL3 := GoodChtX_lift (GoodChtX_emb hL hEs) hub'
    have hQ3 := PG_lift (PG_emb hQ hEs) hub'
    have hus3 : GT t (S ++ A) o (addF f g') b' (mlTs c (b' - c) (relTs A H (addF G g') c us)) :=
      GT_lift (GT_emb h (EmbU_relift hE g')) (show c ≤ b' by omega)
    have := NXs_snoc_elim (hNX.2.2 b' le_rfl _ hus3) le_rfl (fun _ => 0) [] o (addF f g')
      (EmbU_triv hA hA1 ho _) b' le_rfl _ hL3 _ hQ3 b' le_rfl (relWst (S ++ A) f g' ws)
      (FarCAt_mono hb' (FarCAt_relift hC hRw g')) (RawWsAt_relWst (RawWsAt_mono hb' hR) g')
    have eL3 : (Lds.map (relTs (S ++ A) f g' u)).map (mlTs u (b' - u)) ++
        [plugQ ((Q.map (relTs (S ++ A) f g' u)).map (mlTs u (b' - u))) []]
        = (Lds.map (relTs (S ++ A) f g' u) ++ [plugQ (Q.map (relTs (S ++ A) f g' u)) []]).map
            (mlTs u (b' - u)) := by
      simp [mlTs_plugQ, mlTs]
    have eus3 : mlTs c (b' - c) (relTs A H (addF G g') c us)
        = mlTs u (b' - u) (imgT A H (addF G g') c u us) := by
      unfold imgT
      rw [← relTs_mlTs A H (addF G g') hub', mlTs_comp hcu hub',
        relTs_mlTs A H (addF G g') (show c ≤ b' by omega)]
    simp only [List.nil_append] at this
    rw [imgT_zero, reliftX_zero, Nat.sub_self, mlift_zero, List.length_map, List.length_map, eL3,
      FTLt_rebase hub' le_rfl, fwH_nil_c _ _ _ b' u, eus3, chT_rebase hub' le_rfl] at this
    rw [farWt_botT, List.length_map, show Q.length + 3 - 1 = Q.length + 2 by omega]
    simp only [List.append_assoc, shiftr01_append0] at this ⊢
    exact this

/-- ★ 高さ t+1 の空の並び（高さ t の空のタイの規則の跳びの形）。 -/
theorem GT_nilS {t : ℕ} {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} : GT (t + 1) A k H c [] :=
  GT_of_jump (by simp [RawTs]) (fun G1 S1 o1 f1 _ u _ us0 hus0 => by rw [imgT_nil]; exact GT_tieE hus0)

theorem GT_nil : ∀ (t : ℕ) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ}, GT t A k H c []
  | 0, _, _, _, _ => GT_nil0
  | _ + 1, _, _, _, _ => GT_nilS

/-! ## 低い塊 -/

def ChLowS (c : ℕ) (X : TrioSeq) : Prop :=
  LowC (c + 1) X ∧ ∀ (s : ℕ) (A : List ℕ) (k : ℕ), (∀ a ∈ A, 1 ≤ a) → 1 ≤ k →
    ∀ H : ℕ → ℕ, NXs s A k H c X

/-- ★ 低い塊の族の差し込み口の公理。 -/
theorem ChLowS_ax : SlotAx ChLowS where
  lift := by
    intro c W hW h c1 hc1
    exact ⟨LowC_v1_lift hc1 h.1, fun s A k h1 h2 H =>
      (NXs_ax (s := s) h1 h2 H).lift c W hW (h.2 s A k h1 h2 H) c1 hc1⟩
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
    exact ⟨hLow, fun s A k h1 h2 H =>
      (NXs_ax (s := s) h1 h2 H).oper c W U hW hU hH hlen hp (fun m hm => (hIH m hm).2 s A k h1 h2 H)⟩
  orph := by
    intro c W U h j hW hU hH hj1 hj hnp hz
    have hz0 := hz [] (Wg_nil _) based_nil
    have e0 : W ++ (U ++ shiftr01 h 0 []) = W ++ U := by simp [shiftr01]
    rw [e0] at hz0
    refine ⟨?_, fun s A k h1 h2 H =>
      (NXs_ax (s := s) h1 h2 H).orph c W U h j hW hU hH hj1 hj hnp
        (fun z hz' hbz => (hz z hz' hbz).2 s A k h1 h2 H)⟩
    rw [← List.append_assoc]
    exact LowC_snoc hz0.1 _ (by show j ≤ c + 1; omega)
  tie := by
    intro c W U x hW hU hH hc hload
    have h0 := hload c le_rfl [] (Wg_nil _) based_nil
    have e0 : mlift (W ++ U) c (c - c) ++ shiftr01 x 0 [] = W ++ U := by
      simp [shiftr01, mlift_zero]
    rw [e0] at h0
    refine ⟨?_, fun s A k h1 h2 H =>
      (NXs_ax (s := s) h1 h2 H).tie c W U x hW hU hH hc
        (fun c'' hc'' Z hZ hbZ => (hload c'' hc'' Z hZ hbZ).2 s A k h1 h2 H)⟩
    rw [← List.append_assoc]
    exact LowC_snoc h0.1 _ (by show c + 1 ≤ c + 1; omega)
  flat := by
    intro c W hW h
    exact ⟨LowC_snoc h.1 _ (by show 0 ≤ c + 1; omega), fun s A k h1 h2 H =>
      (NXs_ax (s := s) h1 h2 H).flat c W hW (h.2 s A k h1 h2 H)⟩

def okLowS (c : ℕ) (X : TrioSeq) : Prop := Fr X ∧ ChLowS c X

theorem okLowS_nil (c : ℕ) : okLowS c [] :=
  ⟨Fr_nil, LowC_nil _, fun _ _ _ _ _ H => NXs_nil H c⟩

theorem okLowS_load {c : ℕ} {X : TrioSeq} (h : okLowS c X) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * c))
    (hb : based Z) : okLowS c (X ++ shiftr01 1 0 Z) :=
  ⟨Fr_append h.1 (Fr_shift1 Z), slot_load ChLowS_ax h.1 h.2 Z hZ hb⟩

theorem okLowS_tie {c : ℕ} {X : TrioSeq} (h : okLowS c X) {E : TrioSeq} (hE : GF 1 c E) :
    okLowS c (X ++ ((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 E) := by
  have := ((Gof_one_iff c E).mp hE.1) ChLowS ChLowS_ax c le_rfl X h.1 h.2
  rw [Nat.sub_self, mlift_zero] at this
  exact ⟨Fr_append h.1 (Fr_node _ _), this⟩

/-! ## 低い木の単位の並び -/

mutual
def LRawT (c : ℕ) : UT → Prop
  | .ch X => okLowS c X
  | .tie l us => l = 0 ∧ LRawTs c us
def LRawTs (c : ℕ) : List UT → Prop
  | [] => True
  | x :: us => LRawT c x ∧ LRawTs c us
end

section
variable {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k) (hAk : ∀ a ∈ A, a < k) (H : ℕ → ℕ)
include hA01 hk hAk

mutual
theorem GT_allU {c : ℕ} : ∀ (x : UT) (t : ℕ) (pre : List UT), LRawT c x → GT t A k H c pre →
    GT t A k H c (pre ++ [x])
  | .ch X, t, pre, hx, hpre => by
      have := (hx.2.2 t A k hA01 hk H).2.2 c le_rfl pre hpre
      rwa [Nat.sub_self, mlift_zero] at this
  | .tie l cs, t, pre, hx, hpre => by
      obtain ⟨rfl, hx⟩ := hx
      have hcs := GT_allL (c := c) cs (t + 1) [] hx GT_nilS
      rw [List.nil_append] at hcs
      exact GT_tie hA01 hk hAk hpre hcs
theorem GT_allL {c : ℕ} : ∀ (us : List UT) (t : ℕ) (pre : List UT), LRawTs c us → GT t A k H c pre →
    GT t A k H c (pre ++ us)
  | [], _, pre, _, hpre => by rw [List.append_nil]; exact hpre
  | x :: us, t, pre, hx, hpre => by
      have := GT_allL (c := c) us t (pre ++ [x]) hx.2 (GT_allU (c := c) x t pre hx.1 hpre)
      rwa [List.append_assoc, List.singleton_append] at this
end

/-- ★ 低い木の単位の並びは、全ての高さ・級で良い。 -/
theorem GT_all {c : ℕ} (t : ℕ) {us : List UT} (h : LRawTs c us) : GT t A k H c us := by
  have := GT_allL hA01 hk hAk H us t [] h (GT_nil t)
  rwa [List.nil_append] at this

end

/-- ★ 最後の語の F のタイの子の並びに、低い木の単位の並びを足す。 -/
theorem GoodChtX_snocL {A0 : List ℕ} {o u : ℕ} (hAo : ∀ a ∈ A0, a < o) (hA01 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) {Lds : List (List UT)} (hL : GoodChtX A0 o (fun _ => 0) u Lds) {us : List UT}
    (hus : LRawTs u us) : GoodChtX A0 o (fun _ => 0) u (Lds ++ [us]) := by
  have := GT_good (GT_all hA01 ho hAo (fun _ => 0) 0 hus) (EmbU_triv hAo hA01 ho _) le_rfl
    (S := []) hL PG_zero
  simpa only [plugQ, imgT_zero] using this

end HdP
end TRIO
