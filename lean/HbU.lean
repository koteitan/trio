/-
HbU.lean: 最後の F のタイの子に荷を足す規則。

- based_Wg_ind: Wg (2u) の based な列の帰納法（GxP.slot_load の骨組み。oper / orph / flat だけを使う）。
- child_oper_step / child_orph_step / child_flat_step: 頭 H、中身 (1,r,0) :: (D ++ Z↑1)↑1（中身の段 c = b）。
  flat は F のタイの複製 H ++ ((1,r,0) :: D↑1)^m になる。
- GoodL v Lds := 全ての級と v ≤ c0 で GTWA0 … Lds c0 []、
  ChildG v D := ∀ X, GoodL v X → GoodL v (X ++ [D])。
- ChildG_nil（空の F のタイ、HbT）、ChildG_load（荷）、GoodL_units（F のタイの子が荷だけの並び）。
-/
import HaT
import HbT

namespace TRIO
namespace HbU

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF HaT HbD HbM HbP HbQ HbR HbS HbT

/-! ## based な Wg の列の帰納法 -/

theorem based_Wg_ind {u : ℕ} {Q : TrioSeq → Prop} (hnil : Q [])
    (hflat : ∀ Z, Z ∈ Wg (2 * u) → based Z → Q Z → Q (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))
    (hoper : ∀ Z, Z ∈ Wg (2 * u) → based Z → 2 ≤ Z.length →
      hasParent Z (srow Z (Z.length - 1)) (Z.length - 1) →
      (∀ m, 1 ≤ m → Z⟦m⟧ ∈ Wg (2 * u) ∧ Q (Z⟦m⟧)) → Q Z)
    (horph : ∀ Z h j, Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)] ∈ Wg (2 * u) →
      based (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) → 1 ≤ j → j ≤ u →
      ¬ hasParent (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 Z.length →
      (∀ z ∈ Wg (2 * j - 1), based z →
        Z ++ shiftr01 h 0 z ∈ Wg (2 * u) ∧ Q (Z ++ shiftr01 h 0 z)) →
      Q (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) :
    ∀ Z ∈ Wg (2 * u), based Z → Q Z := by
  have key : Wg (2 * u) ⊆ {Z : TrioSeq | Z ∈ Wg (2 * u) ∧ (based Z → Q Z)} := by
    refine A2g' ?_
    intro Z hAZ
    have hZW : Z ∈ Wg (2 * u) := A1g_intro (Aopg_mono_X hAZ (fun U hU => hU.1))
    refine ⟨hZW, ?_⟩
    intro hb
    have hb0 : entry Z 0 0 = 0 := hb
    by_cases hZnil : Z = []
    · subst hZnil; exact hnil
    have hZlen : 0 < Z.length := List.length_pos_iff.mpr hZnil
    set c := Z.getLast hZnil with hc
    have hsplit : Z = Z.dropLast ++ [c] := (List.dropLast_append_getLast hZnil).symm
    have hclast : ∀ r, entry Z r (Z.length - 1) = entry [c] r 0 := by
      intro r
      have h := entry_append_right Z.dropLast [c] r 0
      rw [← hsplit] at h
      rw [show Z.length - 1 = Z.dropLast.length + 0 by simp]
      exact h
    have hlev0 : lev Z (Z.length - 1) = 0 → c.2.1 = 0 ∧ c.2.2 = 0 := by
      intro hz
      unfold lev at hz
      rw [hclast 1, hclast 2] at hz
      have e1 : entry [c] 1 0 = c.2.1 := rfl
      have e2 : entry [c] 2 0 = c.2.2 := rfl
      rw [e1, e2] at hz
      omega
    have hc10 : Z.length = 1 → c.1 = 0 := by
      intro hZ1
      have : entry Z 0 (Z.length - 1) = c.1 := hclast 0
      rw [show Z.length - 1 = 0 by omega, hb0] at this; omega
    have hflat' : c.2.1 = 0 → c.2.2 = 0 → c.1 = 0 → Z.dropLast ∈ Wg (2 * u) → Q Z.dropLast →
        Q Z := by
      intro h1 h2 h0 hdW hd
      have hceq : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext h0 (Prod.ext h1 h2)
      have e : Z = Z.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
        conv_lhs => rw [hsplit, hceq]
      rw [e]
      exact hflat _ hdW (based_dropLast hb) hd
    have hdrop1 : Z.length = 1 → Z.dropLast = [] := by
      intro hZ1
      exact List.eq_nil_of_length_eq_zero (by simp; omega)
    rcases hAZ with ⟨hl, hw0⟩ | ⟨hnat, hop⟩ | ⟨m', hm, hd, h20, hgr⟩
    · have hZ1 : Z.length = 1 := by omega
      have hz : lev Z (Z.length - 1) = 0 := by rw [hZ1]; exact hw0
      have hdl := hdrop1 hZ1
      exact hflat' (hlev0 hz).1 (hlev0 hz).2 (hc10 hZ1) (by rw [hdl]; exact Wg_nil _)
        (by rw [hdl]; exact hnil)
    · by_cases hp : 2 ≤ Z.length ∧ hasParent Z (srow Z (Z.length - 1)) (Z.length - 1)
      · obtain ⟨hlen2, hp⟩ := hp
        exact hoper Z hZW hb hlen2 hp (fun n hn => ⟨(hop n hn).1, (hop n hn).2 (based_oper hn hb)⟩)
      · have hlev : lev Z (Z.length - 1) = 0 := by
          rcases natDom_iff.mp hnat with h | h
          · exact h
          · exfalso
            have hZ1 : Z.length = 1 := by
              by_contra hne; exact hp ⟨by omega, h⟩
            rw [hZ1] at h
            obtain ⟨j0, hj0, -⟩ := h
            exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
        obtain ⟨h1, h2⟩ := hlev0 hlev
        have hsr0 : srow Z (Z.length - 1) = 0 := by
          unfold srow; rw [hclast 1, hclast 2]
          show (if 0 < c.2.2 then 2 else if 0 < c.2.1 then 1 else 0) = 0
          simp [h1, h2]
        by_cases hZ1 : Z.length = 1
        · have hdl := hdrop1 hZ1
          exact hflat' h1 h2 (hc10 hZ1) (by rw [hdl]; exact Wg_nil _) (by rw [hdl]; exact hnil)
        · have h0 : c.1 = 0 := by
            by_contra hne
            have hc10' : entry Z 0 (Z.length - 1) = c.1 := hclast 0
            exact hp ⟨by omega, by
              rw [hsr0]
              exact (hasParent_zero_iff (by omega)).mpr ⟨0, by omega, by rw [hb0, hc10']; omega⟩⟩
          have h1' := hop 1 le_rfl
          rw [oper_one_eq_dropLast (by omega)] at h1'
          exact hflat' h1 h2 h0 h1'.1 (h1'.2 (based_dropLast hb))
    · have hlev := hd.1
      unfold lev at hlev
      have h20' : entry Z 2 (Z.length - 1) = 0 := h20
      have hj1 : 1 ≤ entry Z 1 (Z.length - 1) := by omega
      have hjv : entry Z 1 (Z.length - 1) ≤ u := by omega
      have hm' : m' = 2 * entry Z 1 (Z.length - 1) - 1 := by omega
      subst hm'
      have hsr : srow Z (Z.length - 1) = 1 := by
        unfold srow; rw [if_neg (by omega), if_pos (by omega)]
      have hnp : ¬ hasParent Z 1 (Z.length - 1) := fun hh => hd.2 (by rw [hsr]; exact hh)
      have hc1' : c.2.1 = entry Z 1 (Z.length - 1) := (hclast 1).symm
      have hc20 : c.2.2 = 0 := by have := hclast 2; rw [h20'] at this; exact this.symm
      generalize hjdef : entry Z 1 (Z.length - 1) = j at hj1 hjv hc1' hgr hnp
      have hcj : c = ((c.1, j, 0) : ℕ × ℕ × ℕ) := Prod.ext rfl (Prod.ext hc1' hc20)
      have eZ : Z = Z.dropLast ++ [((c.1, j, 0) : ℕ × ℕ × ℕ)] := by
        conv_lhs => rw [hsplit, hcj]
      have hlenD : Z.dropLast.length = Z.length - 1 := by simp
      have key2 : Q (Z.dropLast ++ [((c.1, j, 0) : ℕ × ℕ × ℕ)]) := by
        refine horph Z.dropLast c.1 j (by rw [← eZ]; exact hZW) (by rw [← eZ]; exact hb) hj1 hjv
          (by rw [← eZ, hlenD]; exact hnp) (fun z hz hbz => ?_)
        have h1 := hgr z hz hbz
        have e : graft Z z = Z.dropLast ++ shiftr01 c.1 0 z := by
          rw [graft_eq_shift, hclast 0]; rfl
        have hbg := based_graft_arg hZnil hb hbz
        rw [e] at h1 hbg
        exact ⟨h1.1, h1.2 hbg⟩
      rw [eZ]; exact key2
  intro Z hZ hb
  exact (key hZ).2 hb

/-! ## F のタイの子の段（GpT の段） -/

theorem child_oper_step {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (f : ℕ → ℕ) {b r : ℕ} {H P D Z : TrioSeq} (hP : Fr P) (hD : Fr D)
    (hlen : 2 ≤ Z.length) (hp : hasParent Z (srow Z (Z.length - 1)) (Z.length - 1))
    (hIH : ∀ m, 1 ≤ m → GpT A o f b (P ++ fwH b r H b
      (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ shiftr01 1 0 (Z⟦m⟧))))) :
    GpT A o f b (P ++ fwH b r H b
      (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ shiftr01 1 0 Z))) := by
  have hlenS : 2 ≤ (shiftr01 1 0 Z).length := by rw [shiftr01_length]; exact hlen
  have hpS : hasParent (shiftr01 1 0 Z) (srow (shiftr01 1 0 Z) ((shiftr01 1 0 Z).length - 1))
      ((shiftr01 1 0 Z).length - 1) := by
    rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hp
  have hSne : shiftr01 1 0 Z ≠ [] := by
    intro h; rw [h] at hlenS; simp at hlenS
  show GpT A o f b (P ++ fwH b r H b
    ([] ++ ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ shiftr01 1 0 Z)))
  refine fwH_oper_step hA hA1 ho f hP Fr_nil (Fr_node _ _) (Hd_node _ _)
    (by simp only [List.length_cons, shiftr01_length, List.length_append]; omega)
    (node_hasParent _ D _ hpS hSne) (fun m hm => ?_)
  rw [List.nil_append, node_oper _ D _ hlenS hpS m]
  have e := oper_shift [] Z 1 m hlen hp
  simp only [List.nil_append] at e
  rw [e]
  exact hIH m hm

theorem child_orph_step {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (f : ℕ → ℕ) {b r : ℕ} (hbr : b < r) {H P D Z : TrioSeq} (hH : Fr H) (hP : Fr P)
    (hD : Fr D) {h j : ℕ} (hbZ : based (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) (hj1 : 1 ≤ j)
    (hj : j ≤ b) (hnp : ¬ hasParent (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 Z.length)
    (hz : ∀ z ∈ Wg (2 * j - 1), based z → GpT A o f b (P ++ fwH b r H b
      (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ shiftr01 1 0 (Z ++ shiftr01 h 0 z))))) :
    GpT A o f b (P ++ fwH b r H b (((1, r, 0) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (D ++ shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])))) := by
  obtain ⟨U, hU⟩ : ∃ U : TrioSeq,
      U = ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ shiftr01 1 0 Z) := ⟨_, rfl⟩
  have eAB : U ++ [((h + 2, j, 0) : ℕ × ℕ × ℕ)] = (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) ++
      shiftr01 1 0 (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
    rw [hU]; simp [shiftr01, Function.comp_def, Nat.add_assoc]
  have eN : ((1, r, 0) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (D ++ shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
      = U ++ [((h + 2, j, 0) : ℕ × ℕ × ℕ)] := by
    rw [hU]; simp [shiftr01, Function.comp_def, Nat.add_assoc]
  have eZ : ∀ z : TrioSeq, ((1, r, 0) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (D ++ shiftr01 1 0 (Z ++ shiftr01 h 0 z)) = U ++ shiftr01 (h + 2) 0 z := by
    intro z; rw [hU]; simp [shiftr01, Function.comp_def, Nat.add_assoc]
  have hlenU : U.length = (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D).length + Z.length := by
    rw [hU]; simp only [List.length_cons, List.length_append, shiftr01_length]; omega
  rw [eN]
  show GpT A o f b (P ++ fwH b r H b ([] ++ (U ++ [((h + 2, j, 0) : ℕ × ℕ × ℕ)])))
  refine fwH_orph_step hA hA1 ho f (u := b) le_rfl hbr hH hP Fr_nil
    (by rw [← eN]; exact Fr_node _ _) (by rw [← eN]; exact Hd_node _ _) hj1 hj ?_
    (fun z hz' hbz => ?_)
  · have hZl : Z.length < (shiftr01 1 0 (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))).length := by
      simp [shiftr01]
    have hBH : Hd (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := by
      intro _
      rw [entry0_shiftr01 (by simp)]
      have : entry (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 0 0 = 0 := hbZ
      omega
    rw [eAB, hlenU]
    refine noParent_ctx (j := j) hZl (fun k hk hrt => ?_) ?_ ?_
    · have := node_anc_row1 hD hBH (by simp [shiftr01]) hk hZl hrt
      subst this
      show j ≤ r
      omega
    · rw [entry1_shiftr01, entry1_shiftr01, show Z.length = Z.length + 0 from rfl,
        entry_append_right]
      rfl
    · rw [hasParent_shiftr01, hasParent_shiftr01]
      exact hnp
  · rw [List.nil_append, ← eZ z]
    exact hz z hz' hbz

theorem child_flat_step {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a)
    (ho : 1 ≤ o) (f : ℕ → ℕ) {b r : ℕ} {H P D : TrioSeq} (hH : Fr H) (hP : Fr P) (hD : Fr D)
    (hrep : ∀ m, GpT A o f b (P ++ fwH b r (H ++ (List.range m).flatMap
      (fun _ => ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D)) b [])) :
    GpT A o f b (P ++ fwH b r H b
      (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]))) := by
  obtain ⟨M, hM⟩ : ∃ M : TrioSeq, M = ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D := ⟨_, rfl⟩
  have eN : ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
      = M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
    rw [hM]; simp [shiftr01]
  have eF : ∀ Y, fwH b r H b Y = ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (H ++ Y) := by
    intro Y; unfold fwH; rw [Nat.sub_self, mlift_zero]
  rw [eN, eF]
  have hMne : M ≠ [] := by rw [hM]; simp
  have hMpos : 0 < M.length := List.length_pos_iff.mpr hMne
  have hhead : entry M 0 0 < 2 := by rw [hM]; show 1 < 2; omega
  have htail : ∀ r', 1 ≤ r' → r' < M.length → 2 ≤ entry M 0 r' := by
    intro r' hr1 hr2
    obtain ⟨w, rfl⟩ : ∃ w, r' = w + 1 := ⟨r' - 1, by omega⟩
    have hw' : w < D.length := by
      rw [hM] at hr2; simp only [List.length_cons, shiftr01_length] at hr2; omega
    rw [hM, entry_cons, entry0_shiftr01 hw']
    have := getD_row0_ge hD hw'
    omega
  have hlen2 : 2 ≤ (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length := by simp; omega
  have hlast : hasParent (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)])
      (srow (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1))
      ((M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
    have hidx : (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1 = M.length + 0 := by simp
    rw [hidx, srow_append_right]
    have hs : srow [((2, 0, 0) : ℕ × ℕ × ℕ)] 0 = 0 := rfl
    rw [hs]
    refine (hasParent_zero_iff (by simp)).mpr ⟨0, by omega, ?_⟩
    rw [Small.entry_append_left hMpos, entry_append_right]
    exact hhead
  refine (GpT_ax hA hA1 ho f).oper b P
    (((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (H ++ (M ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]))) hP
    (Fr_letter _ _) (Hd_letter _ _) ?_ (node_hasParent _ H _ hlast (by simp)) (fun m hm => ?_)
  · simp only [List.length_cons, shiftr01_length, List.length_append]; omega
  · rw [node_oper _ H _ hlen2 hlast m]
    have eO := oper_snoc00'' [] hMne hhead htail m
    simp only [List.nil_append] at eO
    rw [eO, hM]
    have := hrep m
    unfold fwH at this
    rwa [Nat.sub_self, mlift_zero, List.append_nil] at this

/-! ## 語の並びの形 -/

theorem fwH_FTL0_snoc (b r : ℕ) (X : List TrioSeq) (D : TrioSeq) (c0 : ℕ) :
    fwH b r (FTL0 r (X ++ [D])) c0 []
      = fwH b r (FTL0 r X) b (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) := by
  simp only [fwH, FTL0_snoc, mlift_nil, Nat.sub_self, mlift_zero, List.append_nil]

theorem farW0_child (b r : ℕ) (A0 : List ℕ) (H g : ℕ → ℕ)
    (ws : List (List TrioSeq × ℕ × TrioSeq)) (X : List TrioSeq) (D : TrioSeq) (c0 : ℕ) :
    farW0 b r (relWs0 A0 H g (ws ++ [(X ++ [D], c0, [])]))
      = farW0 b r (relWs0 A0 H g ws) ++
        fwH b r (FTL0 r X) b (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) := by
  have e0 : reliftX c0 H g A0 ([] : TrioSeq) = [] := by unfold reliftX; exact slift_nil _
  simp only [relWs0_snoc, farW0_snoc]
  rw [e0, fwH_FTL0_snoc]

theorem farW0_nilY (b r : ℕ) (A0 : List ℕ) (H g : ℕ → ℕ)
    (ws : List (List TrioSeq × ℕ × TrioSeq)) (Y : List TrioSeq) (c0 : ℕ) :
    farW0 b r (relWs0 A0 H g (ws ++ [(Y, c0, [])]))
      = farW0 b r (relWs0 A0 H g ws) ++ fwH b r (FTL0 r Y) b [] := by
  have e0 : reliftX c0 H g A0 ([] : TrioSeq) = [] := by unfold reliftX; exact slift_nil _
  simp only [relWs0_snoc, farW0_snoc]
  rw [e0]
  simp [fwH, mlift_nil]

theorem FTL0_rep (r : ℕ) (X : List TrioSeq) (D : TrioSeq) : ∀ m,
    FTL0 r (X ++ List.replicate m D)
      = FTL0 r X ++ (List.range m).flatMap (fun _ => ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D)
  | 0 => by simp
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, FTL0_snoc, FTL0_rep r X D m, List.range_succ,
        List.flatMap_append]
      simp

theorem RawWsA0_child {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} {X : List TrioSeq} {D D' : TrioSeq} {c0 : ℕ}
    (hR : RawWsA0 A0 k0 H b (ws ++ [(X ++ [D], c0, [])])) (hD' : Fr D' ∧ LowC b D') :
    RawWsA0 A0 k0 H b (ws ++ [(X ++ [D'], c0, [])]) := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact hR w (List.mem_append_left _ hw)
  · rw [List.mem_singleton] at hw
    subst hw
    have h1 := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
    refine ⟨h1.1, fun Ld hLd => ?_, h1.2.2⟩
    rcases List.mem_append.mp hLd with hLd | hLd
    · exact h1.2.1 Ld (List.mem_append_left _ hLd)
    · rw [List.mem_singleton] at hLd
      rw [hLd]; exact hD'

theorem RawWsA0_rep {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List TrioSeq × ℕ × TrioSeq)} {X : List TrioSeq} {D0 D : TrioSeq} {c0 : ℕ}
    (hR : RawWsA0 A0 k0 H b (ws ++ [(X ++ [D0], c0, [])])) (hD : Fr D ∧ LowC b D) (m : ℕ) :
    RawWsA0 A0 k0 H b (ws ++ [(X ++ List.replicate m D, c0, [])]) := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact hR w (List.mem_append_left _ hw)
  · rw [List.mem_singleton] at hw
    subst hw
    have h1 := hR _ (List.mem_append_right _ (List.mem_singleton_self _))
    refine ⟨h1.1, fun Ld hLd => ?_, h1.2.2⟩
    rcases List.mem_append.mp hLd with hLd | hLd
    · exact h1.2.1 Ld (List.mem_append_left _ hLd)
    · rw [List.eq_of_mem_replicate hLd]; exact hD

/-! ## 子の良さ -/

def GoodL (v : ℕ) (Lds : List TrioSeq) : Prop :=
  ∀ (A0 : List ℕ) (k0 : ℕ), (∀ a ∈ A0, 1 ≤ a) → 1 ≤ k0 →
    ∀ (H : ℕ → ℕ) (b0 c0 : ℕ), v ≤ c0 → GTWA0 A0 k0 H b0 Lds c0 []

def ChildG (v : ℕ) (D : TrioSeq) : Prop := ∀ X, GoodL v X → GoodL v (X ++ [D])

theorem GoodL_nil (v : ℕ) : GoodL v [] := fun A0 k0 _ _ H b0 c0 _ => GTWA0_nil0 A0 k0 H b0 c0

theorem ChildG_nil (v : ℕ) : ChildG v [] :=
  fun _ hX _ _ hA01 hk1 H b0 c0 hv => GTWA0_Fsucc hX hA01 hk1 H b0 c0 hv

theorem GoodL_rep {v : ℕ} {D : TrioSeq} (hD : ChildG v D) {X : List TrioSeq} (hX : GoodL v X) :
    ∀ m, GoodL v (X ++ List.replicate m D)
  | 0 => by simpa using hX
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc]
      exact hD _ (GoodL_rep hD hX m)

theorem lowS {v : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg (2 * v)) : LowC v (shiftr01 1 0 Z) :=
  low_of_Wg hZ 1 le_rfl

/-- ★ 最後の F のタイの子に荷を足す規則。 -/
theorem ChildG_load {v : ℕ} : ∀ Z ∈ Wg (2 * v), based Z →
    ∀ Ld, Fr Ld → LowC v Ld → ChildG v Ld → ChildG v (Ld ++ shiftr01 1 0 Z) := by
  refine based_Wg_ind (u := v)
    (Q := fun Z => ∀ Ld, Fr Ld → LowC v Ld → ChildG v Ld → ChildG v (Ld ++ shiftr01 1 0 Z))
    ?_ ?_ ?_ ?_
  · intro Ld _ _ hLd
    simpa [shiftr01] using hLd
  · intro Z hZW _ hIH Ld hFr hLow hLd
    obtain ⟨D, hD⟩ : ∃ D, D = Ld ++ shiftr01 1 0 Z := ⟨_, rfl⟩
    have hDG : ChildG v D := by rw [hD]; exact hIH Ld hFr hLow hLd
    have hDFr : Fr D := by rw [hD]; exact Fr_append hFr (Fr_shift1 _)
    have hDLow : LowC v D := by rw [hD]; exact LowC_append hLow (lowS hZW)
    have eD : Ld ++ shiftr01 1 0 (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])
        = D ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
      rw [hD]; simp [shiftr01]
    show ChildG v (Ld ++ shiftr01 1 0 (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))
    rw [eD]
    intro X hX A0 k0 hA01 hk1 H b0 c0 hv ws hC g S o f b hf hb hR hSA hA hA1 ho hK hKo
    have hc0 : c0 ≤ b := (hR _ (List.mem_append_right _ (List.mem_singleton_self _))).1
    rw [farW0_child]
    refine child_flat_step hA hA1 ho f (Fr_FTL0 _ _) (Fr_farW0 _ _ _) hDFr (fun m => ?_)
    rw [← FTL0_rep _ X D m]
    have hG := GoodL_rep hDG hX m A0 k0 hA01 hk1 H b0 c0 hv ws hC g S o f b hf hb
      (RawWsA0_rep hR ⟨hDFr, LowC_mono (by omega) hDLow⟩ m) hSA hA hA1 ho hK hKo
    rwa [farW0_nilY] at hG
  · intro Z hZW hbZ hlen hp hIH Ld hFr hLow hLd X hX A0 k0 hA01 hk1 H b0 c0 hv ws hC g S o f b hf
      hb hR hSA hA hA1 ho hK hKo
    have hc0 : c0 ≤ b := (hR _ (List.mem_append_right _ (List.mem_singleton_self _))).1
    rw [farW0_child]
    refine child_oper_step hA hA1 ho f (Fr_farW0 _ _ _) hFr hlen hp (fun m hm => ?_)
    have hm' := hIH m hm
    have := hm'.2 Ld hFr hLow hLd X hX A0 k0 hA01 hk1 H b0 c0 hv ws hC g S o f b hf hb
      (RawWsA0_child hR ⟨Fr_append hFr (Fr_shift1 _),
        LowC_mono (by omega) (LowC_append hLow (lowS hm'.1))⟩) hSA hA hA1 ho hK hKo
    rwa [farW0_child] at this
  · intro Z h j _ hbZ hj1 hjv hnp hz Ld hFr hLow hLd X hX A0 k0 hA01 hk1 H b0 c0 hv ws hC g S o f
      b hf hb hR hSA hA hA1 ho hK hKo
    have hc0 : c0 ≤ b := (hR _ (List.mem_append_right _ (List.mem_singleton_self _))).1
    rw [farW0_child]
    refine child_orph_step hA hA1 ho f (show b < b + liftOff f (S ++ A0) o + 1 by omega)
      (Fr_FTL0 _ _) (Fr_farW0 _ _ _) hFr hbZ hj1 (by omega) hnp (fun z hz' hbz => ?_)
    have hzz := hz z hz' hbz
    have := hzz.2 Ld hFr hLow hLd X hX A0 k0 hA01 hk1 H b0 c0 hv ws hC g S o f b hf hb
      (RawWsA0_child hR ⟨Fr_append hFr (Fr_shift1 _),
        LowC_mono (by omega) (LowC_append hLow (lowS hzz.1))⟩) hSA hA hA1 ho hK hKo
    rwa [farW0_child] at this

/-! ## 荷だけの子 -/

theorem ChildG_units {v : ℕ} : ∀ us : List (Option TrioSeq), GzJ.NoTie us → RawU v us →
    ChildG v (unitsC v us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact ChildG_nil v
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : GzJ.NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          have hu := HaT.units_ok v us hNT' (RawU_prefix hR)
          rw [unitsC_snoc]
          exact ChildG_load Z hZ.1 hZ.2 _ hu.1.1 hu.2 (ih hNT' (RawU_prefix hR))

def LdsOK (v : ℕ) (uss : List (List (Option TrioSeq))) : Prop :=
  ∀ us ∈ uss, GzJ.NoTie us ∧ RawU v us

/-- ★ F のタイの子が荷だけの並びは、全ての級で良い。 -/
theorem GoodL_units {v : ℕ} : ∀ uss : List (List (Option TrioSeq)), LdsOK v uss →
    GoodL v (uss.map (unitsC v)) := by
  intro uss
  induction uss using List.reverseRecOn with
  | nil => intro _; exact GoodL_nil v
  | append_singleton uss us ih =>
      intro h
      have hus := h us (List.mem_append_right _ (List.mem_singleton_self _))
      rw [List.map_append, List.map_singleton]
      exact ChildG_units us hus.1 hus.2 _ (ih (fun us' h' => h us' (List.mem_append_left _ h')))

end HbU
end TRIO
