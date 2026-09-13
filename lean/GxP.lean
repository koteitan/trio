/-
GxP.lean: 差し込み口の公理と、差し込み口によらないタイの子の並びの良さ。

差し込み口 = 子の並び W についての段つき述語 ok u W。公理 SlotAx は、W の後ろに足す単位 U の
最後の列の展開の場合分け（U の中の親・行 1 が段以下の孤児・錐のタイ・差し込み口の直下の平らな列）と
持ち上げで閉じていること。

- 最上段（字の中身）: ok u W := GTall u W は公理を満たす（topSlot_ax）。
- どの差し込み口も荷（Wg の元を 1 段ずらしたもの）の追加で閉じる（slot_load）。
-/
import GxN

namespace TRIO
namespace GxP

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ
open GxD
open GxG
open GxJ
open GxK
open GxL
open GxN

def Fr (W : TrioSeq) : Prop := ∀ x ∈ W, 1 ≤ x.1

def Hd (U : TrioSeq) : Prop := U ≠ [] → entry U 0 0 = 1

structure SlotAx (ok : ℕ → TrioSeq → Prop) : Prop where
  lift : ∀ u W, Fr W → ok u W → ∀ u', u ≤ u' → ok u' (mlift W u (u' - u))
  oper : ∀ u W U, Fr W → Fr U → Hd U → 2 ≤ U.length →
    hasParent U (srow U (U.length - 1)) (U.length - 1) →
    (∀ m, 1 ≤ m → ok u (W ++ U⟦m⟧)) → ok u (W ++ U)
  orph : ∀ u W U h j, Fr W → Fr (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) →
    Hd (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) → 1 ≤ j → j ≤ u →
    ¬ hasParent (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1 U.length →
    (∀ z ∈ Wg (2 * j - 1), based z → ok u (W ++ (U ++ shiftr01 h 0 z))) →
    ok u (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
  tie : ∀ u W U x, Fr W → Fr (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) →
    Hd (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) →
    coneV (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u U.length →
    (∀ u', u ≤ u' → ∀ Z ∈ Wg (2 * u'), based Z →
      ok u' (mlift (W ++ U) u (u' - u) ++ shiftr01 x 0 Z)) →
    ok u (W ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]))
  flat : ∀ u W, Fr W → ok u W → ok u (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])

theorem shiftr01_zero' (U : TrioSeq) : shiftr01 0 0 U = U := by simp [shiftr01]

theorem Fr_append {A B : TrioSeq} (hA : Fr A) (hB : Fr B) : Fr (A ++ B) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hA x hx
  · exact hB x hx

theorem rsum_of_Hd {W U : TrioSeq} (hW : Fr W) (hU : Fr U) (hH : Hd U) : rsum W U := by
  intro p hp
  by_cases hUn : U = []
  · subst hUn; simp [entry]
  · rw [hH hUn]
    rcases List.mem_append.mp hp with hp | hp
    · exact hW p hp
    · exact hU p hp

/-! ## 最上段 -/

theorem topSlot_ax : SlotAx (fun u W => GTall u W) where
  lift := fun u W _ h u' hu => GTall_lift h hu
  oper := by
    intro u W U hW hU hH hlen hp hIH
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    have hlenC : 2 ≤ (W ++ U).length := by simp; omega
    have hidx : (W ++ U).length - 1 = W.length + (U.length - 1) := by simp; omega
    have hpC : hasParent (W ++ U) (srow (W ++ U) ((W ++ U).length - 1)) ((W ++ U).length - 1) := by
      rw [hidx, srow_append_right, hasParent_append_gen (by omega) (rsum_of_Hd hW hU hH)]
      exact hp
    refine GTall_oper hlenC hpC (fun m hm => ?_)
    have e := oper_shift W U 0 m hlen hp
    rw [shiftr01_zero', shiftr01_zero'] at e
    rw [e]; exact hIH m hm
  orph := by
    intro u W U h j hW hU hH hj1 hj hnp hz
    rw [← List.append_assoc]
    refine GTall_orph hj1 hj ?_ (fun z hz' hbz => by rw [List.append_assoc]; exact hz z hz' hbz)
    intro hh
    apply hnp
    have hidx : (W ++ U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1 = W.length + U.length := by simp
    rw [hidx, List.append_assoc, hasParent_append_gen (by simp) (rsum_of_Hd hW hU hH)] at hh
    exact hh
  tie := by
    intro u W U x hW hU hH hc hload
    rw [← List.append_assoc]
    refine GTall_tie ?_ hload
    have h := (coneV_append_right (A := W) (B := U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])
      (q := U.length) (by simp) (fun y hy => by rw [hH (by simp)]; exact hW y hy)).mpr hc
    rw [← List.append_assoc] at h
    simpa using h
  flat := fun u W hW h => GTall_flat le_rfl hW hW h

#print axioms topSlot_ax

/-! ## 荷の閉包 -/

theorem slot_load {ok : ℕ → TrioSeq → Prop} (hA : SlotAx ok) {u : ℕ} {W : TrioSeq}
    (hW : Fr W) (hok : ok u W) :
    ∀ Z ∈ Wg (2 * u), based Z → ok u (W ++ shiftr01 1 0 Z) := by
  have key : Wg (2 * u) ⊆ {Z : TrioSeq | Z ∈ Wg (2 * u) ∧
      (based Z → ok u (W ++ shiftr01 1 0 Z))} := by
    refine A2g' ?_
    intro Z hAZ
    have hZW : Z ∈ Wg (2 * u) := A1g_intro (Aopg_mono_X hAZ (fun U hU => hU.1))
    refine ⟨hZW, ?_⟩
    intro hb
    have hb0 : entry Z 0 0 = 0 := hb
    by_cases hZnil : Z = []
    · subst hZnil; simpa [shiftr01] using hok
    have hZlen : 0 < Z.length := List.length_pos_iff.mpr hZnil
    have hFrS : ∀ Y : TrioSeq, Fr (shiftr01 1 0 Y) := by
      intro Y x hx
      simp only [shiftr01, List.mem_map] at hx
      obtain ⟨p, -, rfl⟩ := hx
      dsimp only; omega
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
    have hHdS : Hd (shiftr01 1 0 Z) := by
      intro _
      rw [entry0_shiftr01 hZlen, hb0]
    have hflat : c.2.1 = 0 → c.2.2 = 0 → c.1 = 0 → ok u (W ++ shiftr01 1 0 Z.dropLast) →
        ok u (W ++ shiftr01 1 0 Z) := by
      intro h1 h2 h0 hd
      have hceq : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext h0 (Prod.ext h1 h2)
      have e : W ++ shiftr01 1 0 Z
          = (W ++ shiftr01 1 0 Z.dropLast) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
        conv_lhs => rw [hsplit, hceq]
        rw [shiftr01_append0, shift_col, List.append_assoc]
      rw [e]
      exact hA.flat u _ (Fr_append hW (hFrS _)) hd
    have hdrop1 : Z.length = 1 → ok u (W ++ shiftr01 1 0 Z.dropLast) := by
      intro hZ1
      have hdl : Z.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      rw [hdl]; simpa [shiftr01] using hok
    rcases hAZ with ⟨hl, hw0⟩ | ⟨hnat, hop⟩ | ⟨m', hm, hd, h20, hgr⟩
    · have hZ1 : Z.length = 1 := by omega
      have hz : lev Z (Z.length - 1) = 0 := by rw [hZ1]; exact hw0
      exact hflat (hlev0 hz).1 (hlev0 hz).2 (hc10 hZ1) (hdrop1 hZ1)
    · by_cases hp : 2 ≤ Z.length ∧ hasParent Z (srow Z (Z.length - 1)) (Z.length - 1)
      · obtain ⟨hlen2, hp⟩ := hp
        refine hA.oper u W (shiftr01 1 0 Z) hW (hFrS _) hHdS (by rw [shiftr01_length]; exact hlen2)
          (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hp) (fun n hn => ?_)
        have e := oper_shift [] Z 1 n hlen2 hp
        simp only [List.nil_append] at e
        rw [e]
        exact (hop n hn).2 (based_oper hn hb)
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
        · exact hflat h1 h2 (hc10 hZ1) (hdrop1 hZ1)
        · have h0 : c.1 = 0 := by
            by_contra hne
            have hc10' : entry Z 0 (Z.length - 1) = c.1 := hclast 0
            exact hp ⟨by omega, by
              rw [hsr0]
              exact (hasParent_zero_iff (by omega)).mpr ⟨0, by omega, by rw [hb0, hc10']; omega⟩⟩
          have h1' := (hop 1 le_rfl).2 (based_oper le_rfl hb)
          rw [oper_one_eq_dropLast (by omega)] at h1'
          exact hflat h1 h2 h0 h1'
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
      have eZ : shiftr01 1 0 Z = shiftr01 1 0 Z.dropLast ++ [((c.1 + 1, j, 0) : ℕ × ℕ × ℕ)] := by
        conv_lhs => rw [hsplit, hcj]
        rw [shiftr01_append0, shift_col]
      rw [eZ]
      refine hA.orph u W (shiftr01 1 0 Z.dropLast) (c.1 + 1) j hW (by rw [← eZ]; exact hFrS _)
        (by rw [← eZ]; exact hHdS) hj1 hjv ?_ (fun z hz hbz => ?_)
      · intro hh
        apply hnp
        rw [← eZ, show (shiftr01 1 0 Z.dropLast).length = Z.length - 1 by
          rw [shiftr01_length]; simp, hasParent_shiftr01] at hh
        exact hh
      · have h1 := (hgr z hz hbz).2 (based_graft_arg hZnil hb hbz)
        have e : graft Z z = Z.dropLast ++ shiftr01 c.1 0 z := by
          rw [graft_eq_shift, hclast 0]; rfl
        rw [e, shiftr01_append0, shiftr01_add0] at h1
        exact h1
  intro Z hZ hb
  exact (key hZ).2 hb

#print axioms slot_load


/-! ## 節点の下の差し込み口 -/

theorem Fr_node (r : ℕ) (W : TrioSeq) : Fr (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 W) := by
  intro x hx
  simp only [List.mem_cons, shiftr01, List.mem_map] at hx
  rcases hx with rfl | ⟨p, -, rfl⟩
  · show 1 ≤ 1; omega
  · dsimp only; omega

theorem Hd_node (r : ℕ) (W : TrioSeq) : Hd (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 W) :=
  fun _ => rfl

theorem mlift_app {W U : TrioSeq} (hW : Fr W) (hU : Hd U) (u t : ℕ) :
    mlift (W ++ U) u t = mlift W u t ++ mlift U u t := by
  refine mlift_append (fun x hx => ?_) u t
  by_cases hUn : U = []
  · subst hUn; simp [entry]
  · rw [hU hUn]; exact hW x hx

theorem Fr_mlift {W : TrioSeq} (hW : Fr W) (u t : ℕ) : Fr (mlift W u t) := mlift_row0 hW u t

open Classical in
theorem Hd_mlift {U : TrioSeq} (hU : Hd U) (u t : ℕ) : Hd (mlift U u t) := by
  intro hne
  have hUne : U ≠ [] := by intro h; apply hne; subst h; exact mlift_nil u t
  have hl : 0 < U.length := List.length_pos_iff.mpr hUne
  show ((mlift U u t).getD 0 (0, 0, 0)).1 = 1
  rw [mlift_getD hl]
  exact hU hUne

theorem Hd_oper {U : TrioSeq} (hU : Hd U) (hUne : U ≠ []) {m : ℕ} (hm : 1 ≤ m) : Hd (U⟦m⟧) := by
  intro _
  rw [oper_head_eq hm]; exact hU hUne

theorem Fr_oper {U : TrioSeq} (hU : Fr U) (m : ℕ) : Fr (U⟦m⟧) := oper_mem_ge (c := 1) hU

theorem mlift_oper' (U : TrioSeq) (u t m : ℕ) : (mlift U u t)⟦m⟧ = mlift (U⟦m⟧) u t := by
  rw [mlift_eq_slift, mlift_eq_slift, slift_oper (stair_step u t)]

theorem hasParent_mlift_iff {U : TrioSeq} (u t : ℕ) (hU : U ≠ []) :
    hasParent (mlift U u t) (srow (mlift U u t) ((mlift U u t).length - 1))
      ((mlift U u t).length - 1) ↔
    hasParent U (srow U (U.length - 1)) (U.length - 1) := by
  have hl : 0 < U.length := List.length_pos_iff.mpr hU
  rw [mlift_length, mlift_eq_slift, hasParent_slift (stair_step u t),
    srow_slift (stair_step u t) (by omega)]

theorem node_oper (r : ℕ × ℕ × ℕ) (W U : TrioSeq) (hlen : 2 ≤ U.length)
    (hp : hasParent U (srow U (U.length - 1)) (U.length - 1)) (m : ℕ) :
    (r :: shiftr01 1 0 (W ++ U))⟦m⟧ = r :: shiftr01 1 0 (W ++ U⟦m⟧) := by
  have e1 : r :: shiftr01 1 0 (W ++ U) = (r :: shiftr01 1 0 W) ++ shiftr01 1 0 U := by
    rw [shiftr01_append0]; rfl
  have e2 : r :: shiftr01 1 0 (W ++ U⟦m⟧) = (r :: shiftr01 1 0 W) ++ shiftr01 1 0 (U⟦m⟧) := by
    rw [shiftr01_append0]; rfl
  rw [e1, e2, oper_shift _ U 1 m hlen hp]

theorem node_hasParent (r : ℕ × ℕ × ℕ) (W U : TrioSeq)
    (hp : hasParent U (srow U (U.length - 1)) (U.length - 1)) (hU : U ≠ []) :
    hasParent (r :: shiftr01 1 0 (W ++ U))
      (srow (r :: shiftr01 1 0 (W ++ U)) ((r :: shiftr01 1 0 (W ++ U)).length - 1))
      ((r :: shiftr01 1 0 (W ++ U)).length - 1) := by
  have hl : 0 < U.length := List.length_pos_iff.mpr hU
  have e1 : r :: shiftr01 1 0 (W ++ U) = (r :: shiftr01 1 0 W) ++ shiftr01 1 0 U := by
    rw [shiftr01_append0]; rfl
  rw [e1]
  have hidx : ((r :: shiftr01 1 0 W) ++ shiftr01 1 0 U).length - 1
      = (r :: shiftr01 1 0 W).length + (U.length - 1) := by simp [shiftr01]; omega
  rw [hidx, srow_append_right, srow_shiftr01]
  exact hasParent_append_right_of _ _ (hasParent_shiftr01.mpr hp)

open Classical in
theorem mlift_cons_root {X : TrioSeq} (hX : ∀ x ∈ X, 1 ≤ x.1) {v B : ℕ} (hB : v < B)
    (t z : ℕ) :
    mlift (((0, B, z) : ℕ × ℕ × ℕ) :: X) v t = ((0, B + t, z) : ℕ × ℕ × ℕ) :: mlift X v t := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [mlift_length] at hi
  rw [mlift_getD hi]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · have hc : coneV (((0, B, z) : ℕ × ℕ × ℕ) :: X) v 0 := by
      rw [coneV_iff_amin, amin_zero]; simpa [entry] using hB
    rw [if_pos hc]
    simp [entry]
  · obtain ⟨j, rfl⟩ : ∃ j, i = 1 + j := ⟨i - 1, by omega⟩
    have hj : j < X.length := by simp at hi; omega
    have e : ∀ r, entry (((0, B, z) : ℕ × ℕ × ℕ) :: X) r (1 + j) = entry X r j := by
      intro r; rw [show 1 + j = j + 1 by omega, entry_cons]
    rw [e 0, e 1, e 2]
    have eg : (((0, B + t, z) : ℕ × ℕ × ℕ) :: mlift X v t).getD (1 + j) (0, 0, 0)
        = (mlift X v t).getD j (0, 0, 0) := by
      rw [show 1 + j = j + 1 by omega]; rfl
    rw [eg, mlift_getD hj]
    have hiff := coneV_cons_iff (B := B) (z := z) (v := v) (fun p hp => hX p hp) hj
    by_cases hc : coneV X v j
    · rw [if_pos (hiff.mpr ⟨hB, hc⟩), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.mp h).2), if_neg hc]

theorem mlift_node {u r : ℕ} (hr : u < r) {V : TrioSeq} (hV : Fr V) (t : ℕ) :
    mlift (((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V) u t
      = ((1, r + t, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift V u t) := by
  have e1 : ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V
      = shiftr01 1 0 (((0, r, 0) : ℕ × ℕ × ℕ) :: V) := by simp [shiftr01]
  have e2 : ((1, r + t, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift V u t)
      = shiftr01 1 0 (((0, r + t, 0) : ℕ × ℕ × ℕ) :: mlift V u t) := by simp [shiftr01]
  rw [e1, e2, mlift_shift0, mlift_cons_root hV hr]

/-- 行 1 が u' + k の節点を差し込み口 P に足したときの、その節点の子の差し込み口。 -/
def nslot (P : ℕ → TrioSeq → Prop) (k : ℕ) : ℕ → TrioSeq → Prop :=
  fun u W => ∀ u', u ≤ u' → ∀ X, Fr X → P u' X →
    P u' (X ++ ((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u)))

theorem node_split (r : ℕ × ℕ × ℕ) (A B : TrioSeq) :
    r :: shiftr01 1 0 (A ++ B) = (r :: shiftr01 1 0 A) ++ shiftr01 1 0 B := by
  rw [shiftr01_append0]; rfl

/-- 節点 (1, r, 0) :: A↑1 の後ろに B↑1 を足した列で、A↑1 の列は B↑1 の列の祖先にならない。 -/
theorem node_anc_row1 {r : ℕ} {A B : TrioSeq} (hA : Fr A) (hBH : Hd B) (hBne : B ≠ [])
    {k b : ℕ} (hk : k < ((((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 A)).length)
    (hb : b < (shiftr01 1 0 B).length)
    (h : Relation.ReflTransGen (nextrel0 ((((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 A) ++
      shiftr01 1 0 B)) k ((((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 A).length + b)) :
    k = 0 := by
  by_contra hk0
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hrec := rtg0_rec h ((((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 A)).length hk (by omega)
  rw [Small.entry_append_left hk, show ((((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 A)).length
      = ((((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 A)).length + 0 from rfl,
    entry_append_right, entry_cons] at hrec
  have hk' : k' < A.length := by simp [shiftr01] at hk; omega
  have hBl : 0 < B.length := List.length_pos_iff.mpr hBne
  rw [entry0_shiftr01 hk', entry0_shiftr01 hBl, hBH hBne] at hrec
  have := getD_row0_ge hA hk'
  omega

theorem nslot_ax {P : ℕ → TrioSeq → Prop} (hP : SlotAx P) {k : ℕ} (hk : 1 ≤ k) :
    SlotAx (nslot P k) where
  lift := by
    intro u W _ h u' hu u'' hu'' X hX hPX
    have e := mlift_mlift W u (u' - u) (u'' - u')
    rw [show u + (u' - u) = u' by omega, show u' - u + (u'' - u') = u'' - u by omega] at e
    rw [e]
    exact h u'' (le_trans hu hu'') X hX hPX
  oper := by
    intro u W U hW hU hH hlen hp hIH u' hu X hX hPX
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    rw [mlift_app hW hH u (u' - u)]
    have hlen' : 2 ≤ (mlift U u (u' - u)).length := by rw [mlift_length]; exact hlen
    have hUlne : mlift U u (u' - u) ≠ [] := by
      intro h; have := congrArg List.length h; rw [mlift_length, List.length_nil] at this; omega
    have hp' := (hasParent_mlift_iff u (u' - u) hUne).mpr hp
    refine hP.oper u' X _ hX (Fr_node _ _) (Hd_node _ _)
      (by simp only [List.length_cons, List.length_append, shiftr01_length]; omega)
      (node_hasParent _ _ _ hp' hUlne) (fun m hm => ?_)
    rw [node_oper _ _ _ hlen' hp' m, mlift_oper', ← mlift_app hW (Hd_oper hH hUne hm)]
    exact hIH m hm u' hu X hX hPX
  orph := by
    intro u W U h j hW hU hH hj1 hj hnp hz u' hu X hX hPX
    have hc : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ u := hj
    have hUc : Fr U := fun x hx => hU x (List.mem_append_left _ hx)
    have eL : mlift (W ++ (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) u (u' - u)
        = mlift W u (u' - u) ++ (mlift U u (u' - u) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      rw [mlift_app hW hH, mlift_snoc_low U _ hc]
    have eV : ((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift W u (u' - u) ++ (mlift U u (u' - u) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]))
        = (((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u) ++ mlift U u (u' - u)))
          ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by
      rw [← List.append_assoc, shiftr01_append0, shift_col]; rfl
    rw [eL, eV]
    refine hP.orph u' X _ (h + 1) j hX (by rw [← eV]; exact Fr_node _ _)
      (by rw [← eV]; exact Hd_node _ _) hj1 (le_trans hj hu) ?_ (fun z hz' hbz => ?_)
    · have eAB : (((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift W u (u' - u) ++ mlift U u (u' - u))) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]
          = (((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))) ++
            shiftr01 1 0 (mlift U u (u' - u) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
        rw [← eV, node_split]
      have eidx : (((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift W u (u' - u) ++ mlift U u (u' - u))).length
          = (((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))).length +
            (mlift U u (u' - u)).length := by simp [shiftr01]; omega
      rw [eAB, eidx]
      have hBH : Hd (mlift U u (u' - u) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
        rw [← mlift_snoc_low U _ hc]; exact Hd_mlift hH _ _
      refine noParent_ctx (j := j) (by simp [shiftr01]) (fun k' hk' hrt => ?_) ?_ ?_
      · have := node_anc_row1 (Fr_mlift hW u (u' - u)) hBH (by simp) hk' (by simp [shiftr01]) hrt
        subst this
        show j ≤ u' + k
        omega
      · rw [entry1_shiftr01, show (mlift U u (u' - u)).length = (mlift U u (u' - u)).length + 0
          from rfl, entry_append_right]; rfl
      · intro hh
        apply hnp
        rw [hasParent_shiftr01, ← mlift_snoc_low U _ hc, mlift_eq_slift,
          hasParent_slift (stair_step u (u' - u)), mlift_length] at hh
        exact hh
    · have hzz := hz z hz' hbz u' hu X hX hPX
      have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
      have hHz : Hd (U ++ shiftr01 h 0 z) := by
        intro hne
        by_cases hUn : U = []
        · subst hUn
          have hh1 : h = 1 := by have := hH (by simp); simpa [entry] using this
          have hzne : z ≠ [] := by intro hz0; apply hne; subst hz0; rfl
          simp only [List.nil_append]
          rw [entry0_shiftr01 (List.length_pos_iff.mpr hzne), show entry z 0 0 = 0 from hbz, hh1]
        · rw [Small.entry_append_left (List.length_pos_iff.mpr hUn)]
          have := hH (by simp)
          rwa [Small.entry_append_left (List.length_pos_iff.mpr hUn)] at this
      rw [mlift_app hW hHz, mlift_append_low (low_of_Wg hzW h hj)] at hzz
      rw [show (((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift W u (u' - u) ++ mlift U u (u' - u))) ++ shiftr01 (h + 1) 0 z
          = ((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u) ++
              (mlift U u (u' - u) ++ shiftr01 h 0 z)) by
        rw [← List.append_assoc, shiftr01_append0 _ (mlift W u (u' - u) ++ mlift U u (u' - u)),
          shiftr01_add0]; rfl]
      exact hzz
  tie := by
    intro u W U x hW hU hH hc hload u' hu X hX hPX
    have eL : mlift (W ++ (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)])) u (u' - u)
        = mlift W u (u' - u) ++ (mlift U u (u' - u) ++ [((x, u' + 1, 0) : ℕ × ℕ × ℕ)]) := by
      rw [mlift_app hW hH, mlift_snoc_cone U _ hc]
      show _ ++ (_ ++ [((x, u + 1 + (u' - u), 0) : ℕ × ℕ × ℕ)]) = _
      rw [show u + 1 + (u' - u) = u' + 1 by omega]
    have eV : ((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift W u (u' - u) ++ (mlift U u (u' - u) ++ [((x, u' + 1, 0) : ℕ × ℕ × ℕ)]))
        = (((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u) ++ mlift U u (u' - u)))
          ++ [((x + 1, u' + 1, 0) : ℕ × ℕ × ℕ)] := by
      rw [← List.append_assoc, shiftr01_append0, shift_col]; rfl
    rw [eL, eV]
    refine hP.tie u' X _ (x + 1) hX (by rw [← eV]; exact Fr_node _ _)
      (by rw [← eV]; exact Hd_node _ _) ?_ (fun u'' hu'' Z hZ hbZ => ?_)
    · have eAB : (((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift W u (u' - u) ++ mlift U u (u' - u))) ++ [((x + 1, u' + 1, 0) : ℕ × ℕ × ℕ)]
          = (((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))) ++
            shiftr01 1 0 (mlift U u (u' - u) ++ [((x, u' + 1, 0) : ℕ × ℕ × ℕ)]) := by
        rw [← eV, node_split]
      have eidx : (((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift W u (u' - u) ++ mlift U u (u' - u))).length
          = (((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))).length +
            (mlift U u (u' - u)).length := by simp [shiftr01]; omega
      rw [eAB, eidx]
      have hPCA : PathCone u' 1 (((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))) := by
        intro y hy _ hd
        rcases y with _ | y
        · show u' < u' + k; omega
        · exfalso
          rw [entry_cons] at hd
          have hy' : y < (mlift W u (u' - u)).length := by
            rw [mlift_length]; simp [shiftr01] at hy; omega
          rw [entry0_shiftr01 hy'] at hd
          have := getD_row0_ge (Fr_mlift hW u (u' - u)) hy'
          omega
      have hB0 : shiftr01 1 0 (mlift U u (u' - u) ++ [((x, u' + 1, 0) : ℕ × ℕ × ℕ)]) ≠ [] →
          entry (shiftr01 1 0 (mlift U u (u' - u) ++ [((x, u' + 1, 0) : ℕ × ℕ × ℕ)])) 0 0 = 1 + 1 := by
        intro _
        have hBH : Hd (mlift U u (u' - u) ++ [((x, u' + 1, 0) : ℕ × ℕ × ℕ)]) := by
          have := Hd_mlift hH u (u' - u)
          rwa [mlift_snoc_cone U _ hc, show u + 1 + (u' - u) = u' + 1 by omega] at this
        rw [entry0_shiftr01 (by simp), hBH (by simp)]
      rw [coneV_pathB hPCA hB0 (by simp [shiftr01]), coneV_shift0]
      have := coneV_mlift (by simp) hc (u' - u)
      rwa [mlift_snoc_cone U _ hc, show u + 1 + (u' - u) = u' + 1 by omega,
        show u + (u' - u) = u' by omega, ← mlift_length U u (u' - u)] at this
    · have h1 := hload u'' (le_trans hu hu'') Z hZ hbZ u'' le_rfl (mlift X u' (u'' - u'))
        (Fr_mlift hX _ _) (hP.lift u' X hX hPX u'' hu'')
      rw [Nat.sub_self, mlift_zero] at h1
      have hWU : Fr (mlift W u (u' - u) ++ mlift U u (u' - u)) := by
        refine Fr_append (Fr_mlift hW _ _) (Fr_mlift (fun y hy => hU y (List.mem_append_left _ hy)) _ _)
      have e1 : mlift (mlift W u (u' - u) ++ mlift U u (u' - u)) u' (u'' - u')
          = mlift (W ++ U) u (u'' - u) := by
        have hHU : Hd U := by
          intro hne
          have := hH (by simp)
          rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
        rw [← mlift_app hW hHU]
        have e := mlift_mlift (W ++ U) u (u' - u) (u'' - u')
        rw [show u + (u' - u) = u' by omega, show u' - u + (u'' - u') = u'' - u by omega] at e
        exact e
      rw [mlift_app hX (Hd_node _ _), mlift_node (by omega) hWU, e1,
        show u' + k + (u'' - u') = u'' + k by omega, List.append_assoc]
      rw [shiftr01_append0, shiftr01_add0] at h1
      exact h1
  flat := by
    intro u W hW h u' hu X hX hPX
    rw [mlift_snoc_flat W 1 u (u' - u) hW]
    have eV : ((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (mlift W u (u' - u) ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
        = (((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))) ++
          [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
      rw [node_split, shift_col]
    rw [eV]
    have hM : (((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))) ≠ [] := by simp
    have hhead : entry (((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))) 0 0 < 2 := by
      show 1 < 2; omega
    have htail : ∀ r, 1 ≤ r → r < (((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift W u (u' - u))).length →
        2 ≤ entry (((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))) 0 r := by
      intro r hr1 hr2
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      have hr' : r' < (mlift W u (u' - u)).length := by
        simp only [List.length_cons, shiftr01_length] at hr2; omega
      rw [entry_cons, entry0_shiftr01 hr']
      have := getD_row0_ge (Fr_mlift hW u (u' - u)) hr'
      omega
    have hpV : hasParent ((((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))) ++
          [((2, 0, 0) : ℕ × ℕ × ℕ)])
        (srow ((((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))) ++
          [((2, 0, 0) : ℕ × ℕ × ℕ)]) (((((1, u' + k, 0) : ℕ × ℕ × ℕ) ::
            shiftr01 1 0 (mlift W u (u' - u))) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1))
        (((((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))) ++
          [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
      have hidx : ((((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))) ++
          [((2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1
          = (((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u))).length + 0 := by simp
      rw [hidx, srow_append_right]
      have hs : srow [((2, 0, 0) : ℕ × ℕ × ℕ)] 0 = 0 := rfl
      rw [hs]
      refine (hasParent_zero_iff (by simp)).mpr ⟨0, by simp, ?_⟩
      rw [Small.entry_append_left (by simp), entry_append_right]
      show 1 < 2; omega
    have hrep : ∀ m, P u' (X ++ (List.range m).flatMap (fun _ =>
        ((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u)))) := by
      intro m
      induction m with
      | zero => simpa using hPX
      | succ m ih =>
          rw [List.range_succ, List.flatMap_append]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [← List.append_assoc]
          have hFr : Fr (X ++ (List.range m).flatMap (fun _ =>
              ((1, u' + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (mlift W u (u' - u)))) := by
            refine Fr_append hX (fun y hy => ?_)
            simp only [List.mem_flatMap] at hy
            obtain ⟨-, -, hy⟩ := hy
            exact Fr_node _ _ y hy
          exact h u' hu _ hFr ih
    refine hP.oper u' X _ hX (Fr_append (Fr_node _ _) (by intro y hy; simp at hy; subst hy; show 1 ≤ 2; omega))
      (fun _ => rfl) (by simp) hpV (fun m _ => ?_)
    have eO := oper_snoc00'' [] hM hhead htail m
    simp only [List.nil_append] at eO
    rw [eO]
    exact hrep m

#print axioms nslot_ax


/-! ## タイの子の並び（差し込み口によらない） -/

def GTs (u : ℕ) (D : TrioSeq) : Prop := ∀ ok, SlotAx ok → nslot ok 1 u D

theorem GTs_ax : SlotAx GTs where
  lift := fun u W hW h u' hu ok hA => (nslot_ax hA le_rfl).lift u W hW (h ok hA) u' hu
  oper := fun u W U hW hU hH hlen hp hIH ok hA =>
    (nslot_ax hA le_rfl).oper u W U hW hU hH hlen hp (fun m hm => hIH m hm ok hA)
  orph := fun u W U h j hW hU hH hj1 hj hnp hz ok hA =>
    (nslot_ax hA le_rfl).orph u W U h j hW hU hH hj1 hj hnp (fun z hz' hbz => hz z hz' hbz ok hA)
  tie := fun u W U x hW hU hH hc hload ok hA =>
    (nslot_ax hA le_rfl).tie u W U x hW hU hH hc
      (fun u' hu Z hZ hbZ => hload u' hu Z hZ hbZ ok hA)
  flat := fun u W hW h ok hA => (nslot_ax hA le_rfl).flat u W hW (h ok hA)

theorem GTs_nil (u : ℕ) : GTs u [] := by
  intro ok hA u' _ X hX hPX
  have hc : coneV ([] ++ [((1, u' + 1, 0) : ℕ × ℕ × ℕ)]) u' ([] : TrioSeq).length := by
    intro y hy
    have := rtg0_le hy
    have hy0 : y = 0 := by simp at this; omega
    subst hy0; show u' < u' + 1; omega
  have h := hA.tie u' X [] 1 hX (by intro y hy; simp at hy; subst hy; show 1 ≤ 1; omega)
    (fun _ => rfl) hc (fun u'' hu'' Z hZ hbZ => by
      have := slot_load hA (Fr_mlift hX u' (u'' - u')) (hA.lift u' X hX hPX u'' hu'') Z hZ hbZ
      simpa using this)
  simpa [mlift_nil, shiftr01] using h

theorem GTs_load {u : ℕ} {D : TrioSeq} (hD : Fr D) (h : GTs u D) {Z : TrioSeq}
    (hZ : Z ∈ Wg (2 * u)) (hb : based Z) : GTs u (D ++ shiftr01 1 0 Z) :=
  fun ok hA => slot_load (nslot_ax hA le_rfl) hD (h ok hA) Z hZ hb

theorem GTs_child {u : ℕ} {D E : TrioSeq} (hD : Fr D) (h : GTs u D) (hE : GTs u E) :
    GTs u (D ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 E) := by
  intro ok hA
  have := hE (nslot ok 1) (nslot_ax hA le_rfl) u le_rfl D hD (h ok hA)
  rwa [Nat.sub_self, mlift_zero] at this

theorem coneV_top' {K : TrioSeq} (hK : Fr K) {u r : ℕ} (hr : u < r) :
    coneV (K ++ [((1, r, 0) : ℕ × ℕ × ℕ)]) u K.length := by
  intro y hy
  have hyle := rtg0_le hy
  rcases Nat.lt_or_ge y K.length with hlt | hge
  · exfalso
    have hrec := rtg0_rec hy K.length hlt le_rfl
    rw [Small.entry_append_left hlt, show K.length = K.length + 0 from rfl,
      entry_append_right] at hrec
    have h1 := getD_row0_ge hK hlt
    have e : entry [((1, r, 0) : ℕ × ℕ × ℕ)] 0 0 = 1 := rfl
    rw [e] at hrec
    omega
  · have hy' : y = K.length := by simp at hyle; omega
    subst hy'
    rw [show K.length = K.length + 0 from rfl, entry_append_right]
    show u < r; exact hr

/-- ★ タイの子に 2 段上の錐（そのタイからの塔）。 -/
theorem GTs_C2 {u : ℕ} {D : TrioSeq} (hD : Fr D) (h : GTs u D) :
    GTs u (D ++ [((1, u + 2, 0) : ℕ × ℕ × ℕ)]) := by
  intro ok hA u' hu X hX hPX
  have hc := coneV_top' hD (show u < u + 2 by omega)
  rw [mlift_snoc_cone D _ hc (u' - u)]
  have e2 : (((((1, u + 2, 0) : ℕ × ℕ × ℕ)).1, (((1, u + 2, 0) : ℕ × ℕ × ℕ)).2.1 + (u' - u),
      (((1, u + 2, 0) : ℕ × ℕ × ℕ)).2.2) : ℕ × ℕ × ℕ) = ((1, u' + 2, 0) : ℕ × ℕ × ℕ) := by
    show ((1, u + 2 + (u' - u), 0) : ℕ × ℕ × ℕ) = _
    rw [show u + 2 + (u' - u) = u' + 2 by omega]
  rw [e2]
  have hDl : Fr (mlift D u (u' - u)) := Fr_mlift hD u (u' - u)
  have hGDl : GTs u' (mlift D u (u' - u)) := GTs_ax.lift u D hD h u' hu
  obtain ⟨Dl, hDleq⟩ : ∃ Dl, Dl = mlift D u (u' - u) := ⟨_, rfl⟩
  rw [← hDleq] at hDl hGDl ⊢
  obtain ⟨R, hR⟩ : ∃ R : TrioSeq, R = Dl ++ [((1, u' + 2, 0) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  rw [← hR]
  have hRok : argOK R := by
    intro p hp
    rw [hR] at hp
    rcases List.mem_append.mp hp with hp | hp
    · have := hDl p hp; omega
    · simp at hp; subst hp; show 0 < 1; omega
  have hRne : R ≠ [] := by simp [hR]
  have hRlen : R.length - 1 = Dl.length + 0 := by simp [hR]
  have eL : ∀ r, entry R r (R.length - 1) = entry [((1, u' + 2, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r; rw [hRlen, hR, entry_append_right]
  have e0 : entry R 0 (R.length - 1) = 1 := by rw [eL]; rfl
  have e1 : entry R 1 (R.length - 1) = u' + 2 := by rw [eL]; rfl
  have e2' : entry R 2 (R.length - 1) = 0 := by rw [eL]; rfl
  have hsr : srow R (R.length - 1) = 1 := by unfold srow; rw [e2', e1]; simp
  have hnpR : ¬ hasParent R 1 (R.length - 1) := by
    rintro ⟨k, hk, -⟩
    have hk' : nextrel1 R k (R.length - 1) := by
      unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
    obtain ⟨-, -, hkl, -, hle0, -⟩ := hk'
    have hrec := rtg0_rec hle0.2.2 (R.length - 1) hkl le_rfl
    rw [e0] at hrec
    have hkD : k < Dl.length := by omega
    rw [hR, Small.entry_append_left hkD] at hrec
    have := getD_row0_ge hDl hkD
    omega
  have hd : domT R (2 * (u' + 1) + 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2']; omega
    · rw [hsr]; exact hnpR
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hpM : hasParent (((0, u' + 1, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
    rw [hsr]
    refine hasParent_one_of (b := R.length) (k := 0) (by simp) hRl
      ⟨by simp, by simp, rtg0_zero (fun l hl0 hl => ?_) (by simp)⟩ ?_
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [entry_cons]
      have hl' : l' < R.length := by simp at hl; omega
      have hmem : R.getD l' (0, 0, 0) ∈ R := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl']; exact List.getElem_mem hl'
      have := hRok _ hmem
      show 0 < (R.getD l' (0, 0, 0)).1
      omega
    · rw [entry_cons_last hRne 1, e1]; show u' + 1 < u' + 2; omega
  have hdl : R.dropLast = Dl := by rw [hR, List.dropLast_concat]
  have htow : ∀ j, shiftr01 1 0 (tow (u' + 1) 0 R (j + 1))
      = ((1, u' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (Dl ++ shiftr01 1 0 (tow (u' + 1) 0 R j)) := by
    intro j
    rw [tow, graft_eq_shift, e0, hdl]
    simp [shiftr01]
  have hG : ∀ j, GTs u' (Dl ++ shiftr01 1 0 (tow (u' + 1) 0 R j)) := by
    intro j
    induction j with
    | zero => simpa [tow, shiftr01] using hGDl
    | succ j ih =>
        rw [htow]
        exact GTs_child hDl hGDl ih
  have eV : ((1, u' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 R
      = shiftr01 1 0 (((0, u' + 1, 0) : ℕ × ℕ × ℕ) :: R) := by simp [shiftr01]
  rw [eV]
  have hlen2 : 2 ≤ (((0, u' + 1, 0) : ℕ × ℕ × ℕ) :: R).length := by simp; omega
  have hpM' : hasParent (((0, u' + 1, 0) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, u' + 1, 0) : ℕ × ℕ × ℕ) :: R) ((((0, u' + 1, 0) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, u' + 1, 0) : ℕ × ℕ × ℕ) :: R).length - 1) := by
    have hl : ((((0, u' + 1, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]; exact hpM
  refine hA.oper u' X _ hX (fun y hy => ?_) (fun _ => ?_) (by rw [shiftr01_length]; exact hlen2)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpM') (fun m hm => ?_)
  · simp only [shiftr01, List.mem_map] at hy
    obtain ⟨p, -, rfl⟩ := hy
    dsimp only; omega
  · rw [entry0_shiftr01 (by simp)]; rfl
  · have eO := oper_shift [] (((0, u' + 1, 0) : ℕ × ℕ × ℕ) :: R) 1 m hlen2 hpM'
    simp only [List.nil_append] at eO
    rw [eO, oper_cons_tower1 hRok hRne hd hsr hpM]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [htow]
    have := hG j ok hA u' le_rfl X hX hPX
    rwa [Nat.sub_self, mlift_zero] at this

#print axioms GTs_C2

/-! ## 2 段上の錐の子の差し込み口 -/

def GHs : ℕ → TrioSeq → Prop := nslot GTs 2

theorem GHs_ax : SlotAx GHs := nslot_ax GTs_ax (by omega)

theorem GHs_nil (u : ℕ) : GHs u [] := by
  intro u' _ X hX hGX
  have := GTs_C2 hX hGX
  simpa [mlift_nil, shiftr01] using this

theorem GHs_load {u : ℕ} {C : TrioSeq} (hC : Fr C) (h : GHs u C) {Z : TrioSeq}
    (hZ : Z ∈ Wg (2 * u)) (hb : based Z) : GHs u (C ++ shiftr01 1 0 Z) :=
  slot_load GHs_ax hC h Z hZ hb

theorem GHs_child {u : ℕ} {C E : TrioSeq} (hC : Fr C) (h : GHs u C) (hE : GTs u E) :
    GHs u (C ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 E) := by
  have := hE GHs GHs_ax u le_rfl C hC h
  rwa [Nat.sub_self, mlift_zero] at this

theorem GTs_h {u : ℕ} {D C : TrioSeq} (hD : Fr D) (h : GTs u D) (hC : GHs u C) :
    GTs u (D ++ ((1, u + 2, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 C) := by
  have := hC u le_rfl D hD h
  rwa [Nat.sub_self, mlift_zero] at this

/-! ## 最上段と、森の条件つきの組み立て -/

theorem top_load {u : ℕ} {K : TrioSeq} (hK : Fr K) (h : GTall u K) {Z : TrioSeq}
    (hZ : Z ∈ Wg (2 * u)) (hb : based Z) : GTall u (K ++ shiftr01 1 0 Z) :=
  slot_load topSlot_ax hK h Z hZ hb

theorem top_tie {u : ℕ} {K D : TrioSeq} (hK : Fr K) (h : GTall u K) (hD : GTs u D) :
    GTall u (K ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) := by
  have := hD (fun u W => GTall u W) topSlot_ax u le_rfl K hK h
  rwa [Nat.sub_self, mlift_zero] at this

theorem Fr_nil : Fr [] := fun _ h => by simp at h

theorem Fr_shift1 (Z : TrioSeq) : Fr (shiftr01 1 0 Z) := by
  intro x hx
  simp only [shiftr01, List.mem_map] at hx
  obtain ⟨p, -, rfl⟩ := hx
  dsimp only; omega

def TF (u : ℕ) (K : TrioSeq) : Prop := GTall u K ∧ Fr K
def GTF (u : ℕ) (D : TrioSeq) : Prop := GTs u D ∧ Fr D
def GHF (u : ℕ) (C : TrioSeq) : Prop := GHs u C ∧ Fr C

theorem TF_nil (u : ℕ) : TF u [] := ⟨GTall_nil u, Fr_nil⟩

theorem TF_load {u : ℕ} {K Z : TrioSeq} (h : TF u K) (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    TF u (K ++ shiftr01 1 0 Z) := ⟨top_load h.2 h.1 hZ hb, Fr_append h.2 (Fr_shift1 Z)⟩

theorem TF_tie {u : ℕ} {K D : TrioSeq} (h : TF u K) (hD : GTF u D) :
    TF u (K ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 D) :=
  ⟨top_tie h.2 h.1 hD.1, Fr_append h.2 (Fr_node _ _)⟩

theorem GTF_nil (u : ℕ) : GTF u [] := ⟨GTs_nil u, Fr_nil⟩

theorem GTF_load {u : ℕ} {D Z : TrioSeq} (h : GTF u D) (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    GTF u (D ++ shiftr01 1 0 Z) := ⟨GTs_load h.2 h.1 hZ hb, Fr_append h.2 (Fr_shift1 Z)⟩

theorem GTF_tie {u : ℕ} {D E : TrioSeq} (h : GTF u D) (hE : GTF u E) :
    GTF u (D ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 E) :=
  ⟨GTs_child h.2 h.1 hE.1, Fr_append h.2 (Fr_node _ _)⟩

theorem GTF_h {u : ℕ} {D C : TrioSeq} (h : GTF u D) (hC : GHF u C) :
    GTF u (D ++ ((1, u + 2, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 C) :=
  ⟨GTs_h h.2 h.1 hC.1, Fr_append h.2 (Fr_node _ _)⟩

theorem GHF_nil (u : ℕ) : GHF u [] := ⟨GHs_nil u, Fr_nil⟩

theorem GHF_load {u : ℕ} {C Z : TrioSeq} (h : GHF u C) (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    GHF u (C ++ shiftr01 1 0 Z) := ⟨GHs_load h.2 h.1 hZ hb, Fr_append h.2 (Fr_shift1 Z)⟩

theorem GHF_tie {u : ℕ} {C E : TrioSeq} (h : GHF u C) (hE : GTF u E) :
    GHF u (C ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 E) :=
  ⟨GHs_child h.2 h.1 hE.1, Fr_append h.2 (Fr_node _ _)⟩

theorem WordsG_consT {v : ℕ} {K : TrioSeq} {Ls : List TrioSeq} (h1 : TF v K)
    (h2 : WordsG v Ls) : WordsG v (K :: Ls) := by
  intro K' h
  simp only [List.mem_cons] at h
  rcases h with rfl | h
  · exact ⟨GT_of_GTall h1.1, h1.2⟩
  · exact h2 K' h

/-- 行 780 の試し。 -/
theorem R780_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0)
    (WordsG_consT (TF_tie (TF_nil 0) (GTF_h (GTF_nil 0) (GHF_nil 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

#print axioms R780_mem

end GxP
end TRIO
