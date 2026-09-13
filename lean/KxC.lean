/-
KxC.lean: 成分の族 LCK（字の中身を κ で持ち上げた LC1k。GzC の LCI の写し）。

    LCK A o H S j F K b Y := LC1k (S ++ A) (o + j) F b (klift Y (b + liftOff H A o) (j + Σ_S F) K)

oper は klift_oper の κ' を joinK で Y の κ とつなぐ。tie は 2 ≤ liftOff の場合（o = 1 のタイは後で扱う）。
-/
import KxB
import KlG

namespace TRIO
namespace KxC

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzB KxA KxB KlA KlB KlE KlG

theorem LC1k_congr {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {H1 H2 : ℕ → ℕ}
    (hH : ∀ a ∈ A, H1 a = H2 a) {b : ℕ} {Y : TrioSeq} (h : LC1k A o H1 b Y) : LC1k A o H2 b Y := by
  intro W hW hPV
  have e : liftOff H1 A o = liftOff H2 A o := by unfold liftOff; rw [stepSum_congr 0 o hH]
  have := h W hW (PVK_congr (fun a ha => (hH a ha).symm) hPV)
  rw [e] at this
  exact PVP_congr hA hH this

def LCK (A : List ℕ) (o : ℕ) (H : ℕ → ℕ) (S : List ℕ) (j : ℕ) (F K : ℕ → ℕ) (b : ℕ)
    (Y : TrioSeq) : Prop :=
  LC1k (S ++ A) (o + j) F b (klift Y (b + liftOff H A o) (j + sumOn F S) K)

theorem LCK_nil {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {S : List ℕ} {j : ℕ} (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) (H F K : ℕ → ℕ) (b : ℕ) :
    LCK A o H S j F K b [] := by
  unfold LCK; rw [klift_nil]
  exact LC1k_nil (hA_ins hA hS) (hA1_ins hA1 ho hS) (by omega) _ _

theorem LCK_oper {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {S : List ℕ} {j : ℕ} (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) {F : ℕ → ℕ}
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} (hY : Fr Y) (hU : Fr U) (hH : Hd U)
    (hlen : 2 ≤ U.length) (hp : hasParent U (srow U (U.length - 1)) (U.length - 1))
    (hIH : ∀ m, 1 ≤ m → ∀ K', LCK A o H S j F K' b (Y ++ U⟦m⟧)) (K : ℕ → ℕ) :
    LCK A o H S j F K b (Y ++ U) := by
  unfold LCK at hIH ⊢
  have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  have hv1 : 1 ≤ b + liftOff H A o := by unfold liftOff; omega
  rw [klift_app hY hH]
  refine LC1k_oper (hA_ins hA hS) (hA1_ins hA1 ho hS) (by omega) (Fr_klift hY _ _ _)
    (Fr_klift hU _ _ _) (Hd_klift hH _ _ _) (by rw [klift_length]; exact hlen) ?_ (fun m hm => ?_)
  · rw [klift_length, srow_klift hv1 (by omega), hasParent_klift]; exact hp
  · obtain ⟨K', hK'⟩ := klift_oper (A := U) (o := b + liftOff H A o) (j := j + sumOn F S) hv1
      (fun i => K (Y.length + i)) m
    have h := hIH m hm (joinK Y.length K K')
    rwa [klift_app_join hY (Hd_oper hH hUne hm), hK'] at h

theorem LCK_orph {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {S : List ℕ} {j : ℕ} (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) {F K : ℕ → ℕ}
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} {h j0 : ℕ} (hY : Fr Y)
    (hU : Fr (U ++ [((h, j0, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((h, j0, 0) : ℕ × ℕ × ℕ)]))
    (hj1 : 1 ≤ j0) (hj : j0 ≤ b)
    (hnp : ¬ hasParent (U ++ [((h, j0, 0) : ℕ × ℕ × ℕ)]) 1 U.length)
    (hz : ∀ z ∈ Wg (2 * j0 - 1), based z → LCK A o H S j F K b (Y ++ (U ++ shiftr01 h 0 z))) :
    LCK A o H S j F K b (Y ++ (U ++ [((h, j0, 0) : ℕ × ℕ × ℕ)])) := by
  unfold LCK at hz ⊢
  have hk1 : 1 ≤ liftOff H A o := by unfold liftOff; omega
  have hc : (((h, j0, 0) : ℕ × ℕ × ℕ)).2.1 < b + liftOff H A o := by
    show j0 < b + liftOff H A o; omega
  rw [klift_app hY hH, klift_snoc_low hc]
  refine LC1k_orph (hA_ins hA hS) (hA1_ins hA1 ho hS) (by omega) (Fr_klift hY _ _ _)
    (by rw [← klift_snoc_low hc]; exact Fr_klift hU _ _ _)
    (by rw [← klift_snoc_low hc]; exact Hd_klift hH _ _ _) hj1 hj ?_ (fun z hz' hbz => ?_)
  · intro hh
    apply hnp
    rw [← klift_snoc_low hc, hasParent_klift, klift_length] at hh
    exact hh
  · have hzW : z ∈ Wg (2 * j0) := Wg_mono (by omega) hz'
    have hHz := Hd_append_shift hH hbz
    have h1 := hz z hz' hbz
    have hlow : ∀ i, i < (shiftr01 h 0 z).length → ∃ k,
        Relation.ReflTransGen (nextrel0 (shiftr01 h 0 z)) k i ∧
          entry (shiftr01 h 0 z) 1 k < b + liftOff H A o := by
      intro i hi
      obtain ⟨k, hk, hk1'⟩ := low_of_Wg hzW h (le_refl j0) i hi
      exact ⟨k, hk, by omega⟩
    rw [klift_app hY hHz, klift_append_low hlow] at h1
    exact h1

theorem LCK_tie {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    {S : List ℕ} {j : ℕ} (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) {F K : ℕ → ℕ}
    {H : ℕ → ℕ} {b : ℕ} {Y U : TrioSeq} {x : ℕ} (hk2 : 2 ≤ liftOff H A o) (hY : Fr Y)
    (hU : Fr (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) (hH : Hd (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]))
    (hc : coneV (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)]) b U.length)
    (hload : ∀ b', b ≤ b' → ∀ Z ∈ Wg (2 * b'), based Z →
      LCK A o H S j F K b' (mlift (Y ++ U) b (b' - b) ++ shiftr01 x 0 Z)) :
    LCK A o H S j F K b (Y ++ (U ++ [((x, b + 1, 0) : ℕ × ℕ × ℕ)])) := by
  unfold LCK at hload ⊢
  have hcl : (((x, b + 1, 0) : ℕ × ℕ × ℕ)).2.1 < b + liftOff H A o := by
    show b + 1 < b + liftOff H A o; omega
  have hHU : Hd U := by
    intro hne
    have := hH (by simp)
    rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
  rw [klift_app hY hH, klift_snoc_low hcl]
  refine LC1k_tie (hA_ins hA hS) (hA1_ins hA1 ho hS) (by omega) (Fr_klift hY _ _ _)
    (by rw [← klift_snoc_low hcl]; exact Fr_klift hU _ _ _)
    (by rw [← klift_snoc_low hcl]; exact Hd_klift hH _ _ _) ?_ (fun b'' hb'' Z hZ hbZ => ?_)
  · have := coneV_klift_up (o := b + liftOff H A o) (j := j + sumOn F S)
      (K := fun i => K (Y.length + i)) hc
    rwa [klift_snoc_low hcl,
      ← klift_length U (b + liftOff H A o) (j + sumOn F S) (fun i => K (Y.length + i))] at this
  · have h1 := hload b'' hb'' Z hZ hbZ
    have hlowZ : ∀ i, i < (shiftr01 x 0 Z).length → ∃ k,
        Relation.ReflTransGen (nextrel0 (shiftr01 x 0 Z)) k i ∧
          entry (shiftr01 x 0 Z) 1 k < b'' + liftOff H A o := by
      intro i hi
      obtain ⟨k, hk, hk1'⟩ := low_of_Wg hZ x (le_refl b'') i hi
      exact ⟨k, hk, by omega⟩
    rw [klift_append_low hlowZ,
      show b'' + liftOff H A o = b + liftOff H A o + (b'' - b) by omega,
      ← KlD.klift_mlift_low (show b < b + liftOff H A o by omega), klift_app hY hHU] at h1
    exact h1

theorem LCK_congr {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {S : List ℕ} {j : ℕ}
    (hS : ∀ s ∈ S, o ≤ s ∧ s < o + j) {H1 H2 F1 F2 K : ℕ → ℕ} (hH : ∀ a ∈ A, H1 a = H2 a)
    (hF : ∀ a ∈ S ++ A, F1 a = F2 a) {b : ℕ}
    {Y : TrioSeq} (h : LCK A o H1 S j F1 K b Y) : LCK A o H2 S j F2 K b Y := by
  unfold LCK at h ⊢
  rw [← liftOff_congrA hH, ← sumOn_congr (fun s hs => hF s (List.mem_append_left _ hs))]
  exact LC1k_congr (hA_ins hA hS) hF h

end KxC
end TRIO
