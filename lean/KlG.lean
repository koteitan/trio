/-
KlG.lean: 成分の族で使う klift の補題（κ の範囲での一致・閾値より下の末尾・錐・字への分配・κ の連結）。
-/
import KlF

namespace TRIO
namespace KlG

open Classical Wset KlA KlB KlE GxP GxW

theorem klift_congrK {X : TrioSeq} {o j : ℕ} {K1 K2 : ℕ → ℕ}
    (hK : ∀ i, i < X.length → K1 i = K2 i) : klift X o j K1 = klift X o j K2 := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [klift_length] at hi
  rw [klift_getD hi, klift_getD hi, Lk_congrK (fun y hy => hK y (by omega))]

/-- 末尾の B の各列が、B の中に行 1 < o の祖先を持つなら、B は動かない。 -/
theorem klift_append_low {A B : TrioSeq} {o j : ℕ} {K : ℕ → ℕ}
    (hB : ∀ i, i < B.length → ∃ k, Relation.ReflTransGen (nextrel0 B) k i ∧ entry B 1 k < o) :
    klift (A ++ B) o j K = klift A o j K ++ B := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [klift_length, List.length_append] at hi
  rw [klift_getD (by rw [List.length_append]; omega)]
  rcases Nat.lt_or_ge i A.length with hiA | hiA
  · have eg : (klift A o j K ++ B).getD i (0, 0, 0) = (klift A o j K).getD i (0, 0, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [klift_length]; exact hiA)]
    rw [eg, klift_getD hiA, Small.entry_append_left hiA, Small.entry_append_left hiA,
      Small.entry_append_left hiA, Lk_append_left hiA]
  · obtain ⟨q, rfl⟩ : ∃ q, i = A.length + q := ⟨i - A.length, by omega⟩
    have hq : q < B.length := by omega
    obtain ⟨k, hk, hk1⟩ := hB q hq
    have hL : Lk (A ++ B) o j K (A.length + q) = 0 := by
      have := Lk_le (A := A ++ B) (o := o) (j := j) (K := K) (rtg_nextrel0_lift A B hk)
      rw [lamK_low (by rw [entry_append_right]; exact hk1)] at this
      omega
    rw [hL, Nat.add_zero, getD_app_right _ _ (by rw [klift_length]; omega), klift_length,
      show A.length + q - A.length = q from by omega, entry_append_right, entry_append_right,
      entry_append_right, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
    exact entry_triple hq

theorem klift_snoc_low {U : TrioSeq} {c : ℕ × ℕ × ℕ} {o j : ℕ} {K : ℕ → ℕ} (hc : c.2.1 < o) :
    klift (U ++ [c]) o j K = klift U o j K ++ [c] :=
  klift_append_low (fun i hi => ⟨0, by
    have h0 : i = 0 := by simp at hi; omega
    subst h0; exact Relation.ReflTransGen.refl, by show c.2.1 < o; exact hc⟩)

theorem coneV_klift_up {X : TrioSeq} {v i o j : ℕ} {K : ℕ → ℕ} (h : coneV X v i) :
    coneV (klift X o j K) v i := by
  intro y hy
  have hy' := rtg0_klift.1 hy
  have h1 := h y hy'
  by_cases hyl : y < X.length
  · rw [entry1_klift hyl]; omega
  · have e0 : entry X 1 y = 0 := by
      show (X.getD y (0, 0, 0)).2.1 = 0
      rw [getD_out (by omega)]
    omega

/-- ★ 語 W ++ ℓ :: Y↑1（ℓ は閾値より上）への分配。 -/
theorem klift_letter {W Y : TrioSeq} (hW : Fr W) (hY : Fr Y) {v r J : ℕ} {K : ℕ → ℕ} (hr : v < r) :
    klift (W ++ ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Y) v J K
      = klift W v J K ++ ((1, r + J, 1) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (klift Y v J (fun i => K (W.length + (1 + i)))) := by
  rw [klift_app hW (Hd_letter _ _), klift_node_high hY hr]

/-- 前 n 個は K1、残りは K2 を使う κ。 -/
def joinK (n : ℕ) (K1 K2 : ℕ → ℕ) : ℕ → ℕ := fun i => if i < n then K1 i else K2 (i - n)

theorem klift_app_join {Y U : TrioSeq} (hY : Fr Y) (hU : Hd U) (v J : ℕ) (K1 K2 : ℕ → ℕ) :
    klift (Y ++ U) v J (joinK Y.length K1 K2) = klift Y v J K1 ++ klift U v J K2 := by
  rw [klift_app hY hU]
  congr 1
  · exact klift_congrK (fun i hi => by unfold joinK; rw [if_pos hi])
  · exact klift_congrK (fun i _ => by unfold joinK; rw [if_neg (by omega), Nat.add_sub_cancel_left])

end KlG
end TRIO
