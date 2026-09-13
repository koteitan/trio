/-
KlF.lean: 世界の合成（notes 追記506・509、tools/probe_kappa_comp.py）。

    klift_comp : klift (klift X o j1 K1) (o + j1) j2 K2 = klift X o (j1 + j2) (compK j1 j2 K1 K2)
    compK j1 j2 K1 K2 y = j1 + min (K2 y) j2（j1 ≤ K1 y）、K1 y（そうでなければ）
-/
import KlE

namespace TRIO
namespace KlF

open Classical Wset KlA KlB GxP

def compK (j1 j2 : ℕ) (K1 K2 : ℕ → ℕ) : ℕ → ℕ :=
  fun y => if j1 ≤ K1 y then j1 + min (K2 y) j2 else K1 y

theorem Lk_comp {X : TrioSeq} {o j1 j2 : ℕ} {K1 K2 : ℕ → ℕ} {c : ℕ} (hc : c < X.length) :
    Lk X o j1 K1 c + Lk (klift X o j1 K1) (o + j1) j2 K2 c
      = Lk X o (j1 + j2) (compK j1 j2 K1 K2) c := by
  have hge13 : ∀ y, lamK X o j1 K1 y ≤ lamK X o (j1 + j2) (compK j1 j2 K1 K2) y := by
    intro y; unfold lamK compK; split_ifs <;> omega
  by_cases hA : Lk X o j1 K1 c < j1
  · obtain ⟨y0, hy0, hey0⟩ := Lk_mem (A := X) (o := o) (j := j1) (K := K1) c
    have hy0l : y0 < X.length := by have := rtg0_le hy0; omega
    have hL1y0 : Lk X o j1 K1 y0 = Lk X o j1 K1 c :=
      le_antisymm (by rw [← hey0]; exact Lk_le Relation.ReflTransGen.refl) (Lk_mono hy0)
    have hlt : lamK X o j1 K1 y0 < j1 := by omega
    have he : entry X 1 y0 ≤ o := by
      by_contra h
      push_neg at h
      rw [lamK_high h] at hlt
      omega
    have hl3 : lamK X o (j1 + j2) (compK j1 j2 K1 K2) y0 = lamK X o j1 K1 y0 := by
      unfold lamK at hlt
      unfold lamK compK
      split_ifs at hlt ⊢ <;> omega
    have hL2 : Lk (klift X o j1 K1) (o + j1) j2 K2 c = 0 := by
      have hY1 : entry (klift X o j1 K1) 1 y0 < o + j1 := by
        rw [entry1_klift hy0l, hL1y0]; omega
      have := Lk_le (A := klift X o j1 K1) (o := o + j1) (j := j2) (K := K2) (rtg0_klift.2 hy0)
      rw [lamK_low hY1] at this
      omega
    have hL3le : Lk X o (j1 + j2) (compK j1 j2 K1 K2) c ≤ Lk X o j1 K1 c := by
      have := Lk_le (A := X) (o := o) (j := j1 + j2) (K := compK j1 j2 K1 K2) hy0
      rw [hl3] at this
      omega
    have hL3ge : Lk X o j1 K1 c ≤ Lk X o (j1 + j2) (compK j1 j2 K1 K2) c := by
      obtain ⟨y, hy, hey⟩ := Lk_mem (A := X) (o := o) (j := j1 + j2) (K := compK j1 j2 K1 K2) c
      rw [← hey]
      exact le_trans (Lk_le hy) (hge13 y)
    omega
  · have hj1 : Lk X o j1 K1 c = j1 := le_antisymm (Lk_le_j c) (by omega)
    have hall : ∀ y, Relation.ReflTransGen (nextrel0 X) y c → Lk X o j1 K1 y = j1 :=
      fun y hy => le_antisymm (Lk_le_j y) (by have := Lk_mono (A := X) (o := o) (j := j1) (K := K1) hy; omega)
    have hlam3 : ∀ y, Relation.ReflTransGen (nextrel0 X) y c →
        lamK X o (j1 + j2) (compK j1 j2 K1 K2) y = j1 + lamK (klift X o j1 K1) (o + j1) j2 K2 y := by
      intro y hy
      have hyl : y < X.length := by have := rtg0_le hy; omega
      have hl1 : j1 ≤ lamK X o j1 K1 y := by
        have := Lk_le (A := X) (o := o) (j := j1) (K := K1) hy; omega
      have hY : entry (klift X o j1 K1) 1 y = entry X 1 y + j1 := by
        rw [entry1_klift hyl, hall y hy]
      unfold lamK at hl1
      unfold lamK compK
      rw [hY, entry2_klift]
      split_ifs at hl1 ⊢ <;> omega
    refine le_antisymm ?_ ?_
    · obtain ⟨y, hy, hey⟩ := Lk_mem (A := X) (o := o) (j := j1 + j2) (K := compK j1 j2 K1 K2) c
      rw [← hey, hlam3 y hy, hj1]
      have := Lk_le (A := klift X o j1 K1) (o := o + j1) (j := j2) (K := K2) (rtg0_klift.2 hy)
      omega
    · obtain ⟨y, hy, hey⟩ := Lk_mem (A := klift X o j1 K1) (o := o + j1) (j := j2) (K := K2) c
      have hy' := rtg0_klift.1 hy
      have := Lk_le (A := X) (o := o) (j := j1 + j2) (K := compK j1 j2 K1 K2) hy'
      rw [hlam3 y hy'] at this
      omega

/-- ★ 世界の合成: 閾値 o の klift のあとの閾値 o + j1 の klift は、閾値 o の 1 回の klift。 -/
theorem klift_comp (X : TrioSeq) (o j1 j2 : ℕ) (K1 K2 : ℕ → ℕ) :
    klift (klift X o j1 K1) (o + j1) j2 K2 = klift X o (j1 + j2) (compK j1 j2 K1 K2) := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [klift_length, klift_length] at hi
  rw [klift_getD (by rw [klift_length]; exact hi), klift_getD hi, entry0_klift, entry2_klift,
    entry1_klift hi, ← Lk_comp hi, Nat.add_assoc]

end KlF
end TRIO
