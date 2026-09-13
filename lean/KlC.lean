/-
KlC.lean: klift と既存の持ち上げの関係（notes 追記510 の次）。

    klift_zero_eq_mlift : klift A o j (κ ≡ 0) = mlift A o j
-/
import KlB

namespace TRIO
namespace KlC

open Classical Wset KlA KlB

theorem Lk_zero_eq {A : TrioSeq} {o j c : ℕ} :
    Lk A o j (fun _ => 0) c = if coneV A o c then j else 0 := by
  by_cases h : coneV A o c
  · rw [if_pos h]
    obtain ⟨y, hy, hey⟩ := Lk_mem (A := A) (o := o) (j := j) (K := fun _ => 0) c
    rw [← hey, lamK_high (h y hy)]
  · rw [if_neg h]
    have hex : ∃ y, Relation.ReflTransGen (nextrel0 A) y c ∧ entry A 1 y ≤ o := by
      by_contra hn
      push_neg at hn
      exact h (fun y hy => hn y hy)
    obtain ⟨y, hy, hle⟩ := hex
    have h1 := Lk_le (A := A) (o := o) (j := j) (K := fun _ => 0) hy
    have h2 : lamK A o j (fun _ => 0) y = 0 := by
      unfold lamK
      simp only [Nat.zero_min]
      split_ifs <;> omega
    omega

/-- ★ κ ≡ 0 の klift は、閾値 o のマスクリフト。 -/
theorem klift_zero_eq_mlift (A : TrioSeq) (o j : ℕ) : klift A o j (fun _ => 0) = mlift A o j := by
  unfold klift mlift
  congr 1
  funext c
  rw [Lk_zero_eq]

end KlC
end TRIO
