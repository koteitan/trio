/-
KlD.lean: klift と、段 < o にしか段差のない階段リフトの可換（状態の持ち上げ reliftX との可換）。

    klift_slift_comm : slift (klift X o j K) φ = klift (slift X φ) (φ o) j K     （m ≥ o で φ m − m 一定）
    klift_reliftX    : reliftX b f g A (klift X (b+o) j K) = klift (reliftX b f g A X) (reStair b f g A (b+o)) j K
-/
import KlC
import GyB

namespace TRIO
namespace KlD

open Classical Wset KlA KlB GyB

theorem amin_klift_low {X : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {c : ℕ} (hc : c < X.length)
    (h : amin X c < o) : amin (klift X o j K) c = amin X c := by
  apply le_antisymm
  · obtain ⟨y, hy, hey⟩ := amin_mem X c
    have hyl : y < X.length := by have := rtg0_le hy; omega
    have hlo : entry X 1 y < o := by omega
    have := amin_le (A := klift X o j K) (rtg0_klift.2 hy)
    rw [entry1_klift hyl, Lk_low hlo] at this
    omega
  · obtain ⟨y, hy, hey⟩ := amin_mem (klift X o j K) c
    have hy' := rtg0_klift.1 hy
    have hyl : y < X.length := by have := rtg0_le hy'; omega
    rw [entry1_klift hyl] at hey
    have := amin_le hy'
    omega

theorem amin_klift_high {X : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {c : ℕ} (hc : c < X.length)
    (h : o ≤ amin X c) : o ≤ amin (klift X o j K) c := by
  obtain ⟨y, hy, hey⟩ := amin_mem (klift X o j K) c
  have hy' := rtg0_klift.1 hy
  have hyl : y < X.length := by have := rtg0_le hy'; omega
  rw [entry1_klift hyl] at hey
  have := amin_le hy'
  omega

theorem Lk_slift {X : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {φ : ℕ → ℕ} (hφ : Stair φ)
    (hS : ∀ m, o ≤ m → φ m - m = φ o - o) {c : ℕ} (hc : c < X.length) :
    Lk (slift X φ) (φ o) j K c = Lk X o j K c := by
  by_cases hlo : amin X c < o
  · obtain ⟨y, hy, hey⟩ := amin_mem X c
    have hyl : y < X.length := by have := rtg0_le hy; omega
    have hy1 : entry X 1 y < o := by omega
    have h1 : Lk X o j K c = 0 := by
      have := Lk_le (A := X) (o := o) (j := j) (K := K) hy
      rw [lamK_low hy1] at this; omega
    have h2 : entry (slift X φ) 1 y < φ o := by
      rw [entry1_slift hyl]
      have hs := hφ.step (amin X y) (entry X 1 y) (amin_self_le X y)
      have hge := hφ.ge (amin X y)
      have hmono := stair_strictMono hφ hy1
      have hge2 := hφ.ge (entry X 1 y)
      omega
    have := Lk_le (A := slift X φ) (o := φ o) (j := j) (K := K) (rtg0_slift.2 hy)
    rw [lamK_low h2] at this
    omega
  · have hhi : o ≤ amin X c := by omega
    have hlam : ∀ y, Relation.ReflTransGen (nextrel0 X) y c →
        lamK (slift X φ) (φ o) j K y = lamK X o j K y := by
      intro y hy
      have hyl : y < X.length := by have := rtg0_le hy; omega
      have hay : o ≤ amin X y := le_trans hhi (amin_mono hy)
      have hS1 := hS (amin X y) hay
      have hr : entry (slift X φ) 1 y = entry X 1 y + (φ o - o) := by rw [entry1_slift hyl, hS1]
      have hφo := hφ.ge o
      unfold lamK
      rw [hr, entry2_slift]
      split_ifs <;> omega
    refine le_antisymm ?_ ?_
    · obtain ⟨y, hy, hey⟩ := Lk_mem (A := X) (o := o) (j := j) (K := K) c
      rw [← hey, ← hlam y hy]; exact Lk_le (rtg0_slift.2 hy)
    · obtain ⟨y, hy, hey⟩ := Lk_mem (A := slift X φ) (o := φ o) (j := j) (K := K) c
      have hy' := rtg0_slift.1 hy
      rw [← hey, hlam y hy']; exact Lk_le hy'

/-- ★ klift と、段 < o にしか段差のない階段リフトは可換。 -/
theorem klift_slift_comm {X : TrioSeq} {o j : ℕ} {K : ℕ → ℕ} {φ : ℕ → ℕ} (hφ : Stair φ)
    (hS : ∀ m, o ≤ m → φ m - m = φ o - o) :
    slift (klift X o j K) φ = klift (slift X φ) (φ o) j K := by
  refine List.ext_getElem (by simp) ?_
  intro i hi1 _
  rw [slift_length, klift_length] at hi1
  rw [← entry_triple (X := slift (klift X o j K) φ) (by rw [slift_length, klift_length]; exact hi1),
    ← entry_triple (X := klift (slift X φ) (φ o) j K) (by rw [klift_length, slift_length]; exact hi1)]
  simp only [entry0_slift, entry0_klift, entry2_slift, entry2_klift]
  rw [entry1_slift (A := klift X o j K) (by rw [klift_length]; exact hi1), entry1_klift hi1,
    entry1_klift (A := slift X φ) (by rw [slift_length]; exact hi1), entry1_slift hi1,
    Lk_slift hφ hS hi1]
  have hA : φ (amin (klift X o j K) i) - amin (klift X o j K) i = φ (amin X i) - amin X i := by
    by_cases hlo : amin X i < o
    · rw [amin_klift_low hi1 hlo]
    · have h1 := amin_klift_high (j := j) (K := K) hi1 (by omega : o ≤ amin X i)
      rw [hS _ h1, hS (amin X i) (by omega)]
  rw [hA]
  congr 1
  congr 1
  omega

theorem reStep_const {b o m : ℕ} {f g : ℕ → ℕ} {A0 : List ℕ} (hm : b + o ≤ m) :
    ∀ L : List ℕ, (∀ a ∈ L, liftVal f A0 a < o) →
      reStep b f g A0 L m = reStep b f g A0 L (b + o)
  | [], _ => rfl
  | a :: L, h => by
      have ha := h a (by simp)
      simp only [reStep]
      rw [reStep_const hm L (fun x hx => h x (by simp [hx])), if_pos (by omega), if_pos (by omega)]

/-- ★ klift と状態の持ち上げ reliftX は可換（錨の位置が全て節点の段より下）。 -/
theorem klift_reliftX {X : TrioSeq} {b o j : ℕ} {K : ℕ → ℕ} {f g : ℕ → ℕ} {A : List ℕ}
    (hA : ∀ a ∈ A, liftVal f A a < o) :
    reliftX b f g A (klift X (b + o) j K)
      = klift (reliftX b f g A X) (reStair b f g A (b + o)) j K := by
  unfold reliftX
  refine klift_slift_comm (reStair_stair b f g A) (fun m hm => ?_)
  unfold reStair
  rw [reStep_const hm A hA]
  omega

/-- ★ 段 b < o の基準の持ち上げと klift は可換（閾値は o + d に移る）。 -/
theorem klift_mlift_low {X : TrioSeq} {o j b d : ℕ} {K : ℕ → ℕ} (hb : b < o) :
    mlift (klift X o j K) b d = klift (mlift X b d) (o + d) j K := by
  rw [mlift_eq_slift, mlift_eq_slift]
  have h := klift_slift_comm (X := X) (o := o) (j := j) (K := K) (stair_step b d)
    (fun m hm => by simp [show b < m by omega, hb])
  simpa only [if_pos hb] using h

end KlD
end TRIO
