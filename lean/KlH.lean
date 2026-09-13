/-
KlH.lean: klift と、帯 [v, v+J) にしか段差のない階段リフトの可換（挿入した錨の状態の持ち上げ、tools/probe_kappa_band.py）。

    klift_slift_band : slift (klift X v J K) φ = klift X v (J + C) (bandK v J φ K)
      （φ m = m（m ≤ v）、φ m − m = C（m ≥ v + J））
    bandK v J φ K y = mK + (φ (v + mK) − (v + mK))、mK = min (K y) J
-/
import KlG

namespace TRIO
namespace KlH

open Classical Wset KlA KlB KlE KlG GxP

def bandK (v J : ℕ) (φ : ℕ → ℕ) (K : ℕ → ℕ) : ℕ → ℕ :=
  fun y => min (K y) J + (φ (v + min (K y) J) - (v + min (K y) J))

section Band

variable {X : TrioSeq} {v J C : ℕ} {K : ℕ → ℕ} {φ : ℕ → ℕ}

theorem step_mono (hφ : Stair φ) {a b : ℕ} (h : a ≤ b) :
    a + (φ (v + a) - (v + a)) ≤ b + (φ (v + b) - (v + b)) := by
  have := hφ.step (v + a) (v + b) (by omega); omega

theorem lamK_band (hφ : Stair φ) (hlow : ∀ m, m ≤ v → φ m = m)
    (hC : ∀ m, v + J ≤ m → φ m - m = C) (y : ℕ) :
    lamK X v (J + C) (bandK v J φ K) y
      = lamK X v J K y + (φ (v + lamK X v J K y) - (v + lamK X v J K y)) := by
  have hstep0 : φ (v + 0) - (v + 0) = 0 := by rw [Nat.add_zero, hlow v le_rfl, Nat.sub_self]
  have hJ : φ (v + J) - (v + J) = C := hC _ le_rfl
  by_cases h1 : entry X 1 y < v
  · rw [lamK_low h1, lamK_low h1, hstep0]
  · by_cases h2 : entry X 1 y = v
    · by_cases h3 : entry X 2 y = 0
      · have e1 : lamK X v J K y = min (K y) J := by
          unfold lamK; rw [if_neg h1, if_pos h2, if_pos h3]
        have e2 : lamK X v (J + C) (bandK v J φ K) y = min (bandK v J φ K y) (J + C) := by
          unfold lamK; rw [if_neg h1, if_pos h2, if_pos h3]
        rw [e1, e2]
        have hm := hφ.step (v + min (K y) J) (v + J) (by omega)
        unfold bandK
        omega
      · have e1 : lamK X v J K y = 0 := by unfold lamK; rw [if_neg h1, if_pos h2, if_neg h3]
        have e2 : lamK X v (J + C) (bandK v J φ K) y = 0 := by
          unfold lamK; rw [if_neg h1, if_pos h2, if_neg h3]
        rw [e1, e2, hstep0]
    · have h4 : v < entry X 1 y := by omega
      rw [lamK_high h4, lamK_high h4, hJ]

theorem Lk_band (hφ : Stair φ) (hlow : ∀ m, m ≤ v → φ m = m)
    (hC : ∀ m, v + J ≤ m → φ m - m = C) (c : ℕ) :
    Lk X v (J + C) (bandK v J φ K) c
      = Lk X v J K c + (φ (v + Lk X v J K c) - (v + Lk X v J K c)) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := X) (o := v) (j := J) (K := K) c
    have := Lk_le (A := X) (o := v) (j := J + C) (K := bandK v J φ K) hy
    rw [lamK_band hφ hlow hC, hey] at this
    exact this
  · obtain ⟨y, hy, hey⟩ := Lk_mem (A := X) (o := v) (j := J + C) (K := bandK v J φ K) c
    rw [← hey, lamK_band hφ hlow hC]
    exact step_mono hφ (Lk_le hy)

theorem amin_band (hφ : Stair φ) (hlow : ∀ m, m ≤ v → φ m = m)
    (hC : ∀ m, v + J ≤ m → φ m - m = C) {c : ℕ} (hc : c < X.length) :
    φ (amin (klift X v J K) c) - amin (klift X v J K) c
      = φ (v + Lk X v J K c) - (v + Lk X v J K c) := by
  have hle : ∀ m, m ≤ v → φ m - m = 0 := fun m hm => by rw [hlow m hm, Nat.sub_self]
  rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
  · subst hJ0
    have hstep : ∀ m, φ m - m = 0 := by
      intro m
      by_cases hm : m ≤ v
      · exact hle m hm
      · have h1 := hC m (by omega)
        have h2 := hC v (by omega)
        rw [hle v le_rfl] at h2
        omega
    rw [hstep, hstep]
  obtain ⟨x, hx, hex⟩ := Lk_mem (A := X) (o := v) (j := J) (K := K) c
  have hxl : x < X.length := by have := rtg0_le hx; omega
  have hLx : Lk X v J K x = Lk X v J K c :=
    le_antisymm (by rw [← hex]; exact Lk_le Relation.ReflTransGen.refl) (Lk_mono hx)
  have hax : amin (klift X v J K) c ≤ entry X 1 x + Lk X v J K c := by
    have := amin_le (A := klift X v J K) (rtg0_klift.2 hx)
    rwa [entry1_klift hxl, hLx] at this
  rcases Nat.eq_zero_or_pos (Lk X v J K c) with h0 | hpos
  · have hx1 : entry X 1 x ≤ v := by
      by_contra hh
      push_neg at hh
      rw [lamK_high hh] at hex
      omega
    rw [hle _ (by omega), h0, Nat.add_zero, hle v le_rfl]
  · have hall : ∀ y, Relation.ReflTransGen (nextrel0 X) y c →
        v + Lk X v J K c ≤ entry X 1 y + Lk X v J K y := by
      intro y hy
      have hLy := Lk_mono (A := X) (o := v) (j := J) (K := K) hy
      have hly := Lk_le (A := X) (o := v) (j := J) (K := K) hy
      by_contra hh
      have hy1 : entry X 1 y < v := by omega
      rw [lamK_low hy1] at hly
      omega
    have hamin : v + Lk X v J K c ≤ amin (klift X v J K) c := by
      obtain ⟨y, hy, hey⟩ := amin_mem (klift X v J K) c
      have hy' := rtg0_klift.1 hy
      have hyl : y < X.length := by have := rtg0_le hy'; omega
      rw [entry1_klift hyl] at hey
      have := hall y hy'
      omega
    by_cases hLJ : Lk X v J K c < J
    · have hx1 : entry X 1 x = v := by
        have hx0 : ¬ entry X 1 x < v := by
          intro hh; rw [lamK_low hh] at hex; omega
        have hx2 : ¬ v < entry X 1 x := by
          intro hh; rw [lamK_high hh] at hex; omega
        omega
      rw [show amin (klift X v J K) c = v + Lk X v J K c by omega]
    · have hLJ' : Lk X v J K c = J := le_antisymm (Lk_le_j c) (by omega)
      rw [hC _ (by omega), hLJ', hC _ le_rfl]

/-- ★ 帯の中にしか段差のない階段リフトと klift は可換（J は C だけ増え、κ は bandK）。 -/
theorem klift_slift_band (hφ : Stair φ) (hlow : ∀ m, m ≤ v → φ m = m)
    (hC : ∀ m, v + J ≤ m → φ m - m = C) :
    slift (klift X v J K) φ = klift X v (J + C) (bandK v J φ K) := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [slift_length, klift_length] at hi
  rw [slift_getD (by rw [klift_length]; exact hi), klift_getD hi, entry0_klift, entry2_klift,
    entry1_klift hi, amin_band hφ hlow hC hi, Lk_band hφ hlow hC, Nat.add_assoc]

end Band

end KlH
end TRIO
