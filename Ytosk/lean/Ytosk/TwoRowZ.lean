/-
**2 行・t = 0 の展開。**

t = 0 ではコピーは上昇しない（d = 0）ので、コピーの根の行 0 の親は g = P_0(r)（r の兄弟として並ぶ）。
r の値は x を除いて o_M(r)[1]、g より上は o_M(h)[n]（自然数の基本列、fsD(·, natT n) と同じ）。
-/
import Ytosk.TwoRowR

namespace Ytosk

open T

theorem entry0_gexp_low {M : Mat} {j0 Lb d0 d1 n p : Nat} (hlen : j0 + Lb + 1 = M.length) (hp : p < j0) :
    entry (TRIO.gexp M j0 Lb d0 d1 n) 0 p = entry M 0 p := by
  unfold entry
  rw [TRIO.gexp_getD_low hlen hp]

theorem entry0_gexp_mir {M : Mat} {j0 Lb d0 d1 n k q : Nat} (hlen : j0 + Lb + 1 = M.length)
    (hk : k < n) (hq : q < Lb) :
    entry (TRIO.gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + q)) = entry M 0 (j0 + q) + k * d0 := by
  unfold entry
  rw [TRIO.gexp_getD_mir hlen hk hq]; rfl

/-- **With `d0 = 0`, a copy root hangs on the parent of `r`.** -/
theorem par0_gexp_root_t0 {M : Mat} {j0 Lb d1 n k g : Nat} (hlen : j0 + Lb + 1 = M.length)
    (hLb : 0 < Lb) (hk : k < n) (hA : Anc0 M j0 (j0 + Lb))
    (hg : par M 0 j0 = some g) :
    par (TRIO.gexp M j0 Lb 0 d1 n) 0 (j0 + (k * Lb + 0)) = some g := by
  obtain ⟨hgj, hge, hbet⟩ := (par0_spec M).mp hg
  rw [par0_spec]
  have hroot : entry (TRIO.gexp M j0 Lb 0 d1 n) 0 (j0 + (k * Lb + 0)) = entry M 0 j0 := by
    rw [entry0_gexp_mir hlen hk hLb]; simp
  refine ⟨by omega, ?_, ?_⟩
  · rw [hroot, entry0_gexp_low hlen hgj]; exact hge
  · intro j hj1 hj2
    rw [hroot]
    rcases Nat.lt_or_ge j j0 with h | h
    · rw [entry0_gexp_low hlen h]; exact hbet j hj1 h
    · obtain ⟨k', q', hk', hq', rfl⟩ := TRIO.gexp_pos_decomp (n := n) hLb h (by
        have : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
        have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
        omega)
      rw [entry0_gexp_mir hlen hk' hq']
      simp only [Nat.mul_zero, Nat.add_zero]
      rcases Nat.eq_zero_or_pos q' with hq0 | hq0
      · subst hq0; exact Nat.le_refl _
      · exact Nat.le_of_lt (anc0_interval hA (j0 + q') (by omega) (by omega))

end Ytosk
