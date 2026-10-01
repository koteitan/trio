/-
**2 行・t = 0: g より上の経路。**

g より上の値は自然数型（一番深い位置が後続、`SuccPath`）なので fsD = fs。
枠の条件 (L) は自然数型の項の性質として出る（`L_succ`）。書き換えの持続は PRE と基本列の単調性から。
-/
import Ytosk.TwoRowZ

namespace Ytosk

open T

theorem SuccPath.last' {t : T} (h : SuccPath t) : SuccPath (last t) := by
  induction h with
  | base hb hs => exact SuccPath.base hb hs
  | rest _ ih => exact ih
  | arg hb hs hp => exact SuccPath.arg hb hs hp

theorem SuccPath.ne_z' {t : T} (h : SuccPath t) : t ≠ z := by cases h <;> simp

/-- After a natural fundamental sequence, a successor-type summand keeps its subscript. -/
theorem fs_single_ge {u w s : T} (hp : SuccPath (psi u w z)) {k : Nat}
    (hge : ¬ psi u w z < psi (succ s) z z) :
    ∀ q ∈ summands (fs (psi u w z) (natT k)), ¬ q < psi (succ s) z z := by
  rw [psi_lt_om_iff] at hge
  cases hp with
  | base hb hs =>
    unfold fs
    rw [if_neg hb, if_pos hs, count_natT]
    intro q hq
    rw [summands_mulT ⟨_, _, rfl⟩ k q hq, psi_lt_om_iff]; exact hge
  | arg hb hs hp' =>
    unfold fs
    rw [if_neg hb, if_neg (by rw [hs]; simp), hp'.cof]
    simp only
    intro q hq
    simp [summands] at hq; subst hq
    rw [psi_lt_om_iff]; exact hge

theorem fs_single_ne_z {u w : T} (hp : SuccPath (psi u w z)) {k : Nat} (hk : 1 ≤ k) :
    fs (psi u w z) (natT k) ≠ z := by
  cases hp with
  | base hb hs =>
    unfold fs
    rw [if_neg hb, if_pos hs, count_natT]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [mulT]
  | arg hb hs hp' =>
    unfold fs
    rw [if_neg hb, if_neg (by rw [hs]; simp), hp'.cof]
    simp

/-- **Condition (L) for a successor-type argument** (natural index `k ≥ 1`). -/
theorem L_succ {y s : T} (hy : SuccPath y) {k : Nat} (hk : 1 ≤ k) :
    ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 (natT k) ≠ z) ∧
    ((split y (psi (succ s) z z)).2 = z → (split (fsD y (natT k)) (psi (succ s) z z)).2 = z) := by
  have hyz := hy.ne_z'
  have hL := hy.last'
  obtain ⟨u, w, hlw⟩ := mem_summands (last_mem hyz)
  rw [hlw] at hL
  have hLz : psi u w z ≠ z := by simp
  have hbpl := split_app (psi (succ s) z z) y
  have hpge := split_fst_ge (psi (succ s) z z) y
  constructor
  · intro hlo
    generalize hP : split y (psi (succ s) z z) = pr at hbpl hlo ⊢
    obtain ⟨hi, lo⟩ := pr
    simp only at hbpl hlo ⊢
    have hll : last lo = psi u w z := by rw [← hlw, ← hbpl, last_app hi hlo]
    rw [← init_app_last lo, hll, fsD_app _ hLz, hL.fsD_eq]
    intro h; exact fs_single_ne_z hL hk (app_eq_z h).2
  · intro hlo
    have hyhi : y = (split y (psi (succ s) z z)).1 := by rw [hlo, app_z_right] at hbpl; exact hbpl.symm
    have hsum : ∀ q ∈ summands y, ¬ q < psi (succ s) z z := by
      intro q hq; rw [hyhi] at hq; exact hpge q hq
    rw [← init_app_last y, hlw, fsD_app _ hLz, hL.fsD_eq]
    have hB : ∀ q ∈ summands (app (init y) (fs (psi u w z) (natT k))), ¬ q < psi (succ s) z z := by
      intro q hq
      rw [summands_app] at hq
      rcases List.mem_append.mp hq with hq | hq
      · apply hsum; rw [← init_app_last y, summands_app]; exact List.mem_append_left _ hq
      · exact fs_single_ge hL (hsum _ (by rw [← hlw]; exact last_mem hyz)) q hq
    have := split_app_of (B := app (init y) (fs (psi u w z) (natT k))) (X := z) hB (Or.inl rfl)
    rw [app_z_right] at this; rw [this]

end Ytosk
