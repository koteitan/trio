/-
**2 行: 展開 1 歩で行列の値（根の和 `ev2r`）は下がり標準形のまま（すべての場合）。**

場合分け: 最後の列が (0,0,0)、n = 0, 1（先頭部分）、n ≥ 2 で t = 1（q = r / q ≠ r）・t = 0（r が根 / 根でない）。
残る仮定: 先頭部分で閉じた不変条件（Good2・RootsDec・z0ok）、PRE、q ≠ r での始点の条件。
-/
import Ytosk.TwoRowN

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Two rows: one expansion step lowers the matrix value and keeps it standard.** -/
theorem twoRow_desc {M : Mat} (hM : 1 ≤ M.length) (h2 : entry M 2 (M.length - 1) = 0)
    (hI : ∀ j, j ≤ M.length → Good2 (M.take j) ∧ RootsDec (M.take j) ∧ TRIO.z0ok (M.take j))
    (hr1 : TRIO.r1ok M) (hz0 : TRIO.z0ok M) (h00 : entry M 0 0 = 0)
    (hPRE : ∀ h p s y, Anc0 M p (M.length - 1) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
      bst M h p ≠ z → ∃ rest, y = app (bst M h p) rest ∧ rest ≠ z)
    (hSeed : ∀ r, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) ≠ some r →
      ∀ a', ¬ lt (vr M r) a' = true → isOT (psi a' (argOf (o2r M r)) z) = true →
      SeedOK a' (argOf (o2r M r)) (vr M r) (o2r (expand M 1) r))
    (n : Nat) : isOT (ev2r (expand M n)) = true ∧ ev2r (expand M n) < ev2r M := by
  have hGM : Good2 M := by have := (hI M.length (Nat.le_refl _)).1; rwa [List.take_length] at this
  have hRD : RootsDec M := by have := (hI M.length (Nat.le_refl _)).2.1; rwa [List.take_length] at this
  have htake := ev2r_take_lt hI h00
  by_cases hcol : col M (M.length - 1) = (0, 0, 0)
  · rw [expand_zero_col hM hcol n]; exact htake _ (by omega)
  have hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := by
    rintro ⟨e0, e1, e2⟩; apply hcol; unfold col
    have e0' : (M.getD (M.length - 1) (0, 0, 0)).1 = 0 := e0
    have e1' : (M.getD (M.length - 1) (0, 0, 0)).2.1 = 0 := e1
    have e2' : (M.getD (M.length - 1) (0, 0, 0)).2.2 = 0 := e2
    rcases hc : M.getD (M.length - 1) (0, 0, 0) with ⟨a, b, c⟩
    rw [hc] at e0' e1' e2'; simp at e0' e1' e2'; rw [e0', e1', e2']
  have hx0 : 0 < entry M 0 (M.length - 1) := by
    rcases Nat.eq_zero_or_pos (entry M 0 (M.length - 1)) with h | h
    · exfalso
      obtain ⟨e1, e2⟩ := hz0 (M.length - 1) (by omega) h
      exact hz ⟨h, e1, e2⟩
    · exact h
  have hM2 : 2 ≤ M.length := by
    by_contra hcon
    obtain ⟨k, hk, _⟩ := hr1 (M.length - 1) (by omega) hx0
    omega
  -- the bad root
  have hsrow : TRIO.srow M (M.length - 1) = if 0 < entry M 1 (M.length - 1) then 1 else 0 := by
    unfold TRIO.srow; rw [← entry_eq, ← entry_eq, h2]; simp
  obtain ⟨r, hr⟩ : ∃ r, par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r := by
    rw [hsrow]
    split_ifs with hb
    · obtain ⟨m, hm, _⟩ := hGM.f1 _ hb; exact ⟨m, hm⟩
    · exact par0_some_of (show 0 < M.length - 1 by omega) (by rw [h00]; exact hx0)
  have hrx := par_lt M _ _ _ hr
  rcases n with _ | _ | n
  · rw [expand_n0 hM2 hz hr]; exact htake r (by omega)
  · rw [expand_n1 hM2 hz hr]; exact htake _ (by omega)
  have hn : 2 ≤ n + 2 := by omega
  by_cases hb : 0 < entry M 1 (M.length - 1)
  · have ht1 : TRIO.srow M (M.length - 1) = 1 := by rw [hsrow, if_pos hb]
    have hr1' : par M 1 (M.length - 1) = some r := by have h := hr; rw [ht1] at h; exact h
    obtain ⟨q, hq⟩ := par0_some_of (M := M) (show 0 < M.length - 1 by omega) (by rw [h00]; exact hx0)
    by_cases hqr : q = r
    · subst hqr
      exact twoRow_desc_qr hM2 hz hr ht1 hGM hb hr1 hz0 hRD h00 hq hPRE hn
    · exact twoRow_desc_ne hM2 hz hr ht1 hGM hb hr1 hz0 hRD h00 hq hqr
        (hSeed r hr1' (by rw [hq]; intro h; exact hqr (Option.some.inj h))) hPRE hn
  · have ht0 : TRIO.srow M (M.length - 1) = 0 := by rw [hsrow, if_neg hb]
    cases hg : par M 0 r with
    | none => exact twoRow_desc_t0_root hM2 hz hr ht0 hGM hr1 hz0 hRD h00 hg hn
    | some g => exact twoRow_desc_t0 hM2 hz hr ht0 hGM hr1 hz0 hRD h00 hg hn hPRE

end Ytosk
