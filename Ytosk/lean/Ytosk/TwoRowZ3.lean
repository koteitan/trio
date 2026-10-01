/-
**2 行・t = 0: 行列全体の値（根の和 `ev2r`）の段。**

(a) r が根でない: 写しの列は行 0 が正なので根は増えない。一番上の祖先 ρ は g = P_0(r) の祖先で、
    `twoRow_t0` がそこで値が下がることを与える。
-/
import Ytosk.TwoRowD

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **With `t = 0` and `r` not a root, the expansion keeps the roots.** -/
theorem roots_expand_t0 {M : Mat} {r g n : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht0 : TRIO.srow M (M.length - 1) = 0) (hg : par M 0 r = some g) (hn : 1 ≤ n)
    (hxr : col M (M.length - 1) ≠ (0, 0, 0)) : roots (expand M n) = roots M := by
  have hr0 : par M 0 (M.length - 1) = some r := by have h := hr; rw [ht0] at h; exact h
  have hrx := par_lt M 0 _ r hr0
  have hA : Anc0 M r (M.length - 1) := Anc0.step hr0 (Anc0.refl r)
  have hlen : r + (M.length - 1 - r) + 1 = M.length := by omega
  have hLb : 0 < M.length - 1 - r := by omega
  have heq := expand_eq_gexp_t0 M n hM hz hr ht0
  have hlen' : (expand M n).length = r + n * (M.length - 1 - r) := by
    rw [heq]; exact TRIO.gexp_length hlen
  have hr0pos : 0 < entry M 0 r := by have := ((par0_spec M).mp hg).2.1; omega
  apply roots_eq (x := M.length - 1) (by omega)
  · rw [hlen']; have := Nat.mul_le_mul_right (M.length - 1 - r) hn; simp at this; omega
  · intro c hc
    have h1 := expand_take_prefix M hM hn
    rw [← col_take (expand M n) hc, h1, col_take M hc]
  · exact hxr
  · intro c hc1 hc2
    apply col_ne_zero_of_entry
    rw [hlen'] at hc2
    obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (n := n) (p := c) hLb (by omega) hc2
    rw [heq, entry0_gexp_mir hlen hk hq]
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0; simpa using hr0pos
    · have := anc0_interval hA (r + q) (by omega) (by omega); omega

/-- **Two rows, `t = 0`, `r` not a root: the matrix value drops and stays standard.** Remaining
hypothesis: PRE. -/
theorem twoRow_desc_t0 {M : Mat} {r g n : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht0 : TRIO.srow M (M.length - 1) = 0) (hG : Good2 M)
    (hr1 : TRIO.r1ok M) (hz0 : TRIO.z0ok M) (hRD : RootsDec M) (h00 : entry M 0 0 = 0)
    (hg : par M 0 r = some g) (hn : 2 ≤ n)
    (hPRE : ∀ h p s y, Anc0 M p (M.length - 1) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
      bst M h p ≠ z → ∃ rest, y = app (bst M h p) rest ∧ rest ≠ z) :
    isOT (ev2r (expand M n)) = true ∧ ev2r (expand M n) < ev2r M := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hr0 : par M 0 (M.length - 1) = some r := by have h := hr; rw [ht0] at h; exact h
  have hrx := par_lt M 0 _ r hr0
  have hA : Anc0 M r (M.length - 1) := Anc0.step hr0 (Anc0.refl r)
  have hgA : Anc0 M g (M.length - 1) := anc0_up hg hA
  have hxr : col M (M.length - 1) ≠ (0, 0, 0) := by
    intro h; apply hz; unfold col at h
    rw [← entry_eq, ← entry_eq, ← entry_eq]; unfold entry; rw [h]; simp
  obtain ⟨ρ, hρ, hρn⟩ := top_anc M (M.length - 1)
  have hρ0 := col_zero_of_top hz0 h00 (by have := hρ.le; omega) hρn
  have hρg : Anc0 M ρ g := by
    rcases anc0_total hgA hρ with h' | h'
    · cases h' with
      | refl => exact Anc0.refl _
      | step hp _ => rw [hp] at hρn; cases hρn
    · exact h'
  -- the expansion as `gexp`
  have hlen : r + (M.length - 1 - r) + 1 = M.length := by omega
  have hxe : r + (M.length - 1 - r) = M.length - 1 := by omega
  have hLb : 0 < M.length - 1 - r := by omega
  have hgexp := expand_eq_gexp_t0 M n hM hz hr ht0
  have hpre : ∀ c, c < r + (M.length - 1 - r) →
      par (TRIO.gexp M r (M.length - 1 - r) 0 0 n) 0 c = par M 0 c := by
    intro c hc; rw [← hgexp]; exact par0_expand_prefix M hM (by omega) (by omega)
  have hF : F1 (TRIO.gexp M r (M.length - 1 - r) 0 0 n) := by
    rw [← hgexp]; exact F1_expand hr1 hz0 hM n
  have hA' : Anc0 M r (r + (M.length - 1 - r)) := by rw [hxe]; exact hA
  have hr0' : par M 0 (r + (M.length - 1 - r)) = some r := by rw [hxe]; exact hr0
  obtain ⟨j, hj, hjot, hjlt⟩ := twoRow_t0 hM hz hr ht0 hG hr1 hz0 hg hn hPRE ρ hρg
  apply ev2r_lt_of_top hx hG hRD hρ hρ0 (roots_expand_t0 hM hz hr ht0 hg (by omega) hxr)
  · intro c hc hcρ
    have hcl := (mem_roots.mp hc).1
    have hcx : c < M.length - 1 := by have := hρ.le; omega
    have hnA : ¬ Anc0 M c (M.length - 1) := by
      intro hcA
      rcases anc0_total hcA hρ with h' | h'
      · cases h' with
        | refl => omega
        | step hp _ => rw [hp] at hρn; cases hρn
      · have := h'.le; omega
    rw [hgexp]
    rw [← hxe] at hnA hcx
    refine o2r_off_gen' hlen ?_ ?_ c hcx hnA
    · intro j' hj'
      exact vr_gexp_pre_t0 hlen hLb hA' hg (by omega) hr0' hpre hF hG hj'
    · intro h hh hnA'
      exact children_gexp_off_t0 hlen hLb hA' hg (by omega) hr0' hpre hh hnA'
  · rw [hj]; exact hjot
  · rw [hj]; exact hjlt

end Ytosk
