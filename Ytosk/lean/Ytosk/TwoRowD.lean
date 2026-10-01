/-
**2 行・t = 1・q ≠ r: 行列全体の値（根の和 `ev2r`）が下がる。**

経路の値は fsD(o(h), γ′_m)。r より下は fs、r 以上は始点つき補題 3.3 で、標準形で小さい。
-/
import Ytosk.TwoRowE

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **If `q ≠ r` then `μ = v(r) < v(q)`.** -/
theorem vr_lt_of_ne {M : Mat} {r q : Nat} (hG : Good2 M) (hM : 1 ≤ M.length)
    (hr1 : par M 1 (M.length - 1) = some r) (hb1 : 0 < entry M 1 (M.length - 1))
    (hq : par M 0 (M.length - 1) = some q) (hne : q ≠ r) : lt (vr M r) (vr M q) = true := by
  have hrx := par_lt M 1 _ r hr1
  have hrq : Anc0 M r q := anc0_par (anc0_of_par M 1 r _ hr1) (by omega) hq
  have hlt : r < q := by have := hrq.le; omega
  have h1 := par1_between hr1 q (anc0_of_par M 0 q _ hq) hlt
  obtain ⟨m0, hm0, he⟩ := hG.f1 (M.length - 1) hb1
  rw [hr1] at hm0; cases hm0
  rw [vr_eq_nT hG.f1, vr_eq_nT hG.f1]
  exact lt_nT (by omega)

/-- **On the path, `fsD` with a member of the seeded chain is standard and smaller.** -/
theorem path_ok_seed {M : Mat} {r : Nat} {σ : T} (hM : 2 ≤ M.length) (hG : Good2 M)
    (hr1 : par M 1 (M.length - 1) = some r) (hb1 : 0 < entry M 1 (M.length - 1))
    (hSa : ∀ a', ¬ lt (vr M r) a' = true → isOT (psi a' (argOf (o2r M r)) z) = true →
      SeedOK a' (argOf (o2r M r)) (vr M r) σ) :
    ∀ m h, Anc0 M h (M.length - 1) →
      isOT (fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) σ m)) = true ∧
      fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) σ m) < o2r M h := by
  have hx : M.length - 1 + 1 = M.length := by omega
  obtain ⟨b, hrv, hb, hcb, hbelow, habove⟩ := twoRow_shape hG hx hr1 hb1
  have hbarg : argOf (o2r M r) = b := by rw [hrv]; rfl
  have hμμ : ¬ lt (vr M r) (vr M r) = true := by simp [Bool.eq_false_iff.mpr (lt_irrefl' _)]
  have hot : isOT (psi (vr M r) b z) = true := by rw [← hrv]; exact hG.ot r
  have hS := hSa _ hμμ (by rw [hbarg]; exact hot)
  rw [hbarg] at hS ⊢
  intro m p hp
  rcases Nat.lt_or_ge r p with h1 | h1
  · have hc := hbelow p hp h1
    rw [fsD_eq_fs hc]
    exact fs_ot_lt (hG.ot p) ⟨gamS_ot hot hcb hμμ hS m, by rw [hc]; exact gamS_lt_om hot hcb hμμ hS m⟩
  · obtain ⟨a', ha', hD⟩ := habove p hp h1
    have hSa' := hSa a' ha' (by rw [hbarg]; exact DiagAt.ot_node hD (hG.ot p))
    rw [hbarg] at hSa'
    obtain ⟨h2, h3⟩ := fsD_seed hSa' hD (hG.ot p) m
    exact ⟨h2, h3.1⟩

/-- **Two rows, `t = 1`, `q ≠ r`: the matrix value drops and stays standard.** Remaining hypotheses:
the seed condition and PRE. -/
theorem twoRow_desc_ne {M : Mat} {r q : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hG : Good2 M) (hb1 : 0 < entry M 1 (M.length - 1))
    (hr1 : TRIO.r1ok M) (hz0 : TRIO.z0ok M) (hRD : RootsDec M) (h00 : entry M 0 0 = 0)
    (hq : par M 0 (M.length - 1) = some q) (hne : q ≠ r)
    (hSa : ∀ a', ¬ lt (vr M r) a' = true → isOT (psi a' (argOf (o2r M r)) z) = true →
      SeedOK a' (argOf (o2r M r)) (vr M r) (o2r (expand M 1) r))
    (hPRE : ∀ h p s y, Anc0 M p (M.length - 1) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
      bst M h p ≠ z → ∃ rest, y = app (bst M h p) rest ∧ rest ≠ z) {n : Nat} (hn : 2 ≤ n) :
    isOT (ev2r (expand M n)) = true ∧ ev2r (expand M n) < ev2r M := by
  have hr1' : par M 1 (M.length - 1) = some r := by have h := hr; rw [ht1] at h; exact h
  have hqμ := vr_lt_of_ne hG (by omega) hr1' hb1 hq hne
  have hch := (twoRow_chain_PRE hM hz hr ht1 hG hb1 hq hqμ (fun k _ => F1_expand hr1 hz0 hM k)
    hSa hPRE n hn).2
  apply ev2r_expand_t1 hM hz hr (by omega) hn hG hRD hz0 h00
  intro h hh
  rw [hch h hh]
  exact path_ok_seed hM hG hr1' hb1 hSa _ h hh

end Ytosk
