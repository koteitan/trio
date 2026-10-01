/-
**2 行・t = 1・q ≠ r の組み立て: 残る仮定は (W)・始点の条件・F1 の保存。**

`twoRow_chain'` の枠の条件 `FrameD` を `frameD_path`（`TwoRowF`）と (L)（`TwoRowL`）から出す。
-/
import Ytosk.TwoRowL

namespace Ytosk

open T

/-- `M[1]` is `M` without its last column (`t ≥ 1`). -/
theorem expand_one_eq {M : Mat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    {r : Nat} (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) : expand M 1 = M.take (M.length - 1) := by
  have hrx := par_lt M _ _ _ hr
  have hlen : (expand M 1).length = M.length - 1 := by
    rw [expand_eq_gexp_t1 M 1 hM hz hr ht1, TRIO.gexp_length (by omega)]; omega
  rw [← expand_take_prefix M hM (Nat.le_refl 1), List.take_of_length_le (by omega)]

theorem isSucc_psi_nz {v w : T} (h : psi v w z ≠ one) : isSucc (psi v w z) = false := by
  simp [isSucc, last]; exact h

theorem twoRow_chain_W {M : Mat} {r q : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hG : Good2 M) (hb1 : 0 < entry M 1 (M.length - 1))
    (hq : par M 0 (M.length - 1) = some q) (hqμ : lt (vr M r) (vr M q) = true)
    (hF1 : ∀ k, 1 ≤ k → F1 (expand M k))
    (hSa : ∀ a', ¬ lt (vr M r) a' = true → isOT (psi a' (argOf (o2r M r)) z) = true →
      SeedOK a' (argOf (o2r M r)) (vr M r) (o2r (expand M 1) r))
    (hW : ∀ m h p s y, Anc0 M p (M.length - 1) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
      lt (bst M h p) (fsD y (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) m)) = true) :
    ∀ k, 2 ≤ k →
      o2r (expand M k) r = gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) (k - 1) ∧
      ∀ h, Anc0 M h (M.length - 1) →
        o2r (expand M k) h =
          fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) (k - 2)) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hr1 : par M 1 (M.length - 1) = some r := by have h := hr; rw [ht1] at h; exact h
  have hrx := par_lt M 1 _ r hr1
  obtain ⟨m0, hm0, he⟩ := hG.f1 (M.length - 1) hb1
  rw [hr1] at hm0; cases hm0
  have hvx : vr M (M.length - 1) = succ (vr M r) := by
    rw [vr_eq_nT hG.f1, vr_eq_nT hG.f1, ← he, nT_succ]
  obtain ⟨b, hrv, hb, hcb, hbelow, habove⟩ := twoRow_shape hG hx hr1 hb1
  have hbarg : argOf (o2r M r) = b := by rw [hrv]; rfl
  have hμμ : ¬ lt (vr M r) (vr M r) = true := by simp [Bool.eq_false_iff.mpr (lt_irrefl' _)]
  have hot : isOT (psi (vr M r) b z) = true := by rw [← hrv]; exact hG.ot r
  have hS := hSa _ hμμ (by rw [hbarg]; exact hot)
  rw [hbarg] at hS
  -- the seed has subscript `μ`
  have hc1 : ∃ y1, o2r (expand M 1) r = psi (vr M r) y1 z := by
    rw [expand_one_eq hM hz hr ht1, o2r_eq]
    show ∃ y1, add (sp (sf (vr (M.take (M.length - 1)) r)) z (sf _)) (sf z) = _
    rw [vr_take M r hrx, sf_ot (isOT_vr hG.f1 r), sp_eq_spArg]
    exact ⟨_, rfl⟩
  have hζsingle : ∀ m, ∃ y1, gamS (vr M r) b (o2r (expand M 1) r) m = psi (vr M r) y1 z := by
    intro m; cases m with
    | zero => exact hc1
    | succ m => exact ⟨_, rfl⟩
  apply twoRow_chain' hM hz hr ht1 hG hb1 hF1 hSa
  intro m h p hp hph
  rw [hbarg] at hW ⊢
  have hζne : gamS (vr M r) b (o2r (expand M 1) r) m ≠ z := by
    obtain ⟨y1, hy1⟩ := hζsingle m; rw [hy1]; simp
  apply frameD_path hG hx hp hph
  · -- `fsD` is standard and smaller
    rcases Nat.lt_or_ge r p with h1 | h1
    · have hc := hbelow p hp h1
      rw [fsD_eq_fs hc]
      exact fs_ot_lt (hG.ot p) ⟨gamS_ot hot hcb hμμ hS m, by rw [hc]; exact gamS_lt_om hot hcb hμμ hS m⟩
    · obtain ⟨a', ha', hD⟩ := habove p hp h1
      have hSa' := hSa a' ha' (by rw [hbarg]; exact DiagAt.ot_node hD (hG.ot p))
      rw [hbarg] at hSa'
      obtain ⟨h2, h3⟩ := fsD_seed hSa' hD (hG.ot p) m
      exact ⟨h2, h3.1⟩
  · obtain ⟨w, hw⟩ := o2r_sub hG p
    rw [hw]; apply isSucc_psi_nz; rw [← hw]
    exact path_value_ne_one hG hx hq hvx hqμ hp
  · intro s y hc hy
    have hpx : p < M.length - 1 := by
      rcases Nat.eq_or_lt_of_le hp.le with h' | h'
      · exfalso; rw [h', o2r_leaf hx (isOT_vr hG.f1 _)] at hc; cases hc; exact hy rfl
      · exact h'
    have := isSucc_argOf_path hG hx hq hvx hqμ hp hpx
    rw [hc] at this; exact this
  · intro s hc s' y' hq'
    have hpx : p = M.length - 1 := by
      rcases Nat.eq_or_lt_of_le hp.le with h' | h'
      · exact h'
      · exfalso
        have := argOf_path_ne_z hG hx hp h'
        rw [hc] at this; exact this rfl
    subst hpx
    rw [hq] at hph; cases hph
    rw [o2r_leaf hx (isOT_vr hG.f1 _), hvx, fsD_leaf (isSucc_succ _)
      (by intro h'; have := isSucc_succ (vr M r); rw [h'] at this; simp [isSucc, last, one] at this)] at hq'
    obtain ⟨y1, hy1⟩ := hζsingle m
    rw [hy1] at hq'
    simp [summands] at hq'
    obtain ⟨rfl, _⟩ := hq'
    exact Or.inr hqμ
  · intro s y hc htr1 htr2
    exact hW m h p s y hp hph hc htr1 htr2
  · intro s y hc htr1 _
    have hy : y ≠ z := by rintro rfl; simp [lt] at htr1
    exact L_path hG hx hq hvx hqμ hζne hp hc hy

/-- **The two-row `t = 1`, `q ≠ r` chain from the invariant W2** (`b ≤ y⟨0⟩` at rewriting frames). -/
theorem twoRow_chain_W2 {M : Mat} {r q : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hG : Good2 M) (hb1 : 0 < entry M 1 (M.length - 1))
    (hq : par M 0 (M.length - 1) = some q) (hqμ : lt (vr M r) (vr M q) = true)
    (hF1 : ∀ k, 1 ≤ k → F1 (expand M k))
    (hSa : ∀ a', ¬ lt (vr M r) a' = true → isOT (psi a' (argOf (o2r M r)) z) = true →
      SeedOK a' (argOf (o2r M r)) (vr M r) (o2r (expand M 1) r))
    (hW2 : ∀ h p s y, Anc0 M p (M.length - 1) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true → bst M h p ≤ fsD y z) :
    ∀ k, 2 ≤ k →
      o2r (expand M k) r = gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) (k - 1) ∧
      ∀ h, Anc0 M h (M.length - 1) →
        o2r (expand M k) h =
          fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) (k - 2)) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hr1 : par M 1 (M.length - 1) = some r := by have h := hr; rw [ht1] at h; exact h
  obtain ⟨b, hrv, hb, hcb, hbelow, habove⟩ := twoRow_shape hG hx hr1 hb1
  have hbarg : argOf (o2r M r) = b := by rw [hrv]; rfl
  apply twoRow_chain_W hM hz hr ht1 hG hb1 hq hqμ hF1 hSa
  intro m h p s y hp hph hc htr1 htr2
  have hy : y ≠ z := by rintro rfl; simp [lt] at htr1
  have hζpos : z < gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) m := by
    cases m with
    | zero =>
      obtain ⟨w, w', hw⟩ := o2r_psi_form (expand M 1) r
      show z < o2r (expand M 1) r
      rw [hw]; exact T.z_lt_psi _ _ _
    | succ m => exact T.z_lt_psi _ _ _
  have hmono : fsD y z < fsD y (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) m) := by
    rcases Nat.lt_or_ge r p with h1 | h1
    · have hcp := hbelow p hp h1
      rw [hc] at hcp
      exact fsD_mono_big (cof_psi_inv hy hcp).1 hζpos
    · obtain ⟨a', _, hD⟩ := habove p hp h1
      rw [hc] at hD
      by_cases hne : s = a' ∧ y = b
      · obtain ⟨_, rfl⟩ := hne
        exact fsD_mono_big hcb hζpos
      · exact (DiagAt.arg_inv hD hy hne).fsD_mono hζpos
  exact lt_of_le_of_lt (hW2 h p s y hp hph hc htr1 htr2) hmono

/-- **The two-row `t = 1`, `q ≠ r` chain when the seed is Denis's `γ_1`.** -/
theorem twoRow_chain_gam {M : Mat} {r q : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hG : Good2 M) (hb1 : 0 < entry M 1 (M.length - 1))
    (hq : par M 0 (M.length - 1) = some q) (hqμ : lt (vr M r) (vr M q) = true)
    (hF1 : ∀ k, 1 ≤ k → F1 (expand M k))
    (hc1 : o2r (expand M 1) r = psi (vr M r) (fs (argOf (o2r M r)) z) z)
    (hW2 : ∀ h p s y, Anc0 M p (M.length - 1) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true → bst M h p ≤ fsD y z) :
    ∀ k, 2 ≤ k →
      o2r (expand M k) r = gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) (k - 1) ∧
      ∀ h, Anc0 M h (M.length - 1) →
        o2r (expand M k) h =
          fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) (k - 2)) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hr1 : par M 1 (M.length - 1) = some r := by have h := hr; rw [ht1] at h; exact h
  obtain ⟨b, hrv, _, hcb, _, _⟩ := twoRow_shape hG hx hr1 hb1
  have hbarg : argOf (o2r M r) = b := by rw [hrv]; rfl
  apply twoRow_chain_W2 hM hz hr ht1 hG hb1 hq hqμ hF1 _ hW2
  intro a' ha' hot'
  rw [hc1, hbarg] at *
  exact seedOK_gam1 hot' hcb ha'

end Ytosk
