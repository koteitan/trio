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

section
variable {M : Mat} {j0 Lb n : Nat} (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
  (hA : Anc0 M j0 (j0 + Lb)) {g : Nat} (hg : par M 0 j0 = some g) (hn : 1 ≤ n)
  (hx0 : par M 0 (j0 + Lb) = some j0)
  (hpre : ∀ c, c < j0 + Lb → par (TRIO.gexp M j0 Lb 0 0 n) 0 c = par M 0 c)
include hlen hLb hA hg hn hx0 hpre

/-- Columns before `r` other than `g` keep their children (`t = 0`). -/
theorem children_gexp_lt_t0 {h : Nat} (h1 : h < j0) (hhg : h ≠ g) :
    children (TRIO.gexp M j0 Lb 0 0 n) h = children M h := by
  have hlen' := TRIO.gexp_length (d0 := 0) (d1 := 0) (n := n) hlen
  have hhj : h ≠ j0 := by omega
  apply eq_of_sorted_mem _ _ (children_sorted _ _) (children_sorted _ _)
  intro c
  rw [mem_children_iff, mem_children_iff]
  constructor
  · rintro ⟨hcl, hcp⟩
    rcases Nat.lt_or_ge c (j0 + Lb) with h2 | h2
    · rw [hpre c h2] at hcp; exact ⟨by omega, hcp⟩
    · exfalso
      obtain ⟨k', q'', hk', hq'', rfl⟩ := TRIO.gexp_pos_decomp (j0 := j0) (n := n) (p := c) hLb
        (by omega) (by rw [hlen'] at hcl; exact hcl)
      rcases Nat.eq_zero_or_pos q'' with h0 | h0
      · subst h0
        rw [par0_gexp_root_t0 hlen hLb hk' hA hg] at hcp
        exact hhg (Option.some.inj hcp).symm
      · obtain ⟨pa, hpa⟩ := par0_some_of (show j0 < j0 + q'' by omega)
          (anc0_interval hA (j0 + q'') (by omega) (by omega))
        have hge := par0_ge_of_anc hA (show j0 < j0 + q'' by omega) (by omega) hpa
        have hpa' : par M 0 (j0 + q'') = some (j0 + (pa - j0)) := by rw [hpa]; congr 1; omega
        rw [par0_gexp_mir hlen hk' hq'' hpa'] at hcp
        have := Option.some.inj hcp; omega
  · rintro ⟨hcl, hcp⟩
    have hcx : c < j0 + Lb := by
      rcases Nat.lt_or_ge c (j0 + Lb) with h2 | h2
      · exact h2
      · exfalso
        have : c = j0 + Lb := by omega
        subst this; rw [hx0] at hcp; exact hhj (Option.some.inj hcp).symm
    have hLn : Lb ≤ n * Lb := by
      have := Nat.mul_le_mul_right Lb hn; simpa using this
    exact ⟨by rw [hlen']; omega, by rw [hpre c hcx]; exact hcp⟩

end

/-- From `g` up, the path values (and their arguments) are successor-type (`t = 0`). -/
theorem succPath_up_t0 {M : Mat} {j0 Lb g : Nat} (hlen : j0 + Lb + 1 = M.length)
    (hA : Anc0 M j0 (j0 + Lb)) (hg : par M 0 j0 = some g) (hG : Good2 M)
    (hx0 : par M 0 (j0 + Lb) = some j0) (hx1 : entry M 1 (j0 + Lb) = 0) :
    ∀ p, Anc0 M p g → SuccPath (argOf (o2r M p)) ∧ SuccPath (o2r M p) := by
  have hgA : Anc0 M g (j0 + Lb) := anc0_up hg hA
  have hrj := o2r_r_succ hG hlen hx0 hx1
  have hne : app (bst M j0 (j0 + Lb)) one ≠ z := fun h => absurd (app_eq_z h).2 (by simp [one])
  have hrs : SuccPath (o2r M j0) := by rw [hrj]; exact SuccPath.base hne (isSucc_succ _)
  -- one frame: from a successor-type child to the parent
  have frame : ∀ h p, Anc0 M p (j0 + Lb) → par M 0 p = some h → SuccPath (o2r M p) →
      SuccPath (argOf (o2r M h)) ∧ SuccPath (o2r M h) := by
    intro h p hp hph hsp
    obtain ⟨y, hy⟩ := o2r_sub hG p
    have hpot : isOT (psi (vr M p) y z) = true := by rw [← hy]; exact hG.ot p
    rw [hy] at hsp
    have hX := SuccPath.step (a := vr M h) (b := bst M h p) hpot hsp
    have hoh : o2r M h = psi (vr M h) (step (vr M h) (bst M h p) (vr M p) y z) z := by
      rw [o2r_frame hG hlen hp hph, hy, spArg_single]
    rw [hoh]
    exact ⟨hX, SuccPath.arg hX.ne_z' hX.not_succ hX⟩
  have key : ∀ m p, g - p ≤ m → Anc0 M p g → SuccPath (argOf (o2r M p)) ∧ SuccPath (o2r M p) := by
    intro m
    induction m with
    | zero =>
      intro p h1 hp
      have := hp.le
      rw [show p = g by omega]
      exact frame g j0 hA hg hrs
    | succ m ih =>
      intro p hm hp
      rcases Nat.eq_or_lt_of_le hp.le with heq | hlt
      · rw [heq]; exact frame g j0 hA hg hrs
      obtain ⟨c, hc, hcA⟩ := anc0_child hp (by omega)
      have hpc := par_lt M 0 c p hc
      exact frame p c (hcA.trans hgA) hc (ih c (by omega) hcA).2
  exact fun p hp => key _ p (Nat.le_refl _) hp

/-- **The two-row `t = 0` expansion from `g` up.** Every value on the path from `g` to the root is a
member `[m]` (`m ≥ 1`) of its natural fundamental sequence. Remaining hypothesis: PRE. -/
theorem twoRow_t0_path {M : Mat} {j0 Lb n g : Nat} (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
    (hA : Anc0 M j0 (j0 + Lb)) (hg : par M 0 j0 = some g) (hn : 2 ≤ n)
    (hx0 : par M 0 (j0 + Lb) = some j0)
    (hpre : ∀ c, c < j0 + Lb → par (TRIO.gexp M j0 Lb 0 0 n) 0 c = par M 0 c)
    (hF : F1 (TRIO.gexp M j0 Lb 0 0 n)) (hG : Good2 M) (hx1 : entry M 1 (j0 + Lb) = 0)
    (hPRE : ∀ h p s y, Anc0 M p (j0 + Lb) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
      bst M h p ≠ z → ∃ rest, y = app (bst M h p) rest ∧ rest ≠ z) :
    ∀ h, Anc0 M h g → ∃ j, o2r (TRIO.gexp M j0 Lb 0 0 n) h = fsD (o2r M h) (natT (j + 1)) ∧
      isOT (fsD (o2r M h) (natT (j + 1))) = true ∧ fsD (o2r M h) (natT (j + 1)) < o2r M h := by
  have hn1 : 1 ≤ n := by omega
  have hgA : Anc0 M g (j0 + Lb) := anc0_up hg hA
  have hgj := par_lt M 0 j0 g hg
  have hsp := succPath_up_t0 hlen hA hg hG hx0 hx1
  -- standardness and descent of `fsD = fs` on successor-type values
  have hOK : ∀ p, Anc0 M p g → ∀ k, 1 ≤ k →
      isOT (fsD (o2r M p) (natT k)) = true ∧ fsD (o2r M p) (natT k) < o2r M p := by
    intro p hp k _
    rw [(hsp p hp).2.fsD_eq]
    exact fs_ot_lt (hG.ot p) ⟨isOT_natT k, by rw [(hsp p hp).2.cof]; exact ⟨k, rfl⟩⟩
  apply o2r_path_from hlen hG (fun j => natT (j + 1)) hgA
  · intro j hj; exact vr_gexp_pre_t0 hlen hLb hA hg hn1 hx0 hpre hF hG hj
  · intro h hh hc
    rcases hc with hnA | hhg
    · exact children_gexp_off_t0 hlen hLb hA hg hn1 hx0 hpre hh hnA
    · exact children_gexp_lt_t0 hlen hLb hA hg hn1 hx0 hpre (by omega) (by omega)
  · -- the leaf `g`
    have hgr := o2r_g_fs_t0 hlen hLb hA hg hn1 hx0 hpre hF hG hx1
    rcases hgr with h1 | h1
    · refine ⟨n - 1, ?_, hOK g (Anc0.refl g) _ (by omega)⟩
      rw [show n - 1 + 1 = n by omega, (hsp g (Anc0.refl g)).2.fsD_eq]; exact h1
    · refine ⟨n - 2, ?_, hOK g (Anc0.refl g) _ (by omega)⟩
      rw [show n - 2 + 1 = n - 1 by omega, (hsp g (Anc0.refl g)).2.fsD_eq]; exact h1
  · -- the frames above `g`
    intro h p j hp hph hokOT hoklt
    have hpx : Anc0 M p (j0 + Lb) := hp.trans hgA
    have hhA : Anc0 M h g := anc0_up hph hp
    obtain ⟨hargp, hop⟩ := hsp p hp
    refine ⟨j, ?_, hOK h hhA _ (by omega)⟩
    have hFD : FrameD (vr M h) (bst M h p) (o2r M p) (natT (j + 1)) := by
      apply frameD_path hG hlen hpx hph ⟨hokOT, hoklt⟩ hop.not_succ
      · intro s y hc _
        rw [hc] at hargp; exact hargp.not_succ
      · intro s hc; exfalso; rw [hc] at hargp; exact hargp.ne_z' rfl
      · intro s y hc ht1 ht2
        rw [hc] at hargp
        change SuccPath y at hargp
        apply trig_persist_of_pre _ (hPRE h p s y hpx hph hc ht1 ht2)
        rw [hargp.fsD_eq, hargp.fsD_eq]
        exact hargp.fs_mono_nat' (show 0 < j + 1 by omega)
      · intro s y hc _ _
        rw [hc] at hargp
        exact L_succ hargp (by omega)
    rw [o2r_frame hG hlen hpx hph]
    exact (node_fsD hFD).symm

end Ytosk
