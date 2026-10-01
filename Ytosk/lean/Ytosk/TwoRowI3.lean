/-
**(I2) 展開で不変条件 Inv2 が保たれる: t = 1（2 行）。**

N = M[n] = gexp M r L d0 0 n、P = M[n−1]。写しの領域（x 以降）は P の r 以降をずらしたもの（値・子・状態・添字）。
x 以前は経路の外が同じ、経路の上が小さい。つなぎ目は (q, x) の枠だけ。
-/
import Ytosk.TwoRowI2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

theorem lenN_t1 : (TRIO.gexp M r L d0 0 n).length = r + L + (n - 1) * L := by
  rw [TRIO.gexp_length hlen]
  have : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
  omega

theorem lenP_t1 : (TRIO.gexp M r L d0 0 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen

/-- **Children shift by one copy.** -/
theorem children_shift {p : Nat} (hp : p < (n - 1) * L) :
    children (TRIO.gexp M r L d0 0 n) (r + L + p) =
      (children (TRIO.gexp M r L d0 0 (n - 1)) (r + p)).map (· + L) := by
  have hlenN := lenN_t1 hlen hL hA hd0e hn
  have hlenP := lenP_t1 hlen hL hA hd0e hn
  rw [children_above _ (r + L) ((n - 1) * L) _ hlenN (fun c hc h => by
        have := par_lt _ 0 c _ h; omega),
      children_above _ r ((n - 1) * L) _ hlenP (fun c hc h => by
        have := par_lt _ 0 c _ h; omega)]
  have hF : (List.range ((n - 1) * L)).filter
        (fun j => decide (par (TRIO.gexp M r L d0 0 n) 0 (r + L + j) = some (r + L + p))) =
      (List.range ((n - 1) * L)).filter
        (fun j => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + j) = some (r + p))) := by
    apply List.filter_congr
    intro j hj
    have hj' := List.mem_range.mp hj
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      have e1 : par (TRIO.gexp M r L d0 0 n) 0 (r + L + 0) ≠ some (r + L + p) := by
        intro h; have := par_lt _ 0 _ _ h; omega
      have e2 : par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + 0) ≠ some (r + p) := by
        intro h; have := par_lt _ 0 _ _ h; omega
      rw [decide_eq_false e1, decide_eq_false e2]
    · rw [par0_gexp_shift hlen hL hA hd0e hn h0 hj']
      cases par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + j) with
      | none => simp
      | some v => simp; omega
  rw [hF, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp]; omega

theorem vr_shift (hF1n : F1 (TRIO.gexp M r L d0 0 n)) (hF1p : F1 (TRIO.gexp M r L d0 0 (n - 1)))
    {p : Nat} (hp : p < (n - 1) * L) :
    vr (TRIO.gexp M r L d0 0 n) (r + L + p) = vr (TRIO.gexp M r L d0 0 (n - 1)) (r + p) := by
  obtain ⟨k, qb, hk, hqb, hpk⟩ := TRIO.gexp_pos_decomp (j0 := 0) (n := n - 1) (p := p) hL
    (Nat.zero_le _) (by simpa using hp)
  simp only [Nat.zero_add] at hpk
  rw [vr_eq_nT hF1n, vr_eq_nT hF1p]
  congr 1
  rw [show r + L + p = r + ((k + 1) * L + qb) by rw [hpk, Nat.succ_mul]; omega,
    entry1_gexp_d1z hlen (by omega) hqb, hpk, entry1_gexp_d1z hlen hk hqb]

/-- **The state in a copy frame is the shifted state.** -/
theorem bst_shift (hF1n : F1 (TRIO.gexp M r L d0 0 n)) (hF1p : F1 (TRIO.gexp M r L d0 0 (n - 1)))
    {p1 p2 : Nat} (hp1 : p1 < (n - 1) * L) (hp12 : p1 < p2) (hp2 : p2 < (n - 1) * L) :
    bst (TRIO.gexp M r L d0 0 n) (r + L + p1) (r + L + p2) =
      bst (TRIO.gexp M r L d0 0 (n - 1)) (r + p1) (r + p2) := by
  unfold bst
  rw [vr_shift hlen hL hA hd0e hn hF1n hF1p hp1, children_shift hlen hL hA hd0e hn hp1,
    List.filter_map, List.map_map]
  congr 2
  have hfe : (children (TRIO.gexp M r L d0 0 (n - 1)) (r + p1)).filter
      ((fun d => decide (d < r + L + p2)) ∘ (· + L)) =
      (children (TRIO.gexp M r L d0 0 (n - 1)) (r + p1)).filter (fun d => decide (d < r + p2)) := by
    apply List.filter_congr; intro d _; simp only [Function.comp, decide_eq_decide]; omega
  rw [hfe]
  apply List.map_congr_left
  intro d hd
  rw [List.mem_filter] at hd
  have hdc := mem_children hd.1
  rw [lenP_t1 hlen hL hA hd0e hn] at hdc
  simp only [Function.comp]
  rw [show d + L = r + L + (d - r) by omega,
    o2r_gexp_shift hlen hL hA hd0e hn hF1n hF1p (d - r) (by omega), show r + (d - r) = d by omega]

/-- The parent of a non-root copy column is a shifted column of `P`, at or after `r`. -/
theorem par_shift_ge {j h : Nat} (hj0 : 0 < j) (hj : j < (n - 1) * L)
    (hp : par (TRIO.gexp M r L d0 0 n) 0 (r + L + j) = some h) :
    ∃ h', h = h' + L ∧ par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + j) = some h' := by
  rw [par0_gexp_shift hlen hL hA hd0e hn hj0 hj] at hp
  cases hq : par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + j) with
  | none => rw [hq] at hp; cases hp
  | some h' => rw [hq] at hp; exact ⟨h', (Option.some.inj hp).symm, rfl⟩

/-- **The frames in the copies are the shifted frames of `P`** (for a property of the frame data). -/
theorem frames_shift (Q : T → T → T → T → Prop)
    (hF1n : F1 (TRIO.gexp M r L d0 0 n)) (hF1p : F1 (TRIO.gexp M r L d0 0 (n - 1)))
    (hP : ∀ h p s y, p < (TRIO.gexp M r L d0 0 (n - 1)).length →
      par (TRIO.gexp M r L d0 0 (n - 1)) 0 p = some h →
      o2r (TRIO.gexp M r L d0 0 (n - 1)) p = psi s y z →
      Q (vr (TRIO.gexp M r L d0 0 (n - 1)) h) (bst (TRIO.gexp M r L d0 0 (n - 1)) h p) s y)
    {j h : Nat} (hj0 : 0 < j) (hj : j < (n - 1) * L)
    (hp : par (TRIO.gexp M r L d0 0 n) 0 (r + L + j) = some h) {s y : T}
    (hc : o2r (TRIO.gexp M r L d0 0 n) (r + L + j) = psi s y z) :
    Q (vr (TRIO.gexp M r L d0 0 n) h) (bst (TRIO.gexp M r L d0 0 n) h (r + L + j)) s y := by
  obtain ⟨h', rfl, hp'⟩ := par_shift_ge hlen hL hA hd0e hn hj0 hj hp
  have hh'lt := par_lt _ 0 _ _ hp'
  have hh'ge : r ≤ h' := by
    by_contra hc'
    -- the parent of `r + j` (`j > 0`) is at or after `r`
    have hP0 : entry (TRIO.gexp M r L d0 0 (n - 1)) 0 h' < entry (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + j) :=
      ((par0_spec _).mp hp').2.1
    have hbet := ((par0_spec _).mp hp').2.2
    have hr' := hbet r (by omega) (by omega)
    -- row 0 at `r` is at most row 0 at `r + j`, and the row-0 entry of `r` equals that in `M`
    have hr0 : entry (TRIO.gexp M r L d0 0 (n - 1)) 0 r = entry M 0 r := by
      have := entry0_gexp_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := 0) (n := n - 1)
        (k := 0) (q := 0) hlen (by omega) hL
      simpa using this
    rcases Nat.lt_or_ge j L with hjL | hjL
    · have := entry0_gexp_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := 0) (n := n - 1)
        (k := 0) (q := j) hlen (by omega) hjL
      simp at this
      have h2 := anc0_interval hA (r + j) (by omega) (by omega)
      rw [this] at hr'; rw [hr0] at hr'; omega
    · obtain ⟨k, qb, hk, hqb, hjk⟩ := TRIO.gexp_pos_decomp (j0 := 0) (n := n - 1) (p := j) hL
        (Nat.zero_le _) (by simpa using hj)
      simp only [Nat.zero_add] at hjk
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp at hjk; omega
        · exact h0
      have := entry0_gexp_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := 0) (n := n - 1)
        (k := k) (q := qb) hlen hk hqb
      rw [hjk] at hr'; rw [this, hr0] at hr'
      have hd0 : 0 < d0 := by
        have := anc0_interval hA (r + L) (by omega) (le_refl _); omega
      have hmono : entry M 0 r ≤ entry M 0 (r + qb) := by
        rcases Nat.eq_zero_or_pos qb with h0 | h0
        · subst h0; simp
        · exact le_of_lt (anc0_interval hA (r + qb) (by omega) (by omega))
      have : d0 ≤ k * d0 := Nat.le_mul_of_pos_left d0 (by omega)
      omega
  have hjh : h' - r < j := by omega
  rw [show h' + L = r + L + (h' - r) by omega,
    vr_shift hlen hL hA hd0e hn hF1n hF1p (show h' - r < (n - 1) * L by omega),
    bst_shift hlen hL hA hd0e hn hF1n hF1p (show h' - r < (n - 1) * L by omega) hjh hj,
    show r + (h' - r) = h' by omega]
  rw [o2r_gexp_shift hlen hL hA hd0e hn hF1n hF1p j hj] at hc
  exact hP h' (r + j) s y (by rw [lenP_t1 hlen hL hA hd0e hn]; omega) hp' hc

end

/-! ## x より前の領域と経路 -/

/-- `par0` depends only on row 0 up to the column. -/
theorem par0_congr {M M' : Mat} {i : Nat} (he : ∀ j, j ≤ i → entry M 0 j = entry M' 0 j) :
    par M 0 i = par M' 0 i := by
  cases h : par M 0 i with
  | some a =>
    obtain ⟨hai, hlt, hbet⟩ := (par0_spec M).mp h
    symm
    rw [par0_spec]
    refine ⟨hai, by rw [← he a (by omega), ← he i le_rfl]; exact hlt, fun j h1 h2 => ?_⟩
    rw [← he j (by omega), ← he i le_rfl]; exact hbet j h1 h2
  | none =>
    cases h' : par M' 0 i with
    | none => rfl
    | some a =>
      exfalso
      obtain ⟨hai, hlt, hbet⟩ := (par0_spec M').mp h'
      have : par M 0 i = some a := by
        rw [par0_spec]
        refine ⟨hai, by rw [he a (by omega), he i le_rfl]; exact hlt, fun j h1 h2 => ?_⟩
        rw [he j (by omega), he i le_rfl]; exact hbet j h1 h2
      rw [h] at this; cases this

/-- **The path values drop** (`t = 1`, `n ≥ 2`). -/
theorem path_lt_t1 {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hI : Inv2 M) {n : Nat} (hn : 2 ≤ n) :
    ∀ h, Anc0 M h (M.length - 1) →
      isOT (o2r (expand M n) h) = true ∧ o2r (expand M n) h < o2r M h := by
  have hr1' : par M 1 (M.length - 1) = some r := by have h := hr; rw [ht1] at h; exact h
  have hb1 : 0 < entry M 1 (M.length - 1) := by have := par1_entry_lt hr1'; omega
  have hPRE : ∀ h p s y, Anc0 M p (M.length - 1) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
      bst M h p ≠ z → ∃ rest, y = app (bst M h p) rest ∧ rest ≠ z := by
    intro h p s y hp hph hc h1 h2 h3
    have hpl : p < M.length := by have := hp.le; omega
    obtain ⟨hhi, hlo⟩ := hI.hi h p s y hpl hph hc h3 h1 h2
    refine ⟨loP s y, ?_, hlo⟩
    have := hiP_loP s y; rw [hhi] at this; exact this.symm
  have hx0 : 0 < entry M 0 (M.length - 1) := by
    rcases Nat.eq_zero_or_pos (entry M 0 (M.length - 1)) with h | h
    · exfalso; obtain ⟨e1, e2⟩ := hI.z0 (M.length - 1) (by omega) h; exact hz ⟨h, e1, e2⟩
    · exact h
  obtain ⟨q, hq⟩ := par0_some_of (M := M) (show 0 < M.length - 1 by omega) (by rw [hI.e00]; exact hx0)
  intro h hh
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨j, hj, hjot, hjlt⟩ := twoRow_qr_PRE hM hz hr ht1 hI.g2 hb1 hI.r1 hI.z0 hq hPRE n hn h hh
    rw [hj]; exact ⟨hjot, hjlt⟩
  · have hqμ := vr_lt_of_ne hI.g2 (by omega) hr1' hb1 hq hqr
    have hSa : ∀ a', ¬ lt (vr M r) a' = true → isOT (psi a' (argOf (o2r M r)) z) = true →
        SeedOK a' (argOf (o2r M r)) (vr M r) (o2r (expand M 1) r) := by
      intro a' ha' hot
      rw [expand_n1 hM hz hr]
      exact seed_of_drop hM hI.g2 hI.hi hI.fc hr1' hb1 a' ha' hot
    have hch := (twoRow_chain_PRE hM hz hr ht1 hI.g2 hb1 hq hqμ
      (fun k _ => F1_expand hI.r1 hI.z0 hM k) hSa hPRE n hn).2
    rw [hch h hh]
    exact path_ok_seed hM hI.g2 hr1' hb1 hSa _ h hh

/-- Pairwise order survives lowering the last value. -/
theorem pairwise_last_lower {C : List T} {a a' : T}
    (h : (C ++ [a]).Pairwise (fun u v => v ≤ u)) (ha : a' ≤ a) :
    (C ++ [a']).Pairwise (fun u v => v ≤ u) := by
  have h' := List.pairwise_append.mp h
  rw [List.pairwise_append]
  refine ⟨h'.1, List.pairwise_singleton _ _, fun u hu v hv => ?_⟩
  rw [List.mem_singleton] at hv; subst hv
  exact le_trans ha (h'.2.2 u hu _ (by simp))

/-- **Good2 of a `t = 1` expansion**, from the invariants of `M` and `M[n−1]`. -/
theorem good2_expand_t1 {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hI : Inv2 M) {n : Nat} (hn : 2 ≤ n)
    (hIP : Inv2 (expand M (n - 1))) : Good2 (expand M n) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  obtain ⟨d1, heqd, hlen, hL, hA, hd0e⟩ := expand_gexp_data M n hM hz hr (by omega)
  have hN := expand_eq_gexp_t1 M n hM hz hr ht1
  have hP := expand_eq_gexp_t1 M (n - 1) hM hz hr ht1
  have hrx := par_lt M _ _ _ hr
  set L := M.length - 1 - r with hLdef
  set d0 := entry M 0 (M.length - 1) - entry M 0 r with hd0def
  have hxe : r + L = M.length - 1 := by omega
  have hF1n : F1 (TRIO.gexp M r L d0 0 n) := by rw [← hN]; exact F1_expand hI.r1 hI.z0 hM n
  have hF1p : F1 (TRIO.gexp M r L d0 0 (n - 1)) := by rw [← hP]; exact hIP.g2.f1
  have hpath := path_lt_t1 hM hz hr ht1 hI hn
  have hlenN := lenN_t1 hlen hL hA hd0e hn
  refine ⟨F1_expand hI.r1 hI.z0 hM n, ?_, ?_⟩
  · intro i
    rcases Nat.lt_or_ge i (M.length - 1) with h1 | h1
    · by_cases hiA : Anc0 M i (M.length - 1)
      · exact (hpath i hiA).1
      · rw [o2r_expand_off hM hz hr (by omega) hn i h1 hiA]; exact hI.g2.ot i
    · rw [hN]
      rcases Nat.lt_or_ge i (r + L + (n - 1) * L) with h2 | h2
      · rw [show i = r + L + (i - (r + L)) by omega,
          o2r_gexp_shift hlen hL hA hd0e hn hF1n hF1p _ (by omega), ← hP]
        exact hIP.g2.ot _
      · rw [o2r_out (by rw [hlenN]; omega)]; rfl
  · intro h
    rcases Nat.lt_or_ge h (M.length - 1) with h1 | h1
    · rw [children_expand_lt M n hM hz hr (by omega) hn h1]
      by_cases hhA : Anc0 M h (M.length - 1)
      · obtain ⟨c, hc, hcA⟩ := anc0_child hhA (by omega)
        have hle := children_le_of_anc_last hcA hx hc
        have hcmem : c ∈ children M h := mem_children_iff.mpr ⟨by have := hcA.le; omega, hc⟩
        have hsplit := split_last_max _ c (children_sorted M h) hcmem hle
        have hdM := hI.g2.dec h
        rw [hsplit, List.map_append] at hdM ⊢
        have hCv : ((children M h).filter (fun d => decide (d < c))).map (o2r (expand M n)) =
            ((children M h).filter (fun d => decide (d < c))).map (o2r M) := by
          apply List.map_congr_left; intro d hd
          rw [List.mem_filter] at hd
          have hdc : d < c := by simpa using hd.2
          have hdp := mem_children_iff.mp hd.1
          exact o2r_expand_off hM hz hr (by omega) hn d (by have := hcA.le; omega)
            (not_anc_of_earlier hdp.2 hc hdc hcA.le)
        rw [hCv]
        simp only [List.map_cons, List.map_nil] at hdM ⊢
        exact pairwise_last_lower hdM (le_of_lt (hpath c hcA).2)
      · have hv : (children M h).map (o2r (expand M n)) = (children M h).map (o2r M) := by
          apply List.map_congr_left; intro d hd
          have hdp := mem_children_iff.mp hd
          have hdh := par_lt M 0 d h hdp.2
          have hdx : d < M.length - 1 := by
            by_contra hc
            have hde : d = M.length - 1 := by omega
            exact hhA (by rw [← hde]; exact anc0_of_par M 0 h d hdp.2)
          exact o2r_expand_off hM hz hr (by omega) hn d hdx (fun hdA => hhA (anc0_up hdp.2 hdA))
        rw [hv]; exact hI.g2.dec h
    · rw [hN]
      rcases Nat.lt_or_ge h (r + L + (n - 1) * L) with h2 | h2
      · rw [show h = r + L + (h - (r + L)) by omega,
          children_shift hlen hL hA hd0e hn (show h - (r + L) < (n - 1) * L by omega), List.map_map]
        have hv : ((children (TRIO.gexp M r L d0 0 (n - 1)) (r + (h - (r + L)))).map
            ((o2r (TRIO.gexp M r L d0 0 n)) ∘ (· + L))) =
            (children (TRIO.gexp M r L d0 0 (n - 1)) (r + (h - (r + L)))).map
              (o2r (TRIO.gexp M r L d0 0 (n - 1))) := by
          apply List.map_congr_left; intro d hd
          have hdc := mem_children hd
          rw [lenP_t1 hlen hL hA hd0e hn] at hdc
          simp only [Function.comp]
          rw [show d + L = r + L + (d - r) by omega,
            o2r_gexp_shift hlen hL hA hd0e hn hF1n hF1p (d - r) (by omega),
            show r + (d - r) = d by omega]
        rw [hv]
        have := hIP.g2.dec (r + (h - (r + L)))
        rwa [hP] at this
      · have : children (TRIO.gexp M r L d0 0 n) h = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro c hc; have := mem_children hc; rw [hlenN] at this; omega
        rw [this]; exact List.Pairwise.nil

/-- The state before a column `≤ x` is unchanged by a `t ≥ 1` expansion (`n ≥ 2`). -/
theorem bst_expand_le {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht : 0 < TRIO.srow M (M.length - 1)) {n : Nat} (hn : 2 ≤ n) {h c : Nat}
    (hc : par M 0 c = some h) (hcx : c ≤ M.length - 1) :
    bst (expand M n) h c = bst M h c := by
  have hhc := par_lt M 0 c h hc
  unfold bst
  rw [vr_expand_lt hM hn (show h < M.length - 1 by omega),
    children_expand_lt M n hM hz hr ht hn (show h < M.length - 1 by omega)]
  congr 2
  apply List.map_congr_left
  intro d hd
  rw [List.mem_filter] at hd
  have hdc : d < c := by simpa using hd.2
  have hdp := mem_children_iff.mp hd.1
  exact o2r_expand_off hM hz hr ht hn d (by omega) (not_anc_of_earlier hdp.2 hc hdc hcx)

/-- The new value of `x` is `r`'s value in `M[n−1]`, below `Ω_{μ+1}`. -/
theorem o2r_x_t1 {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hI : Inv2 M) {n : Nat} (hn : 2 ≤ n)
    (hIP : Inv2 (expand M (n - 1))) :
    o2r (expand M n) (M.length - 1) = o2r (expand M (n - 1)) r := by
  obtain ⟨d1, heqd, hlen, hL, hA, hd0e⟩ := expand_gexp_data M n hM hz hr (by omega)
  have hN := expand_eq_gexp_t1 M n hM hz hr ht1
  have hP := expand_eq_gexp_t1 M (n - 1) hM hz hr ht1
  have hrx := par_lt M _ _ _ hr
  have hF1n := F1_expand hI.r1 hI.z0 hM n
  have hF1p := hIP.g2.f1
  rw [hN] at hF1n ⊢; rw [hP] at hF1p ⊢
  have := o2r_gexp_shift hlen hL hA hd0e hn hF1n hF1p 0 (by
    have : 1 ≤ n - 1 := by omega
    have : M.length - 1 - r ≤ (n - 1) * (M.length - 1 - r) := Nat.le_mul_of_pos_left _ (by omega)
    omega)
  simpa [show r + (M.length - 1 - r) = M.length - 1 by omega] using this

/-- **Shared case split for the frames of a `t = 1` expansion.** -/
theorem frames_t1 {M : Mat} {r q : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hI : Inv2 M) {n : Nat} (hn : 2 ≤ n)
    (hIP : Inv2 (expand M (n - 1))) (hq : par M 0 (M.length - 1) = some q)
    (Pred : T → T → T → T → Prop)
    (hlow : ∀ h c s y y', c < M.length - 1 → par M 0 c = some h → o2r M c = psi s y z →
      o2r (expand M n) c = psi s y' z → y' ≤ y →
      Pred (vr M h) (bst M h c) s y → Pred (vr M h) (bst M h c) s y')
    (hjoin : ∀ s y, o2r (expand M (n - 1)) r = psi s y z →
      Pred (vr M q) (bst M q (M.length - 1)) s y)
    (hPP : ∀ h p s y, p < (expand M (n - 1)).length → par (expand M (n - 1)) 0 p = some h →
      o2r (expand M (n - 1)) p = psi s y z →
      Pred (vr (expand M (n - 1)) h) (bst (expand M (n - 1)) h p) s y)
    (hMP : ∀ h p s y, p < M.length → par M 0 p = some h → o2r M p = psi s y z →
      Pred (vr M h) (bst M h p) s y) :
    ∀ h c s y, c < (expand M n).length → par (expand M n) 0 c = some h →
      o2r (expand M n) c = psi s y z → Pred (vr (expand M n) h) (bst (expand M n) h c) s y := by
  have hx : M.length - 1 + 1 = M.length := by omega
  obtain ⟨d1, heqd, hlen, hL, hA, hd0e⟩ := expand_gexp_data M n hM hz hr (by omega)
  have hN := expand_eq_gexp_t1 M n hM hz hr ht1
  have hP := expand_eq_gexp_t1 M (n - 1) hM hz hr ht1
  have hrx := par_lt M _ _ _ hr
  have hG2 := good2_expand_t1 hM hz hr ht1 hI hn hIP
  have hpath := path_lt_t1 hM hz hr ht1 hI hn
  intro h c s y hcl hp hc
  rcases Nat.lt_or_ge c (M.length - 1) with h1 | h1
  · -- before `x`
    have hp' : par M 0 c = some h := by rw [← par0_expand_prefix M hM (show 1 ≤ n by omega) h1]; exact hp
    have hhc := par_lt M 0 c h hp'
    rw [bst_expand_le hM hz hr (by omega) hn hp' (by omega), vr_expand_lt hM hn (show h < M.length - 1 by omega)]
    obtain ⟨yM, hyM⟩ := o2r_sub hI.g2 c
    obtain ⟨yN, hyN⟩ := o2r_sub hG2 c
    rw [vr_expand_lt hM hn h1] at hyN
    rw [hyN] at hc
    obtain ⟨rfl, rfl, _⟩ := psi.inj hc
    have hle : yN ≤ yM := by
      by_cases hcA : Anc0 M c (M.length - 1)
      · have hlt := (hpath c hcA).2
        rw [hyN, hyM, psi_lt_psi_z_iff] at hlt
        rcases hlt with h' | ⟨_, h'⟩
        · exact absurd h' (lt_irrefl' _)
        · exact le_of_lt h'
      · rw [o2r_expand_off hM hz hr (by omega) hn c h1 hcA, hyM] at hyN
        rw [(psi.inj hyN).2.1]
    exact hlow h c (vr M c) yM yN h1 hp' hyM hyN hle (hMP h c (vr M c) yM (by omega) hp' hyM)
  rcases Nat.eq_or_lt_of_le h1 with h2 | h2
  · -- `x`: the join frame under `q`
    subst h2
    have hpx : par (expand M n) 0 (M.length - 1) = par M 0 (M.length - 1) := by
      apply par0_congr
      intro j hj
      rcases Nat.lt_or_ge j (M.length - 1) with h3 | h3
      · rw [← entry_take (expand M n) 0 h3, expand_take_prefix M hM (by omega), entry_take M 0 h3]
      · have hjx : j = M.length - 1 := by omega
        subst hjx
        rw [hN]
        have := entry0_gexp_mir (M := M) (j0 := r) (Lb := M.length - 1 - r)
          (d0 := entry M 0 (M.length - 1) - entry M 0 r) (d1 := 0) (n := n) (k := 1) (q := 0)
          (by omega) (by omega) (by omega)
        simp only [Nat.one_mul, Nat.add_zero] at this
        rw [show r + (M.length - 1 - r) = M.length - 1 by omega] at this
        rw [this]
        have := anc0_interval hA (r + (M.length - 1 - r)) (by omega) (le_refl _)
        rw [show r + (M.length - 1 - r) = M.length - 1 by omega] at this
        omega
    rw [hpx, hq] at hp
    cases hp
    rw [bst_expand_le hM hz hr (by omega) hn hq (le_refl _), vr_expand_lt hM hn (par_lt M 0 _ _ hq)]
    rw [o2r_x_t1 hM hz hr ht1 hI hn hIP] at hc
    exact hjoin s y hc
  · -- the copies: shifted frames of `M[n−1]`
    have hF1n : F1 (TRIO.gexp M r (M.length - 1 - r) (entry M 0 (M.length - 1) - entry M 0 r) 0 n) := by
      rw [← hN]; exact F1_expand hI.r1 hI.z0 hM n
    have hF1p : F1 (TRIO.gexp M r (M.length - 1 - r) (entry M 0 (M.length - 1) - entry M 0 r) 0 (n - 1)) := by
      rw [← hP]; exact hIP.g2.f1
    have hlenN := lenN_t1 hlen hL hA hd0e hn
    rw [hN] at hcl hp hc ⊢
    rw [hlenN] at hcl
    rw [show c = r + (M.length - 1 - r) + (c - (r + (M.length - 1 - r))) by omega] at hp hc ⊢
    apply frames_shift hlen hL hA hd0e hn Pred hF1n hF1p _ (by omega) (by omega) hp hc
    intro h' p' s' y' hpl' hp' hc'
    rw [← hP] at hpl' hp' hc' ⊢
    exact hPP h' p' s' y' hpl' hp' hc'

/-- `r`'s subscript in `M[n−1]` (`n ≥ 2`). -/
theorem vr_P_r {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r) {n : Nat} (hn : 2 ≤ n) :
    vr (expand M (n - 1)) r = vr M r := by
  have hrx := par_lt M _ _ _ hr
  rcases Nat.eq_or_lt_of_le (show 2 ≤ n from hn) with h | h
  · subst h; rw [show 2 - 1 = 1 by rfl, expand_n1 hM hz hr]; exact vr_take M r hrx
  · exact vr_expand_lt hM (show 2 ≤ n - 1 by omega) hrx

/-- **`r` over `x` in `M[n−1]`** when `q = r` (`n ≥ 3`): one step over the copy root `x`. -/
theorem P_r_qr {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hI : Inv2 M) {n : Nat} (hn : 3 ≤ n)
    (hIP : Inv2 (expand M (n - 1))) (hq : par M 0 (M.length - 1) = some r) :
    ∃ yP', o2r (expand M (n - 1)) (M.length - 1) = psi (vr M r) yP' z ∧
      o2r (expand M (n - 1)) r =
        psi (vr M r) (step (vr M r) (bst M r (M.length - 1)) (vr M r) yP' z) z ∧
      par (expand M (n - 1)) 0 (M.length - 1) = some r ∧
      bst (expand M (n - 1)) r (M.length - 1) = bst M r (M.length - 1) ∧
      vr (expand M (n - 1)) r = vr M r := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hrx := par_lt M _ _ _ hr
  have hn1 : 2 ≤ n - 1 := by omega
  set P := expand M (n - 1) with hPdef
  have hvr : vr P r = vr M r := vr_expand_lt hM hn1 hrx
  have hchP : children P r = children M r := children_expand_lt M (n - 1) hM hz hr (by omega) hn1 hrx
  have hle := children_le_of_anc_last (Anc0.refl (M.length - 1)) hx hq
  have hxmem : M.length - 1 ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have hsplit := split_last_max _ (M.length - 1) (children_sorted M r) hxmem hle
  have hpxP : par P 0 (M.length - 1) = some r := by
    have := mem_children_iff.mp (show M.length - 1 ∈ children P r by rw [hchP]; exact hxmem)
    exact this.2
  have hchP' : children P r = (children P r).filter (fun d => decide (d < M.length - 1)) ++
      [M.length - 1] := by rw [hchP]; exact hsplit
  have hsingP : ∀ t ∈ (children P r).map (o2r P), Single t := by
    intro t ht; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hIP.g2 i
  have hfr := o2r_frame' hIP.g2.f1 hchP' hsingP (hIP.g2.dec r)
  have hbP : bst P r (M.length - 1) = bst M r (M.length - 1) :=
    bst_expand_le hM hz hr (by omega) hn1 hq (le_refl _)
  -- the subscript of the copy root `x` in `M[n−1]` is that of `r`
  have hvx : vr P (M.length - 1) = vr M r := by
    obtain ⟨d1, heqd, hlen, hL, hA, hd0e⟩ := expand_gexp_data M (n - 1) hM hz hr (by omega)
    have hPg := expand_eq_gexp_t1 M (n - 1) hM hz hr ht1
    rw [vr_eq_nT hIP.g2.f1, vr_eq_nT hI.g2.f1]
    congr 1
    rw [hPdef, hPg]
    have := entry1_gexp_d1z (M := M) (r := r) (L := M.length - 1 - r)
      (d0 := entry M 0 (M.length - 1) - entry M 0 r) (k := 1) (q := 0) (m := n - 1) (by omega) (by omega) (by omega)
    simp only [Nat.one_mul, Nat.add_zero] at this
    rw [show r + (M.length - 1 - r) = M.length - 1 by omega] at this
    rw [this]
  obtain ⟨yP', hyP'⟩ := o2r_sub hIP.g2 (M.length - 1)
  rw [hvx] at hyP'
  refine ⟨yP', hyP', ?_, hpxP, hbP, hvr⟩
  rw [hfr, hvr, hbP, hyP', spArg_single]

section join
variable {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
  (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
    TRIO.entry M 2 (M.length - 1) = 0))
  (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
  (ht1 : TRIO.srow M (M.length - 1) = 1) (hI : Inv2 M) {n : Nat} (hn : 2 ≤ n)
  (hIP : Inv2 (expand M (n - 1)))
include hM hz hr ht1 hI hn hIP

/-- The state before `x` under `r` is all high (`≥ Ω_{μ+1}`), when `q = r`. -/
theorem bst_high_qr (hq : par M 0 (M.length - 1) = some r) :
    ∀ g ∈ summands (bst M r (M.length - 1)), ¬ g < psi (succ (vr M r)) z z := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hr1' : par M 1 (M.length - 1) = some r := by have h := hr; rw [ht1] at h; exact h
  have hb1 : 0 < entry M 1 (M.length - 1) := by have := par1_entry_lt hr1'; omega
  have hvx : vr M (M.length - 1) = succ (vr M r) := by
    obtain ⟨m0, hm0, he⟩ := hI.g2.f1 _ hb1
    rw [hr1'] at hm0; cases hm0
    rw [vr_eq_nT hI.g2.f1, vr_eq_nT hI.g2.f1, ← he, nT_succ]
  intro g hg hlt
  have hge := bst_summands_ge hI.g2 hx (Anc0.refl _) hq g hg
  rw [o2r_leaf hx (isOT_vr hI.g2.f1 _), hvx] at hge
  exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl' _)

theorem bst_ot_qr (hq : par M 0 (M.length - 1) = some r) : isOT (bst M r (M.length - 1)) = true := by
  have hG' := good2_take hM hI.g2 hI.hi hI.fc
  have := hG'.ot r
  rw [drop_frameQ hM hI.g2 hq] at this
  exact isOT_arg this

/-- **PreHi at the join frame.** -/
theorem preHi_join_t1 {q : Nat} (hq : par M 0 (M.length - 1) = some q) {s y : T}
    (hc : o2r (expand M (n - 1)) r = psi s y z) (hB : bst M q (M.length - 1) ≠ z)
    (h1 : lt (bst M q (M.length - 1)) y = true) (h2 : lt (psi (vr M q) z z) (psi s y z) = true) :
    hiP s y = bst M q (M.length - 1) ∧ loP s y ≠ z := by
  have hrx := par_lt M _ _ _ hr
  have hr1' : par M 1 (M.length - 1) = some r := by have h := hr; rw [ht1] at h; exact h
  have hb1 : 0 < entry M 1 (M.length - 1) := by have := par1_entry_lt hr1'; omega
  obtain ⟨yP, hyP⟩ := o2r_sub hIP.g2 r
  rw [vr_P_r hM hz hr hn] at hyP
  rw [hyP] at hc
  obtain ⟨rfl, rfl, _⟩ := psi.inj hc
  by_cases hqr : q = r
  · subst hqr
    rcases Nat.eq_or_lt_of_le (show 2 ≤ n from hn) with h | h
    · -- `M[1] = M.take x`
      subst h
      have h3 : o2r (expand M (2 - 1)) q = psi (vr M q) (bst M q (M.length - 1)) z := by
        rw [show 2 - 1 = 1 by rfl, expand_n1 hM hz hr]; exact drop_frameQ hM hI.g2 hq
      rw [h3] at hyP
      rw [← (psi.inj hyP).2.1] at h1
      exact absurd h1 (lt_irrefl' _)
    · obtain ⟨yP', hyP', hval, hpxP, hbP, hvrP⟩ := P_r_qr hM hz hr ht1 hI (show 3 ≤ n by omega) hIP hq
      rw [hval] at hyP
      have hyy := (psi.inj hyP).2.1
      rw [← hyy]
      have hcot : isOT (psi (vr M q) yP' z) = true := by rw [← hyP']; exact hIP.g2.ot _
      have hhigh := bst_high_qr hM hz hr ht1 hI hn hIP hq
      have hlow : psi (vr M q) yP' z < psi (succ (vr M q)) z z := psi_lt_om_succ.mpr (lt_succ_self _)
      have happ : isOT (app (bst M q (M.length - 1)) (psi (vr M q) yP' z)) = true := by
        apply isOT_app_of (bst_ot_qr hM hz hr ht1 hI hn hIP hq) hcot
        intro g hg
        exact le_of_lt (lt_of_lt_of_le hlow (le_of_not_gt (hhigh g hg)))
      have hstep : step (vr M q) (bst M q (M.length - 1)) (vr M q) yP' z =
          app (bst M q (M.length - 1)) (psi (vr M q) yP' z) := by
        apply step_append hcot happ
        intro t1 t2
        have hpl : M.length - 1 < (expand M (n - 1)).length := by
          rw [expand_eq_gexp_t1 M (n - 1) hM hz hr ht1, TRIO.gexp_length (by omega)]
          have : 2 * (M.length - 1 - q) ≤ (n - 1) * (M.length - 1 - q) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        have := hIP.hi q (M.length - 1) (vr M q) yP' hpl hpxP hyP'
        rw [hbP, hvrP] at this
        exact this hB t1 t2
      rw [hstep]
      have hsp := split_app_of (t := psi (succ (vr M q)) z z) hhigh
        (Or.inr (show head (psi (vr M q) yP' z) < psi (succ (vr M q)) z z from hlow))
      unfold hiP loP
      rw [hsp]
      exact ⟨rfl, by simp⟩
  · exfalso
    have hqμ := vr_lt_of_ne hI.g2 (by omega) hr1' hb1 hq hqr
    have h2' : psi (vr M q) z z < psi (vr M r) yP z := h2
    rw [psi_lt_psi_z_iff] at h2'
    rcases h2' with h' | ⟨h', _⟩
    · exact absurd (lt_trans (a := vr M r) hqμ h') (lt_irrefl' _)
    · rw [h'] at hqμ; exact absurd hqμ (lt_irrefl' _)

/-- **PreFC at the join frame.** -/
theorem preFC_join_t1 {q : Nat} (hq : par M 0 (M.length - 1) = some q) {s y : T}
    (hc : o2r (expand M (n - 1)) r = psi s y z) (hB : bst M q (M.length - 1) = z)
    (h1 : lt z y = true) (h2 : lt (psi (vr M q) z z) (psi s y z) = true) (hv : vr M q = s) :
    hiP s y = z ∧ loP s y ≠ z := by
  have hrx := par_lt M _ _ _ hr
  have hr1' : par M 1 (M.length - 1) = some r := by have h := hr; rw [ht1] at h; exact h
  have hb1 : 0 < entry M 1 (M.length - 1) := by have := par1_entry_lt hr1'; omega
  obtain ⟨yP, hyP⟩ := o2r_sub hIP.g2 r
  rw [vr_P_r hM hz hr hn] at hyP
  rw [hyP] at hc
  obtain ⟨rfl, rfl, _⟩ := psi.inj hc
  by_cases hqr : q = r
  · subst hqr
    rcases Nat.eq_or_lt_of_le (show 2 ≤ n from hn) with h | h
    · subst h
      have h3 : o2r (expand M (2 - 1)) q = psi (vr M q) (bst M q (M.length - 1)) z := by
        rw [show 2 - 1 = 1 by rfl, expand_n1 hM hz hr]; exact drop_frameQ hM hI.g2 hq
      rw [h3] at hyP
      rw [← (psi.inj hyP).2.1, hB] at h1
      exact absurd h1 (lt_irrefl' _)
    · obtain ⟨yP', hyP', hval, hpxP, hbP, hvrP⟩ := P_r_qr hM hz hr ht1 hI (show 3 ≤ n by omega) hIP hq
      rw [hval, hB] at hyP
      have hyy := (psi.inj hyP).2.1
      have hcot : isOT (psi (vr M q) yP' z) = true := by rw [← hyP']; exact hIP.g2.ot _
      have hlow : psi (vr M q) yP' z < psi (succ (vr M q)) z z := psi_lt_om_succ.mpr (lt_succ_self _)
      have hy1 : step (vr M q) z (vr M q) yP' z = psi (vr M q) yP' z := by
        rw [step_first hcot]
        by_cases htr : lt z yP' = true ∧ lt (psi (vr M q) z z) (psi (vr M q) yP' z) = true
        · rw [if_pos htr]
          have hpl : M.length - 1 < (expand M (n - 1)).length := by
            rw [expand_eq_gexp_t1 M (n - 1) hM hz hr ht1, TRIO.gexp_length (by omega)]
            have : 2 * (M.length - 1 - q) ≤ (n - 1) * (M.length - 1 - q) :=
              Nat.mul_le_mul_right _ (by omega)
            omega
          have := hIP.fc q (M.length - 1) (vr M q) yP' hpl hpxP hyP'
          rw [hbP, hvrP] at this
          obtain ⟨hhi, hlo⟩ := this hB htr.1 htr.2 rfl
          rw [if_neg hlo, hhi, app_z]
        · rw [if_neg htr]
      rw [← hyy, hy1]
      have hsp : split (psi (vr M q) yP' z) (psi (succ (vr M q)) z z) = (z, psi (vr M q) yP' z) := by
        simp [split, show lt (psi (vr M q) yP' z) (psi (succ (vr M q)) z z) = true from hlow]
      unfold hiP loP
      rw [hsp]
      exact ⟨rfl, by simp⟩
  · exfalso
    have hqμ := vr_lt_of_ne hI.g2 (by omega) hr1' hb1 hq hqr
    rw [hv] at hqμ
    exact absurd hqμ (lt_irrefl' _)

end join

/-- **(I2), `t = 1`**, from the invariants of `M` and `M[n−1]`. -/
theorem inv2_expand_t1 {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hI : Inv2 M) {n : Nat} (hn : 2 ≤ n)
    (hIP : Inv2 (expand M (n - 1))) : Inv2 (expand M n) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  obtain ⟨hz0', hr1', he00, hrow⟩ := basic_expand hI hM (show 1 ≤ n by omega)
  have hx0 : 0 < entry M 0 (M.length - 1) := by
    rcases Nat.eq_zero_or_pos (entry M 0 (M.length - 1)) with h | h
    · exfalso; obtain ⟨e1, e2⟩ := hI.z0 (M.length - 1) (by omega) h; exact hz ⟨h, e1, e2⟩
    · exact h
  obtain ⟨q, hq⟩ := par0_some_of (M := M) (show 0 < M.length - 1 by omega) (by rw [hI.e00]; exact hx0)
  have hpath := path_lt_t1 hM hz hr ht1 hI hn
  refine ⟨good2_expand_t1 hM hz hr ht1 hI hn hIP, ?_, ?_, ?_, hz0', hr1', he00, hrow⟩
  · intro h c s y hcl hp hc
    apply frames_t1 hM hz hr ht1 hI hn hIP hq
      (fun a B s y => B ≠ z → lt B y = true → lt (psi a z z) (psi s y z) = true →
        hiP s y = B ∧ loP s y ≠ z) _ _ _ _ h c s y hcl hp hc
    · intro h c s y y' _ _ _ _ hle hP hB h1 h2
      rcases (le_iff _ _).mp hle with hlt | heq
      · obtain ⟨t1, t2⟩ := trig_mono hlt h1 h2
        obtain ⟨hhi, hlo⟩ := hP hB t1 t2
        exact prehi_of_lt hhi hlo h1 hlt
      · subst heq; exact hP hB h1 h2
    · intro s y hc hB h1 h2
      exact preHi_join_t1 hM hz hr ht1 hI hn hIP hq hc hB h1 h2
    · intro h p s y hpl hp hc hB h1 h2
      exact hIP.hi h p s y hpl hp hc hB h1 h2
    · intro h p s y hpl hp hc hB h1 h2
      exact hI.hi h p s y hpl hp hc hB h1 h2
  · intro h c s y hcl hp hc
    apply frames_t1 hM hz hr ht1 hI hn hIP hq
      (fun a B s y => B = z → lt z y = true → lt (psi a z z) (psi s y z) = true → a = s →
        hiP s y = z ∧ loP s y ≠ z) _ _ _ _ h c s y hcl hp hc
    · intro h c s y y' _ _ _ _ hle hP hB h1 h2 hv
      have hz' : z < y := lt_of_lt_of_le h1 hle
      have h2' : lt (psi (vr M h) z z) (psi s y z) = true := by
        rcases (le_iff _ _).mp hle with hlt | heq
        · exact (trig_mono (B := z) hlt h1 h2).2
        · rw [← heq]; exact h2
      obtain ⟨hhi, hlo⟩ := hP hB hz' h2' hv
      exact prefc_of_le hhi hlo h1 hle
    · intro s y hc hB h1 h2 hv
      exact preFC_join_t1 hM hz hr ht1 hI hn hIP hq hc hB h1 h2 hv
    · intro h p s y hpl hp hc hB h1 h2 hv
      exact hIP.fc h p s y hpl hp hc hB h1 h2 hv
    · intro h p s y hpl hp hc hB h1 h2 hv
      exact hI.fc h p s y hpl hp hc hB h1 h2 hv
  · -- RootsDec: only the top root drops
    have hxr : col M (M.length - 1) ≠ (0, 0, 0) := by
      intro h; apply hz; unfold col at h
      rw [← entry_eq, ← entry_eq, ← entry_eq]; unfold entry; rw [h]; simp
    unfold RootsDec
    rw [roots_expand_t1 hM hz hr (by omega) (by omega) hxr]
    obtain ⟨ρ, hρ, hρn⟩ := top_anc M (M.length - 1)
    have hρ0 := col_zero_of_top hI.z0 hI.e00 (by have := hρ.le; omega) hρn
    have hρx : ρ < M.length - 1 := by
      rcases Nat.eq_or_lt_of_le hρ.le with h | h
      · rw [h] at hρ0; exact absurd hρ0 hxr
      · exact h
    have hsplit := roots_split hx hρ hρ0
    set R := (roots M).filter (fun c => decide (c < ρ)) with hRd
    have hRv : R.map (o2r (expand M n)) = R.map (o2r M) := by
      apply List.map_congr_left
      intro c hc
      rw [hRd, List.mem_filter] at hc
      have hcρ : c < ρ := by simpa using hc.2
      apply o2r_expand_off hM hz hr (by omega) hn c (by omega)
      intro hcA
      rcases anc0_total hcA hρ with h' | h'
      · cases h' with
        | refl => omega
        | step hp _ => rw [hp] at hρn; cases hρn
      · have := h'.le; omega
    have hRD := hI.rd
    unfold RootsDec at hRD
    rw [hsplit, List.map_append] at hRD ⊢
    rw [hRv]
    simp only [List.map_cons, List.map_nil] at hRD ⊢
    exact pairwise_last_lower hRD (le_of_lt (hpath ρ hρ).2)

/-- **(I2), `t = 1`, for every `n ≥ 1`.** -/
theorem inv2_expand_t1_all {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hI : Inv2 M) :
    ∀ n, 1 ≤ n → Inv2 (expand M n) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; rw [expand_n1 hM hz hr]; exact inv2_take hI hM
    · exact inv2_expand_t1 hM hz hr ht1 hI (show 2 ≤ n + 1 by omega) (by simpa using ih h0)

end Ytosk
