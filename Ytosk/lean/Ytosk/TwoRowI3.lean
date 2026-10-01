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

end Ytosk
