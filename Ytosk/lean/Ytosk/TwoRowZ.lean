/-
**2 行・t = 0 の展開。**

t = 0 ではコピーは上昇しない（d = 0）ので、コピーの根の行 0 の親は g = P_0(r)（r の兄弟として並ぶ）。
r の値は x を除いて o_M(r)[1]、g より上は o_M(h)[n]（自然数の基本列、fsD(·, natT n) と同じ）。
-/
import Ytosk.TwoRowR

namespace Ytosk

open T

set_option linter.unusedSectionVars false

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

/-- Strictly increasing lists with the same members are equal. -/
theorem eq_of_sorted_mem : ∀ (l1 l2 : List Nat), l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (∀ a, a ∈ l1 ↔ a ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr List.mem_cons_self) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp List.mem_cons_self) (by simp)
  | a :: l1, b :: l2, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      have ha := (h a).mp List.mem_cons_self
      have hb := (h b).mpr List.mem_cons_self
      rcases List.mem_cons.mp ha with ha | ha
      · exact ha
      · rcases List.mem_cons.mp hb with hb | hb
        · exact hb.symm
        · have := h2.1 a ha; have := h1.1 b hb; omega
    subst hab
    congr 1
    apply eq_of_sorted_mem l1 l2 h1.2 h2.2
    intro c
    constructor
    · intro hc
      have := (h c).mp (List.mem_cons_of_mem _ hc)
      rcases List.mem_cons.mp this with h' | h'
      · have := h1.1 c hc; omega
      · exact h'
    · intro hc
      have := (h c).mpr (List.mem_cons_of_mem _ hc)
      rcases List.mem_cons.mp this with h' | h'
      · have := h2.1 c hc; omega
      · exact h'

/-- The expansion with `t = 0` (no ascent). -/
theorem expand_eq_gexp_t0 (M : Mat) (n : Nat) (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    {r : Nat} (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht : TRIO.srow M (M.length - 1) = 0) :
    expand M n = TRIO.gexp M r (M.length - 1 - r) 0 0 n := by
  rw [expand_eq_gexp M n hM hz hr, if_neg (by omega), if_neg (by omega)]

section
variable {M : Mat} {j0 Lb d1 n : Nat} (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
  (hA : Anc0 M j0 (j0 + Lb)) {g : Nat} (hg : par M 0 j0 = some g)
include hlen hLb hA hg

/-- **Children inside a copy (`d0 = 0`)**: the mirror of the children inside the block. -/
theorem children_gexp_t0 {k q : Nat} (hk : k < n) (hq : q < Lb) :
    children (TRIO.gexp M j0 Lb 0 d1 n) (j0 + (k * Lb + q)) =
      ((List.range Lb).filter (fun q' => decide (0 < q' ∧ par M 0 (j0 + q') = some (j0 + q)))).map
        (fun q' => j0 + (k * Lb + q')) := by
  have hlen' := TRIO.gexp_length (d0 := 0) (d1 := d1) (n := n) hlen
  apply eq_of_sorted_mem _ _ (children_sorted _ _)
  · apply List.Pairwise.map _ _ (List.Pairwise.filter _ List.pairwise_lt_range)
    intro a b hab; omega
  · intro c
    rw [mem_children_iff, List.mem_map]
    constructor
    · rintro ⟨hcl, hcp⟩
      have hidx := par_lt _ 0 c _ hcp
      have hkn : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
      obtain ⟨k', q'', hk', hq'', rfl⟩ := TRIO.gexp_pos_decomp (j0 := j0) (n := n) (p := c) hLb
        (by omega) (by rw [hlen'] at hcl; exact hcl)
      rcases Nat.eq_zero_or_pos q'' with h0 | h0
      · subst h0
        have hgj := par_lt M 0 j0 g hg
        rw [par0_gexp_root_t0 hlen hLb hk' hA hg] at hcp
        have := Option.some.inj hcp; omega
      · obtain ⟨pa, hpa⟩ := par0_some_of (show j0 < j0 + q'' by omega)
          (anc0_interval hA (j0 + q'') (by omega) (by omega))
        have hge := par0_ge_of_anc hA (show j0 < j0 + q'' by omega) (by omega) hpa
        have hplt := par_lt M 0 _ _ hpa
        have hpa' : par M 0 (j0 + q'') = some (j0 + (pa - j0)) := by rw [hpa]; congr 1; omega
        rw [par0_gexp_mir hlen hk' hq'' hpa'] at hcp
        have hcp' := Option.some.inj hcp
        have hu := TRIO.mir_decomp_unique (j0 := j0) (Lb := Lb) (show pa - j0 < Lb by omega) hq
          (show j0 + (k' * Lb + (pa - j0)) = j0 + (k * Lb + q) from hcp')
        obtain ⟨rfl, hq2⟩ := hu
        refine ⟨q'', ?_, rfl⟩
        rw [List.mem_filter, List.mem_range]
        refine ⟨hq'', ?_⟩
        simp only [decide_eq_true_eq]
        exact ⟨h0, by rw [hpa]; congr 1; omega⟩
    · rintro ⟨q', hq', rfl⟩
      rw [List.mem_filter, List.mem_range] at hq'
      obtain ⟨hq'L, hq'd⟩ := hq'
      simp only [decide_eq_true_eq] at hq'd
      refine ⟨?_, par0_gexp_mir hlen hk hq'L hq'd.2⟩
      rw [hlen']
      have : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
      have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
      omega

end

/-- **Children of a block column in `M`**: inside the block, plus the last column if it hangs there. -/
theorem children_block {M : Mat} {j0 Lb q : Nat} (hlen : j0 + Lb + 1 = M.length) :
    children M (j0 + q) =
      ((List.range Lb).filter (fun q' => decide (0 < q' ∧ par M 0 (j0 + q') = some (j0 + q)))).map
        (fun q' => j0 + q') ++
      (if par M 0 (j0 + Lb) = some (j0 + q) then [j0 + Lb] else []) := by
  apply eq_of_sorted_mem _ _ (children_sorted _ _)
  · rw [List.pairwise_append]
    refine ⟨List.Pairwise.map _ (by intro a b hab; omega)
      (List.Pairwise.filter _ List.pairwise_lt_range), ?_, ?_⟩
    · split <;> simp
    · intro a ha b hb
      split at hb
      · simp at hb; subst hb
        obtain ⟨q', hq', rfl⟩ := List.mem_map.mp ha
        rw [List.mem_filter, List.mem_range] at hq'; omega
      · simp at hb
  · intro c
    rw [mem_children_iff, List.mem_append, List.mem_map]
    constructor
    · rintro ⟨hcl, hcp⟩
      have hcq := par_lt M 0 c _ hcp
      rcases Nat.lt_or_ge c (j0 + Lb) with h | h
      · left
        refine ⟨c - j0, ?_, by omega⟩
        rw [List.mem_filter, List.mem_range]
        refine ⟨by omega, ?_⟩
        simp only [decide_eq_true_eq]
        exact ⟨by omega, by rw [show j0 + (c - j0) = c by omega]; exact hcp⟩
      · right
        have hc : c = j0 + Lb := by omega
        subst hc
        rw [if_pos hcp]; simp
    · rintro (⟨q', hq', rfl⟩ | h)
      · rw [List.mem_filter, List.mem_range] at hq'
        simp only [decide_eq_true_eq] at hq'
        exact ⟨by omega, hq'.2.2⟩
      · split at h
        · rename_i hp
          simp at h; subst h
          exact ⟨by omega, hp⟩
        · simp at h

section
variable {M : Mat} {j0 Lb n : Nat} (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
  (hA : Anc0 M j0 (j0 + Lb)) {g : Nat} (hg : par M 0 j0 = some g)
  (hF : F1 (TRIO.gexp M j0 Lb 0 0 n))
include hlen hLb hA hg hF

/-- **Copies have the values of the first copy** (`t = 0`). -/
theorem o2r_gexp_copy_t0 {k : Nat} (hk : k < n) :
    ∀ q, q < Lb → o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (k * Lb + q)) =
      o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (0 * Lb + q)) := by
  have hn0 : 0 < n := by omega
  have key : ∀ m q, Lb - q ≤ m → q < Lb → o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (k * Lb + q)) =
      o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (0 * Lb + q)) := by
    intro m
    induction m with
    | zero => intro q h1 h2; omega
    | succ m ih =>
      intro q hm hq
      apply o2r_congr
      · rw [vr_eq_nT hF, vr_eq_nT hF, entry1_gexp_d1z hlen hk hq, entry1_gexp_d1z hlen hn0 hq]
      · rw [children_gexp_t0 hlen hLb hA hg hk hq, children_gexp_t0 hlen hLb hA hg hn0 hq,
          List.map_map, List.map_map]
        apply List.map_congr_left
        intro q' hq'
        rw [List.mem_filter, List.mem_range] at hq'
        simp only [decide_eq_true_eq] at hq'
        have := par_lt M 0 _ _ hq'.2.2
        exact ih q' (by omega) hq'.1
  exact fun q hq => key _ q (Nat.le_refl _) hq

end

section
variable {M : Mat} {j0 Lb n : Nat} (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
  (hA : Anc0 M j0 (j0 + Lb)) {g : Nat} (hg : par M 0 j0 = some g)
  (hF : F1 (TRIO.gexp M j0 Lb 0 0 n)) (hFM : F1 M) (hn : 1 ≤ n)
  (hx0 : par M 0 (j0 + Lb) = some j0)
include hlen hLb hA hg hF hFM hn hx0

theorem vr_gexp_block {q : Nat} (hq : q < Lb) :
    vr (TRIO.gexp M j0 Lb 0 0 n) (j0 + (0 * Lb + q)) = vr M (j0 + q) := by
  rw [vr_eq_nT hF, vr_eq_nT hFM, entry1_gexp_d1z hlen (show 0 < n by omega) hq]

/-- **The first copy keeps the values of the block** (away from `r`, `t = 0`). -/
theorem o2r_gexp_block_t0 : ∀ q, 0 < q → q < Lb →
    o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (0 * Lb + q)) = o2r M (j0 + q) := by
  have key : ∀ m q, Lb - q ≤ m → 0 < q → q < Lb →
      o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (0 * Lb + q)) = o2r M (j0 + q) := by
    intro m
    induction m with
    | zero => intro q h1 _ h2; omega
    | succ m ih =>
      intro q hm hq0 hq
      apply o2r_congr (vr_gexp_block hlen hLb hA hg hF hFM hn hx0 hq)
      rw [children_gexp_t0 hlen hLb hA hg (show 0 < n by omega) hq, children_block hlen,
        if_neg (by rw [hx0]; intro h; have := Option.some.inj h; omega), List.append_nil,
        List.map_map, List.map_map]
      apply List.map_congr_left
      intro q' hq'
      rw [List.mem_filter, List.mem_range] at hq'
      simp only [decide_eq_true_eq] at hq'
      have := par_lt M 0 _ _ hq'.2.2
      exact ih q' (by omega) hq'.2.1 hq'.1
  exact fun q => key _ q (Nat.le_refl _)

end

section
variable {M : Mat} {j0 Lb n : Nat} (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
  (hA : Anc0 M j0 (j0 + Lb)) {g : Nat} (hg : par M 0 j0 = some g)
  (hF : F1 (TRIO.gexp M j0 Lb 0 0 n)) (hG : Good2 M) (hn : 1 ≤ n)
  (hx0 : par M 0 (j0 + Lb) = some j0)
include hlen hLb hA hg hF hG hn hx0

/-- **The value of `r` after a `t = 0` expansion**: `ψ_v(b)` with `b` the state of the siblings before
`x`. -/
theorem o2r_gexp_r_t0 :
    o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (0 * Lb + 0)) = psi (vr M j0) (bst M j0 (j0 + Lb)) z := by
  have hFM := hG.f1
  set F0 := (List.range Lb).filter (fun q' => decide (0 < q' ∧ par M 0 (j0 + q') = some (j0 + 0)))
    with hF0
  have hch : children (TRIO.gexp M j0 Lb 0 0 n) (j0 + (0 * Lb + 0)) =
      F0.map (fun q' => j0 + (0 * Lb + q')) := children_gexp_t0 hlen hLb hA hg (by omega) hLb
  have hvals : (children (TRIO.gexp M j0 Lb 0 0 n) (j0 + (0 * Lb + 0))).map
      (o2r (TRIO.gexp M j0 Lb 0 0 n)) = (F0.map (fun q' => j0 + q')).map (o2r M) := by
    rw [hch, List.map_map, List.map_map]
    apply List.map_congr_left
    intro q' hq'
    rw [hF0, List.mem_filter, List.mem_range] at hq'
    simp only [decide_eq_true_eq] at hq'
    exact o2r_gexp_block_t0 hlen hLb hA hg hF hFM hn hx0 q' hq'.2.1 hq'.1
  have hC : (children M j0).filter (fun d => decide (d < j0 + Lb)) = F0.map (fun q' => j0 + q') := by
    have hb : children M j0 = F0.map (fun q' => j0 + q') ++ [j0 + Lb] := by
      have := children_block (q := 0) hlen (M := M)
      rw [if_pos (show par M 0 (j0 + Lb) = some (j0 + 0) from hx0)] at this
      exact this
    rw [hb, List.filter_append]
    simp only [List.filter_cons, List.filter_nil, Nat.lt_irrefl, decide_false, Bool.false_eq_true,
      if_false, List.append_nil]
    apply List.filter_eq_self.mpr
    intro c hc
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hc
    rw [List.mem_filter, List.mem_range] at hq'
    simpa using hq'.1
  have hsub : ((F0.map (fun q' => j0 + q')).map (o2r M)).Pairwise (fun a b => b ≤ a) := by
    rw [← hC]
    exact List.Pairwise.sublist (List.Sublist.map _ List.filter_sublist) (hG.dec j0)
  obtain ⟨hSot, _⟩ := sumN_dec _ (fun t ht => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hG i) hsub
  rw [o2r_eq, hvals, vr_gexp_block hlen hLb hA hg hF hFM hn hx0 hLb]
  show add (sp (sf (vr M (j0 + 0))) z (sf _)) (sf z) = _
  rw [sf_ot (isOT_vr hFM _), sf_ot hSot, sp_eq_spArg]
  unfold bst
  rw [hC]
  rfl

end

section
variable {M : Mat} {j0 Lb n : Nat} (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
  (hA : Anc0 M j0 (j0 + Lb)) {g : Nat} (hg : par M 0 j0 = some g) (hn : 1 ≤ n)
  (hx0 : par M 0 (j0 + Lb) = some j0)
  (hpre : ∀ c, c < j0 + Lb → par (TRIO.gexp M j0 Lb 0 0 n) 0 c = par M 0 c)
include hlen hLb hA hg hn hx0 hpre

/-- **The children of `g` after a `t = 0` expansion**: those of `M`, then the copy roots. -/
theorem children_gexp_g_t0 :
    children (TRIO.gexp M j0 Lb 0 0 n) g =
      children M g ++ (List.range (n - 1)).map (fun k => j0 + ((k + 1) * Lb + 0)) := by
  have hlen' := TRIO.gexp_length (d0 := 0) (d1 := 0) (n := n) hlen
  have hgj := par_lt M 0 j0 g hg
  have hchM : ∀ c ∈ children M g, c < j0 + Lb := by
    intro c hc
    have hcm := mem_children_iff.mp hc
    rcases Nat.lt_or_ge c (j0 + Lb) with h | h
    · exact h
    · exfalso
      have : c = j0 + Lb := by omega
      subst this; rw [hx0] at hcm; have := Option.some.inj hcm.2; omega
  apply eq_of_sorted_mem _ _ (children_sorted _ _)
  · rw [List.pairwise_append]
    refine ⟨children_sorted M g, ?_, ?_⟩
    · apply List.Pairwise.map _ _ List.pairwise_lt_range
      intro a b hab
      have : (a + 1) * Lb < (b + 1) * Lb := Nat.mul_lt_mul_of_pos_right (by omega) hLb
      omega
    · intro a ha b hb
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb
      have := hchM a ha
      have : Lb ≤ (k + 1) * Lb := by
        have := Nat.mul_le_mul_right Lb (show 1 ≤ k + 1 by omega); simpa using this
      omega
  · intro c
    rw [mem_children_iff, List.mem_append, List.mem_map, mem_children_iff]
    constructor
    · rintro ⟨hcl, hcp⟩
      rcases Nat.lt_or_ge c (j0 + Lb) with h | h
      · left; rw [hpre c h] at hcp; exact ⟨by omega, hcp⟩
      · right
        obtain ⟨k', q'', hk', hq'', rfl⟩ := TRIO.gexp_pos_decomp (j0 := j0) (n := n) (p := c) hLb
          (by omega) (by rw [hlen'] at hcl; exact hcl)
        have hk1 : 1 ≤ k' := by
          rcases Nat.eq_zero_or_pos k' with h0 | h0
          · subst h0; simp at h; omega
          · exact h0
        rcases Nat.eq_zero_or_pos q'' with h0 | h0
        · subst h0
          exact ⟨k' - 1, List.mem_range.mpr (by omega), by
            rw [show k' - 1 + 1 = k' by omega]⟩
        · exfalso
          obtain ⟨pa, hpa⟩ := par0_some_of (show j0 < j0 + q'' by omega)
            (anc0_interval hA (j0 + q'') (by omega) (by omega))
          have hge := par0_ge_of_anc hA (show j0 < j0 + q'' by omega) (by omega) hpa
          have hplt := par_lt M 0 _ _ hpa
          have hpa' : par M 0 (j0 + q'') = some (j0 + (pa - j0)) := by rw [hpa]; congr 1; omega
          rw [par0_gexp_mir hlen hk' hq'' hpa'] at hcp
          have := Option.some.inj hcp; omega
    · rintro (⟨hcl, hcp⟩ | ⟨k, hk, rfl⟩)
      · have hc := hchM c (mem_children_iff.mpr ⟨hcl, hcp⟩)
        have hLn : Lb ≤ n * Lb := by
          have := Nat.mul_le_mul_right Lb hn; simpa using this
        refine ⟨by rw [hlen']; omega, by rw [hpre c hc]; exact hcp⟩
      · have hk' := List.mem_range.mp hk
        refine ⟨?_, par0_gexp_root_t0 hlen hLb (by omega) hA hg⟩
        rw [hlen']
        have : (k + 1 + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
        have h2 : (k + 1 + 1) * Lb = (k + 1) * Lb + Lb := Nat.succ_mul (k + 1) Lb
        omega

end

end Ytosk
