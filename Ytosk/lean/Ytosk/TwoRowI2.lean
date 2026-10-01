/-
**(I2) 展開で不変条件 Inv2 が保たれる: t = 0（2 行）。**

N = M[n] = gexp M r L 0 0 n（n ≥ 2）。写しの列の値はブロックの値（r だけ ψ_v(b)、b = x の前の兄弟の状態）。
r より前の列は、経路の上の列が `twoRow_t0` で小さく、ほかは同じ。
-/
import Ytosk.TwoRowJ

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {j0 Lb n : Nat} (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
  (hA : Anc0 M j0 (j0 + Lb)) (hR : CopyRootsLow (TRIO.gexp M j0 Lb 0 0 n) j0 Lb n)
  (hF : F1 (TRIO.gexp M j0 Lb 0 0 n)) (hG : Good2 M) (hn : 2 ≤ n)
  (hx0 : par M 0 (j0 + Lb) = some j0) (hx1 : entry M 1 (j0 + Lb) = 0)
include hlen hLb hA hR hF hG hn hx0 hx1

/-- **The values in the copies** (`t = 0`). -/
theorem o2r_copy_t0 {k q : Nat} (hk : k < n) (hq : q < Lb) :
    o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (k * Lb + q)) =
      if q = 0 then psi (vr M j0) (bst M j0 (j0 + Lb)) z else o2r M (j0 + q) := by
  rw [o2r_gexp_copy_t0 hlen hLb hA hR hF hk q hq]
  split_ifs with hq0
  · subst hq0; exact o2r_gexp_r_t0 hlen hLb hA hR hF hG (by omega) hx0
  · exact o2r_gexp_block_t0 hlen hLb hA hR hF hG.f1 (by omega) hx0 q (by omega) hq

theorem ot_r_t0 : isOT (psi (vr M j0) (bst M j0 (j0 + Lb)) z) = true := by
  have h := hG.ot j0
  rw [o2r_r_succ hG hlen hx0 hx1] at h
  exact ot_prefix h

/-- **Standardness of the values**, given the columns before `r`. -/
theorem ot_t0 (hlow : ∀ c, c < j0 → isOT (o2r (TRIO.gexp M j0 Lb 0 0 n) c) = true) :
    ∀ i, isOT (o2r (TRIO.gexp M j0 Lb 0 0 n) i) = true := by
  have hlen' := TRIO.gexp_length (d0 := 0) (d1 := 0) (n := n) hlen
  intro i
  rcases Nat.lt_or_ge i j0 with h1 | h1
  · exact hlow i h1
  · rcases Nat.lt_or_ge i (j0 + n * Lb) with h2 | h2
    · obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := j0) (n := n) (p := i) hLb h1 h2
      rw [o2r_copy_t0 hlen hLb hA hR hF hG hn hx0 hx1 hk hq]
      split_ifs
      · exact ot_r_t0 hlen hLb hA hR hF hG hn hx0 hx1
      · exact hG.ot _
    · rw [o2r_out (by rw [hlen']; exact h2)]; rfl

/-- **Sibling order in the copies and the block** (`t = 0`). -/
theorem dec_copy_t0 {k q : Nat} (hk : k < n) (hq : q < Lb) :
    ((children (TRIO.gexp M j0 Lb 0 0 n) (j0 + (k * Lb + q))).map
      (o2r (TRIO.gexp M j0 Lb 0 0 n))).Pairwise (fun a b => b ≤ a) := by
  rw [children_gexp_t0 hlen hLb hA hR hk hq, List.map_map]
  set F := (List.range Lb).filter (fun q' => decide (0 < q' ∧ par M 0 (j0 + q') = some (j0 + q)))
    with hFdef
  have hv : F.map ((o2r (TRIO.gexp M j0 Lb 0 0 n)) ∘ (fun q' => j0 + (k * Lb + q'))) =
      (F.map (fun q' => j0 + q')).map (o2r M) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro q' hq'
    rw [hFdef, List.mem_filter, List.mem_range] at hq'
    simp only [decide_eq_true_eq] at hq'
    simp only [Function.comp]
    rw [o2r_copy_t0 hlen hLb hA hR hF hG hn hx0 hx1 hk hq'.1, if_neg (by omega)]
  rw [hv]
  have hb := children_block (q := q) hlen (M := M)
  have hsub : (F.map (fun q' => j0 + q')).Sublist (children M (j0 + q)) := by
    rw [hb]; exact List.sublist_append_left _ _
  exact List.Pairwise.sublist (List.Sublist.map _ hsub) (hG.dec (j0 + q))

/-- **Sibling order**, given the columns before `r`. -/
theorem dec_t0
    (hlow : ∀ h, h < j0 → ((children (TRIO.gexp M j0 Lb 0 0 n) h).map
      (o2r (TRIO.gexp M j0 Lb 0 0 n))).Pairwise (fun a b => b ≤ a)) :
    ∀ h, ((children (TRIO.gexp M j0 Lb 0 0 n) h).map
      (o2r (TRIO.gexp M j0 Lb 0 0 n))).Pairwise (fun a b => b ≤ a) := by
  have hlen' := TRIO.gexp_length (d0 := 0) (d1 := 0) (n := n) hlen
  intro h
  rcases Nat.lt_or_ge h j0 with h1 | h1
  · exact hlow h h1
  · rcases Nat.lt_or_ge h (j0 + n * Lb) with h2 | h2
    · obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := j0) (n := n) (p := h) hLb h1 h2
      exact dec_copy_t0 hlen hLb hA hR hF hG hn hx0 hx1 hk hq
    · have : children (TRIO.gexp M j0 Lb 0 0 n) h = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro c hc; have := mem_children hc; omega
      rw [this]; exact List.Pairwise.nil

/-- The parent of a non-root copy column is in the same copy. -/
theorem par_copy_t0 {k q' h : Nat} (hk : k < n) (hq'0 : 0 < q') (hq' : q' < Lb)
    (hp : par (TRIO.gexp M j0 Lb 0 0 n) 0 (j0 + (k * Lb + q')) = some h) :
    ∃ q, q < q' ∧ h = j0 + (k * Lb + q) ∧ par M 0 (j0 + q') = some (j0 + q) := by
  obtain ⟨pa, hpa⟩ := par0_some_of (show j0 < j0 + q' by omega)
    (anc0_interval hA (j0 + q') (by omega) (by omega))
  have hge := par0_ge_of_anc hA (show j0 < j0 + q' by omega) (by omega) hpa
  have hplt := par_lt M 0 _ _ hpa
  have hpa' : par M 0 (j0 + q') = some (j0 + (pa - j0)) := by rw [hpa]; congr 1; omega
  rw [par0_gexp_mir hlen hk hq' hpa'] at hp
  exact ⟨pa - j0, by omega, (Option.some.inj hp).symm, hpa'⟩

/-- **The state in a copy frame is the state in the block frame of `M`.** -/
theorem bst_copy_t0 {k q q' : Nat} (hk : k < n) (hq : q < Lb) (hq'0 : 0 < q') (hq' : q' < Lb) :
    bst (TRIO.gexp M j0 Lb 0 0 n) (j0 + (k * Lb + q)) (j0 + (k * Lb + q')) = bst M (j0 + q) (j0 + q') := by
  unfold bst
  have hv : vr (TRIO.gexp M j0 Lb 0 0 n) (j0 + (k * Lb + q)) = vr M (j0 + q) := by
    rw [vr_eq_nT hF, vr_eq_nT hG.f1, entry1_gexp_d1z hlen hk hq]
  rw [hv, children_gexp_t0 hlen hLb hA hR hk hq, children_block (q := q) hlen]
  congr 2
  set F := (List.range Lb).filter (fun q'' => decide (0 < q'' ∧ par M 0 (j0 + q'') = some (j0 + q)))
    with hFdef
  rw [List.filter_append]
  have hx_out : (if par M 0 (j0 + Lb) = some (j0 + q) then [j0 + Lb] else []).filter
      (fun d => decide (d < j0 + q')) = [] := by
    split <;> simp; omega
  rw [hx_out, List.append_nil, List.filter_map, List.filter_map, List.map_map, List.map_map]
  have hfe : F.filter ((fun d => decide (d < j0 + (k * Lb + q'))) ∘ fun q'' => j0 + (k * Lb + q'')) =
      F.filter ((fun d => decide (d < j0 + q')) ∘ fun q'' => j0 + q'') := by
    apply List.filter_congr
    intro q'' _
    simp only [Function.comp, decide_eq_decide]
    omega
  rw [hfe]
  apply List.map_congr_left
  intro q'' hq''
  rw [List.mem_filter, hFdef, List.mem_filter, List.mem_range] at hq''
  simp only [decide_eq_true_eq, Function.comp] at hq'' ⊢
  rw [o2r_copy_t0 hlen hLb hA hR hF hG hn hx0 hx1 hk hq''.1.1, if_neg (by omega)]

/-- **PreHi in a copy frame** (non-root copy column). -/
theorem preHi_copy_t0 (hH : PreHi M) {k q' h : Nat} (hk : k < n) (hq'0 : 0 < q') (hq' : q' < Lb)
    (hp : par (TRIO.gexp M j0 Lb 0 0 n) 0 (j0 + (k * Lb + q')) = some h) {s y : T}
    (hc : o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (k * Lb + q')) = psi s y z)
    (hB : bst (TRIO.gexp M j0 Lb 0 0 n) h (j0 + (k * Lb + q')) ≠ z)
    (h1 : lt (bst (TRIO.gexp M j0 Lb 0 0 n) h (j0 + (k * Lb + q'))) y = true)
    (h2 : lt (psi (vr (TRIO.gexp M j0 Lb 0 0 n) h) z z) (psi s y z) = true) :
    hiP s y = bst (TRIO.gexp M j0 Lb 0 0 n) h (j0 + (k * Lb + q')) ∧ loP s y ≠ z := by
  obtain ⟨q, hqq, rfl, hpM⟩ := par_copy_t0 hlen hLb hA hR hF hG hn hx0 hx1 hk hq'0 hq' hp
  rw [o2r_copy_t0 hlen hLb hA hR hF hG hn hx0 hx1 hk hq', if_neg (by omega)] at hc
  rw [bst_copy_t0 hlen hLb hA hR hF hG hn hx0 hx1 hk (by omega) hq'0 hq'] at hB h1 ⊢
  rw [vr_eq_nT hF, entry1_gexp_d1z hlen hk (show q < Lb by omega), ← vr_eq_nT hG.f1] at h2
  exact hH (j0 + q) (j0 + q') s y (by omega) hpM hc hB h1 h2

/-- **PreFC in a copy frame** (non-root copy column). -/
theorem preFC_copy_t0 (hFC : PreFC M) {k q' h : Nat} (hk : k < n) (hq'0 : 0 < q') (hq' : q' < Lb)
    (hp : par (TRIO.gexp M j0 Lb 0 0 n) 0 (j0 + (k * Lb + q')) = some h) {s y : T}
    (hc : o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (k * Lb + q')) = psi s y z)
    (hB : bst (TRIO.gexp M j0 Lb 0 0 n) h (j0 + (k * Lb + q')) = z)
    (h1 : lt z y = true)
    (h2 : lt (psi (vr (TRIO.gexp M j0 Lb 0 0 n) h) z z) (psi s y z) = true)
    (hv : vr (TRIO.gexp M j0 Lb 0 0 n) h = s) : hiP s y = z ∧ loP s y ≠ z := by
  obtain ⟨q, hqq, rfl, hpM⟩ := par_copy_t0 hlen hLb hA hR hF hG hn hx0 hx1 hk hq'0 hq' hp
  rw [o2r_copy_t0 hlen hLb hA hR hF hG hn hx0 hx1 hk hq', if_neg (by omega)] at hc
  rw [bst_copy_t0 hlen hLb hA hR hF hG hn hx0 hx1 hk (by omega) hq'0 hq'] at hB
  have hvv : vr (TRIO.gexp M j0 Lb 0 0 n) (j0 + (k * Lb + q)) = vr M (j0 + q) := by
    rw [vr_eq_nT hF, entry1_gexp_d1z hlen hk (show q < Lb by omega), ← vr_eq_nT hG.f1]
  rw [hvv] at h2 hv
  exact hFC (j0 + q) (j0 + q') s y (by omega) hpM hc hB h1 h2 hv

end

end Ytosk
