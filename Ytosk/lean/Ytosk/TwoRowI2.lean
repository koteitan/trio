/-
**(I2) 展開で不変条件 Inv2 が保たれる: t = 0（2 行）。**

N = M[n] = gexp M r L 0 0 n（n ≥ 2）。写しの列の値はブロックの値（r だけ ψ_v(b)、b = x の前の兄弟の状態）。
r より前の列は、経路の上の列が `twoRow_t0` で小さく、ほかは同じ。
-/
import Ytosk.TwoRowJ

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## 状態は子を足しても減らない -/

theorem step_ge {a S s y c : T} (hc : isOT (psi s y z) = true) : S ≤ step a S s y c := by
  unfold step
  split_ifs with htr
  · exact le_of_lt (lt_of_lt_of_le htr.1 (le_H hc))
  · exact le_of_lt (lt_add_principal s y S)

theorem spArg_ge {a : T} : ∀ (X S : T), isOT X = true → S ≤ spArg a S X
  | z, S, _ => le_refl _
  | psi s y c, S, hX => by
    rw [spArg_cons]
    have hc : isOT (psi s y z) = true := by
      obtain ⟨h1, h2, _, _, h5⟩ := isOT_psi_iff.mp hX
      rw [isOT_psi_iff]; exact ⟨h1, h2, rfl, z_le _, h5⟩
    exact le_trans (step_ge hc) (spArg_ge c _ (isOT_rest hX))

theorem sumN_append_dec {L1 L2 : List T} (hs : ∀ t ∈ L1 ++ L2, Single t)
    (hp : (L1 ++ L2).Pairwise (fun a b => b ≤ a)) : sumN (L1 ++ L2) = app (sumN L1) (sumN L2) := by
  have hp' := List.pairwise_append.mp hp
  obtain ⟨_, h12⟩ := sumN_dec _ hs hp
  obtain ⟨_, h1⟩ := sumN_dec L1 (fun t ht => hs t (List.mem_append_left _ ht)) hp'.1
  obtain ⟨_, h2⟩ := sumN_dec L2 (fun t ht => hs t (List.mem_append_right _ ht)) hp'.2.1
  apply eq_of_summands
  rw [h12, summands_app, h1, h2]

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

/-! ## r が根でない場合（g = P_0(r)） -/

section
variable {M : Mat} {j0 Lb n : Nat} (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
  (hA : Anc0 M j0 (j0 + Lb)) {g : Nat} (hg : par M 0 j0 = some g)
  (hF : F1 (TRIO.gexp M j0 Lb 0 0 n)) (hI : Inv2 M) (hn : 2 ≤ n)
  (hx0 : par M 0 (j0 + Lb) = some j0) (hx1 : entry M 1 (j0 + Lb) = 0)
  (hpre : ∀ c, c < j0 + Lb → par (TRIO.gexp M j0 Lb 0 0 n) 0 c = par M 0 c)
include hlen hLb hA hg hF hI hn hx0 hx1 hpre

theorem hR_g : CopyRootsLow (TRIO.gexp M j0 Lb 0 0 n) j0 Lb n := copyRootsLow_of_g hlen hLb hA hg

/-- Off the path, the columns before `r` keep their values. -/
theorem low_off_t0 : ∀ c, c < j0 + Lb → ¬ Anc0 M c (j0 + Lb) →
    o2r (TRIO.gexp M j0 Lb 0 0 n) c = o2r M c := by
  intro c hc hnA
  refine o2r_off_gen' hlen ?_ ?_ c hc hnA
  · intro j' hj'
    exact vr_gexp_pre_t0 hlen hLb hA hg (by omega) hx0 hpre hF hI.g2 hj'
  · intro h hh hnA'
    exact children_gexp_off_t0 hlen hLb hA hg (by omega) hx0 hpre hh hnA'

/-- On the path from `g` up, the values drop and stay standard. -/
theorem low_path_t0 : ∀ c, Anc0 M c g →
    isOT (o2r (TRIO.gexp M j0 Lb 0 0 n) c) = true ∧ o2r (TRIO.gexp M j0 Lb 0 0 n) c < o2r M c := by
  have hPRE : ∀ h p s y, Anc0 M p (j0 + Lb) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
      bst M h p ≠ z → ∃ rest, y = app (bst M h p) rest ∧ rest ≠ z := by
    intro h p s y hp hph hc h1 h2 h3
    have hpl : p < M.length := by have := hp.le; omega
    obtain ⟨hhi, hlo⟩ := hI.hi h p s y hpl hph hc h3 h1 h2
    refine ⟨loP s y, ?_, hlo⟩
    have := hiP_loP s y; rw [hhi] at this; exact this.symm
  intro c hc
  obtain ⟨j, hj, hot, hlt⟩ := twoRow_t0_path hlen hLb hA hg hn hx0 hpre hF hI.g2 hx1 hPRE c hc
  rw [hj]; exact ⟨hot, hlt⟩

/-- An earlier sibling of a column before `x` is off the path. -/
theorem earlier_off {h p d : Nat} (hp : par M 0 p = some h) (hpx : p ≤ j0 + Lb)
    (hd : d ∈ (children M h).filter (fun d => decide (d < p))) : ¬ Anc0 M d (j0 + Lb) := by
  rw [List.mem_filter] at hd
  have hdp : d < p := by simpa using hd.2
  exact not_anc_of_earlier (mem_children_iff.mp hd.1).2 hp hdp hpx

theorem anc_g_of_lt {c : Nat} (hcA : Anc0 M c (j0 + Lb)) (hcj : c < j0) : Anc0 M c g := by
  rcases anc0_total hcA hA with h' | h'
  · exact anc0_par h' (by omega) hg
  · have := h'.le; omega

/-- The state before a column `≤ r` is unchanged. -/
theorem bst_low_t0 {h p : Nat} (hp : par M 0 p = some h) (hpj : p ≤ j0) :
    bst (TRIO.gexp M j0 Lb 0 0 n) h p = bst M h p := by
  have hhp := par_lt M 0 p h hp
  unfold bst
  rw [vr_gexp_pre_t0 hlen hLb hA hg (by omega) hx0 hpre hF hI.g2 (show h < j0 + Lb by omega)]
  have hfil : (children (TRIO.gexp M j0 Lb 0 0 n) h).filter (fun d => decide (d < p)) =
      (children M h).filter (fun d => decide (d < p)) := by
    by_cases hhg : h = g
    · subst hhg
      rw [children_gexp_g_t0 hlen hLb hA hg (by omega) hx0 hpre, List.filter_append]
      have : ((List.range (n - 1)).map (fun k => j0 + ((k + 1) * Lb + 0))).filter
          (fun d => decide (d < p)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro d hd; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd
        have : Lb ≤ (k + 1) * Lb := by rw [Nat.succ_mul]; omega
        simp; omega
      rw [this, List.append_nil]
    · rw [children_gexp_lt_t0 hlen hLb hA hg (by omega) hx0 hpre (by omega) hhg]
  rw [hfil]
  congr 2
  apply List.map_congr_left
  intro d hd
  have hdp : d < p := by rw [List.mem_filter] at hd; simpa using hd.2
  exact low_off_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre d (by omega) (earlier_off hlen hLb hA hg hF hI hn hx0 hx1 hpre hp (by omega) hd)

theorem o2r_r_new_t0 : o2r (TRIO.gexp M j0 Lb 0 0 n) j0 = psi (vr M j0) (bst M j0 (j0 + Lb)) z := by
  have := o2r_copy_t0 hlen hLb hA (hR_g hlen hLb hA hg hF hI hn hx0 hx1 hpre) hF hI.g2 hn hx0 hx1
    (k := 0) (q := 0) (by omega) hLb
  simpa using this

theorem o2r_root_new_t0 {k : Nat} (hk : k < n) :
    o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (k * Lb + 0)) = psi (vr M j0) (bst M j0 (j0 + Lb)) z := by
  have := o2r_copy_t0 hlen hLb hA (hR_g hlen hLb hA hg hF hI hn hx0 hx1 hpre) hF hI.g2 hn hx0 hx1
    (k := k) (q := 0) hk hLb
  simpa using this

/-- `r`'s children before `x` ... `g`'s children in the expansion: those of `M`, then the copy roots,
in non-increasing order. -/
theorem dec_g_t0 : ((children (TRIO.gexp M j0 Lb 0 0 n) g).map
    (o2r (TRIO.gexp M j0 Lb 0 0 n))).Pairwise (fun a b => b ≤ a) := by
  have hgj := par_lt M 0 j0 g hg
  have hle := children_le_of_anc_last hA hlen hg
  have hjmem : j0 ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
  have hsplit := split_last_max _ j0 (children_sorted M g) hjmem hle
  rw [children_gexp_g_t0 hlen hLb hA hg (by omega) hx0 hpre, hsplit]
  set C := (children M g).filter (fun d => decide (d < j0)) with hCdef
  have hCv : C.map (o2r (TRIO.gexp M j0 Lb 0 0 n)) = C.map (o2r M) := by
    apply List.map_congr_left; intro d hd
    exact low_off_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre d (by
      rw [hCdef, List.mem_filter] at hd; have : d < j0 := by simpa using hd.2
      omega) (earlier_off hlen hLb hA hg hF hI hn hx0 hx1 hpre hg (by omega) hd)
  have hRv : ((List.range (n - 1)).map (fun k => j0 + ((k + 1) * Lb + 0))).map
      (o2r (TRIO.gexp M j0 Lb 0 0 n)) =
      List.replicate (n - 1) (psi (vr M j0) (bst M j0 (j0 + Lb)) z) := by
    rw [List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate, Function.comp]
    exact o2r_root_new_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre (by simp at h1; omega)
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [hCv, hRv, o2r_r_new_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre]
  have hdM := hI.g2.dec g
  rw [hsplit, List.map_append] at hdM
  have hdM' := List.pairwise_append.mp hdM
  have hrlt : psi (vr M j0) (bst M j0 (j0 + Lb)) z < o2r M j0 := by
    rw [o2r_r_succ hI.g2 hlen hx0 hx1, psi_lt_psi_z_iff]
    exact Or.inr ⟨rfl, lt_app_of (by simp [one])⟩
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨hdM'.1, List.pairwise_singleton _ _, fun a ha c hc => ?_⟩,
    List.pairwise_replicate.mpr (Or.inr (le_refl _)), fun a ha c hc => ?_⟩
  · rw [List.mem_singleton] at hc; subst hc
    exact le_trans (le_of_lt hrlt) (hdM'.2.2 a ha _ (by simp))
  · rw [List.eq_of_mem_replicate hc]
    rcases List.mem_append.mp ha with ha | ha
    · exact le_trans (le_of_lt hrlt) (hdM'.2.2 a ha _ (by simp))
    · rw [List.mem_singleton] at ha; rw [ha]

/-- **No rewriting at the copy roots** (`t = 0`): the state before a copy root is at least `b` or the
subscripts forbid rewriting. -/
theorem join_notrig_t0 {k : Nat} (hk1 : 1 ≤ k) (hk : k < n) :
    ¬ (lt (bst (TRIO.gexp M j0 Lb 0 0 n) g (j0 + (k * Lb + 0))) (bst M j0 (j0 + Lb)) = true ∧
      lt (psi (vr (TRIO.gexp M j0 Lb 0 0 n) g) z z)
        (psi (vr M j0) (bst M j0 (j0 + Lb)) z) = true) := by
  set N := TRIO.gexp M j0 Lb 0 0 n with hN
  set b := bst M j0 (j0 + Lb) with hbdef
  set v := vr M j0 with hvdef
  have hgj := par_lt M 0 j0 g hg
  have hvg : vr N g = vr M g := vr_gexp_pre_t0 hlen hLb hA hg (by omega) hx0 hpre hF hI.g2 (by omega)
  rw [hvg]
  set a := vr M g with hadef
  set Bg := bst M g j0 with hBgdef
  -- the state after `r` in the expansion
  have hle := children_le_of_anc_last hA hlen hg
  have hjmem : j0 ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
  have hsplit := split_last_max _ j0 (children_sorted M g) hjmem hle
  set C := (children M g).filter (fun d => decide (d < j0)) with hCdef
  have hCv : C.map (o2r N) = C.map (o2r M) := by
    apply List.map_congr_left; intro d hd
    exact low_off_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre d (by
      rw [hCdef, List.mem_filter] at hd; have : d < j0 := by simpa using hd.2
      omega) (earlier_off hlen hLb hA hg hF hI hn hx0 hx1 hpre hg (by omega) hd)
  have hdecN := dec_g_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre
  have hot := ot_t0 hlen hLb hA (hR_g hlen hLb hA hg hF hI hn hx0 hx1 hpre) hF hI.g2 hn hx0 hx1
    (fun c hc => by
      by_cases hcA : Anc0 M c (j0 + Lb)
      · exact (low_path_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre c
          (anc_g_of_lt hlen hLb hA hg hF hI hn hx0 hx1 hpre hcA hc)).1
      · rw [low_off_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre c (by omega) hcA]; exact hI.g2.ot c)
  have hsingN : ∀ t ∈ (children N g).map (o2r N), Single t := by
    intro t ht; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
    exact ⟨hot i, o2r_psi_form N i⟩
  have hchN := children_gexp_g_t0 hlen hLb hA hg (by omega) hx0 hpre
  -- `bst` at the root is at least the state after `r`
  have hS1 : step a Bg v b z ≤ bst N g (j0 + (k * Lb + 0)) := by
    unfold bst
    rw [hvg, hchN, List.filter_append]
    have hall : (children M g).filter (fun d => decide (d < j0 + (k * Lb + 0))) = children M g := by
      apply List.filter_eq_self.mpr; intro d hd
      have := hle d hd
      have : Lb ≤ k * Lb := Nat.le_mul_of_pos_left Lb (by omega)
      simp; omega
    rw [hall]
    set R' := ((List.range (n - 1)).map (fun k => j0 + ((k + 1) * Lb + 0))).filter
      (fun d => decide (d < j0 + (k * Lb + 0))) with hR'def
    have hsub : ((children M g).map (o2r N) ++ R'.map (o2r N)).Sublist
        ((children N g).map (o2r N)) := by
      rw [hchN, List.map_append]
      exact List.Sublist.append (List.Sublist.refl _) (List.Sublist.map _ List.filter_sublist)
    rw [List.map_append, sumN_append_dec (fun t ht => hsingN t (hsub.subset ht))
      (List.Pairwise.sublist hsub hdecN), spArg_app]
    refine le_trans ?_ (spArg_ge _ _ (sumN_dec _ (fun t ht => hsingN t (hsub.subset
      (List.mem_append_right _ ht))) (List.Pairwise.sublist (List.Sublist.trans
        (List.sublist_append_right _ _) hsub) hdecN)).1)
    rw [hsplit, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [hCv, o2r_r_new_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre]
    have hsM : ∀ t ∈ C.map (o2r M) ++ [psi v b z], Single t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hI.g2 i
      · rw [List.mem_singleton] at ht; subst ht
        exact ⟨ot_r_t0 hlen hLb hA (hR_g hlen hLb hA hg hF hI hn hx0 hx1 hpre) hF hI.g2 hn hx0 hx1,
          _, _, rfl⟩
    have hdM := hI.g2.dec g
    rw [hsplit, List.map_append] at hdM
    have hdM' := List.pairwise_append.mp hdM
    have hrlt : psi v b z < o2r M j0 := by
      rw [o2r_r_succ hI.g2 hlen hx0 hx1, psi_lt_psi_z_iff]
      exact Or.inr ⟨rfl, lt_app_of (by simp [one])⟩
    have hdC : (C.map (o2r M) ++ [psi v b z]).Pairwise (fun a b => b ≤ a) := by
      rw [List.pairwise_append]
      refine ⟨hdM'.1, List.pairwise_singleton _ _, fun a' ha c hc => ?_⟩
      rw [List.mem_singleton] at hc; subst hc
      exact le_trans (le_of_lt hrlt) (hdM'.2.2 a' ha _ (by simp))
    rw [sumN_snoc_dec hsM hdC, spArg_app, spArg_single]
    exact le_refl _
  -- now `b` is not above the state
  rintro ⟨h1, h2⟩
  have hS1b : step a Bg v b z < b := lt_of_le_of_lt hS1 h1
  have hbot : isOT (psi v b z) = true :=
    ot_r_t0 hlen hLb hA (hR_g hlen hLb hA hg hF hI hn hx0 hx1 hpre) hF hI.g2 hn hx0 hx1
  by_cases hB : Bg = z
  · rw [hB] at hS1b
    unfold step at hS1b
    split_ifs at hS1b with htr
    · exact absurd (le_H hbot) (not_le_of_gt hS1b)
    · have hb0 : b = z := by
        by_contra hb0
        exact htr ⟨lt_of_le_of_ne (z_le _) (Ne.symm hb0), h2⟩
      rw [hb0] at hS1b; exact T.not_lt_z _ hS1b
  · by_cases htrN : lt Bg b = true ∧ lt (psi a z z) (psi v b z) = true
    · -- `PreHi` from `M`'s frame `(g, r)` carried down
      have hoM := o2r_r_succ hI.g2 hlen hx0 hx1
      have hbb1 : b < app b one := lt_app_of (by simp [one])
      obtain ⟨t1, t2⟩ := trig_mono hbb1 htrN.1 htrN.2
      obtain ⟨hhi, hlo⟩ := hI.hi g j0 v (app b one) (by omega) hg hoM hB t1 t2
      obtain ⟨hhi', hlo'⟩ := prehi_of_lt hhi hlo htrN.1 hbb1
      have hstep : step a Bg v b z = app Bg (psi v b z) := by
        unfold step; rw [if_pos htrN, H_eq hbot]
        unfold hiP at hhi'; unfold loP at hlo'
        rw [if_neg hlo', hhi']
      rw [hstep] at hS1b
      have hb' : b = app Bg (loP v b) := by have := hiP_loP v b; rw [hhi'] at this; exact this.symm
      have hlolt : loP v b < psi v b z := split_lo_lt hbot hlo'
      have h3 : app Bg (psi v b z) < app Bg (loP v b) := by rw [← hb']; exact hS1b
      have := (app_lt_app_left_iff Bg).mp h3
      exact absurd hlolt (not_lt_of_gt this)
    · have hBb : b ≤ Bg := by
        by_contra hc
        exact htrN ⟨lt_of_not_ge hc, h2⟩
      exact absurd (lt_of_le_of_lt (le_trans hBb (step_ge hbot)) hS1b) (lt_irrefl' _)

end

end Ytosk
