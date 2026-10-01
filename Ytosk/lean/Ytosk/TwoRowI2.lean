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

theorem low_ot_t0 : ∀ c, c < j0 → isOT (o2r (TRIO.gexp M j0 Lb 0 0 n) c) = true := by
  intro c hc
  by_cases hcA : Anc0 M c (j0 + Lb)
  · exact (low_path_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre c
      (anc_g_of_lt hlen hLb hA hg hF hI hn hx0 hx1 hpre hcA hc)).1
  · rw [low_off_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre c (by omega) hcA]; exact hI.g2.ot c

/-- **Good2 of the expansion** (`t = 0`, `r` not a root). -/
theorem good2_gexp_t0 : Good2 (TRIO.gexp M j0 Lb 0 0 n) := by
  have hRg := hR_g hlen hLb hA hg hF hI hn hx0 hx1 hpre
  refine ⟨hF, ot_t0 hlen hLb hA hRg hF hI.g2 hn hx0 hx1 (low_ot_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre),
    dec_t0 hlen hLb hA hRg hF hI.g2 hn hx0 hx1 ?_⟩
  intro h hh
  by_cases hhg : h = g
  · subst hhg; exact dec_g_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre
  rw [children_gexp_lt_t0 hlen hLb hA hg (by omega) hx0 hpre hh hhg]
  by_cases hA' : Anc0 M h (j0 + Lb)
  · have hhgA := anc_g_of_lt hlen hLb hA hg hF hI hn hx0 hx1 hpre hA' hh
    obtain ⟨c, hc, hcg⟩ := anc0_child hhgA hhg
    have hcA : Anc0 M c (j0 + Lb) := hcg.trans (anc0_up hg hA)
    have hle := children_le_of_anc_last hcA hlen hc
    have hcmem : c ∈ children M h := mem_children_iff.mpr ⟨by have := hcA.le; omega, hc⟩
    have hsplit := split_last_max _ c (children_sorted M h) hcmem hle
    have hdM := hI.g2.dec h
    rw [hsplit, List.map_append] at hdM ⊢
    have hdM' := List.pairwise_append.mp hdM
    have hCv : ((children M h).filter (fun d => decide (d < c))).map (o2r (TRIO.gexp M j0 Lb 0 0 n)) =
        ((children M h).filter (fun d => decide (d < c))).map (o2r M) := by
      apply List.map_congr_left; intro d hd
      have hdc : d < c := by rw [List.mem_filter] at hd; simpa using hd.2
      have := hcg.le; have := par_lt M 0 j0 g hg
      exact low_off_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre d (by omega)
        (earlier_off hlen hLb hA hg hF hI hn hx0 hx1 hpre hc hcA.le hd)
    rw [hCv]
    simp only [List.map_cons, List.map_nil]
    rw [List.pairwise_append]
    refine ⟨hdM'.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    exact le_trans (le_of_lt (low_path_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre c hcg).2)
      (hdM'.2.2 a ha _ (by simp))
  · have hv : (children M h).map (o2r (TRIO.gexp M j0 Lb 0 0 n)) = (children M h).map (o2r M) := by
      apply List.map_congr_left; intro d hd
      have hdp := mem_children_iff.mp hd
      have hdh := par_lt M 0 d h hdp.2
      have hdx : d < j0 + Lb := by
        by_contra hc
        have hdl := hdp.1
        have hde : d = j0 + Lb := by omega
        have h2 := hdp.2
        rw [hde, hx0] at h2
        have := Option.some.inj h2; omega
      apply low_off_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre d hdx
      intro hdA; exact hA' (anc0_up hdp.2 hdA)
    rw [hv]; exact hI.g2.dec h

/-- Shared case split for the frames of the expansion (`t = 0`, `r` not a root). -/
theorem frames_gexp_t0 (P : T → T → T → T → Prop)
    (hlow : ∀ h p s y y', p < j0 → par M 0 p = some h → o2r M p = psi s y z →
      o2r (TRIO.gexp M j0 Lb 0 0 n) p = psi s y' z → y' ≤ y →
      P (vr M h) (bst M h p) s y → P (vr M h) (bst M h p) s y')
    (hr : P (vr M g) (bst M g j0) (vr M j0) (app (bst M j0 (j0 + Lb)) one) →
      P (vr M g) (bst M g j0) (vr M j0) (bst M j0 (j0 + Lb)))
    (hcopy : ∀ k q' h s y, k < n → 0 < q' → q' < Lb →
      par (TRIO.gexp M j0 Lb 0 0 n) 0 (j0 + (k * Lb + q')) = some h →
      o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (k * Lb + q')) = psi s y z →
      P (vr (TRIO.gexp M j0 Lb 0 0 n) h) (bst (TRIO.gexp M j0 Lb 0 0 n) h (j0 + (k * Lb + q'))) s y)
    (hjoin : ∀ k, 1 ≤ k → k < n →
      ¬ (lt (bst (TRIO.gexp M j0 Lb 0 0 n) g (j0 + (k * Lb + 0))) (bst M j0 (j0 + Lb)) = true ∧
        lt (psi (vr (TRIO.gexp M j0 Lb 0 0 n) g) z z) (psi (vr M j0) (bst M j0 (j0 + Lb)) z) = true) →
      P (vr (TRIO.gexp M j0 Lb 0 0 n) g) (bst (TRIO.gexp M j0 Lb 0 0 n) g (j0 + (k * Lb + 0)))
        (vr M j0) (bst M j0 (j0 + Lb)))
    (hM : ∀ h p s y, p < M.length → par M 0 p = some h → o2r M p = psi s y z →
      P (vr M h) (bst M h p) s y) :
    ∀ h p s y, p < (TRIO.gexp M j0 Lb 0 0 n).length → par (TRIO.gexp M j0 Lb 0 0 n) 0 p = some h →
      o2r (TRIO.gexp M j0 Lb 0 0 n) p = psi s y z →
      P (vr (TRIO.gexp M j0 Lb 0 0 n) h) (bst (TRIO.gexp M j0 Lb 0 0 n) h p) s y := by
  have hlen' := TRIO.gexp_length (d0 := 0) (d1 := 0) (n := n) hlen
  have hG2 := good2_gexp_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre
  intro h p s y hpl hp hc
  rcases Nat.lt_or_ge p j0 with h1 | h1
  · -- before `r`
    have hp' : par M 0 p = some h := by rw [← hpre p (by omega)]; exact hp
    have hhp := par_lt M 0 p h hp'
    rw [bst_low_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre hp' (by omega),
      vr_gexp_pre_t0 hlen hLb hA hg (by omega) hx0 hpre hF hI.g2 (show h < j0 + Lb by omega)]
    obtain ⟨yM, hyM⟩ := o2r_sub hI.g2 p
    have hvp := vr_gexp_pre_t0 hlen hLb hA hg (by omega) hx0 hpre hF hI.g2 (show p < j0 + Lb by omega)
    obtain ⟨yN, hyN⟩ := o2r_sub hG2 p
    rw [hvp] at hyN
    rw [hyN] at hc
    obtain ⟨rfl, rfl, _⟩ := psi.inj hc
    have hle : yN ≤ yM := by
      by_cases hpA : Anc0 M p (j0 + Lb)
      · have hlt := (low_path_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre p
          (anc_g_of_lt hlen hLb hA hg hF hI hn hx0 hx1 hpre hpA h1)).2
        rw [hyN, hyM, psi_lt_psi_z_iff] at hlt
        rcases hlt with h' | ⟨_, h'⟩
        · exact absurd h' (lt_irrefl' _)
        · exact le_of_lt h'
      · rw [low_off_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre p (by omega) hpA, hyM] at hyN
        rw [(psi.inj hyN).2.1]
    exact hlow h p (vr M p) yM yN h1 hp' hyM hyN hle (hM h p (vr M p) yM (by omega) hp' hyM)
  · obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := j0) (n := n) (p := p) hLb h1
      (by rw [hlen'] at hpl; exact hpl)
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · subst hq0
      have hroot := par0_gexp_root_t0 (d1 := 0) hlen hLb hk hA hg
      rw [hroot] at hp
      cases hp
      rw [o2r_root_new_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre hk] at hc
      obtain ⟨rfl, rfl, _⟩ := psi.inj hc
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        simp only [Nat.zero_mul, Nat.add_zero]
        rw [bst_low_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre hg (le_refl _),
          vr_gexp_pre_t0 hlen hLb hA hg (by omega) hx0 hpre hF hI.g2
            (show g < j0 + Lb by have := par_lt M 0 j0 g hg; omega)]
        exact hr (hM g j0 _ _ (by omega) hg (o2r_r_succ hI.g2 hlen hx0 hx1))
      · exact hjoin k hk0 hk (join_notrig_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre hk0 hk)
    · exact hcopy k q h s y hk hq0 hq hp hc

/-- **PreHi of the expansion** (`t = 0`, `r` not a root). -/
theorem preHi_gexp_t0 : PreHi (TRIO.gexp M j0 Lb 0 0 n) := by
  have hRg := hR_g hlen hLb hA hg hF hI hn hx0 hx1 hpre
  intro h p s y hpl hp hc
  apply frames_gexp_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre
    (fun a B s y => B ≠ z → lt B y = true → lt (psi a z z) (psi s y z) = true →
      hiP s y = B ∧ loP s y ≠ z) _ _ _ _ _ h p s y hpl hp hc
  · intro h p s y y' _ _ _ _ hle hP hB h1 h2
    rcases (le_iff _ _).mp hle with hlt | heq
    · obtain ⟨t1, t2⟩ := trig_mono hlt h1 h2
      obtain ⟨hhi, hlo⟩ := hP hB t1 t2
      exact prehi_of_lt hhi hlo h1 hlt
    · subst heq; exact hP hB h1 h2
  · intro hP hB h1 h2
    have hlt : bst M j0 (j0 + Lb) < app (bst M j0 (j0 + Lb)) one := lt_app_of (by simp [one])
    obtain ⟨t1, t2⟩ := trig_mono hlt h1 h2
    obtain ⟨hhi, hlo⟩ := hP hB t1 t2
    exact prehi_of_lt hhi hlo h1 hlt
  · intro k q' h s y hk hq0 hq hp hc hB h1 h2
    exact preHi_copy_t0 hlen hLb hA hRg hF hI.g2 hn hx0 hx1 hI.hi hk hq0 hq hp hc hB h1 h2
  · intro k _ _ hno hB h1 h2
    exact absurd ⟨h1, h2⟩ hno
  · intro h p s y hpl hp hc hB h1 h2
    exact hI.hi h p s y hpl hp hc hB h1 h2

/-- **PreFC of the expansion** (`t = 0`, `r` not a root). -/
theorem preFC_gexp_t0 : PreFC (TRIO.gexp M j0 Lb 0 0 n) := by
  have hRg := hR_g hlen hLb hA hg hF hI hn hx0 hx1 hpre
  intro h p s y hpl hp hc
  apply frames_gexp_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre
    (fun a B s y => B = z → lt z y = true → lt (psi a z z) (psi s y z) = true → a = s →
      hiP s y = z ∧ loP s y ≠ z) _ _ _ _ _ h p s y hpl hp hc
  · intro h p s y y' _ _ _ _ hle hP hB h1 h2 hv
    have hz : z < y := lt_of_lt_of_le h1 hle
    have h2' : lt (psi (vr M h) z z) (psi s y z) = true := by
      rcases (le_iff _ _).mp hle with hlt | heq
      · exact (trig_mono (B := z) hlt h1 h2).2
      · rw [← heq]; exact h2
    obtain ⟨hhi, hlo⟩ := hP hB hz h2' hv
    exact prefc_of_le hhi hlo h1 hle
  · intro hP hB h1 h2 hv
    have hlt : bst M j0 (j0 + Lb) < app (bst M j0 (j0 + Lb)) one := lt_app_of (by simp [one])
    obtain ⟨t1, t2⟩ := trig_mono (B := z) hlt h1 h2
    obtain ⟨hhi, hlo⟩ := hP hB t1 t2 hv
    exact prefc_of_le hhi hlo h1 (le_of_lt hlt)
  · intro k q' h s y hk hq0 hq hp hc hB h1 h2 hv
    exact preFC_copy_t0 hlen hLb hA hRg hF hI.g2 hn hx0 hx1 hI.fc hk hq0 hq hp hc hB h1 h2 hv
  · intro k _ _ hno hB h1 h2 _
    exact absurd ⟨by rw [hB]; exact h1, h2⟩ hno
  · intro h p s y hpl hp hc hB h1 h2 hv
    exact hI.fc h p s y hpl hp hc hB h1 h2 hv

end

/-! ## r が根の場合 -/

section
variable {M : Mat} {j0 Lb n : Nat} (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
  (hA : Anc0 M j0 (j0 + Lb)) (hrn : par M 0 j0 = none)
  (hF : F1 (TRIO.gexp M j0 Lb 0 0 n)) (hI : Inv2 M) (hn : 2 ≤ n)
  (hx0 : par M 0 (j0 + Lb) = some j0) (hx1 : entry M 1 (j0 + Lb) = 0)
  (hpre : ∀ c, c < j0 + Lb → par (TRIO.gexp M j0 Lb 0 0 n) 0 c = par M 0 c)
include hlen hLb hA hrn hF hI hn hx0 hx1 hpre

theorem e0_root : entry M 0 j0 = 0 := by
  have hc := col_zero_of_top hI.z0 hI.e00 (by omega) hrn
  unfold entry; unfold col at hc; rw [hc]; rfl

theorem e0N_root {k : Nat} (hk : k < n) : entry (TRIO.gexp M j0 Lb 0 0 n) 0 (j0 + (k * Lb + 0)) = 0 := by
  rw [entry0_gexp_mir hlen hk hLb]
  simp only [Nat.add_zero, Nat.mul_zero]
  exact e0_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre

theorem hR_root : CopyRootsLow (TRIO.gexp M j0 Lb 0 0 n) j0 Lb n := by
  intro k hk p hp
  have h0 := e0N_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre hk
  have := ((par0_spec _).mp hp).2.1; omega

theorem take_root : (TRIO.gexp M j0 Lb 0 0 n).take j0 = M.take j0 := by
  unfold TRIO.gexp; exact List.take_left' (by rw [List.length_take]; omega)

/-- Before the root `r`, the values are unchanged. -/
theorem low_root {c : Nat} (hc : c < j0) : o2r (TRIO.gexp M j0 Lb 0 0 n) c = o2r M c := by
  have h0N : entry (TRIO.gexp M j0 Lb 0 0 n) 0 j0 = 0 := by
    have := e0N_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre (k := 0) (by omega); simpa using this
  rw [← o2r_take_low h0N c hc, take_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre,
    o2r_take_low (e0_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre) c hc]

/-- Before the root `r`, the children are unchanged. -/
theorem children_low_root {h : Nat} (hh : h < j0) :
    children (TRIO.gexp M j0 Lb 0 0 n) h = children M h := by
  have h0N : entry (TRIO.gexp M j0 Lb 0 0 n) 0 j0 = 0 := by
    have := e0N_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre (k := 0) (by omega); simpa using this
  have h0M := e0_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre
  have hlen' := TRIO.gexp_length (d0 := 0) (d1 := 0) (n := n) hlen
  apply eq_of_sorted_mem _ _ (children_sorted _ _) (children_sorted _ _)
  intro d
  rw [mem_children_iff, mem_children_iff]
  constructor
  · rintro ⟨hdl, hdp⟩
    rcases Nat.lt_or_ge d j0 with h1 | h1
    · rw [hpre d (by omega)] at hdp; exact ⟨by omega, hdp⟩
    · exact absurd (par_ge_of_zero h0N h1 hdp) (by omega)
  · rintro ⟨hdl, hdp⟩
    rcases Nat.lt_or_ge d j0 with h1 | h1
    · rw [← hpre d (by omega)] at hdp; exact ⟨by rw [hlen']; omega, hdp⟩
    · exact absurd (par_ge_of_zero h0M h1 hdp) (by omega)

theorem bst_low_root {h p : Nat} (hp : par M 0 p = some h) (hpj : p < j0) :
    bst (TRIO.gexp M j0 Lb 0 0 n) h p = bst M h p := by
  have hhp := par_lt M 0 p h hp
  unfold bst
  have hvh : vr (TRIO.gexp M j0 Lb 0 0 n) h = vr M h := by
    rw [vr_eq_nT hF, vr_eq_nT hI.g2.f1]
    congr 1
    have h1 := expand_take_prefix
    rw [← entry_take (TRIO.gexp M j0 Lb 0 0 n) 1 (show h < j0 by omega),
      take_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre, entry_take M 1 (show h < j0 by omega)]
  rw [hvh, children_low_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre (by omega)]
  congr 2
  apply List.map_congr_left
  intro d hd
  have hdp : d < p := by rw [List.mem_filter] at hd; simpa using hd.2
  exact low_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre (by omega)


theorem good2_root : Good2 (TRIO.gexp M j0 Lb 0 0 n) := by
  have hRr := hR_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre
  have h0M := e0_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre
  refine ⟨hF, ot_t0 hlen hLb hA hRr hF hI.g2 hn hx0 hx1 (fun c hc => by
      rw [low_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre hc]; exact hI.g2.ot c),
    dec_t0 hlen hLb hA hRr hF hI.g2 hn hx0 hx1 (fun h hh => ?_)⟩
  rw [children_low_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre hh]
  have hv : (children M h).map (o2r (TRIO.gexp M j0 Lb 0 0 n)) = (children M h).map (o2r M) := by
    apply List.map_congr_left; intro d hd
    have hdp := mem_children_iff.mp hd
    have hdj : d < j0 := by
      by_contra hc; exact absurd (par_ge_of_zero h0M (by omega) hdp.2) (by omega)
    exact low_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre hdj
  rw [hv]; exact hI.g2.dec h

/-- Shared case split for the frames (`t = 0`, `r` a root). -/
theorem frames_root (P : T → T → T → T → Prop)
    (hcopy : ∀ k q' h s y, k < n → 0 < q' → q' < Lb →
      par (TRIO.gexp M j0 Lb 0 0 n) 0 (j0 + (k * Lb + q')) = some h →
      o2r (TRIO.gexp M j0 Lb 0 0 n) (j0 + (k * Lb + q')) = psi s y z →
      P (vr (TRIO.gexp M j0 Lb 0 0 n) h) (bst (TRIO.gexp M j0 Lb 0 0 n) h (j0 + (k * Lb + q'))) s y)
    (hM : ∀ h p s y, p < M.length → par M 0 p = some h → o2r M p = psi s y z →
      P (vr M h) (bst M h p) s y) :
    ∀ h p s y, p < (TRIO.gexp M j0 Lb 0 0 n).length → par (TRIO.gexp M j0 Lb 0 0 n) 0 p = some h →
      o2r (TRIO.gexp M j0 Lb 0 0 n) p = psi s y z →
      P (vr (TRIO.gexp M j0 Lb 0 0 n) h) (bst (TRIO.gexp M j0 Lb 0 0 n) h p) s y := by
  have hlen' := TRIO.gexp_length (d0 := 0) (d1 := 0) (n := n) hlen
  intro h p s y hpl hp hc
  rcases Nat.lt_or_ge p j0 with h1 | h1
  · have hp' : par M 0 p = some h := by rw [← hpre p (by omega)]; exact hp
    have hhp := par_lt M 0 p h hp'
    rw [bst_low_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre hp' h1]
    have hvh : vr (TRIO.gexp M j0 Lb 0 0 n) h = vr M h := by
      rw [vr_eq_nT hF, vr_eq_nT hI.g2.f1]
      congr 1
      rw [← entry_take (TRIO.gexp M j0 Lb 0 0 n) 1 (show h < j0 by omega),
        take_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre, entry_take M 1 (show h < j0 by omega)]
    rw [hvh]
    rw [low_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre h1] at hc
    exact hM h p s y (by omega) hp' hc
  · obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := j0) (n := n) (p := p) hLb h1
      (by rw [hlen'] at hpl; exact hpl)
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · subst hq0
      exfalso
      have h0 := e0N_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre hk
      have := ((par0_spec _).mp hp).2.1; omega
    · exact hcopy k q h s y hk hq0 hq hp hc

theorem preHi_root : PreHi (TRIO.gexp M j0 Lb 0 0 n) := by
  have hRr := hR_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre
  intro h p s y hpl hp hc
  apply frames_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre
    (fun a B s y => B ≠ z → lt B y = true → lt (psi a z z) (psi s y z) = true →
      hiP s y = B ∧ loP s y ≠ z) _ _ h p s y hpl hp hc
  · intro k q' h s y hk hq0 hq hp hc hB h1 h2
    exact preHi_copy_t0 hlen hLb hA hRr hF hI.g2 hn hx0 hx1 hI.hi hk hq0 hq hp hc hB h1 h2
  · intro h p s y hpl hp hc hB h1 h2
    exact hI.hi h p s y hpl hp hc hB h1 h2

theorem preFC_root : PreFC (TRIO.gexp M j0 Lb 0 0 n) := by
  have hRr := hR_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre
  intro h p s y hpl hp hc
  apply frames_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre
    (fun a B s y => B = z → lt z y = true → lt (psi a z z) (psi s y z) = true → a = s →
      hiP s y = z ∧ loP s y ≠ z) _ _ h p s y hpl hp hc
  · intro k q' h s y hk hq0 hq hp hc hB h1 h2 hv
    exact preFC_copy_t0 hlen hLb hA hRr hF hI.g2 hn hx0 hx1 hI.fc hk hq0 hq hp hc hB h1 h2 hv
  · intro h p s y hpl hp hc hB h1 h2 hv
    exact hI.fc h p s y hpl hp hc hB h1 h2 hv

end

/-! ## 展開の形での組み立て -/

/-- The trio invariants, the top-left zero and the zero row 2 survive an expansion. -/
theorem basic_expand {M : Mat} (hI : Inv2 M) (hM : 2 ≤ M.length) {n : Nat} (hn : 1 ≤ n) :
    TRIO.z0ok (expand M n) ∧ TRIO.r1ok (expand M n) ∧ entry (expand M n) 0 0 = 0 ∧
      ∀ j, entry (expand M n) 2 j = 0 := by
  refine ⟨by rw [expand_eq_oper M n hM]; exact TRIO.z0ok_oper hI.z0,
    by rw [expand_eq_oper M n hM]; exact TRIO.r1ok_oper hI.r1, ?_, ?_⟩
  · have h1 := expand_take_prefix M hM hn
    rw [← entry_take (expand M n) 0 (show 0 < M.length - 1 by omega), h1,
      entry_take M 0 (show 0 < M.length - 1 by omega)]
    exact hI.e00
  · intro j
    by_cases hcol : col M (M.length - 1) = (0, 0, 0)
    · rw [expand_zero_col (by omega) hcol n]
      by_cases hj : j < M.length - 1
      · rw [entry_take M 2 hj]; exact hI.row2 j
      · unfold entry; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
    · have hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
          TRIO.entry M 2 (M.length - 1) = 0) := by
        rintro ⟨e0, e1, e2⟩; apply hcol; unfold col
        have e0' : (M.getD (M.length - 1) (0, 0, 0)).1 = 0 := e0
        have e1' : (M.getD (M.length - 1) (0, 0, 0)).2.1 = 0 := e1
        have e2' : (M.getD (M.length - 1) (0, 0, 0)).2.2 = 0 := e2
        rcases hc : M.getD (M.length - 1) (0, 0, 0) with ⟨a, b, c⟩
        rw [hc] at e0' e1' e2'; simp at e0' e1' e2'; rw [e0', e1', e2']
      by_cases hj : j < M.length - 1
      · rw [← entry_take (expand M n) 2 hj, expand_take_prefix M hM hn, entry_take M 2 hj]
        exact hI.row2 j
      · have hx0 : 0 < entry M 0 (M.length - 1) := by
          rcases Nat.eq_zero_or_pos (entry M 0 (M.length - 1)) with h | h
          · exfalso; obtain ⟨e1, e2⟩ := hI.z0 (M.length - 1) (by omega) h; exact hz ⟨h, e1, e2⟩
          · exact h
        have hsrow : ∃ r, par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r := by
          unfold TRIO.srow; rw [← entry_eq, ← entry_eq, hI.row2]
          simp only [Nat.lt_irrefl, if_false]
          split_ifs with hb
          · obtain ⟨m, hm, _⟩ := hI.g2.f1 _ hb; exact ⟨m, hm⟩
          · exact par0_some_of (show 0 < M.length - 1 by omega) (by rw [hI.e00]; exact hx0)
        obtain ⟨r, hr⟩ := hsrow
        have hrx := par_lt M _ _ r hr
        rw [expand_eq_gexp M n hM hz hr]
        unfold entry
        rcases Nat.lt_or_ge j (r + n * (M.length - 1 - r)) with h2 | h2
        · obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (n := n) (p := j)
            (show 0 < M.length - 1 - r by omega) (by omega) h2
          rw [TRIO.gexp_getD_mir (by omega) hk hq]
          simp only [if_neg (show (2 : Nat) ≠ 0 by omega), if_neg (show (2 : Nat) ≠ 1 by omega)]
          exact hI.row2 (r + q)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
            rw [TRIO.gexp_length (by omega)]; omega)]; rfl

/-- **(I2), `t = 0`, `r` not a root.** -/
theorem inv2_expand_t0_g {M : Mat} {r g n : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht0 : TRIO.srow M (M.length - 1) = 0) (hI : Inv2 M) (hg : par M 0 r = some g) (hn : 2 ≤ n) :
    Inv2 (expand M n) := by
  obtain ⟨hz0', hr1', he00, hrow⟩ := basic_expand hI hM (show 1 ≤ n by omega)
  have hx : M.length - 1 + 1 = M.length := by omega
  have hr0 : par M 0 (M.length - 1) = some r := by have h := hr; rw [ht0] at h; exact h
  have hrx := par_lt M 0 _ r hr0
  have hxr : col M (M.length - 1) ≠ (0, 0, 0) := by
    intro h; apply hz; unfold col at h
    rw [← entry_eq, ← entry_eq, ← entry_eq]; unfold entry; rw [h]; simp
  have hroots := roots_expand_t0 hM hz hr ht0 hg (show 1 ≤ n by omega) hxr
  have hgexp := expand_eq_gexp_t0 M n hM hz hr ht0
  have hF : F1 (TRIO.gexp M r (M.length - 1 - r) 0 0 n) := by
    rw [← hgexp]; exact F1_expand hI.r1 hI.z0 hM n
  have hpre0 : ∀ c, c < M.length - 1 →
      par (TRIO.gexp M r (M.length - 1 - r) 0 0 n) 0 c = par M 0 c := by
    intro c hc; rw [← hgexp]; exact par0_expand_prefix M hM (by omega) hc
  obtain ⟨Lb, hLbd⟩ : ∃ Lb, Lb = M.length - 1 - r := ⟨_, rfl⟩
  rw [← hLbd] at hF hgexp hpre0
  have hlen : r + Lb + 1 = M.length := by omega
  have hLb : 0 < Lb := by omega
  have hxe : r + Lb = M.length - 1 := by omega
  have hA : Anc0 M r (r + Lb) := by rw [hxe]; exact Anc0.step hr0 (Anc0.refl r)
  have hx0 : par M 0 (r + Lb) = some r := by rw [hxe]; exact hr0
  have hx1 : entry M 1 (r + Lb) = 0 := by
    rw [hxe]
    unfold TRIO.srow at ht0
    split_ifs at ht0 with h1 h2
    change ¬ 0 < (M.getD (M.length - 1) (0, 0, 0)).2.1 at h2
    show (M.getD (M.length - 1) (0, 0, 0)).2.1 = 0
    omega
  have hpre : ∀ c, c < r + Lb → par (TRIO.gexp M r Lb 0 0 n) 0 c = par M 0 c := by
    intro c hc; exact hpre0 c (by omega)
  -- the matrix value pieces in `gexp` form
  have hG2 := good2_gexp_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre
  have hH2 := preHi_gexp_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre
  have hFC2 := preFC_gexp_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre
  refine ⟨by rw [hgexp]; exact hG2, by rw [hgexp]; exact hH2, by rw [hgexp]; exact hFC2, ?_,
    hz0', hr1', he00, hrow⟩
  -- RootsDec: only the top root drops
  unfold RootsDec
  rw [hroots]
  obtain ⟨ρ, hρ, hρn⟩ := top_anc M (M.length - 1)
  have hρ0 := col_zero_of_top hI.z0 hI.e00 (by have := hρ.le; omega) hρn
  have hsplit := roots_split hx hρ hρ0
  have hρr : ρ < r := by
    rcases anc0_total hρ (Anc0.step hr0 (Anc0.refl r)) with h' | h'
    · rcases Nat.eq_or_lt_of_le h'.le with h2 | h2
      · rw [h2, hg] at hρn; cases hρn
      · exact h2
    · cases h' with
      | refl => rw [hg] at hρn; cases hρn
      | step hp _ => rw [hp] at hρn; cases hρn
  set R := (roots M).filter (fun c => decide (c < ρ)) with hRd
  have hRv : R.map (o2r (expand M n)) = R.map (o2r M) := by
    apply List.map_congr_left
    intro c hc
    rw [hRd, List.mem_filter] at hc
    have hcρ : c < ρ := by simpa using hc.2
    rw [hgexp]
    apply low_off_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre c (by omega)
    intro hcA
    rw [hxe] at hcA
    rcases anc0_total hcA hρ with h' | h'
    · cases h' with
      | refl => omega
      | step hp _ => rw [hp] at hρn; cases hρn
    · have := h'.le; omega
  have hρlt : o2r (expand M n) ρ < o2r M ρ := by
    rw [hgexp]
    refine (low_path_t0 hlen hLb hA hg hF hI hn hx0 hx1 hpre ρ ?_).2
    exact anc_g_of_lt hlen hLb hA hg hF hI hn hx0 hx1 hpre (by rw [hxe]; exact hρ) hρr
  have hRD := hI.rd
  unfold RootsDec at hRD
  rw [hsplit, List.map_append] at hRD ⊢
  rw [hRv]
  have hRD' := List.pairwise_append.mp hRD
  rw [List.pairwise_append]
  refine ⟨hRD'.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb; subst hb
  exact le_trans (le_of_lt hρlt) (hRD'.2.2 a ha _ (by simp))

/-- **(I2), `t = 0`, `r` a root.** -/
theorem inv2_expand_t0_root {M : Mat} {r n : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht0 : TRIO.srow M (M.length - 1) = 0) (hI : Inv2 M) (hrn : par M 0 r = none) (hn : 2 ≤ n) :
    Inv2 (expand M n) := by
  obtain ⟨hz0', hr1', he00, hrow⟩ := basic_expand hI hM (show 1 ≤ n by omega)
  have hx : M.length - 1 + 1 = M.length := by omega
  have hr0 : par M 0 (M.length - 1) = some r := by have h := hr; rw [ht0] at h; exact h
  have hrx := par_lt M 0 _ r hr0
  have hgexp := expand_eq_gexp_t0 M n hM hz hr ht0
  have hF : F1 (TRIO.gexp M r (M.length - 1 - r) 0 0 n) := by
    rw [← hgexp]; exact F1_expand hI.r1 hI.z0 hM n
  have hpre0 : ∀ c, c < M.length - 1 →
      par (TRIO.gexp M r (M.length - 1 - r) 0 0 n) 0 c = par M 0 c := by
    intro c hc; rw [← hgexp]; exact par0_expand_prefix M hM (by omega) hc
  have hroots0 := roots_split hx (Anc0.step hr0 (Anc0.refl r))
    (col_zero_of_top hI.z0 hI.e00 (by omega) hrn)
  have hr0c := col_zero_of_top hI.z0 hI.e00 (by omega) hrn
  obtain ⟨Lb, hLbd⟩ : ∃ Lb, Lb = M.length - 1 - r := ⟨_, rfl⟩
  rw [← hLbd] at hF hgexp hpre0
  have hlen : r + Lb + 1 = M.length := by omega
  have hLb : 0 < Lb := by omega
  have hxe : r + Lb = M.length - 1 := by omega
  have hA : Anc0 M r (r + Lb) := by rw [hxe]; exact Anc0.step hr0 (Anc0.refl r)
  have hx0 : par M 0 (r + Lb) = some r := by rw [hxe]; exact hr0
  have hx1 : entry M 1 (r + Lb) = 0 := by
    rw [hxe]
    unfold TRIO.srow at ht0
    split_ifs at ht0 with h1 h2
    change ¬ 0 < (M.getD (M.length - 1) (0, 0, 0)).2.1 at h2
    show (M.getD (M.length - 1) (0, 0, 0)).2.1 = 0
    omega
  have hpre : ∀ c, c < r + Lb → par (TRIO.gexp M r Lb 0 0 n) 0 c = par M 0 c := by
    intro c hc; exact hpre0 c (by omega)
  have hG2 := good2_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre
  have hH2 := preHi_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre
  have hFC2 := preFC_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre
  refine ⟨by rw [hgexp]; exact hG2, by rw [hgexp]; exact hH2, by rw [hgexp]; exact hFC2, ?_,
    hz0', hr1', he00, hrow⟩
  -- the roots: those before `r`, then `r` and its copies
  unfold RootsDec
  rw [hgexp]
  set N := TRIO.gexp M r Lb 0 0 n with hN
  have hlenN : N.length = r + n * Lb := TRIO.gexp_length hlen
  have he0 : entry M 0 r = 0 := by unfold entry; unfold col at hr0c; rw [hr0c]; rfl
  have he1 : entry M 1 r = 0 := by unfold entry; unfold col at hr0c; rw [hr0c]; rfl
  have he2 : entry M 2 r = 0 := by unfold entry; unfold col at hr0c; rw [hr0c]; rfl
  set R := (roots M).filter (fun c => decide (c < r)) with hRd
  have hroots : roots N = R ++ (List.range n).map (fun k => r + k * Lb) := by
    apply eq_of_sorted_mem _ _ (roots_sorted N)
    · rw [List.pairwise_append]
      refine ⟨List.Pairwise.filter _ (roots_sorted M), ?_, ?_⟩
      · apply List.Pairwise.map _ _ List.pairwise_lt_range
        intro a c hac; have := Nat.mul_lt_mul_of_pos_right hac hLb; omega
      · intro a ha c hc
        rw [hRd, List.mem_filter] at ha
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
        simp at ha; omega
    intro c
    rw [mem_roots, List.mem_append, hRd, List.mem_filter, mem_roots, List.mem_map]
    constructor
    · rintro ⟨hcl, hc0⟩
      rcases Nat.lt_or_ge c r with h1 | h1
      · left
        refine ⟨⟨by omega, ?_⟩, by simpa using h1⟩
        unfold col at hc0 ⊢; rw [hN, TRIO.gexp_getD_low hlen h1] at hc0; exact hc0
      · right
        rw [hlenN] at hcl
        obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (n := n) (p := c) hLb h1 hcl
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · subst h0; exact ⟨k, List.mem_range.mpr hk, by omega⟩
        · exfalso
          unfold col at hc0; rw [hN, TRIO.gexp_getD_mir hlen hk hq] at hc0
          have h2 := congrArg Prod.fst hc0
          have h3 := anc0_interval hA (r + q) (by omega) (by omega)
          simp only [Nat.mul_zero, Nat.add_zero] at h2
          rw [← entry_eq] at h2
          omega
    · rintro (⟨⟨hcl, hc0⟩, hcr⟩ | ⟨k, hk, rfl⟩)
      · simp at hcr
        refine ⟨by omega, ?_⟩
        unfold col at hc0 ⊢; rw [hN, TRIO.gexp_getD_low hlen hcr]; exact hc0
      · have hk' := List.mem_range.mp hk
        refine ⟨?_, ?_⟩
        · rw [hlenN]; have := Nat.mul_lt_mul_of_pos_right hk' hLb; omega
        · unfold col
          rw [hN, show r + k * Lb = r + (k * Lb + 0) by omega, TRIO.gexp_getD_mir hlen hk' hLb]
          rw [← entry_eq, ← entry_eq, ← entry_eq]
          simp [he0, he1, he2]
  rw [hroots, List.map_append]
  have hRv : R.map (o2r N) = R.map (o2r M) := by
    apply List.map_congr_left
    intro c hc
    rw [hRd, List.mem_filter] at hc
    exact low_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre (by simpa using hc.2)
  have hRr := hR_root hlen hLb hA hrn hF hI hn hx0 hx1 hpre
  have hCv : ((List.range n).map (fun k => r + k * Lb)).map (o2r N) =
      List.replicate n (psi (vr M r) (bst M r (r + Lb)) z) := by
    rw [List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate, Function.comp]
    have := o2r_copy_t0 hlen hLb hA hRr hF hI.g2 hn hx0 hx1 (k := i) (q := 0) (by simpa using h1) hLb
    simpa using this
  rw [hRv, hCv]
  have hRD := hI.rd
  unfold RootsDec at hRD
  rw [hroots0, List.map_append] at hRD
  have hRD' := List.pairwise_append.mp hRD
  have hrlt : psi (vr M r) (bst M r (r + Lb)) z < o2r M r := by
    rw [o2r_r_succ hI.g2 hlen hx0 hx1, psi_lt_psi_z_iff]
    exact Or.inr ⟨rfl, lt_app_of (by simp [one])⟩
  rw [List.pairwise_append]
  refine ⟨hRD'.1, List.pairwise_replicate.mpr (Or.inr (le_refl _)), fun a ha c hc => ?_⟩
  rw [List.eq_of_mem_replicate hc]
  exact le_trans (le_of_lt hrlt) (hRD'.2.2 a ha _ (by simp))

end Ytosk
