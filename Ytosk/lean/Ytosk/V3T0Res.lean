/-
**3 行・t = 0: Res3A.t0 の値の 2 項目（hVr と VSmallNewN）を構造から出す。**

- 次の列型の上げ upg M (r − 1) = some r があると、g = P_0(r) は r より前に数える子を持つ（`cnt_before_next_upg`）。
  r − 1 を含む g の子 c は、bump なら SibDec に反し（col r > bump g）、isUpg ∧ topped なら UAT から次の列型の
  上げの的なので帰納法で前に進む。
- M.take x で g が r を数えないのは、上の上げがあるときだけ（`upg_prev_of_take`）。
- VSmallNewN: N で v(cs) が変わる cs（cs < r）は DepX、したがって TopC で、M でも数える子がない。o(cs) = ψ_v(0)
  なので書き換えの条件 B < 0 は成り立たない（`t0_vsmallNewN`）。
- hVr: g が M.take x でも r を数えるなら CL が一致し、Res3A.drop の VSmallNew がそのまま使える。数えないなら
  g に前の数える子があって B ≠ 0、r の数える子は x だけで o(r) の引数は 1 なので、書き換えの条件は成り立たない
  （`t0_vr`）。
-/
import Ytosk.V3Top

namespace Ytosk

open T

/-- An ancestor that is not the column itself is an ancestor of its parent. -/
theorem anc0_of_par_ne {M : Mat} {a b c : Nat} (hA : Anc0 M a c) (hne : a ≠ c)
    (hp : par M 0 c = some b) : Anc0 M a b := by
  cases hA with
  | refl => exact absurd rfl hne
  | step hp' hA' => rw [hp] at hp'; cases hp'; exact hA'

/-- **A next-type upgrade target has an earlier counted sibling.** -/
theorem cnt_before_next_upg {M : Mat} (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hUAT : UAT M) :
    ∀ r, 0 < r → upg M (r - 1) = some r → ∀ g, par M 0 r = some g →
      ∃ c, c ∈ children M g ∧ c < r ∧ Counted M g c := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  intro hr0 hu g hg
  have hrlen : r < M.length := by have := upg_lt_len hu; omega
  obtain ⟨m, hm1, hm2, hcol, _⟩ := upg_spec hu
  have hcol' := congrArg (fun t => t.1) hcol
  have hcol1 := congrArg (fun t => t.2.1) hcol
  simp only [col_eq_entries] at hcol' hcol1
  -- `m = g`
  have hmg : m = g := by
    have hAmr : Anc0 M m r := anc0_of_par M 1 m r hm2
    have hmr : m ≠ r := by have := par_lt M 1 r m hm2; omega
    have hAmg := anc0_of_par_ne hAmr hmr hg
    have he0 := hR0 r g hg
    by_contra hne
    have := anc0_e0_lt hAmg hne
    omega
  subst hmg
  have he1 : entry M 1 m < entry M 1 r := par1_entry_lt hm2
  have hmr1 : m < r - 1 := par_lt M 1 (r - 1) m hm1
  have hA : Anc0 M m (r - 1) := anc0_of_par M 1 m (r - 1) hm1
  obtain ⟨c, hcp, hcA⟩ := anc0_child hA (by omega)
  have hcle := hcA.le
  have hcM : c ∈ children M m := mem_children_iff.mpr ⟨by omega, hcp⟩
  by_cases hcnt : Counted M m c
  · exact ⟨c, hcM, by omega, hcnt⟩
  unfold Counted at hcnt
  rw [not_and_or, not_not, not_not] at hcnt
  rcases hcnt with hb | ⟨hU, hT⟩
  · -- a bump sibling before `r` contradicts `SibDec`
    exfalso
    have hrM : r ∈ children M m := mem_children_iff.mpr ⟨hrlen, hg⟩
    obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hcM
    have hrl : r ∈ l₂ := by
      have hs := children_sorted M m
      rw [hsplit] at hs hrM
      rcases List.mem_append.mp hrM with h' | h'
      · exfalso; have := (List.pairwise_append.mp hs).2.2 r h' c (by simp); omega
      · simp only [List.mem_cons] at h'
        rcases h' with h' | h'
        · omega
        · exact h'
    have hle := sib_le hSD l₂ l₁ c hsplit r hrl
    rw [hb] at hle
    unfold colLe bump at hle
    simp only [col_eq_entries] at hle
    have := hR0 r m hg
    omega
  · -- an upgrade target that is topped is a next-type target: go to the earlier one
    unfold isUpg at hU
    rw [List.any_eq_true] at hU
    obtain ⟨j, _, hj⟩ := hU
    have hj' : upg M j = some c := by simpa using hj
    by_cases hcj : c = j + 1
    · have hc0 : 0 < c := by omega
      rw [show j = c - 1 by omega] at hj'
      obtain ⟨c', hc'M, hc'c, hc'⟩ := ih c (by omega) hc0 hj' m hcp
      exact ⟨c', hc'M, by omega, hc'⟩
    · rw [hUAT j c hj' hcj] at hT; cases hT

section
variable {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r)
include hlen hL hp

/-- A child other than `r` keeps its children in `M.take x`. -/
theorem children_take_ne_r {c : Nat} (hcr : c ≠ r) :
    children (M.take (r + L)) c = children M c := by
  rw [children_take, List.filter_eq_self]
  intro d hd
  simp only [decide_eq_true_eq]
  have hdl := (mem_children hd).2
  by_contra h
  have hdx : d = r + L := by omega
  subst hdx
  have := (mem_children_iff.mp hd).2; rw [hp] at this
  exact hcr (Option.some.inj this).symm

/-- **Counting a child other than `r` (before `x`) passes from `M` to `M.take x`.** -/
theorem counted_take_of {i c : Nat} (hcx : c < r + L) (hcr : c ≠ r) (hM : Counted M i c)
    (hix : i < r + L) : Counted (M.take (r + L)) i c := by
  refine ⟨by rw [col_take M hcx, bump_take M hix]; exact hM.1, ?_⟩
  rintro ⟨hU, hT⟩
  apply hM.2
  refine ⟨?_, ?_⟩
  · unfold isUpg at hU ⊢
    rw [List.any_eq_true] at hU ⊢
    obtain ⟨j, hj, hu⟩ := hU
    have hjl : j < r + L := by
      have := List.mem_range.mp hj; rw [List.length_take] at this; omega
    have hu' : upg (M.take (r + L)) j = some c := by simpa using hu
    by_cases hj1 : j + 1 < r + L
    · rw [upg_take M hj1] at hu'
      exact ⟨j, List.mem_range.mpr (by omega), by simp [hu']⟩
    · have : j = r + L - 1 := by omega
      subst this
      rw [upg_take_last M (by omega) (by omega)] at hu'; cases hu'
  · unfold topped at hT ⊢
    rw [children_take_ne_r hlen hL hp hcr] at hT
    cases hl : (children M c).getLast? with
    | none => rfl
    | some d =>
      rw [hl] at hT
      have hd := List.mem_of_getLast? hl
      have hdx : d < r + L := by
        have hdl := (mem_children hd).2
        by_contra h
        have : d = r + L := by omega
        subst this
        have := (mem_children_iff.mp hd).2; rw [hp] at this
        exact hcr (Option.some.inj this).symm
      simp only at hT ⊢
      rw [col_take M hdx, bump_take M hcx] at hT
      exact hT

omit hL in
/-- **`r` is an upgrade target that is topped in `M.take x` only through a next-type upgrade.** -/
theorem upg_prev_of_take (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAB : UAB M)
    (hU : isUpg (M.take (r + L)) r = true) (hT : topped (M.take (r + L)) r = true) :
    0 < r ∧ upg M (r - 1) = some r := by
  unfold isUpg at hU
  rw [List.any_eq_true] at hU
  obtain ⟨j, hj, hu⟩ := hU
  have hjl : j < r + L := by
      have := List.mem_range.mp hj; rw [List.length_take] at this; omega
  have hu' : upg (M.take (r + L)) j = some r := by simpa using hu
  have hj1 : j + 1 < r + L := by
    by_contra h
    have : j = r + L - 1 := by omega
    subst this
    rw [upg_take_last M (by omega) (by omega)] at hu'; cases hu'
  rw [upg_take M hj1] at hu'
  obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu'
  rcases hcase with h | ⟨_, hrj⟩
  · refine ⟨by omega, ?_⟩
    rw [show r - 1 = j by omega]; exact hu'
  · exfalso
    have hq := upg_r_not_topped hlen hp hR0 hZ2 hSD hZ1 hUAB (q := j - r) (by omega) (by omega)
      (by rw [show r + (j - r) = j by omega]; exact hu')
    rw [hq] at hT; cases hT

/-- **`g` counts `r` in `M.take x`, or it has no counted child at all there.** If `g` does not count `r`
in `M.take x` while it does in `M`, an earlier child is counted in both. -/
theorem counted_take_r_or (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M)
    (hUAB : UAB M) {g : Nat} (hg : par M 0 r = some g) (hcnt : Counted M g r)
    (hn : ¬ Counted (M.take (r + L)) g r) :
    0 < r ∧ upg M (r - 1) = some r ∧
      ∃ c, c ∈ children M g ∧ c < r ∧ Counted M g c ∧ Counted (M.take (r + L)) g c := by
  have hgr := par_lt M 0 r g hg
  have hn' : isUpg (M.take (r + L)) r = true ∧ topped (M.take (r + L)) r = true := by
    by_contra h
    exact hn ⟨by rw [col_take M (by omega), bump_take M (by omega)]; exact hcnt.1, h⟩
  obtain ⟨hr0, hu⟩ := upg_prev_of_take hlen hp hR0 hZ2 hSD hZ1 hUAB hn'.1 hn'.2
  obtain ⟨c, hcM, hcr, hc⟩ := cnt_before_next_upg hR0 hZ2 hSD hUAT r hr0 hu g hg
  exact ⟨hr0, hu, c, hcM, hcr, hc, counted_take_of hlen hL hp (by omega) (by omega) hc (by omega)⟩

end

/-! ## 値の 2 項目 -/

section
variable {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hR12 : R12 M)
include hlen hL hp he1 hR0 hZ2 hSD hZ1 hUAT hUAB hR12

/-- `x` has no children. -/
theorem children_x_nil : children M (r + L) = [] := by
  rw [children, List.filter_eq_nil_iff]
  intro c hc h
  have hcl := List.mem_range.mp hc
  have := par_lt M 0 c (r + L) (by simpa using h)
  omega

/-- **`o(x) = 1`** (`x` has row 1 equal to `0` and no children). -/
theorem o_x_one0 {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) : ρ.o (r + L) = one := by
  have hxM : r + L < M.length := by omega
  have hv : ρ.v (r + L) = z := by
    rw [(hC (r + L) hxM).2]; unfold vRhs; rw [if_pos he1]
  rw [o_spArg hC hG hxM, cvals_eq_map hC hG, hv]
  unfold CL
  rw [children_x_nil hlen hL hp he1 hR0 hZ2 hSD hZ1 hUAT hUAB hR12]
  rfl

/-- If `v(r)` changes in `M.take x`, the only counted child of `r` in `M` is `x`. -/
theorem cl_r_of_chg (hchg : ChgX M (r + L) false r) : CL M r = [r + L] := by
  have hx : r + L + 1 = M.length := hlen
  have he2 := hR12 _ he1
  have hTop := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hchg).1 rfl (by omega)
  have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
  have hsplit := split_last_max _ _ (children_sorted M r) hxr
    (fun d hd => by have := (mem_children hd).2; omega)
  unfold CL
  rw [hsplit, List.filter_append]
  have hxc : Counted M r (r + L) := by
    refine ⟨fun h => ?_, fun h => by rw [isUpg_x0 hlen hL hp he2] at h; exact absurd h.1 (by simp)⟩
    have := congrArg (fun t => t.2.2) h
    simp [col_eq_entries, bump] at this; omega
  rw [List.filter_eq_nil_iff.mpr]
  · simp [hxc]
  · intro d hd hcd
    rw [List.mem_filter] at hd
    have hdx : d < r + L := by simpa using hd.2
    have hdr : d ≠ r := by have := (mem_children hd.1).1; omega
    have hdT : d ∈ children (M.take (r + L)) r := by
      rw [children_take, List.mem_filter]; exact ⟨hd.1, by simpa using hdx⟩
    exact hTop.2.1 d hdT (counted_take_of hlen hL hp hdx hdr (of_decide_eq_true hcd) (by omega))

/-- **`hVr`**: a changed `v(r)` in `M.take x`, in a rewriting frame of `g`, is small. -/
theorem t0_vr {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hR : Rk M rk) (hI : ValInv M ρ)
    (hD : DropRes M (r + L) ρ (drop1 M (r + L) rk)) :
    ∀ s' y', (drop1 M (r + L) rk).o r = psi s' y' z → s' ≠ ρ.v r → ∀ g Lc,
      par M 0 r = some g → CL M g = Lc ++ [r] → ∀ s y, ρ.o r = psi s y z →
      lt (spArg (ρ.v g) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v g) z z) (psi s y z) = true →
      VSmallV s' := by
  have hx : r + L + 1 = M.length := hlen
  have hcntT := counted_take_last (M := M) (by omega) hR0 hZ2 hSD hZ1 hUAT
  rw [show M.length - 1 = r + L by omega] at hcntT
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) hR hcntT
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hG1 : Good3 (M.take (r + L)) (drop1 M (r + L) rk) :=
    good3_drop1 hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hR hI hD
  intro s' y' hs hne g Lc hg hcl s y hos htr
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  have hs'v : s' = (drop1 M (r + L) rk).v r := by
    obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
    rw [hs] at hy0
    simp only [psi.injEq] at hy0
    rw [hy0.1, sf_ot (hG1.ot_v r hrT)]
  have hne' : (drop1 M (r + L) rk).v r ≠ ρ.v r := hs'v ▸ hne
  have hchg : ChgX M (r + L) false r := by
    by_contra h; exact hne' ((chg_off hx hC hI.g hC1 hRk1 r (by omega)).2 h)
  have hgr := par_lt M 0 r g hg
  have hgM : g < M.length := by omega
  have hrcl : r ∈ CL M g := by rw [hcl]; simp
  have hcnt : Counted M g r := of_decide_eq_true (List.mem_filter.mp hrcl).2
  have hchM := children_g_last hlen hL hp hg
  by_cases hct : Counted (M.take (r + L)) g r
  · -- the frame of `g` is the same in `M.take x`: `VSmallNew`
    have hclT : CL (M.take (r + L)) g = Lc ++ [r] := by
      have hF : ((children M g).filter (fun d => decide (d < r))).filter
          (fun d => decide (Counted (M.take (r + L)) g d)) =
          ((children M g).filter (fun d => decide (d < r))).filter (fun d => decide (Counted M g d)) := by
        apply List.filter_congr
        intro d hd
        rw [List.mem_filter] at hd
        have hdr : d < r := by simpa using hd.2
        have hdT : d ∈ children (M.take (r + L)) g := by
          rw [children_take, List.mem_filter]; exact ⟨hd.1, by simp; omega⟩
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        exact ⟨fun h => hcntT g d (by omega) hdT h,
          fun h => counted_take_of hlen hL hp (by omega) (by omega) h (by omega)⟩
      have hLc : Lc = ((children M g).filter (fun d => decide (d < r))).filter
          (fun d => decide (Counted M g d)) := by
        have h := hcl
        unfold CL at h
        rw [hchM, List.filter_append] at h
        simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hcnt] at h
        exact (List.append_cancel_right h).symm
      unfold CL
      rw [children_take_ne_r hlen hL hp (by omega), hchM, List.filter_append, hF, ← hLc]
      simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hct]
    rw [hs'v]
    exact (hD.vst g (by omega) Lc r hclT hne').2 s y hos htr
  · -- `g` loses `r` in `M.take x`: an earlier child is counted, and `o(r) = ψ_v(1)`
    exfalso
    obtain ⟨_, _, c, hcM, hcr, hcMc, _⟩ :=
      counted_take_r_or hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB hg hcnt hct
    have hcLc : c ∈ Lc := by
      have h : c ∈ CL M g := List.mem_filter.mpr ⟨hcM, decide_eq_true hcMc⟩
      rw [hcl] at h
      rcases List.mem_append.mp h with h | h
      · exact h
      · simp at h; omega
    have hB : spArg (ρ.v g) z (sumN (Lc.map ρ.o)) ≠ z := by
      apply spArg_ne_z; right
      have hv := cl_vals hC hI.g hgM
      rw [hcl, List.map_append] at hv
      apply sumN_ne_z_of_single (fun t ht => hv.1 t (List.mem_append_left _ ht))
        (List.pairwise_append.mp hv.2).1
      intro h; rw [List.map_eq_nil_iff] at h; rw [h] at hcLc; simp at hcLc
    have hrM : r < M.length := by omega
    have hy : y = one := by
      have ho := o_spArg hC hI.g hrM
      rw [cvals_eq_map hC hI.g, cl_r_of_chg hlen hL hp he1 hR0 hZ2 hSD hZ1 hUAT hUAB hR12
        hchg] at ho
      simp only [List.map_cons, List.map_nil] at ho
      rw [sumN_singleton (single_o hC hI.g (by omega)),
        o_x_one0 hlen hL hp he1 hR0 hZ2 hSD hZ1 hUAT hUAB hR12 hC hI.g] at ho
      rw [hos] at ho
      simp only [psi.injEq] at ho
      rw [ho.2.1, one, spArg_cons, step_leaf]
      rfl
    rw [hy] at htr
    apply hB
    have h1 := htr.1
    generalize spArg (ρ.v g) z (sumN (Lc.map ρ.o)) = B at h1 ⊢
    cases B with
    | z => rfl
    | psi a b c =>
      exfalso
      simp only [one, lt] at h1
      split_ifs at h1 <;> simp [lt] at h1

/-- **`VSmallNewN`**: in `N = M[n]` a changed `v` of a last counted child before `r` never comes with
the rewriting condition (that child has no counted child, so its argument is `0`). -/
theorem t0_vsmallNewN {ρ : Valn} {rk : Bool → Nat → Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hR : Rk M rk) {n : Nat} (hn2 : 2 ≤ n) {σ : Valn} (hCN : Cons (TRIO.gexp M r L 0 0 n) σ) :
    VSmallNewN M r ρ σ := by
  have hx : r + L + 1 = M.length := hlen
  have hn : 1 ≤ n := by omega
  have he2 := hR12 _ he1
  have hcntT := counted_take_last (M := M) (by omega) hR0 hZ2 hSD hZ1 hUAT
  rw [show M.length - 1 = r + L by omega] at hcntT
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) hR hcntT
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hoff := chg_off hx hC hG hC1 hRk1
  have hRN := rk_N0 hlen hL hp hn hR0 hZ2 he2 hn2 hR
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
  have hvD := t0_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB) hC hG hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  intro i hi Lc cs hcl hne s y hos htr
  have hcsM : cs ∈ children M i := cl_mem_children (by rw [hcl]; simp)
  have hcsr : cs ≤ r := by
    by_cases hig : par M 0 r = some i
    · exact children_g_le hlen hL hp hig hcsM
    · exact le_of_lt (children_lt_r hlen hL hp hi hig hcsM)
  rcases Nat.lt_or_ge cs r with hcs | hcs
  · have hDep : DepX M (r + L) false cs := by
      by_contra h
      apply hne
      rw [(hvD cs (by rw [hlN]; omega)).2 (fun h' => h h'.2), tau_v_lt hcs]
    have hTop := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hDep)).1 rfl (by omega)
    have hcl0 : CL M cs = [] := by
      unfold CL
      rw [List.filter_eq_nil_iff]
      intro d hd hcd
      have hdc := of_decide_eq_true hcd
      have hdl := (mem_children hd).2
      have hdx : d < r + L := by
        by_contra h
        have : d = r + L := by omega
        subst this
        have := (mem_children_iff.mp hd).2; rw [hp] at this
        have := Option.some.inj this; omega
      have hdT : d ∈ children (M.take (r + L)) cs := by
        rw [children_take, List.mem_filter]; exact ⟨hd, by simpa using hdx⟩
      by_cases hdr : d = r
      · subst hdr
        have hg : par M 0 d = some cs := (mem_children_iff.mp hd).2
        by_cases hct : Counted (M.take (d + L)) cs d
        · exact hTop.2.1 d hdT hct
        · obtain ⟨_, _, c, hcM, hcr, _, hcT⟩ :=
            counted_take_r_or hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB hg hdc hct
          have hcT' : c ∈ children (M.take (d + L)) cs := by
            rw [children_take, List.mem_filter]; exact ⟨hcM, by simp; omega⟩
          exact hTop.2.1 c hcT' hcT
      · exact hTop.2.1 d hdT (counted_take_of hlen hL hp hdx hdr hdc (by omega))
    have ho := o_spArg hC hG (show cs < M.length by omega)
    rw [cvals_eq_map hC hG, hcl0, hos] at ho
    simp only [psi.injEq] at ho
    have hyz : y = z := by rw [ho.2.1]; rfl
    rw [hyz] at htr
    exact absurd htr.1 (by simp [lt])
  · have hcsr' : cs = r := by omega
    subst hcsr'
    exfalso
    apply hne
    rw [(hvD cs (by rw [hlN]; omega)).2 (fun h' => by omega), tau_v_x hn2 (by omega)]

end

end Ytosk
