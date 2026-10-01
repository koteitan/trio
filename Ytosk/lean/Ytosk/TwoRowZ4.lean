/-
**2 行・t = 0・r が根: 行列全体の値（根の和 `ev2r`）が下がる。**

写しの根 r + k·Lb（k < n）はどれも値 ψ_0(b)、元の r は ψ_0(b + 1)（b は x の前の兄弟の状態）。
根の和は A + ψ_0(b)·n = A + ψ_0(b + 1)[n] < A + ψ_0(b + 1)。r より前の根は先頭 r 列だけで値が決まる。
-/
import Ytosk.TwoRowZ3

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- A column with row 0 equal to `0` cuts the forest: later columns hang at or after it. -/
theorem par_ge_of_zero {M : Mat} {k c p : Nat} (hk : entry M 0 k = 0) (hkc : k ≤ c)
    (hp : par M 0 c = some p) : k ≤ p := by
  obtain ⟨hpc, hlt, hbet⟩ := (par0_spec M).mp hp
  by_contra h
  rcases Nat.eq_or_lt_of_le hkc with h1 | h1
  · subst h1; omega
  · have := hbet k (by omega) h1; omega

/-- **Before a zero column, the values are those of the prefix.** -/
theorem o2r_take_low {M : Mat} {k : Nat} (hk : entry M 0 k = 0) :
    ∀ j, j < k → o2r (M.take k) j = o2r M j := by
  have key : ∀ m j, k - j ≤ m → j < k → o2r (M.take k) j = o2r M j := by
    intro m
    induction m with
    | zero => intro j h1 h2; omega
    | succ m ih =>
      intro j hm hj
      apply o2r_congr (vr_take M j hj)
      have hf : (children M j).filter (fun c => decide (c < k)) = children M j := by
        apply List.filter_eq_self.mpr
        intro c hc
        obtain ⟨_, hcp⟩ := mem_children_iff.mp hc
        have := par_lt M 0 c j hcp
        by_contra hck
        have := par_ge_of_zero hk (show k ≤ c by simp at hck; omega) hcp
        omega
      rw [children_take, hf]
      apply List.map_congr_left
      intro c hc
      obtain ⟨_, hcp⟩ := mem_children_iff.mp hc
      have := par_lt M 0 c j hcp
      have hck : c < k := by
        by_contra hck
        have := par_ge_of_zero hk (show k ≤ c by omega) hcp
        omega
      exact ih c (by omega) hck
  exact fun j => key _ j (Nat.le_refl _)

theorem cof_succ_arg (v b : T) : cof (psi v (app b one) z) = .omega := by
  have hne : app b one ≠ z := fun h => by simp [one] at h; exact absurd (app_eq_z h).2 (by simp)
  have hs : isSucc (app b one) = true := isSucc_succ b
  simp [cof, hne, hs]

/-- **Two rows, `t = 0`, `r` a root: the matrix value drops and stays standard.** No PRE needed. -/
theorem twoRow_desc_t0_root {M : Mat} {r n : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht0 : TRIO.srow M (M.length - 1) = 0) (hG : Good2 M)
    (hr1 : TRIO.r1ok M) (hz0 : TRIO.z0ok M) (hRD : RootsDec M) (h00 : entry M 0 0 = 0)
    (hrn : par M 0 r = none) (hn : 2 ≤ n) :
    isOT (ev2r (expand M n)) = true ∧ ev2r (expand M n) < ev2r M := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hr0 : par M 0 (M.length - 1) = some r := by have h := hr; rw [ht0] at h; exact h
  have hrx := par_lt M 0 _ r hr0
  have hA : Anc0 M r (M.length - 1) := Anc0.step hr0 (Anc0.refl r)
  have hx1 : entry M 1 (M.length - 1) = 0 := by
    unfold TRIO.srow at ht0
    split_ifs at ht0 with h1 h2
    change ¬ 0 < (M.getD (M.length - 1) (0, 0, 0)).2.1 at h2
    show (M.getD (M.length - 1) (0, 0, 0)).2.1 = 0
    omega
  have hgexp := expand_eq_gexp_t0 M n hM hz hr ht0
  have hF : F1 (TRIO.gexp M r (M.length - 1 - r) 0 0 n) := by
    rw [← hgexp]; exact F1_expand hr1 hz0 hM n
  have hroots0 := roots_split hx hA (col_zero_of_top hz0 h00 (by omega) hrn)
  have hr0c := col_zero_of_top hz0 h00 (by omega) hrn
  rw [hgexp]
  obtain ⟨Lb, hLbd⟩ : ∃ Lb, Lb = M.length - 1 - r := ⟨_, rfl⟩
  rw [← hLbd] at hF ⊢
  have hlen : r + Lb + 1 = M.length := by omega
  have hLb : 0 < Lb := by omega
  have hxe : r + Lb = M.length - 1 := by omega
  rw [← hxe] at hA hr0 hx1
  set N := TRIO.gexp M r Lb 0 0 n with hN
  have hlenN : N.length = r + n * Lb := TRIO.gexp_length hlen
  have he0 : entry M 0 r = 0 := by unfold entry; unfold col at hr0c; rw [hr0c]; rfl
  have he1 : entry M 1 r = 0 := by unfold entry; unfold col at hr0c; rw [hr0c]; rfl
  have he2 : entry M 2 r = 0 := by unfold entry; unfold col at hr0c; rw [hr0c]; rfl
  have hR : CopyRootsLow N r Lb n := by
    intro k hk p hp
    have h0 : entry N 0 (r + (k * Lb + 0)) = 0 := by
      rw [hN, entry0_gexp_mir hlen hk hLb]; simp [he0]
    have := ((par0_spec _).mp hp).2.1; omega
  have hvz : vr M r = z := by unfold vr; rw [if_pos he1]
  set b := bst M r (r + Lb) with hb
  have hcopy : ∀ k, k < n → o2r N (r + k * Lb) = psi z b z := by
    intro k hk
    rw [show r + k * Lb = r + (k * Lb + 0) by omega, o2r_gexp_copy_t0 hlen hLb hA hR hF hk 0 hLb,
      o2r_gexp_r_t0 hlen hLb hA hR hF hG (by omega) hr0, hvz]
  have hoM : o2r M r = psi z (app b one) z := by rw [o2r_r_succ hG hlen hr0 hx1, hvz]
  -- the roots of `N`
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
  -- values of the old roots
  have hNtake : N.take r = M.take r := by
    rw [hN]; unfold TRIO.gexp; exact List.take_left' (by rw [List.length_take]; omega)
  have heN0 : entry N 0 r = 0 := by
    have := entry0_gexp_mir (M := M) (Lb := Lb) (d0 := 0) (d1 := 0) (k := 0) (q := 0) hlen
      (show 0 < n by omega) hLb
    simp at this; rw [hN, this, he0]
  have hRv : R.map (o2r N) = R.map (o2r M) := by
    apply List.map_congr_left
    intro c hc
    rw [hRd, List.mem_filter] at hc
    have hcr : c < r := by simpa using hc.2
    rw [← o2r_take_low heN0 c hcr, hNtake, o2r_take_low he0 c hcr]
  have hCv : ((List.range n).map (fun k => r + k * Lb)).map (o2r N) = List.replicate n (psi z b z) := by
    rw [List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate, Function.comp]
    exact hcopy i (by simpa using h1)
  -- the sums
  set A := R.map (o2r M) with hAd
  have hdM : (A ++ [o2r M r]).Pairwise (fun a b => b ≤ a) := by
    have := hRD; unfold RootsDec at this
    rw [hroots0, List.map_append] at this; exact this
  have hdM' := List.pairwise_append.mp hdM
  have hsA : ∀ t ∈ A, Single t := by
    intro t ht; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hG i
  have hYot : isOT (psi z (app b one) z) = true := by rw [← hoM]; exact hG.ot r
  have hcot : isOT (psi z b z) = true := by
    have h1 := isOT_arg hYot
    rw [isOT_psi_iff]; refine ⟨isOT_sub hYot, isOT_app_left h1, rfl, z_le _, ?_⟩
    intro q hq
    have h2 := comps_lt hYot q (by rw [comps_app]; exact List.mem_append_left _ hq)
    exact comps_lt_prefix hq h2
  have hfs := fs_ot_lt hYot ⟨isOT_natT n, by rw [cof_succ_arg]; exact ⟨n, rfl⟩⟩
  rw [fs_succ_arg] at hfs
  have hcle : psi z b z ≤ psi z (app b one) z := by
    rcases n with _ | n
    · omega
    · have : psi z b z ≤ mulT (psi z b z) (n + 1) := by
        show psi z b z ≤ app (psi z b z) (mulT (psi z b z) n)
        exact le_app_self _ _
      exact le_trans this (le_of_lt hfs.2)
  have hdN : (A ++ List.replicate n (psi z b z)).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_append]
    refine ⟨hdM'.1, List.pairwise_replicate.mpr (Or.inr (le_refl _)), fun a ha c hc => ?_⟩
    rw [List.eq_of_mem_replicate hc]
    have := hdM'.2.2 a ha _ (List.mem_singleton_self _)
    rw [hoM] at this
    exact le_trans hcle this
  have hsN : ∀ t ∈ A ++ List.replicate n (psi z b z), Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsA t ht
    · rw [List.eq_of_mem_replicate ht]; exact ⟨hcot, _, _, rfl⟩
  have hsM : ∀ t ∈ A ++ [o2r M r], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsA t ht
    · rw [List.mem_singleton] at ht; subst ht; exact single_o2r hG r
  obtain ⟨hNot, hNsum⟩ := sumN_dec _ hsN hdN
  obtain ⟨_, hAsum⟩ := sumN_dec _ hsA hdM'.1
  have eN : ev2r N = app (sumN A) (mulT (psi z b z) n) := by
    rw [ev2r_roots, hroots, List.map_append, hRv, hCv]
    apply eq_of_summands
    rw [hNsum, summands_app, hAsum, summands_mulT_eq ⟨z, b, rfl⟩]
  have eM : ev2r M = app (sumN A) (o2r M r) := by
    rw [ev2r_roots, hroots0, List.map_append]
    exact sumN_snoc_dec hsM hdM
  refine ⟨?_, ?_⟩
  · rw [ev2r_roots, hroots, List.map_append, hRv, hCv]; exact hNot
  · rw [eN, eM, hoM]; exact (app_lt_app_left_iff _).mpr hfs.2

end Ytosk
