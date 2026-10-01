/-
**経路の定理の一般化: 枠ごとに ζ が鎖 Z の中でずれてよい。**

各枠で「子の新しい値が fsD(o_M(p), Z_j) なら、親の新しい値は fsD(o_M(h), Z_{j′})」（`hstep`）を仮定すると、
経路上のすべての列で o_{M[n]}(h) = fsD(o_M(h), Z_j) となる（j は列ごと）。q = r（引き上げで ζ がずれる）に使う。
-/
import Ytosk.F1

namespace Ytosk

open T

section
variable {M : Mat} {n r : Nat} (hM : 2 ≤ M.length)
  (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
  (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
  (ht : 0 < TRIO.srow M (M.length - 1)) (hn : 2 ≤ n)
include hM hz hr ht hn

/-- **The path after expansion, with the index moving along a chain.** -/
theorem o2r_expand_path_gen (hG : Good2 M) (Z : Nat → T)
    (hleaf : ∃ j, o2r (expand M n) (M.length - 1) = fsD (o2r M (M.length - 1)) (Z j) ∧
      isOT (fsD (o2r M (M.length - 1)) (Z j)) = true ∧
      fsD (o2r M (M.length - 1)) (Z j) < o2r M (M.length - 1))
    (hstep : ∀ h p j, Anc0 M p (M.length - 1) → par M 0 p = some h →
      isOT (fsD (o2r M p) (Z j)) = true → fsD (o2r M p) (Z j) < o2r M p →
      ∃ j', psi (vr M h) (spArg (vr M h) (bst M h p) (fsD (o2r M p) (Z j))) z =
          fsD (o2r M h) (Z j') ∧
        isOT (fsD (o2r M h) (Z j')) = true ∧ fsD (o2r M h) (Z j') < o2r M h) :
    ∀ h, Anc0 M h (M.length - 1) → ∃ j, o2r (expand M n) h = fsD (o2r M h) (Z j) ∧
      isOT (fsD (o2r M h) (Z j)) = true ∧ fsD (o2r M h) (Z j) < o2r M h := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have key : ∀ m h, M.length - 1 - h ≤ m → Anc0 M h (M.length - 1) →
      ∃ j, o2r (expand M n) h = fsD (o2r M h) (Z j) ∧
        isOT (fsD (o2r M h) (Z j)) = true ∧ fsD (o2r M h) (Z j) < o2r M h := by
    intro m
    induction m with
    | zero =>
      intro h h1 hA
      have := hA.le
      rw [show h = M.length - 1 by omega]; exact hleaf
    | succ m ih =>
      intro h hm hA
      rcases Nat.eq_or_lt_of_le hA.le with heq | hlt
      · rw [heq]; exact hleaf
      obtain ⟨c, hc, hcA⟩ := anc0_child hA (by omega)
      have hcx := hcA.le
      have hpc := par_lt M 0 c h hc
      have hle := children_le_of_anc_last hcA hx hc
      have hcmem : c ∈ children M h := mem_children_iff.mpr ⟨by omega, hc⟩
      have hsplit := split_last_max _ c (children_sorted M h) hcmem hle
      have hoff : ∀ d ∈ (children M h).filter (fun d => decide (d < c)),
          o2r (expand M n) d = o2r M d := by
        intro d hd
        rw [List.mem_filter] at hd
        have hdc : d < c := by simpa using hd.2
        have hdp := mem_children_iff.mp hd.1
        apply o2r_expand_off hM hz hr ht hn d (by omega)
        intro hdA
        rcases anc0_total hdA hcA with h' | h'
        · have := (anc0_par h' (by omega) hc).le; have := par_lt M 0 d h hdp.2; omega
        · have := h'.le; omega
      obtain ⟨j, hIH, hjot, hjlt⟩ := ih c (by omega) hcA
      set C := (children M h).filter (fun d => decide (d < c)) with hCdef
      have hCv : C.map (o2r (expand M n)) = C.map (o2r M) := List.map_congr_left hoff
      have hsing : ∀ t ∈ C.map (o2r M), Single t := by
        intro t ht'
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht'; exact single_o2r hG i
      have hdM := hG.dec h
      simp only [hsplit, List.map_append, List.map_cons, List.map_nil] at hdM
      have hc'ot : isOT (o2r (expand M n) c) = true := by rw [hIH]; exact hjot
      have hc'le : o2r (expand M n) c ≤ o2r M c := by rw [hIH]; exact le_of_lt hjlt
      have hdM' : (C.map (o2r M) ++ [o2r (expand M n) c]).Pairwise (fun a b => b ≤ a) := by
        rw [List.pairwise_append] at hdM ⊢
        refine ⟨hdM.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
        rw [List.mem_singleton] at hb; subst hb
        exact le_trans hc'le (hdM.2.2 a ha _ (List.mem_singleton_self _))
      have hsing' : ∀ t ∈ C.map (o2r M) ++ [o2r (expand M n) c], Single t := by
        intro t ht'
        rcases List.mem_append.mp ht' with ht' | ht'
        · exact hsing t ht'
        · rw [List.mem_singleton] at ht'; subst ht'; exact ⟨hc'ot, o2r_psi_form _ c⟩
      have hch' : (children (expand M n) h).map (o2r (expand M n)) =
          C.map (o2r M) ++ [o2r (expand M n) c] := by
        rw [children_expand_lt M n hM hz hr ht hn (by omega), hsplit, List.map_append, hCv]; rfl
      have hS' := sumN_dec _ hsing' hdM'
      have hv' : vr (expand M n) h = vr M h := vr_expand_lt hM hn (by omega)
      have hvM := isOT_vr hG.f1 h
      have hM2 : o2r (expand M n) h =
          psi (vr M h) (spArg (vr M h) (bst M h c) (o2r (expand M n) c)) z := by
        rw [o2r_spArg (by rw [hv']; exact hvM) (by rw [hch']; exact hS'.1), hch', hv',
          sumN_snoc_dec hsing' hdM', spArg_app]; rfl
      obtain ⟨j', hj', hj'ot, hj'lt⟩ := hstep h c j hcA hc hjot hjlt
      exact ⟨j', by rw [hM2, hIH, hj'], hj'ot, hj'lt⟩
  exact fun h hA => key _ h (Nat.le_refl _) hA

end

/-! ## q = r の枠 (r, x) -/

/-- If the copy-root value `ψ_μ(y)` has `y = b + lo` with `b` above `Ω_{μ+1}` and `lo` below it, then
`sp` at `r` just appends it (with or without a rewrite). -/
theorem spArg_rx {μ b y lo : T} (hc : isOT (psi μ y z) = true)
    (hb : ∀ q ∈ summands b, ¬ q < psi (succ μ) z z)
    (hy : y = app b lo) (hlo : lo = z ∨ head lo < psi (succ μ) z z) :
    spArg μ b (psi μ y z) = app b (psi μ y z) := by
  have hsp : split y (psi (succ μ) z z) = (b, lo) := by rw [hy]; exact split_app_of hb hlo
  rw [spArg_single]
  unfold step
  by_cases htr : lt b y = true ∧ lt (psi μ z z) (psi μ y z) = true
  · rw [if_pos htr, H_eq hc, hsp]
    rcases hlo with rfl | _
    · simp [app_z_right] at hy; subst hy; exact absurd htr.1 (lt_irrefl' _)
    · have hloz : lo ≠ z := by rintro rfl; simp at hy; subst hy; exact lt_irrefl' _ htr.1
      simp [hloz]
  · rw [if_neg htr]
    apply add_eq_app_of_ge ⟨μ, y, rfl⟩
    intro q hq
    apply le_of_lt
    have := hb q hq
    rcases lt_trichotomy' q (psi (succ μ) z z) with h1 | h1 | h1
    · exact absurd h1 this
    · rw [h1]; rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ)
    · exact lt_trans (by rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ)) h1

/-- `path_last` without `v(q) > μ`: if the leaf is the last summand, the argument is `q`'s. -/
theorem path_last_gen {M : Mat} {x q : Nat} (hG : Good2 M) (hx : x + 1 = M.length)
    (hq : par M 0 x = some q) :
    ∀ p, Anc0 M p x → p < x → ∃ d, Anc0 M d x ∧ p < d ∧
      last (argOf (o2r M p)) = o2r M d ∧ (d = x → argOf (o2r M p) = argOf (o2r M q)) := by
  have key : ∀ m p, x - p ≤ m → Anc0 M p x → p < x → ∃ d, Anc0 M d x ∧ p < d ∧
      last (argOf (o2r M p)) = o2r M d ∧ (d = x → argOf (o2r M p) = argOf (o2r M q)) := by
    intro m
    induction m with
    | zero => intro p h1 _ h3; omega
    | succ m ih =>
      intro p hm hp hpx
      obtain ⟨c, hc, hcA⟩ := anc0_child hp (by omega)
      have hpc := par_lt M 0 c p hc
      obtain ⟨y, hy⟩ := o2r_sub hG c
      have hcot : isOT (psi (vr M c) y z) = true := by rw [← hy]; exact hG.ot c
      have hop : o2r M p = psi (vr M p) (step (vr M p) (bst M p c) (vr M c) y z) z := by
        rw [o2r_frame hG hx hcA hc, hy, spArg_single]
      rcases step_cases (a := vr M p) (b := bst M p c) hcot with ⟨B, hB⟩ | ⟨h1, hlo, h3, _⟩
      · refine ⟨c, hcA, hpc, ?_, ?_⟩
        · rw [hop]; show last (step _ _ _ _ _) = _
          rw [hB, last_app B (by simp), hy]; rfl
        · intro hcx; subst hcx; rw [hq] at hc; cases hc; rfl
      · have hcx : c < x := by
          rcases Nat.eq_or_lt_of_le hcA.le with h' | h'
          · exfalso; subst h'
            rw [o2r_leaf hx (isOT_vr hG.f1 c)] at hy; cases hy; exact h3 rfl
          · exact h'
        obtain ⟨d, hdA, hcd, hld, hdx⟩ := ih c (by omega) hcA hcx
        have hargp : argOf (o2r M p) = argOf (o2r M c) := by
          rw [hop, hy]; show step _ _ _ _ _ = y; exact h1
        refine ⟨d, hdA, by omega, by rw [hargp]; exact hld, fun hd => ?_⟩
        rw [hargp]; exact hdx hd
  exact fun p => key _ p (Nat.le_refl _)

theorem DiagAt.size_lt {a b μ : T} {t : T} (h : DiagAt a b μ t) : size b < size t := by
  induction h with
  | here => simp [size]; omega
  | rest _ ih => simp [size] at *; omega
  | arg _ _ _ ih => simp [size] at *; omega
  | sub _ _ _ ih => simp [size] at *; omega

/-! ## 抽象的な行列 N での経路の定理（展開とその先頭部分の両方に使う） -/

/-- Off the path, values agree when subscripts and children agree before `x`. -/
theorem o2r_off_gen {M N : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hA1 : ∀ j, j < x → vr N j = vr M j) (hA2 : ∀ h, h < x → children N h = children M h) :
    ∀ j, j < x → ¬ Anc0 M j x → o2r N j = o2r M j := by
  have key : ∀ m j, x - j ≤ m → j < x → ¬ Anc0 M j x → o2r N j = o2r M j := by
    intro m
    induction m with
    | zero => intro j h1 h2; omega
    | succ m ih =>
      intro j hm hj hA
      apply o2r_congr (hA1 j hj)
      rw [hA2 j hj]
      apply List.map_congr_left
      intro c hc
      have hpc : par M 0 c = some j := (mem_children_iff.mp hc).2
      have hcl := (mem_children hc).2
      have hjc := (mem_children hc).1
      have hcA : ¬ Anc0 M c x := fun hcA => hA (anc0_up hpc hcA)
      have hcx : c < x := by
        rcases Nat.lt_or_ge c x with h | h
        · exact h
        · have : c = x := by omega
          subst this; exact absurd (Anc0.refl _) hcA
      exact ih c (by omega) hcx hcA
  exact fun j => key _ j (Nat.le_refl _)

/-- **The path theorem for an abstract `N`** agreeing with `M` before `x` (subscripts and children). -/
theorem o2r_path_abs {M N : Mat} {x : Nat} (hx : x + 1 = M.length) (hG : Good2 M) (Z : Nat → T)
    (hA1 : ∀ j, j < x → vr N j = vr M j) (hA2 : ∀ h, h < x → children N h = children M h)
    (hleaf : ∃ j, o2r N x = fsD (o2r M x) (Z j) ∧
      isOT (fsD (o2r M x) (Z j)) = true ∧ fsD (o2r M x) (Z j) < o2r M x)
    (hstep : ∀ h p j, Anc0 M p x → par M 0 p = some h →
      isOT (fsD (o2r M p) (Z j)) = true → fsD (o2r M p) (Z j) < o2r M p →
      ∃ j', psi (vr M h) (spArg (vr M h) (bst M h p) (fsD (o2r M p) (Z j))) z =
          fsD (o2r M h) (Z j') ∧
        isOT (fsD (o2r M h) (Z j')) = true ∧ fsD (o2r M h) (Z j') < o2r M h) :
    ∀ h, Anc0 M h x → ∃ j, o2r N h = fsD (o2r M h) (Z j) ∧
      isOT (fsD (o2r M h) (Z j)) = true ∧ fsD (o2r M h) (Z j) < o2r M h := by
  have key : ∀ m h, x - h ≤ m → Anc0 M h x →
      ∃ j, o2r N h = fsD (o2r M h) (Z j) ∧
        isOT (fsD (o2r M h) (Z j)) = true ∧ fsD (o2r M h) (Z j) < o2r M h := by
    intro m
    induction m with
    | zero =>
      intro h h1 hA
      have := hA.le
      rw [show h = x by omega]; exact hleaf
    | succ m ih =>
      intro h hm hA
      rcases Nat.eq_or_lt_of_le hA.le with heq | hlt
      · rw [heq]; exact hleaf
      obtain ⟨c, hc, hcA⟩ := anc0_child hA (by omega)
      have hcx := hcA.le
      have hpc := par_lt M 0 c h hc
      have hle := children_le_of_anc_last hcA hx hc
      have hcmem : c ∈ children M h := mem_children_iff.mpr ⟨by omega, hc⟩
      have hsplit := split_last_max _ c (children_sorted M h) hcmem hle
      have hoff : ∀ d ∈ (children M h).filter (fun d => decide (d < c)), o2r N d = o2r M d := by
        intro d hd
        rw [List.mem_filter] at hd
        have hdc : d < c := by simpa using hd.2
        have hdp := mem_children_iff.mp hd.1
        apply o2r_off_gen hx hA1 hA2 d (by omega)
        intro hdA
        rcases anc0_total hdA hcA with h' | h'
        · have := (anc0_par h' (by omega) hc).le; have := par_lt M 0 d h hdp.2; omega
        · have := h'.le; omega
      obtain ⟨j, hIH, hjot, hjlt⟩ := ih c (by omega) hcA
      set C := (children M h).filter (fun d => decide (d < c)) with hCdef
      have hCv : C.map (o2r N) = C.map (o2r M) := List.map_congr_left hoff
      have hsing : ∀ t ∈ C.map (o2r M), Single t := by
        intro t ht'
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht'; exact single_o2r hG i
      have hdM := hG.dec h
      simp only [hsplit, List.map_append, List.map_cons, List.map_nil] at hdM
      have hc'ot : isOT (o2r N c) = true := by rw [hIH]; exact hjot
      have hc'le : o2r N c ≤ o2r M c := by rw [hIH]; exact le_of_lt hjlt
      have hdM' : (C.map (o2r M) ++ [o2r N c]).Pairwise (fun a b => b ≤ a) := by
        rw [List.pairwise_append] at hdM ⊢
        refine ⟨hdM.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
        rw [List.mem_singleton] at hb; subst hb
        exact le_trans hc'le (hdM.2.2 a ha _ (List.mem_singleton_self _))
      have hsing' : ∀ t ∈ C.map (o2r M) ++ [o2r N c], Single t := by
        intro t ht'
        rcases List.mem_append.mp ht' with ht' | ht'
        · exact hsing t ht'
        · rw [List.mem_singleton] at ht'; subst ht'; exact ⟨hc'ot, o2r_psi_form _ c⟩
      have hch' : (children N h).map (o2r N) = C.map (o2r M) ++ [o2r N c] := by
        rw [hA2 h (by omega), hsplit, List.map_append, hCv]; rfl
      have hS' := sumN_dec _ hsing' hdM'
      have hv' : vr N h = vr M h := hA1 h (by omega)
      have hvM := isOT_vr hG.f1 h
      have hM2 : o2r N h = psi (vr M h) (spArg (vr M h) (bst M h c) (o2r N c)) z := by
        rw [o2r_spArg (by rw [hv']; exact hvM) (by rw [hch']; exact hS'.1), hch', hv',
          sumN_snoc_dec hsing' hdM', spArg_app]; rfl
      obtain ⟨j', hj', hj'ot, hj'lt⟩ := hstep h c j hcA hc hjot hjlt
      exact ⟨j', by rw [hM2, hIH, hj'], hj'ot, hj'lt⟩
  exact fun h hA => key _ h (Nat.le_refl _) hA

/-- `o2r_off_gen` with children agreeing only off the path. -/
theorem o2r_off_gen' {M N : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hA1 : ∀ j, j < x → vr N j = vr M j)
    (hA2 : ∀ h, h < x → ¬ Anc0 M h x → children N h = children M h) :
    ∀ j, j < x → ¬ Anc0 M j x → o2r N j = o2r M j := by
  have key : ∀ m j, x - j ≤ m → j < x → ¬ Anc0 M j x → o2r N j = o2r M j := by
    intro m
    induction m with
    | zero => intro j h1 h2; omega
    | succ m ih =>
      intro j hm hj hA
      apply o2r_congr (hA1 j hj)
      rw [hA2 j hj hA]
      apply List.map_congr_left
      intro c hc
      have hpc : par M 0 c = some j := (mem_children_iff.mp hc).2
      have hcl := (mem_children hc).2
      have hjc := (mem_children hc).1
      have hcA : ¬ Anc0 M c x := fun hcA => hA (anc0_up hpc hcA)
      have hcx : c < x := by
        rcases Nat.lt_or_ge c x with h | h
        · exact h
        · have : c = x := by omega
          subst this; exact absurd (Anc0.refl _) hcA
      exact ih c (by omega) hcx hcA
  exact fun j => key _ j (Nat.le_refl _)

/-- **The path theorem from a path node `ℓ` upward.** Children agree off the path and strictly above
`ℓ`; the new value at `ℓ` is given. -/
theorem o2r_path_from {M N : Mat} {x ℓ : Nat} (hx : x + 1 = M.length) (hG : Good2 M) (Z : Nat → T)
    (hℓ : Anc0 M ℓ x)
    (hA1 : ∀ j, j < x → vr N j = vr M j)
    (hA2 : ∀ h, h < x → (¬ Anc0 M h x ∨ h < ℓ) → children N h = children M h)
    (hleaf : ∃ j, o2r N ℓ = fsD (o2r M ℓ) (Z j) ∧
      isOT (fsD (o2r M ℓ) (Z j)) = true ∧ fsD (o2r M ℓ) (Z j) < o2r M ℓ)
    (hstep : ∀ h p j, Anc0 M p ℓ → par M 0 p = some h →
      isOT (fsD (o2r M p) (Z j)) = true → fsD (o2r M p) (Z j) < o2r M p →
      ∃ j', psi (vr M h) (spArg (vr M h) (bst M h p) (fsD (o2r M p) (Z j))) z =
          fsD (o2r M h) (Z j') ∧
        isOT (fsD (o2r M h) (Z j')) = true ∧ fsD (o2r M h) (Z j') < o2r M h) :
    ∀ h, Anc0 M h ℓ → ∃ j, o2r N h = fsD (o2r M h) (Z j) ∧
      isOT (fsD (o2r M h) (Z j)) = true ∧ fsD (o2r M h) (Z j) < o2r M h := by
  have hℓx := hℓ.le
  have key : ∀ m h, ℓ - h ≤ m → Anc0 M h ℓ →
      ∃ j, o2r N h = fsD (o2r M h) (Z j) ∧
        isOT (fsD (o2r M h) (Z j)) = true ∧ fsD (o2r M h) (Z j) < o2r M h := by
    intro m
    induction m with
    | zero =>
      intro h h1 hA
      have := hA.le
      rw [show h = ℓ by omega]; exact hleaf
    | succ m ih =>
      intro h hm hA
      rcases Nat.eq_or_lt_of_le hA.le with heq | hlt
      · rw [heq]; exact hleaf
      have hAx : Anc0 M h x := hA.trans hℓ
      obtain ⟨c, hc, hcA⟩ := anc0_child hA (by omega)
      have hcAx : Anc0 M c x := hcA.trans hℓ
      have hpc := par_lt M 0 c h hc
      have hle := children_le_of_anc_last hcAx hx hc
      have hcmem : c ∈ children M h := mem_children_iff.mpr ⟨by have := hcAx.le; omega, hc⟩
      have hsplit := split_last_max _ c (children_sorted M h) hcmem hle
      have hoff : ∀ d ∈ (children M h).filter (fun d => decide (d < c)), o2r N d = o2r M d := by
        intro d hd
        rw [List.mem_filter] at hd
        have hdc : d < c := by simpa using hd.2
        have hdp := mem_children_iff.mp hd.1
        apply o2r_off_gen' hx hA1 (fun h' hh' hn => hA2 h' hh' (Or.inl hn)) d
          (by have := hcAx.le; omega)
        intro hdA
        rcases anc0_total hdA hcAx with h' | h'
        · have := (anc0_par h' (by omega) hc).le; have := par_lt M 0 d h hdp.2; omega
        · have := h'.le; omega
      obtain ⟨j, hIH, hjot, hjlt⟩ := ih c (by omega) hcA
      set C := (children M h).filter (fun d => decide (d < c)) with hCdef
      have hCv : C.map (o2r N) = C.map (o2r M) := List.map_congr_left hoff
      have hsing : ∀ t ∈ C.map (o2r M), Single t := by
        intro t ht'
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht'; exact single_o2r hG i
      have hdM := hG.dec h
      simp only [hsplit, List.map_append, List.map_cons, List.map_nil] at hdM
      have hc'ot : isOT (o2r N c) = true := by rw [hIH]; exact hjot
      have hc'le : o2r N c ≤ o2r M c := by rw [hIH]; exact le_of_lt hjlt
      have hdM' : (C.map (o2r M) ++ [o2r N c]).Pairwise (fun a b => b ≤ a) := by
        rw [List.pairwise_append] at hdM ⊢
        refine ⟨hdM.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
        rw [List.mem_singleton] at hb; subst hb
        exact le_trans hc'le (hdM.2.2 a ha _ (List.mem_singleton_self _))
      have hsing' : ∀ t ∈ C.map (o2r M) ++ [o2r N c], Single t := by
        intro t ht'
        rcases List.mem_append.mp ht' with ht' | ht'
        · exact hsing t ht'
        · rw [List.mem_singleton] at ht'; subst ht'; exact ⟨hc'ot, o2r_psi_form _ c⟩
      have hch' : (children N h).map (o2r N) = C.map (o2r M) ++ [o2r N c] := by
        rw [hA2 h (by omega) (Or.inr hlt), hsplit, List.map_append, hCv]; rfl
      have hS' := sumN_dec _ hsing' hdM'
      have hv' : vr N h = vr M h := hA1 h (by omega)
      have hvM := isOT_vr hG.f1 h
      have hM2 : o2r N h = psi (vr M h) (spArg (vr M h) (bst M h c) (o2r N c)) z := by
        rw [o2r_spArg (by rw [hv']; exact hvM) (by rw [hch']; exact hS'.1), hch', hv',
          sumN_snoc_dec hsing' hdM', spArg_app]; rfl
      obtain ⟨j', hj', hj'ot, hj'lt⟩ := hstep h c j hcA hc hjot hjlt
      exact ⟨j', by rw [hM2, hIH, hj'], hj'ot, hj'lt⟩
  exact fun h hA => key _ h (Nat.le_refl _) hA

end Ytosk
