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

end Ytosk
