/-
**2 行・t = 1・n ≥ 2: 経路上の値は fsD(o_M(h), Y)（Y = M[n] での x の値）。**

各枠の交換の条件（`FrameD`）と ζ の条件（`DV`）を仮定に置く。経路にない x より前の列の値は変わらない。
-/
import Ytosk.TwoRowT
import Ytosk.ExpGexp
import Ytosk.SPFSD

namespace Ytosk

open T


/-! ## 葉 -/

theorem o2r_psi_form (M : Mat) (i : Nat) : ∃ s y, o2r M i = psi s y z := by
  rw [o2r_eq]
  show ∃ s y, add (sp (sf (vr M i)) z (sf _)) (sf z) = psi s y z
  rw [sp_eq_spArg]; exact ⟨_, _, rfl⟩

theorem children_last {M : Mat} {x : Nat} (hx : x + 1 = M.length) : children M x = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro c hc
  have := mem_children hc; omega

theorem o2r_leaf {M : Mat} {x : Nat} (hx : x + 1 = M.length) (hv : isOT (vr M x) = true) :
    o2r M x = psi (vr M x) z z := by
  rw [o2r_eq, children_last hx]
  show add (sp (sf (vr M x)) z (sf z)) (sf z) = _
  rw [sf_ot hv]; rfl

theorem isSucc_nT_succ (k : Nat) : isSucc (nT (k + 1)) = true := by
  show isSucc (sf (add (nT k) one)) = true
  rw [sf_ot (isOT_add (isOT_nT k) isOT_one), add_one_eq_succ (isOT_nT k)]
  exact isSucc_succ _

/-- The leaf `Ω_{v_x}` takes any smaller index as its fundamental sequence. -/
theorem fsD_leaf {v ζ : T} (hs : isSucc v = true) (hv : v ≠ z) : fsD (psi v z z) ζ = ζ := by
  unfold fsD; rw [if_pos rfl, if_neg hv, if_pos hs]

section
variable {M : Mat} {n r : Nat} (hM : 2 ≤ M.length)
  (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
  (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
  (ht : 0 < TRIO.srow M (M.length - 1)) (hn : 2 ≤ n)
include hM hz hr ht hn

omit hz hr ht in
theorem vr_expand_lt {j : Nat} (hj : j < M.length - 1) : vr (expand M n) j = vr M j := by
  rw [← vr_take (expand M n) j hj, expand_take_prefix M hM (by omega), vr_take M j hj]

/-- **Off the path, values are unchanged.** -/
theorem o2r_expand_off : ∀ j, j < M.length - 1 → ¬ Anc0 M j (M.length - 1) →
    o2r (expand M n) j = o2r M j := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have key : ∀ m j, M.length - 1 - j ≤ m → j < M.length - 1 → ¬ Anc0 M j (M.length - 1) →
      o2r (expand M n) j = o2r M j := by
    intro m
    induction m with
    | zero => intro j h1 h2; omega
    | succ m ih =>
      intro j hm hj hA
      apply o2r_congr (vr_expand_lt hM hn hj)
      rw [children_expand_lt M n hM hz hr ht hn hj]
      apply List.map_congr_left
      intro c hc
      have hpc : par M 0 c = some j := (mem_children_iff.mp hc).2
      have hcl := (mem_children hc).2
      have hjc := (mem_children hc).1
      have hcA : ¬ Anc0 M c (M.length - 1) := fun hcA => hA (anc0_up hpc hcA)
      have hcx : c < M.length - 1 := by
        rcases Nat.lt_or_ge c (M.length - 1) with h | h
        · exact h
        · have : c = M.length - 1 := by omega
          subst this; exact absurd (Anc0.refl _) hcA
      exact ih c (by omega) hcx hcA
  exact fun j => key _ j (Nat.le_refl _)

/-- The state of the earlier siblings of `p` at `h`. -/
def bst (M : Mat) (h p : Nat) : T :=
  spArg (vr M h) z (sumN (((children M h).filter (fun d => decide (d < p))).map (o2r M)))

/-- **The path after expansion (two rows).** -/
theorem o2r_expand_path (hG : Good2 M) (hb1 : 0 < entry M 1 (M.length - 1))
    (hOK : ∀ p, Anc0 M p (M.length - 1) →
      isOT (fsD (o2r M p) (o2r (expand M n) (M.length - 1))) = true ∧
        fsD (o2r M p) (o2r (expand M n) (M.length - 1)) < o2r M p)
    (hF : ∀ h p, Anc0 M p (M.length - 1) → par M 0 p = some h →
      FrameD (vr M h) (bst M h p) (o2r M p) (o2r (expand M n) (M.length - 1))) :
    ∀ h, Anc0 M h (M.length - 1) →
      o2r (expand M n) h = fsD (o2r M h) (o2r (expand M n) (M.length - 1)) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  generalize hYdef : o2r (expand M n) (M.length - 1) = Y at hOK hF
  -- the leaf
  have hleaf : o2r (expand M n) (M.length - 1) = fsD (o2r M (M.length - 1)) Y := by
    have hv := isOT_vr hG.f1 (M.length - 1)
    rw [o2r_leaf hx hv, vr_eq_nT hG.f1, show entry M 1 (M.length - 1) =
      (entry M 1 (M.length - 1) - 1) + 1 by omega, fsD_leaf (isSucc_nT_succ _)
      (by intro h; have := isSucc_nT_succ (entry M 1 (M.length - 1) - 1); rw [h] at this;
          simp [isSucc, last, one] at this), hYdef]
  have key : ∀ m h, M.length - 1 - h ≤ m → Anc0 M h (M.length - 1) →
      o2r (expand M n) h = fsD (o2r M h) Y := by
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
      have hIH : o2r (expand M n) c = fsD (o2r M c) Y := ih c (by omega) hcA
      set C := (children M h).filter (fun d => decide (d < c)) with hCdef
      have hCv : C.map (o2r (expand M n)) = C.map (o2r M) := List.map_congr_left hoff
      have hsing : ∀ t ∈ C.map (o2r M), Single t := by
        intro t ht'
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht'; exact single_o2r hG i
      have hdM := hG.dec h
      simp only [hsplit, List.map_append, List.map_cons, List.map_nil] at hdM
      -- the value in `M`
      have hsumM : sumN ((children M h).map (o2r M)) = app (sumN (C.map (o2r M))) (o2r M c) := by
        simp only [hsplit, List.map_append, List.map_cons, List.map_nil]
        refine sumN_snoc_dec ?_ hdM
        intro t ht'
        rcases List.mem_append.mp ht' with ht' | ht'
        · exact hsing t ht'
        · rw [List.mem_singleton] at ht'; subst ht'; exact single_o2r hG c
      have hvM := isOT_vr hG.f1 h
      have hM1 : o2r M h = psi (vr M h) (spArg (vr M h) (bst M h c) (o2r M c)) z := by
        rw [o2r_spArg hvM (sumN_children hG h).1, hsumM, spArg_app]; rfl
      -- the value in `M[n]`
      have hc'ot : isOT (o2r (expand M n) c) = true := by
        rw [hIH]; exact (hOK c hcA).1
      have hc'le : o2r (expand M n) c ≤ o2r M c := by
        rw [hIH]; exact le_of_lt (hOK c hcA).2
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
      have hM2 : o2r (expand M n) h =
          psi (vr M h) (spArg (vr M h) (bst M h c) (o2r (expand M n) c)) z := by
        rw [o2r_spArg (by rw [hv']; exact hvM) (by rw [hch']; exact hS'.1), hch', hv',
          sumN_snoc_dec hsing' hdM', spArg_app]; rfl
      rw [hM2, hM1, hIH, node_fsD (hF h c hcA hc)]
  exact fun h hA => key _ h (Nat.le_refl _) hA

end

end Ytosk
