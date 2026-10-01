/-
**2 行・t = 1 の経路の値の形。**

x から根への経路で、r より下（r と x の間と x）の値は cof が Ω_{μ+1}（μ = v(r)）、r の値は ψ_μ(b)（cof b = Ω_{μ+1}）、
r 以上の値は対角化の点（ψ_{a′}(b)、引き上げで a′ が上に動く）を持つ。
-/
import Ytosk.TwoRowA

namespace Ytosk

open T

/-! ## 祖先と climb の鎖 -/

theorem anc0_of_rtg {M : Mat} {a b : Nat} (h : Relation.ReflTransGen (StepRel (par M 0)) a b) :
    Anc0 M a b := by
  induction h with
  | refl => exact Anc0.refl _
  | tail _ h2 ih => exact Anc0.step h2 ih

theorem rtg_of_anc0 {M : Mat} {a b : Nat} (h : Anc0 M a b) :
    Relation.ReflTransGen (StepRel (par M 0)) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | step hp _ ih => exact Relation.ReflTransGen.tail ih hp

/-- **Between the row-1 parent and the column, row 1 is at least the column's.** -/
theorem par1_between {M : Mat} {x r : Nat} (hr : par M 1 x = some r) :
    ∀ p, Anc0 M p x → r < p → entry M 1 x ≤ entry M 1 p := by
  intro p hp hrp
  rcases Nat.eq_or_lt_of_le hp.le with heq | hlt
  · rw [heq]
  have hr' : climb (par M 0) (fun q => decide (entry M 1 q < entry M 1 x)) (x + 1) (par M 0 x) = some r := hr
  clear hr
  cases hq : par M 0 x with
  | none => rw [hq] at hr'; simp [climb] at hr'
  | some q0 =>
    rw [hq] at hr'
    have hq0 := par_lt M 0 x q0 hq
    have := (climb_chain_iff (par M 0) _ (par_lt M 0) r (x + 1) q0 (by omega)).mp hr'
    have hpq : Anc0 M p q0 := anc0_par hp (by omega) hq
    have h3 := this.2.2 p (rtg_of_anc0 hpq) hrp
    simp at h3; omega

/-! ## 項の小補題 -/

theorem init_succ : ∀ ν : T, init (succ ν) = ν
  | z => rfl
  | psi a b c => by
    show init (psi a b (app c one)) = psi a b c
    have hne : app c one ≠ z := fun h => by exact absurd (app_eq_z h).2 (by simp [one])
    cases hc : app c one with
    | z => exact absurd hc hne
    | psi d e f =>
      show psi a b (init (psi d e f)) = psi a b c
      rw [← hc]; congr 1; exact init_succ c

theorem cof_leaf (ν : T) : cof (psi (succ ν) z z) = .big ν := by
  have hs : isSucc (succ ν) = true := isSucc_succ ν
  have hne : succ ν ≠ z := by
    intro h; rw [h] at hs; simp [isSucc, last, one] at hs
  simp only [cof, if_neg hne, hs, if_true, init_succ]

theorem nT_succ (k : Nat) : nT (k + 1) = succ (nT k) := by
  show sf (add (nT k) one) = _
  rw [sf_ot (isOT_add (isOT_nT k) isOT_one), add_one_eq_succ (isOT_nT k)]

theorem lt_nT : ∀ {k l : Nat}, k < l → nT k < nT l := by
  intro k l h
  induction l with
  | zero => omega
  | succ l ih =>
    rw [nT_succ]
    rcases Nat.lt_or_ge k l with h' | h'
    · exact lt_trans (ih h') (lt_succ_self _)
    · have : k = l := by omega
      subst this; exact lt_succ_self _

theorem DiagAt.not_succ {a b μ : T} {t : T} (h : DiagAt a b μ t) : isSucc t = false := by
  induction h with
  | here hb _ _ =>
    simp only [isSucc, last, beq_eq_false_iff_ne]
    intro h; simp [one] at h; exact hb h.2
  | rest _ ih => rw [isSucc_psi_rest _ _ _ (by simp)]; exact ih
  | arg hb _ _ _ =>
    simp only [isSucc, last, beq_eq_false_iff_ne]
    intro h; simp [one] at h; exact hb h.2
  | sub ha _ _ _ =>
    simp only [isSucc, last, beq_eq_false_iff_ne]
    intro h; simp [one] at h; exact ha h

/-- The node over a path child, as `ψ_a` of one `sp` step. -/
theorem o2r_frame {M : Mat} {x : Nat} (hG : Good2 M) (hx : x + 1 = M.length) {h p : Nat}
    (hpA : Anc0 M p x) (hp : par M 0 p = some h) :
    o2r M h = psi (vr M h) (spArg (vr M h) (bst M h p) (o2r M p)) z := by
  have hpc := par_lt M 0 p h hp
  have hle := children_le_of_anc_last hpA hx hp
  have hcmem : p ∈ children M h := mem_children_iff.mpr ⟨by have := hpA.le; omega, hp⟩
  have hsplit := split_last_max _ p (children_sorted M h) hcmem hle
  set C := (children M h).filter (fun d => decide (d < p)) with hCdef
  have hdM := hG.dec h
  simp only [hsplit, List.map_append, List.map_cons, List.map_nil] at hdM
  have hsumM : sumN ((children M h).map (o2r M)) = app (sumN (C.map (o2r M))) (o2r M p) := by
    simp only [hsplit, List.map_append, List.map_cons, List.map_nil]
    refine sumN_snoc_dec ?_ hdM
    intro t ht'
    rcases List.mem_append.mp ht' with ht' | ht'
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht'; exact single_o2r hG i
    · rw [List.mem_singleton] at ht'; subst ht'; exact single_o2r hG p
  rw [o2r_spArg (isOT_vr hG.f1 h) (sumN_children hG h).1, hsumM, spArg_app, hCdef]; rfl

theorem spArg_single (a b s y : T) : spArg a b (psi s y z) = step a b s y z := rfl

/-! ## 経路の値の形 -/

/-- **The shape of the path values (two rows, `t = 1`).** Below `r` the cofinality is `Ω_{μ+1}`
(`μ = v(r)`), `o(r) = ψ_μ(b)`, and from `r` up the values have their diagonal point at `ψ_{a′}(b)`,
`a′ ≤ μ`. -/
theorem twoRow_shape {M : Mat} {x r : Nat} (hG : Good2 M) (hx : x + 1 = M.length)
    (hr : par M 1 x = some r) (hb1 : 0 < entry M 1 x) :
    ∃ b, o2r M r = psi (vr M r) b z ∧ b ≠ z ∧ cof b = .big (vr M r) ∧
      (∀ p, Anc0 M p x → r < p → cof (o2r M p) = .big (vr M r)) ∧
      (∀ p, Anc0 M p x → p ≤ r → ∃ a', ¬ lt (vr M r) a' = true ∧ DiagAt a' b (vr M r) (o2r M p)) := by
  have hrx := par_lt M 1 x r hr
  have hA := anc0_of_par M 1 r x hr
  obtain ⟨m0, hm0, he⟩ := hG.f1 x hb1
  rw [hr] at hm0; cases hm0
  have hvx : vr M x = succ (vr M r) := by
    rw [vr_eq_nT hG.f1, vr_eq_nT hG.f1, ← he, nT_succ]
  have hlow : ∀ p, Anc0 M p x → r < p → lt (vr M r) (vr M p) = true := by
    intro p hp hrp
    have := par1_between hr p hp hrp
    rw [vr_eq_nT hG.f1, vr_eq_nT hG.f1]
    exact lt_nT (by omega)
  -- below `r`
  have partA : ∀ m p, x - p ≤ m → Anc0 M p x → r < p → cof (o2r M p) = .big (vr M r) := by
    intro m
    induction m with
    | zero =>
      intro p h1 hp _
      have : p = x := by have := hp.le; omega
      subst this
      rw [o2r_leaf hx (isOT_vr hG.f1 p), hvx]; exact cof_leaf _
    | succ m ih =>
      intro p hm hp hrp
      rcases Nat.eq_or_lt_of_le hp.le with heq | hlt
      · subst heq
        rw [o2r_leaf hx (isOT_vr hG.f1 p), hvx]; exact cof_leaf _
      obtain ⟨c, hc, hcA⟩ := anc0_child hp (by omega)
      have hpc := par_lt M 0 c p hc
      have hcc := ih c (by omega) hcA (by omega)
      obtain ⟨y, hy⟩ := o2r_sub hG c
      rw [o2r_frame hG hx hcA hc, hy, spArg_single]
      rw [hy] at hcc
      have hcot : isOT (psi (vr M c) y z) = true := by rw [← hy]; exact hG.ot c
      have hst := cof_step (a := vr M p) (b := bst M p c) hcot hcc
      have hne : step (vr M p) (bst M p c) (vr M c) y z ≠ z := by
        rcases step_cases (a := vr M p) (b := bst M p c) hcot with ⟨B, hB⟩ | ⟨h1, _, h3, _⟩
        · rw [hB]; intro h; exact absurd (app_eq_z h).2 (by simp)
        · rw [h1]; exact h3
      exact cof_psi_pass hne hst (hlow p hp hrp)
  -- at `r`
  have hrne : r ≠ x := by omega
  obtain ⟨c, hc, hcA⟩ := anc0_child hA hrne
  have hrc := par_lt M 0 c r hc
  have hcc := partA _ c (Nat.le_refl _) hcA hrc
  obtain ⟨y, hy⟩ := o2r_sub hG c
  have hcot : isOT (psi (vr M c) y z) = true := by rw [← hy]; exact hG.ot c
  rw [hy] at hcc
  refine ⟨step (vr M r) (bst M r c) (vr M c) y z, ?_, ?_, cof_step hcot hcc,
    fun p hp hrp => partA _ p (Nat.le_refl _) hp hrp, ?_⟩
  · rw [o2r_frame hG hx hcA hc, hy, spArg_single]
  · rcases step_cases (a := vr M r) (b := bst M r c) hcot with ⟨B, hB⟩ | ⟨h1, _, h3, _⟩
    · rw [hB]; intro h; exact absurd (app_eq_z h).2 (by simp)
    · rw [h1]; exact h3
  · -- from `r` up
    generalize hbdef : step (vr M r) (bst M r c) (vr M c) y z = b
    have hbne : b ≠ z := by
      rw [← hbdef]
      rcases step_cases (a := vr M r) (b := bst M r c) hcot with ⟨B, hB⟩ | ⟨h1, _, h3, _⟩
      · rw [hB]; intro h; exact absurd (app_eq_z h).2 (by simp)
      · rw [h1]; exact h3
    have hbc : cof b = .big (vr M r) := by rw [← hbdef]; exact cof_step hcot hcc
    have hro : o2r M r = psi (vr M r) b z := by rw [o2r_frame hG hx hcA hc, hy, spArg_single, hbdef]
    have hμμ : ¬ lt (vr M r) (vr M r) = true := by simp [Bool.eq_false_iff.mpr (lt_irrefl' _)]
    have partC : ∀ m p, r - p ≤ m → Anc0 M p x → p ≤ r →
        ∃ a', ¬ lt (vr M r) a' = true ∧ DiagAt a' b (vr M r) (o2r M p) := by
      intro m
      induction m with
      | zero =>
        intro p h1 _ h3
        have : p = r := by omega
        subst this
        exact ⟨vr M p, hμμ, by rw [hro]; exact DiagAt.here hbne hbc hμμ⟩
      | succ m ih =>
        intro p hm hp hpr
        rcases Nat.eq_or_lt_of_le hpr with heq | hlt
        · subst heq
          exact ⟨vr M p, hμμ, by rw [hro]; exact DiagAt.here hbne hbc hμμ⟩
        obtain ⟨c', hc', hc'A⟩ := anc0_child hp (by omega)
        have hpc' := par_lt M 0 c' p hc'
        have hc'r : c' ≤ r := by
          rcases anc0_total hc'A hA with h' | h'
          · exact h'.le
          · rcases Nat.eq_or_lt_of_le h'.le with h2 | h2
            · omega
            · have := (anc0_par h' (by omega) hc').le; omega
        obtain ⟨a', ha', hD⟩ := ih c' (by omega) hc'A hc'r
        obtain ⟨y', hy'⟩ := o2r_sub hG c'
        have hc'ot : isOT (psi (vr M c') y' z) = true := by rw [← hy']; exact hG.ot c'
        rw [hy'] at hD
        rw [o2r_frame hG hx hc'A hc', hy', spArg_single]
        rcases step_cases (a := vr M p) (b := bst M p c') hc'ot with ⟨B, hB⟩ | ⟨h1, _, h3, htr⟩
        · refine ⟨a', ha', ?_⟩
          rw [hB]
          have hD2 := DiagAt.append B (by simp) hD
          exact DiagAt.arg (fun h => absurd (app_eq_z h).2 (by simp)) hD2.not_succ hD2
        · rw [h1]
          by_cases hne : vr M c' = a' ∧ y' = b
          · obtain ⟨rfl, rfl⟩ := hne
            have hvp : ¬ lt (vr M r) (vr M p) = true := by
              intro hlt'
              have h4 := not_lt_of_trig htr.2
              exact ha' (lt_of_lt_of_le hlt' (le_of_not_gt h4))
            exact ⟨vr M p, hvp, DiagAt.here hbne hbc hvp⟩
          · have hDy := DiagAt.arg_inv hD h3 hne
            exact ⟨a', ha', DiagAt.arg h3 hDy.not_succ hDy⟩
    exact fun p hp hpr => partC _ p (Nat.le_refl _) hp hpr

/-- The argument of a collapse. -/
def argOf : T → T
  | z => z
  | psi _ b _ => b

/-- **The two-row `t = 1` chain with the path shape built in.** -/
theorem twoRow_chain' {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hG : Good2 M) (hb1 : 0 < entry M 1 (M.length - 1))
    (hF1 : ∀ k, 1 ≤ k → F1 (expand M k))
    (hSa : ∀ a', ¬ lt (vr M r) a' = true →
      SeedOK a' (argOf (o2r M r)) (vr M r) (o2r (expand M 1) r))
    (hFr : ∀ m h p, Anc0 M p (M.length - 1) → par M 0 p = some h →
      FrameD (vr M h) (bst M h p) (o2r M p)
        (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) m)) :
    ∀ k, 2 ≤ k →
      o2r (expand M k) r = gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) (k - 1) ∧
      ∀ h, Anc0 M h (M.length - 1) →
        o2r (expand M k) h =
          fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) (k - 2)) := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hr1 : par M 1 (M.length - 1) = some r := by have h := hr; rw [ht1] at h; exact h
  obtain ⟨b, hrv, hb, hcb, hbelow, habove⟩ := twoRow_shape hG hx hr1 hb1
  have hbarg : argOf (o2r M r) = b := by rw [hrv]; rfl
  rw [hbarg] at hSa hFr ⊢
  have hμμ : ¬ lt (vr M r) (vr M r) = true := by simp [Bool.eq_false_iff.mpr (lt_irrefl' _)]
  apply twoRow_chain hM hz hr ht1 hG hb1 hrv hb hcb (hSa _ hμμ) hF1 _ hFr
  intro p hp
  rcases Nat.lt_or_ge r p with h1 | h1
  · exact Or.inl (hbelow p hp h1)
  · obtain ⟨a', ha', hD⟩ := habove p hp h1
    exact Or.inr ⟨a', hSa a' ha', hD⟩

end Ytosk
