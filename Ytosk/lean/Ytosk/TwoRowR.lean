/-
**2 行・t = 1・q = r の組み立て。**

q = r では o_M(r) = ψ_μ(b + Ω_{μ+1})（b は x の前の兄弟の状態）。r より上で引き上げが起きると、ζ が鎖の次の項にずれる
（`frame_fsD_shift`）。経路上の各列 h で o_{M[k]}(h) = fsD(o_M(h), Z_j)（j は列ごと、Z は始点 γ_1 = ψ_μ(b) の鎖）。
-/
import Ytosk.TwoRowQ

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {x q : Nat} {μ : T} (hG : Good2 M) (hx : x + 1 = M.length)
  (hq : par M 0 x = some q) (hvx : vr M x = succ μ)
include hG hx hq hvx

theorem pvne1 {d : Nat} (hd : Anc0 M d x) : o2r M d ≠ one := by
  rcases Nat.eq_or_lt_of_le hd.le with h | h
  · subst h
    rw [o2r_leaf hx (isOT_vr hG.f1 _), hvx]
    intro h; simp [one] at h
    exact absurd (app_eq_z h).2 (by simp [one])
  · obtain ⟨w, hw⟩ := o2r_sub hG d
    have hne := argOf_path_ne_z hG hx hd h
    rw [hw] at hne ⊢
    intro h'; simp [one] at h'; exact hne h'.2

theorem isSucc_argOf' {d : Nat} (hd : Anc0 M d x) (hdx : d < x) :
    isSucc (argOf (o2r M d)) = false := by
  obtain ⟨d', hd'A, _, hl, _⟩ := path_last_gen hG hx hq d hd hdx
  unfold isSucc
  rw [hl]
  simpa using pvne1 hG hx hq hvx hd'A

theorem fsD_path_value' {d : Nat} {ζ : T} (hd : Anc0 M d x) (hdx : d < x) :
    fsD (o2r M d) ζ = psi (vr M d) (fsD (argOf (o2r M d)) ζ) z := by
  obtain ⟨w, hw⟩ := o2r_sub hG d
  have hne := argOf_path_ne_z hG hx hd hdx
  have hs := isSucc_argOf' hG hx hq hvx hd hdx
  rw [hw] at hne hs ⊢
  exact fsD_psi hne hs ζ

/-- **Condition (L) away from `q`'s argument** (no assumption on `v(q)`). -/
theorem L_gen {p : Nat} {ζ : T} (hp : Anc0 M p x) {s y : T}
    (hc : o2r M p = psi s y z) (hy : y ≠ z) (hne : y ≠ argOf (o2r M q)) :
    ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 ζ ≠ z) ∧
    ((split y (psi (succ s) z z)).2 = z → (split (fsD y ζ) (psi (succ s) z z)).2 = z) := by
  have hpx : p < x := by
    rcases Nat.eq_or_lt_of_le hp.le with h' | h'
    · exfalso; subst h'
      rw [o2r_leaf hx (isOT_vr hG.f1 _)] at hc; cases hc; exact hy rfl
    · exact h'
  obtain ⟨d, hdA, hpd, hl, hdx⟩ := path_last_gen hG hx hq p hp hpx
  rw [hc] at hl hdx
  change last y = o2r M d at hl
  have hdne : d ≠ x := fun hd => hne (hdx hd)
  have hdx' : d < x := by have := hdA.le; omega
  have hfe := fsD_path_value' hG hx hq hvx (ζ := ζ) hdA hdx'
  obtain ⟨w, hw⟩ := o2r_sub hG d
  have hwne : w ≠ z := by have := argOf_path_ne_z hG hx hdA hdx'; rw [hw] at this; exact this
  have hLne : o2r M d ≠ z := by rw [hw]; simp
  have hfne : fsD (o2r M d) ζ ≠ z := by rw [hfe]; simp
  have hbpl := split_app (psi (succ s) z z) y
  have hpge := split_fst_ge (psi (succ s) z z) y
  constructor
  · intro hlo
    generalize hP : split y (psi (succ s) z z) = pr at hbpl hlo ⊢
    obtain ⟨hi, lo⟩ := pr
    simp only at hbpl hlo ⊢
    have hll : last lo = o2r M d := by rw [← hl, ← hbpl, last_app hi hlo]
    rw [← init_app_last lo, hll, fsD_app _ hLne]
    intro h'; exact hfne (app_eq_z h').2
  · intro hlo
    have hyhi : y = (split y (psi (succ s) z z)).1 := by rw [hlo, app_z_right] at hbpl; exact hbpl.symm
    rw [← init_app_last y, hl, fsD_app _ hLne, hfe, hw]
    have hsum : ∀ q ∈ summands y, ¬ q < psi (succ s) z z := by
      intro q hq; rw [hyhi] at hq; exact hpge q hq
    have hB : ∀ q ∈ summands (app (init y) (psi (vr M d) (fsD (argOf (psi (vr M d) w z)) ζ) z)),
        ¬ q < psi (succ s) z z := by
      intro q hq
      rw [summands_app] at hq
      rcases List.mem_append.mp hq with hq | hq
      · apply hsum
        rw [← init_app_last y, summands_app]; exact List.mem_append_left _ hq
      · simp [summands] at hq; subst hq
        have hL := hsum _ (last_mem hy)
        rw [hl, hw, psi_lt_om_iff] at hL
        rw [psi_lt_om_iff]; exact hL
    have := split_app_of (B := app (init y) (psi (vr M d) (fsD (argOf (psi (vr M d) w z)) ζ) z))
      (X := z) hB (Or.inl rfl)
    rw [app_z_right] at this
    rw [this]

end

/-! ## 本体 -/

/-- `M[1]`'s value at `r` when `q = r`: `ψ_μ(b)` with `b` the state of the earlier siblings of `x`. -/
theorem o2r_take_r_qr {M : Mat} {r : Nat} (hG : Good2 M) (hx1 : 2 ≤ M.length)
    (hqr : par M 0 (M.length - 1) = some r) :
    o2r (M.take (M.length - 1)) r = psi (vr M r) (bst M r (M.length - 1)) z := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hrx := par_lt M 0 _ r hqr
  have hle := children_le_of_anc_last (Anc0.refl (M.length - 1)) hx hqr
  have hcmem : M.length - 1 ∈ children M r := mem_children_iff.mpr ⟨by omega, hqr⟩
  have hsplit := split_last_max _ (M.length - 1) (children_sorted M r) hcmem hle
  set C := (children M r).filter (fun d => decide (d < M.length - 1)) with hCdef
  have hch : children (M.take (M.length - 1)) r = C := by
    rw [children_take, hsplit, List.filter_append]
    simp [hCdef]
  have hoff : ∀ d ∈ C, o2r (M.take (M.length - 1)) d = o2r M d := by
    intro d hd
    rw [hCdef, List.mem_filter] at hd
    have hdc : d < M.length - 1 := by simpa using hd.2
    have hdp := mem_children_iff.mp hd.1
    apply o2r_take_off hx d hdc
    intro hdA
    rcases Nat.eq_or_lt_of_le hdA.le with h' | h'
    · omega
    · have := (anc0_par hdA (by omega) hqr).le; have := par_lt M 0 d r hdp.2; omega
  have hdM := hG.dec r
  simp only [hsplit, List.map_append, List.map_cons, List.map_nil] at hdM
  have hS := sumN_dec (C.map (o2r M)) (fun t ht => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hG i) (List.pairwise_append.mp hdM).1
  rw [o2r_eq, hch, List.map_congr_left hoff, vr_take M r hrx]
  show add (sp (sf (vr M r)) z (sf _)) (sf z) = _
  rw [sf_ot (isOT_vr hG.f1 r), sf_ot hS.1, sp_eq_spArg]
  rfl

/-- **The two-row `t = 1`, `q = r` expansion.** Every path value after expansion is
`fsD(o_M(h), Z_j)` for a member `Z_j` of the chain with seed `γ_1 = ψ_μ(b)` (the index moves up the chain
where a hoisting happens). Remaining hypothesis: rewriting persists (from W2 or PRE). -/
theorem twoRow_qr {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hG : Good2 M) (hb1 : 0 < entry M 1 (M.length - 1))
    (hqr : par M 0 (M.length - 1) = some r) (hn : 2 ≤ n)
    (hY : ∃ j, o2r (expand M n) (M.length - 1) =
      gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) j)
    (hP : ∀ h p s y, Anc0 M p (M.length - 1) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
      ∀ ζ, fsD y z < fsD y ζ → lt (bst M h p) (fsD y ζ) = true) :
    ∀ h, Anc0 M h (M.length - 1) → ∃ j,
      o2r (expand M n) h = fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) j) ∧
      isOT (fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) j)) = true ∧
      fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) j) < o2r M h := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have ht : 0 < TRIO.srow M (M.length - 1) := by omega
  have hr1 : par M 1 (M.length - 1) = some r := by have h := hr; rw [ht1] at h; exact h
  have hrx := par_lt M 1 _ r hr1
  obtain ⟨m0, hm0, he⟩ := hG.f1 (M.length - 1) hb1
  rw [hr1] at hm0; cases hm0
  have hvx : vr M (M.length - 1) = succ (vr M r) := by
    rw [vr_eq_nT hG.f1, vr_eq_nT hG.f1, ← he, nT_succ]
  obtain ⟨B, hrv, hBz, hcb, _, habove⟩ := twoRow_shape hG hx hr1 hb1
  have hbarg : argOf (o2r M r) = B := by rw [hrv]; rfl
  generalize hμdef : vr M r = μ at hrv hcb habove hvx hY ⊢
  generalize hbdef : bst M r (M.length - 1) = b
  -- `B = b + Ω_{μ+1}`
  have hΩ : o2r M (M.length - 1) = psi (succ μ) z z := by
    rw [o2r_leaf hx (isOT_vr hG.f1 _), hvx]
  have hbge : ∀ q ∈ summands b, psi (succ μ) z z ≤ q := by
    rw [← hbdef, ← hΩ]; exact bst_summands_ge hG hx (Anc0.refl _) hqr
  have hbge' : ∀ q ∈ summands b, ¬ q < psi (succ μ) z z := fun q hq h =>
    lt_irrefl' _ (lt_of_lt_of_le h (hbge q hq))
  have hBeq : B = app b (psi (succ μ) z z) := by
    have := o2r_frame hG hx (Anc0.refl _) hqr
    rw [hrv, hΩ, spArg_single, hμdef, hbdef] at this
    unfold step at this
    rw [if_neg (by simp [lt])] at this
    cases this
    exact add_eq_app_of_ge ⟨_, _, rfl⟩ b hbge
  -- the seed `γ_1 = ψ_μ(b) = ψ_μ(B[0])`
  have hΩz : psi (succ μ) z z ≠ z := by simp
  have hfsB : ∀ ζ, fs B ζ = app b ζ := by
    intro ζ; rw [hBeq, fs_app b hΩz, fs_Om_succ]
  have hγ : o2r (expand M 1) r = psi μ (fs B z) z := by
    rw [expand_one_eq hM hz hr ht1, o2r_take_r_qr hG hM hqr, hμdef, hbdef, hfsB, app_z_right]
  rw [hbarg]
  generalize hγdef : o2r (expand M 1) r = γ1 at hγ hY
  rw [hbarg] at hY
  have hot : isOT (psi μ B z) = true := by rw [← hrv]; exact hG.ot r
  have hμμ : ¬ lt μ μ = true := by simp [Bool.eq_false_iff.mpr (lt_irrefl' _)]
  have hSa : ∀ a', ¬ lt μ a' = true → isOT (psi a' B z) = true → SeedOK a' B μ γ1 := by
    intro a' ha' hot'; rw [hγ]; exact seedOK_gam1 hot' hcb ha'
  have hS0 := hSa μ hμμ hot
  have hZs : ∀ j, gamS μ B γ1 (j + 1) = psi μ (app b (gamS μ B γ1 j)) z := by
    intro j; show psi μ (fs B _) z = _; rw [hfsB]
  have hZne : ∀ j, gamS μ B γ1 j ≠ z := by
    intro j; cases j with
    | zero => show γ1 ≠ z; rw [hγ]; simp
    | succ j => rw [hZs]; simp
  have hZlt := gamS_lt_om hot hcb hμμ hS0
  have hZot := gamS_ot hot hcb hμμ hS0
  have hZform : ∀ j, ∃ lo, gamS μ B γ1 j = psi μ (app b lo) z ∧
      (lo = z ∨ head lo < psi (succ μ) z z) := by
    intro j; cases j with
    | zero => exact ⟨z, by show γ1 = _; rw [hγ, hfsB], Or.inl rfl⟩
    | succ j => exact ⟨_, hZs j, Or.inr (lt_of_le_of_lt (head_le_self _) (hZlt j))⟩
  have hfsDr : ∀ ζ, fsD (psi μ B z) ζ = psi μ (app b ζ) z := by
    intro ζ; rw [fsD_here hBz hcb, hfsB]
  -- the path theorem with the chain
  apply o2r_expand_path_gen hM hz hr ht hn hG (gamS μ B γ1)
  · obtain ⟨j, hj⟩ := hY
    refine ⟨j, ?_, ?_, ?_⟩
    · rw [hj, hΩ, fsD_leaf (isSucc_succ μ)
        (by intro h'; have := isSucc_succ μ; rw [h'] at this; simp [isSucc, last, one] at this)]
    · rw [hΩ, fsD_leaf (isSucc_succ μ)
        (by intro h'; have := isSucc_succ μ; rw [h'] at this; simp [isSucc, last, one] at this)]
      exact hZot j
    · rw [hΩ, fsD_leaf (isSucc_succ μ)
        (by intro h'; have := isSucc_succ μ; rw [h'] at this; simp [isSucc, last, one] at this)]
      exact hZlt j
  · intro h p j hp hph hokOT hoklt
    -- standardness and descent for the parent from the seeded Lemma 3.3
    have hOKpar : ∀ j', isOT (fsD (o2r M h) (gamS μ B γ1 j')) = true ∧
        fsD (o2r M h) (gamS μ B γ1 j') < o2r M h := by
      intro j'
      have hhx : h < M.length - 1 := by have := par_lt M 0 p h hph; have := hp.le; omega
      have hhA : Anc0 M h (M.length - 1) := anc0_up hph hp
      have hhr : h ≤ r := (anc0_par hhA (by omega) hqr).le
      obtain ⟨a'', ha'', hD''⟩ := habove h hhA hhr
      obtain ⟨h1, h2⟩ := fsD_seed (hSa a'' ha'' (DiagAt.ot_node hD'' (hG.ot h))) hD'' (hG.ot h) j'
      exact ⟨h1, h2.1⟩
    rcases Nat.eq_or_lt_of_le hp.le with hpx | hpx
    · -- the frame `(r, x)`
      subst hpx
      rw [hqr] at hph; cases hph
      refine ⟨j, ?_, hOKpar j⟩
      have hleafv : fsD (o2r M (M.length - 1)) (gamS μ B γ1 j) = gamS μ B γ1 j := by
        rw [hΩ, fsD_leaf (isSucc_succ μ)
          (by intro h'; have := isSucc_succ μ; rw [h'] at this; simp [isSucc, last, one] at this)]
      rw [hleafv, hrv, hfsDr, hμdef, hbdef]
      obtain ⟨lo, hlo1, hlo2⟩ := hZform j
      have := spArg_rx (hZot j |> fun h' => by rw [hlo1] at h'; exact h') hbge' rfl hlo2
      rw [hlo1, this]
    · have hpr : p ≤ r := (anc0_par hp (by omega) hqr).le
      obtain ⟨a', ha', hD⟩ := habove p hp hpr
      obtain ⟨y, hy⟩ := o2r_sub hG p
      have hoh := o2r_frame hG hx hp hph
      have hyne : y ≠ z := by
        have := argOf_path_ne_z hG hx hp hpx; rw [hy] at this; exact this
      have hpot : isOT (psi (vr M p) y z) = true := by rw [← hy]; exact hG.ot p
      rw [hy] at hD hoh hokOT hoklt ⊢
      -- whether `p` is the diagonal node itself
      have hdiag : y = B → vr M p = a' := by
        intro hyB
        rw [hyB] at hD
        cases hD with
        | here => rfl
        | arg _ _ h' => exact absurd h'.size_lt (Nat.lt_irrefl _)
        | sub _ _ _ => exact absurd rfl hBz
      by_cases hsh : y = B ∧ vr M p = μ ∧
          (lt (bst M h p) y = true ∧ lt (psi (vr M h) z z) (psi (vr M p) y z) = true)
      · -- the shift: the index moves one step up the chain
        obtain ⟨hyB, hvp, htr⟩ := hsh
        have hbη : lt (bst M h p) (app b (gamS μ B γ1 j)) = true := by
          have h1 := hP h p (vr M p) y hp hph hy htr.1 htr.2 (gamS μ B γ1 j) (by
            rw [hyB, fsD_eq_fs hcb, fsD_eq_fs hcb, hfsB, hfsB, app_z_right]; exact lt_app_of (hZne j))
          rw [hyB, fsD_eq_fs hcb, hfsB] at h1; exact h1
        rw [hyB, hvp] at htr hpot hoh
        refine ⟨j + 1, ?_, hOKpar (j + 1)⟩
        rw [hyB, hvp, hfsDr, ← hZs, hoh]
        have hlo : (split B (psi (succ μ) z z)).2 = z := by
          rw [hBeq]
          have := split_app_of (B := app b (psi (succ μ) z z)) (X := z) (t := psi (succ μ) z z)
            (by intro q hq; rw [summands_app] at hq
                rcases List.mem_append.mp hq with hq | hq
                · exact hbge' q hq
                · simp [summands] at hq; subst hq; exact lt_irrefl' _) (Or.inl rfl)
          rw [app_z_right] at this; rw [this]
        have hsne : spArg (vr M h) (bst M h p) (psi μ B z) = B := by
          rw [spArg_single]; unfold step; rw [if_pos htr, H_eq hpot, if_pos hlo, app_z_right]
          have := split_app (psi (succ μ) z z) B; rw [hlo, app_z_right] at this; exact this
        rw [fsD_psi (by rw [hsne]; exact hBz) (by rw [hsne]; exact not_succ_of_cof_big hcb)]
        congr 1
        rw [hZs]
        have hpot' : isOT (psi μ (app b (psi (succ μ) z z)) z) = true := by rw [← hBeq]; exact hpot
        have htr' : lt (bst M h p) (app b (psi (succ μ) z z)) = true ∧
            lt (psi (vr M h) z z) (psi μ (app b (psi (succ μ) z z)) z) = true := by
          rw [← hBeq]; exact htr
        have hfr := frame_fsD_shift hpot' (by rw [← hZs]; exact hZot (j + 1)) htr' hbge' hμμ (hZlt j)
          (hZne j) hbη
        rw [← hBeq] at hfr
        exact hfr.symm
      · -- no shift: the same index
        refine ⟨j, ?_, hOKpar j⟩
        have hzZ : z < gamS μ B γ1 j := by
          obtain ⟨lo, hlo1, _⟩ := hZform j; rw [hlo1]; exact T.z_lt_psi _ _ _
        have hsumB : ∀ s', s' < μ → ∀ q ∈ summands B, ¬ q < psi (succ s') z z := by
          intro s' hs' q hq hlt
          have hΩs : psi (succ s') z z < psi (succ μ) z z := omS_lt_omS hs'
          rw [hBeq, summands_app] at hq
          rcases List.mem_append.mp hq with hq | hq
          · exact lt_irrefl' _ (lt_trans hlt (lt_of_lt_of_le hΩs (hbge q hq)))
          · simp [summands] at hq; subst hq; exact lt_irrefl' _ (lt_trans hlt hΩs)
        have hZge : ∀ s', s' < μ → ¬ gamS μ B γ1 j < psi (succ s') z z := by
          intro s' hs' hlt
          obtain ⟨lo, hlo1, _⟩ := hZform j
          rw [hlo1, psi_lt_om_iff] at hlt
          exact lt_irrefl' _ (lt_of_lt_of_le hs' (lt_succ_iff.mp hlt))
        have hFD : FrameD (vr M h) (bst M h p) (o2r M p) (gamS μ B γ1 j) := by
          apply frameD_path hG hx hp hph
          · rw [hy]; exact ⟨hokOT, hoklt⟩
          · have := pvne1 hG hx hqr hvx hp; rw [hy] at this ⊢; exact isSucc_psi_nz this
          · intro s' y' hc' _
            have := isSucc_argOf' hG hx hqr hvx hp hpx; rw [hc'] at this; exact this
          · intro s' hc'; exfalso; rw [hy] at hc'; cases hc'; exact hyne rfl
          · intro s' y' hc' ht1' ht2'
            rw [hy] at hc'; cases hc'
            apply hP h p (vr M p) y hp hph hy ht1' ht2'
            by_cases hyB : y = B
            · rw [hyB, fsD_eq_fs hcb, fsD_eq_fs hcb, hfsB, hfsB, app_z_right]
              exact lt_app_of (hZne j)
            · have hDy := DiagAt.arg_inv hD hyne (fun h' => hyB h'.2)
              exact hDy.fsD_mono hzZ
          · intro s' y' hc' ht1' ht2'
            rw [hy] at hc'; cases hc'
            by_cases hyB : y = B
            · have hvpa := hdiag hyB
              have hvpμ : vr M p ≠ μ := fun h' => hsh ⟨hyB, h', ht1', ht2'⟩
              have hvplt : vr M p < μ := by
                have h3 : ¬ μ < vr M p := by rw [hvpa]; exact ha'
                rcases lt_trichotomy' (vr M p) μ with h4 | h4 | h4
                · exact h4
                · exact absurd h4 hvpμ
                · exact absurd h4 h3
              rw [hyB]
              have hloB : (split B (psi (succ (vr M p)) z z)).2 = z := by
                have := split_app_of (B := B) (X := z) (hsumB _ hvplt) (Or.inl rfl)
                rw [app_z_right] at this; rw [this]
              refine ⟨fun h' => absurd hloB h', fun _ => ?_⟩
              rw [fsD_eq_fs hcb, hfsB]
              have hB' : ∀ q ∈ summands (app b (gamS μ B γ1 j)), ¬ q < psi (succ (vr M p)) z z := by
                intro q hq
                rw [summands_app] at hq
                rcases List.mem_append.mp hq with hq | hq
                · apply hsumB _ hvplt; rw [hBeq, summands_app]; exact List.mem_append_left _ hq
                · obtain ⟨lo, hlo1, _⟩ := hZform j
                  rw [hlo1] at hq; simp [summands] at hq; subst hq
                  rw [← hlo1]; exact hZge _ hvplt
              have := split_app_of (B := app b (gamS μ B γ1 j)) (X := z) hB' (Or.inl rfl)
              rw [app_z_right] at this; rw [this]
            · exact L_gen hG hx hqr hvx hp hy hyne (by rw [hrv]; exact hyB)
        rw [hy] at hFD
        rw [hoh]
        exact (node_fsD hFD).symm

/-- **The two-row `t = 1`, `q = r` expansion, for every `k ≥ 2`.** Remaining hypothesis: rewriting
persists (from W2 or PRE). -/
theorem twoRow_qr_all {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hG : Good2 M) (hb1 : 0 < entry M 1 (M.length - 1))
    (hr1 : TRIO.r1ok M) (hz0 : TRIO.z0ok M)
    (hqr : par M 0 (M.length - 1) = some r)
    (hP : ∀ h p s y, Anc0 M p (M.length - 1) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
      ∀ ζ, fsD y z < fsD y ζ → lt (bst M h p) (fsD y ζ) = true) :
    ∀ k, 2 ≤ k → ∀ h, Anc0 M h (M.length - 1) → ∃ j,
      o2r (expand M k) h = fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) j) ∧
      isOT (fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) j)) = true ∧
      fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) j) < o2r M h := by
  have hx : M.length - 1 + 1 = M.length := by omega
  have hrx := par_lt M 0 _ r hqr
  have hA : Anc0 M r (M.length - 1) := Anc0.step hqr (Anc0.refl r)
  have hr1' : par M 1 (M.length - 1) = some r := by have h := hr; rw [ht1] at h; exact h
  obtain ⟨B, hrv, hBz, hcb, _, _⟩ := twoRow_shape hG hx hr1' hb1
  -- copy shift at the copy root
  have hgexp := fun k => expand_eq_gexp_t1 M k hM hz hr ht1
  have hlen : r + (M.length - 1 - r) + 1 = M.length := by omega
  have hL : 0 < M.length - 1 - r := by omega
  have hA' : Anc0 M r (r + (M.length - 1 - r)) := by
    rw [show r + (M.length - 1 - r) = M.length - 1 by omega]; exact hA
  have hd0e : entry M 0 (r + (M.length - 1 - r)) =
      entry M 0 r + (entry M 0 (M.length - 1) - entry M 0 r) := by
    rw [show r + (M.length - 1 - r) = M.length - 1 by omega]
    have := anc0_interval hA (M.length - 1) hrx (Nat.le_refl _); omega
  have hshift : ∀ k, 2 ≤ k → o2r (expand M k) (M.length - 1) = o2r (expand M (k - 1)) r := by
    intro k hk
    have h1 := o2r_gexp_shift hlen hL hA' hd0e hk
      (by rw [← hgexp]; exact F1_expand hr1 hz0 hM k)
      (by rw [← hgexp]; exact F1_expand hr1 hz0 hM (k - 1)) 0
      (by have := Nat.mul_le_mul_right (M.length - 1 - r) (show 1 ≤ k - 1 by omega); simp at this; omega)
    rw [hgexp, hgexp]
    simpa [show r + (M.length - 1 - r) = M.length - 1 by omega] using h1
  -- the chain value at `r` after one more step
  have hrstep : ∀ j, fsD (o2r M r) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) j) =
      gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) (j + 1) := by
    intro j; rw [hrv, fsD_here hBz hcb]; show _ = psi (vr M r) (fs B _) z
    rw [show argOf (psi (vr M r) B z) = B from rfl]
  have main : ∀ k, 2 ≤ k → (∃ j, o2r (expand M k) (M.length - 1) =
      gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) j) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact ⟨0, by rw [hshift 2 (Nat.le_refl _)]; rfl⟩
    | succ k hk ih =>
      obtain ⟨j, hj, _, _⟩ := twoRow_qr hM hz hr ht1 hG hb1 hqr hk ih hP r hA
      exact ⟨j + 1, by rw [hshift (k + 1) (by omega), show k + 1 - 1 = k by omega, hj, hrstep]⟩
  intro k hk
  exact twoRow_qr hM hz hr ht1 hG hb1 hqr hk (main k hk) hP

/-- **The two-row `t = 1`, `q = r` expansion from the invariant PRE.** -/
theorem twoRow_qr_PRE {M : Mat} {r : Nat} (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    (hr : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r)
    (ht1 : TRIO.srow M (M.length - 1) = 1) (hG : Good2 M) (hb1 : 0 < entry M 1 (M.length - 1))
    (hr1 : TRIO.r1ok M) (hz0 : TRIO.z0ok M)
    (hqr : par M 0 (M.length - 1) = some r)
    (hPRE : ∀ h p s y, Anc0 M p (M.length - 1) → par M 0 p = some h → o2r M p = psi s y z →
      lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
      bst M h p ≠ z → ∃ rest, y = app (bst M h p) rest ∧ rest ≠ z) :
    ∀ k, 2 ≤ k → ∀ h, Anc0 M h (M.length - 1) → ∃ j,
      o2r (expand M k) h = fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) j) ∧
      isOT (fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) j)) = true ∧
      fsD (o2r M h) (gamS (vr M r) (argOf (o2r M r)) (o2r (expand M 1) r) j) < o2r M h :=
  twoRow_qr_all hM hz hr ht1 hG hb1 hr1 hz0 hqr (fun h p s y hp hph hc ht1' ht2' ζ hmono =>
    trig_persist_of_pre hmono (hPRE h p s y hp hph hc ht1' ht2'))

end Ytosk
