/-
**3 行・t = 0・n ≥ 2: r より前の D の列の値が標準形（hOTD）を、引数の ◁ から。**

実測（C′ の標本、n = 2, 3、69572 件、例外 0）: N = M[n] の D の o の列 i（v は変わらない）では、
o_N(i) = ψ_a(X′)、o_M(i) = ψ_a(X) の引数どうしが X′ ◁ X。したがって `ot_parent_lhd` で ψ_a(X′) は標準形。

- 枠 1 段（`node_arg_lhd`）: 子の引数が y′ ◁ y で、組が型 A（Ω_{s+1} 以上の部分が同じで N の低い部分が 0 でない）か
  型 B（どちらも低い部分が 0）なら、親の引数も ◁。M で書き換えるとき N でも書き換える、を仮定する。
- 始点 g（`s1_core_arg`）: 写しの根が並ぶ枠。中間の値 ψ_a(B + O·n) は基本列の項で、引数のレベルでも基本列の項。
-/
import Ytosk.V3T0M

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## 型 A・B -/

/-- **The class of a pair of arguments** at the level `s` (`θ = Ω_{s+1}`):
(A) the same part above `θ` and a nonzero low part in the new one; (B) no low part in either, with a
rewrite of the old frame also one of the new frame (`hB`); (C) the new one is the high part of the old one. -/
def ClsABC (B s y' y : T) (trigM : Prop) : Prop :=
  ((split y' (psi (succ s) z z)).1 = (split y (psi (succ s) z z)).1 ∧ (split y' (psi (succ s) z z)).2 ≠ z) ∨
  ((split y' (psi (succ s) z z)).2 = z ∧ (split y (psi (succ s) z z)).2 = z ∧ (trigM → lt B y' = true)) ∨
  y' = (split y (psi (succ s) z z)).1

/-- The rewriting condition of a frame. -/
def Trig (a B s y : T) : Prop := lt B y = true ∧ lt (psi a z z) (psi s y z) = true

/-- **One frame at the level of the arguments**: the last child drops by `◁` in its argument (same
subscript, class A, B or C), or it is a bare `ψ_{s′}(0)` below `ψ_s(0)`. Then the new state is `◁` the
old one. -/
theorem node_arg_lhd {a B s s' y y' : T}
    (hc : isOT (psi s y z) = true) (hc' : isOT (psi s' y' z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hch : (s' = s ∧ Lhd z y' y ∧ ClsABC B s y' y (Trig a B s y)) ∨
      (y = z ∧ y' = z ∧ Lhd z s' s)) :
    Lhd z (step a B s' y' z) (step a B s y z) := by
  rcases hch with ⟨rfl, hl, hcl⟩ | ⟨rfl, rfl, hl⟩
  · have hyy : y' < y := hl.1
    have hpsi : Lhd z (psi s' y' z) (psi s' y z) := lhd_psi s' hl
    have hBc' : ∀ q ∈ summands B, psi s' y' z ≤ q := fun q hq => le_trans (le_of_lt hpsi.1) (hBc q hq)
    set θ := psi (succ s') z z with hθ
    have ey := split_app θ y
    have ey' := split_app θ y'
    -- a rewrite of the new frame is one of the old frame
    have hNM : (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) →
        (lt B y = true ∧ lt (psi a z z) (psi s' y z) = true) := fun h =>
      ⟨lt_trans (show B < y' from h.1) hyy, lt_trans (show psi a z z < psi s' y' z from h.2) hpsi.1⟩
    -- the second half of the rewriting condition passes down when `B < y′`
    have hdown : lt (psi a z z) (psi s' y z) = true → lt B y' = true →
        lt (psi a z z) (psi s' y' z) = true := by
      intro h2 hB'
      change psi a z z < psi s' y z at h2
      change psi a z z < psi s' y' z
      rcases psi_lt_psi_z_iff.mp h2 with h | ⟨rfl, _⟩
      · exact psi_lt_psi_z_iff.mpr (Or.inl h)
      · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt (z_le B) hB'⟩)
    by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s' y z) = true
    · by_cases ht' : lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true
      · -- both rewrite
        unfold step
        rw [if_pos ht', if_pos ht, H_eq hc', H_eq hc]
        rcases hcl with ⟨hhi, hlo'⟩ | ⟨hl0', hl0, _⟩ | hC
        · have hlo : (split y θ).2 ≠ z := by
            intro h0
            rw [h0, app_z_right] at ey
            have : (split y' θ).1 < y' := by
              have h := lt_app_of (x := (split y' θ).1) hlo'; rwa [ey'] at h
            rw [hhi, ey] at this
            exact absurd (lt_trans this hyy) (lt_irrefl' _)
          rw [if_neg hlo', if_neg hlo, hhi]
          exact lhd_app _ hpsi
        · rw [if_pos hl0', if_pos hl0, app_z_right, app_z_right]
          have e1 : (split y' θ).1 = y' := by rw [hl0', app_z_right] at ey'; exact ey'
          have e2 : (split y θ).1 = y := by rw [hl0, app_z_right] at ey; exact ey
          rw [e1, e2]; exact hl
        · -- class C: `y′` is the high part of `y`
          have hlo : (split y θ).2 ≠ z := by
            intro h0; rw [h0, app_z_right, ← hC] at ey; rw [ey] at hyy; exact absurd hyy (lt_irrefl' _)
          have hs' : split y' θ = (y', z) := by rw [hC]; exact split_hi_self θ y
          rw [hs', if_neg hlo]
          simp only [if_true, app_z_right]
          rw [← hC]
          exact lhd_of_lhdE_lt (lhdE_prefix _ _) (lt_app_of (by simp))
      · -- only the old frame rewrites: class C with `B = y′`
        rcases hcl with ⟨hhi, hlo'⟩ | ⟨_, _, htr⟩ | hC
        · exfalso; apply ht'
          have hBhi : B ≤ (split y θ).1 := B_le_hi hc ht.1 hBc
          have hB' : lt B y' = true := by
            show B < y'
            rw [← hhi] at hBhi
            refine lt_of_le_of_lt hBhi ?_
            have h := lt_app_of (x := (split y' θ).1) hlo'; rwa [ey'] at h
          exact ⟨hB', hdown ht.2 hB'⟩
        · exact absurd ⟨htr ht, hdown ht.2 (htr ht)⟩ ht'
        · have hBhi : B ≤ y' := by rw [hC]; exact B_le_hi hc ht.1 hBc
          have hBy : B = y' := by
            rcases (le_iff _ _).mp hBhi with h | h
            · exact absurd ⟨h, hdown ht.2 h⟩ ht'
            · exact h
          have hlo : (split y θ).2 ≠ z := by
            intro h0; rw [h0, app_z_right, ← hC] at ey; rw [ey] at hyy; exact absurd hyy (lt_irrefl' _)
          unfold step
          rw [if_neg ht', if_pos ht, H_eq hc, if_neg hlo, ← hC, add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc', hBy]
          exact lhd_app _ hpsi
    · -- the old frame does not rewrite, so neither does the new one
      have ht' : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) := fun h => ht (hNM h)
      unfold step
      rw [if_neg ht', if_neg ht, add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc, add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc']
      exact lhd_app _ hpsi
  · -- bare subscripts
    have hpsi : Lhd z (psi s' z z) (psi s z z) := lhd_psi_sub hl
    have hn : ∀ s0, ¬ (lt B z = true ∧ lt (psi a z z) (psi s0 z z) = true) := by
      rintro s0 ⟨h, _⟩; exact T.not_lt_z _ h
    unfold step
    rw [if_neg (hn s'), if_neg (hn s), add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc,
      add_eq_app_of_ge ⟨_, _, rfl⟩ B (fun q hq => le_trans (le_of_lt hpsi.1) (hBc q hq))]
    exact lhd_app _ hpsi

/-- `fs` of `ψ_a(X)` goes into the argument when `X` has cofinality `ω`. -/
theorem fs_psi_omega {a X η : T} (hX : X ≠ z) (hs : isSucc X = false) (hc : cof X = .omega) :
    fs (psi a X z) η = psi a (fs X η) z := by
  conv => lhs; unfold fs
  rw [if_neg hX, if_neg (by rw [hs]; simp), hc]

/-- A sum ending with `ψ_v(b + 1)` has cofinality `ω` and is not a successor. -/
theorem cof_app_succ_end (P v b : T) :
    app P (psi v (app b one) z) ≠ z ∧ isSucc (app P (psi v (app b one) z)) = false ∧
      cof (app P (psi v (app b one) z)) = .omega := by
  have hcz : psi v (app b one) z ≠ z := by simp
  have hne : app b one ≠ z := fun h => absurd (app_eq_z h).2 (by simp [one])
  have hs1 : isSucc (app b one) = true := isSucc_succ b
  refine ⟨fun h => hcz (app_eq_z h).2, ?_, ?_⟩
  · rw [isSucc_app P hcz]; simp [isSucc, last, one]; exact fun _ h => hne h
  · rw [cof_app P hcz]; simp [cof, hne, hs1]

theorem mem_summands_app_end (s y : T) : ∀ P : T, psi s y z ∈ summands (app P (psi s y z))
  | z => by simp [summands]
  | psi a b c => by
    simp only [app_psi, summands, List.mem_cons]
    exact Or.inr (mem_summands_app_end s y c)

/-- The low part of `b + 1` (at `Ω_{v+1}`) is not empty. -/
theorem split_succ_lo_ne (v b : T) : (split (app b one) (psi (succ v) z z)).2 ≠ z := by
  intro h0
  have e := split_app (psi (succ v) z z) (app b one)
  rw [h0, app_z_right] at e
  have hmem : one ∈ summands (split (app b one) (psi (succ v) z z)).1 := by
    rw [e]; exact mem_summands_app_end z z b
  apply split_fst_ge _ _ one hmem
  show psi z z z < _; rw [psi_lt_psi_z_iff]; left
  exact lt_of_le_of_lt (z_le v) (lt_succ_self v)

/-- The state after the child `ψ_v(b + 1)` ends with that child. -/
theorem step_succ_end {a B v b : T} (hc : isOT (psi v (app b one) z) = true)
    (hBc : ∀ q ∈ summands B, psi v (app b one) z ≤ q) :
    ∃ P, step a B v (app b one) z = app P (psi v (app b one) z) := by
  unfold step
  split
  · rw [H_eq hc, if_neg (split_succ_lo_ne v b)]; exact ⟨_, rfl⟩
  · exact ⟨B, add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc⟩

/-- **The frame of `g` at the level of the arguments** (`t = 0`, `m ≥ 1` middle copies): the children
`ψ_v(Y0)` × m and then `X′ ◁ ψ_v(Y0 + 1)`, against the single child `ψ_v(Y0 + 1)`. -/
theorem s1_core_arg {a B v Y0 X' : T} {m : Nat} (hm : 1 ≤ m)
    (hOld : isOT (psi a (spArg a B (psi v (app Y0 one) z)) z) = true)
    (hX : isOT (psi v (app Y0 one) z) = true) (hO : isOT (psi v Y0 z) = true)
    (hBX : ∀ q ∈ summands B, psi v (app Y0 one) z ≤ q)
    (hX' : Single X') (hl : Lhd z X' (psi v (app Y0 one) z))
    (hX'O : X' ≤ psi v Y0 z)
    (hy' : ∀ s' y', X' = psi s' y' z → s' ≠ v → y' = z) :
    Lhd z (spArg a (spArg a B (mulT (psi v Y0 z) m)) X') (spArg a B (psi v (app Y0 one) z)) := by
  obtain ⟨s', y', rfl⟩ := hX'.2
  have hOX : psi v Y0 z < psi v (app Y0 one) z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one Y0⟩)
  set O := psi v Y0 z with hOdef
  set B' := spArg a B (mulT O m) with hB'
  have hnr := no_rw_after (a := a) (B := B) hO hm
  rw [← hOdef, ← hB'] at hnr
  have hB'O : ∀ q ∈ summands B', O ≤ q :=
    spArg_summands_ge ⟨v, Y0, rfl⟩ (mulT O m) B (isOT_mulT hO ⟨_, _, rfl⟩ m)
      (fun q hq => by rw [summands_mulT ⟨_, _, rfl⟩ m q hq])
      (fun q hq => le_trans (le_of_lt hOX) (hBX q hq))
  -- the middle value: `m + 1` copies, `B′ + O`
  have hMid : spArg a B (mulT O (m + 1)) = app B' O := by
    rw [mulT_succ', spArg_app, hOdef, spArg_single]
    unfold step; rw [if_neg hnr]
    exact add_eq_app_of_ge ⟨_, _, rfl⟩ _ hB'O
  -- the new value: `B′ + X′` (no rewrite)
  have hnew : ¬ (lt B' y' = true ∧ lt (psi a z z) (psi s' y' z) = true) := by
    rintro ⟨h1, h2⟩
    by_cases hs : s' = v
    · subst hs
      have hyy : y' ≤ Y0 := by
        rcases (le_iff _ _).mp hX'O with h | h
        · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact le_of_lt h
        · rw [hOdef] at h; simp only [psi.injEq] at h; rw [h.2.1]
      exact hnr ⟨lt_of_lt_of_le h1 hyy, lt_of_lt_of_le h2 hX'O⟩
    · have := hy' s' y' rfl hs
      rw [this] at h1; exact T.not_lt_z _ h1
  have hN : spArg a B' (psi s' y' z) = app B' (psi s' y' z) := by
    rw [spArg_single]; unfold step; rw [if_neg hnew]
    exact add_eq_app_of_ge ⟨_, _, rfl⟩ _ (fun q hq => le_trans hX'O (hB'O q hq))
  -- the middle value is a term of the fundamental sequence, also in the argument
  have hArg : spArg a B (psi v (app Y0 one) z) ≠ z := by
    intro h
    have := lt_spArg a (b := B) hX (by simp)
    rw [h] at this; exact T.not_lt_z _ this
  have hfsM : ∃ k, psi a (spArg a B (mulT O (m + 1))) z =
      fs (psi a (spArg a B (psi v (app Y0 one) z)) z) (natT k) := by
    by_cases htr : lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true
    · by_cases hbad : lt B Y0 = true ∧ (split Y0 (psi (succ v) z z)).2 = z
      · refine ⟨m, ?_⟩
        have := t0_frame_swallow (n := m + 1) (by omega) hX hO htr hbad.1 hbad.2
        rw [show m + 1 - 1 = m by omega] at this
        exact this.symm
      · exact ⟨m + 1, (t0_frame_trig (n := m + 1) (by omega) hOld hX hO htr hbad).symm⟩
    · have hXapp : isOT (app B (psi v (app Y0 one) z)) = true := by
        have h1 := isOT_arg hOld
        rw [spArg_single] at h1; unfold step at h1
        rw [if_neg htr, add_eq_app_of_ge ⟨_, _, rfl⟩ _ hBX] at h1
        exact h1
      exact ⟨m + 1, (t0_frame_notrig (m + 1) hXapp htr hBX).symm⟩
  obtain ⟨k, hk⟩ := hfsM
  set X := spArg a B (psi v (app Y0 one) z) with hXdef
  obtain ⟨P, hP⟩ := step_succ_end (a := a) hX hBX
  rw [← spArg_single] at hP
  obtain ⟨hXz, hXs, hXc⟩ := cof_app_succ_end P v Y0
  rw [← hP] at hXz hXs hXc
  rw [fs_psi_omega hXz hXs hXc] at hk
  simp only [psi.injEq] at hk
  have hlM : Lhd z (spArg a B (mulT O (m + 1))) X := by
    rw [hk.2.1]
    apply lhd_natT_z
    apply lhd_fs (isOT_arg hOld)
    unfold ValidLt; rw [hXc]; trivial
  rw [hMid] at hlM
  rw [hN]
  by_cases heq : psi s' y' z = O
  · rw [heq]; exact hlM
  · have hlt' : psi s' y' z < O := lt_of_le_of_ne hX'O heq
    have hlO : Lhd z (psi s' y' z) O := lhd_restrict hl hlt' (le_of_lt hOX)
    exact lhd_trans (lhd_app B' hlO) hlM

theorem isOT_spArg (a : T) : ∀ (c B : T), isOT B = true → isOT c = true → isOT (spArg a B c) = true
  | z, _, hB, _ => hB
  | psi s y c, B, hB, hc => by
    rw [spArg_cons, step_rest a B s y c z]
    exact isOT_spArg a c _ (isOT_step hB (isOT_head hc)) (isOT_rest hc)

/-! ## `v` の標準形を局所に -/

/-- **`v(i)` is standard** when the values it reads are. -/
theorem ot_v_at {N : Mat} {σ : Valn} (hC : Cons N σ) {i : Nat} (hi : i < N.length)
    (hV : entry N 1 i ≠ 0 → isOT (vOpt σ (par N 1 i)) = true)
    (hU : entry N 1 i ≠ 0 → entry N 2 i = 0 → ∀ k, upg N i = some k → isOT (σ.v k) = true)
    (hB : entry N 1 i ≠ 0 → entry N 2 i ≠ 0 → ∀ j ∈ children N i, col N j = bump N i →
      ∀ k ∈ children N j, isOT (σ.o k) = true) :
    isOT (σ.v i) = true := by
  rw [(hC i hi).2]; unfold vRhs
  split_ifs with h1 h2
  · rfl
  · cases hu : upg N i with
    | none =>
      have h' : isOT (add (vOpt σ (par N 1 i)) one) = true := isOT_add (hV h1) rfl
      show isOT (sf (add (vOpt σ (par N 1 i)) one)) = true
      rw [sf_ot h']; exact h'
    | some k =>
      have hk : isOT (last (σ.v k)) = true := isOT_last (hU h1 h2 k hu)
      have h' : isOT (add (vOpt σ (par N 1 i)) (last (σ.v k))) = true := isOT_add (hV h1) hk
      show isOT (sf (add (vOpt σ (par N 1 i)) (last (σ.v k)))) = true
      rw [sf_ot h']; exact h'
  · have hBo : isOT (omega (sumN (one :: (children N i).map (bumpTerm N σ i)))) = true := by
      apply isOT_omega; apply isOT_sumN
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
        unfold bumpTerm
        split
        · rename_i hjb
          apply isOT_omega; apply isOT_sumN
          intro t' ht'
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht'
          exact hB h1 h2 j hj hjb k hk
        · rfl
    rw [sf_ot (isOT_add (hV h1) hBo)]; exact isOT_add (hV h1) hBo

/-! ## 型の伝わり方（枠 1 段） -/

/-- **The class of a node's argument pair** at its own level `a` (`θ = Ω_{a+1}`): A, both without low
part (B0), or the new one is the high part of the old one (C). -/
def ClsNode (a X' X : T) : Prop :=
  ((split X' (psi (succ a) z z)).1 = (split X (psi (succ a) z z)).1 ∧ (split X' (psi (succ a) z z)).2 ≠ z) ∨
  ((split X' (psi (succ a) z z)).2 = z ∧ (split X (psi (succ a) z z)).2 = z) ∨
  X' = (split X (psi (succ a) z z)).1

theorem succ_le_succ' {a s : T} (h : a ≤ s) : succ a ≤ succ s := by
  rcases lt_or_ge (succ s) (succ a) with h' | h'
  · exfalso
    have h1 : succ s ≤ a := lt_succ_iff.mp h'
    exact absurd (lt_of_le_of_lt (le_trans h1 h) (lt_succ_self s)) (lt_irrefl' _)
  · exact h'

theorem theta_mono {a s : T} (h : a ≤ s) : psi (succ a) z z ≤ psi (succ s) z z := le_psi_sub (succ_le_succ' h)

/-- A child below `Ω_{a+1}` has subscript at most `a`. -/
theorem lt_theta_iff {a s y : T} : psi s y z < psi (succ a) z z ↔ s ≤ a := by
  rw [psi_lt_psi_z_iff, ← lt_succ_iff]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact h
    · exact absurd h (T.not_lt_z _)
  · exact Or.inl

theorem split_all_high {θ : T} : ∀ X : T, (∀ q ∈ summands X, ¬ q < θ) → split X θ = (X, z) := by
  intro X hX
  have := split_app_of (t := θ) (B := X) (X := z) hX (Or.inl rfl)
  rwa [app_z_right] at this

/-- **The class of `B + c′` against `B + c`** at the level `a`. -/
theorem cls_app_pair {a B c c' : T} (hc : ∃ s y, c = psi s y z) (hc' : ∃ s y, c' = psi s y z)
    (hcc : c' ≤ c) (hB : ∀ q ∈ summands B, c ≤ q)
    (hhigh : ¬ c < psi (succ a) z z → ¬ c' < psi (succ a) z z) :
    ClsNode a (app B c') (app B c) := by
  set θ := psi (succ a) z z with hθ
  by_cases hlow : c < θ
  · have hlow' : c' < θ := lt_of_le_of_lt hcc hlow
    left
    obtain ⟨s, y, rfl⟩ := hc
    obtain ⟨s', y', rfl⟩ := hc'
    rw [split_app_low (P := B) (R := psi s' y' z) (Or.inr hlow'),
      split_app_low (P := B) (R := psi s y z) (Or.inr hlow)]
    refine ⟨rfl, ?_⟩
    intro h; exact absurd (app_eq_z h).2 (by simp)
  · have hhigh' := hhigh hlow
    right; left
    have hBh : ∀ q ∈ summands B, ¬ q < θ := fun q hq h => hlow (lt_of_le_of_lt (hB q hq) h)
    obtain ⟨s, y, rfl⟩ := hc
    obtain ⟨s', y', rfl⟩ := hc'
    rw [split_all_high (app B (psi s' y' z)) (by
        intro q hq; rw [summands_app] at hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hBh q hq
        · simp [summands] at hq; rw [hq]; exact hhigh'),
      split_all_high (app B (psi s y z)) (by
        intro q hq; rw [summands_app] at hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hBh q hq
        · simp [summands] at hq; rw [hq]; exact hlow)]
    exact ⟨rfl, rfl⟩

/-- The high part at `Ω_{s+1}` has no summand below `Ω_{a+1}` when `a ≤ s`. -/
theorem hi_all_high {a s : T} (has : a ≤ s) (y : T) :
    ∀ q ∈ summands (split y (psi (succ s) z z)).1, ¬ q < psi (succ a) z z :=
  fun q hq h => split_fst_ge _ y q hq (lt_of_lt_of_le h (theta_mono has))

/-- **The class passes up one frame** (`a = v(parent)`): from the class of the child's argument pair
(with the rewrite agreement in class B), or a bare child `ψ_{s′}(0)` that stays at least `Ω_{a+1}` when
`ψ_s(0)` is. -/
theorem cls_node {a B s s' y y' : T} (hc : isOT (psi s y z) = true) (hc' : isOT (psi s' y' z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (hch : (s' = s ∧ Lhd z y' y ∧ ClsABC B s y' y (Trig a B s y)) ∨
      (y = z ∧ y' = z ∧ Lhd z s' s ∧
        (¬ psi s z z < psi (succ a) z z → ¬ psi s' z z < psi (succ a) z z))) :
    ClsNode a (step a B s' y' z) (step a B s y z) := by
  rcases hch with ⟨rfl, hl, hcl⟩ | ⟨rfl, rfl, hl, hhv⟩
  · have hyy : y' < y := hl.1
    have hpsi : psi s' y' z < psi s' y z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hyy⟩)
    have hBc' : ∀ q ∈ summands B, psi s' y' z ≤ q := fun q hq => le_trans (le_of_lt hpsi) (hBc q hq)
    set θs := psi (succ s') z z with hθs
    have ey := split_app θs y
    have ey' := split_app θs y'
    have hdown : lt (psi a z z) (psi s' y z) = true → lt B y' = true →
        lt (psi a z z) (psi s' y' z) = true := by
      intro h2 hB'
      change psi a z z < psi s' y z at h2
      change psi a z z < psi s' y' z
      rcases psi_lt_psi_z_iff.mp h2 with h | ⟨rfl, _⟩
      · exact psi_lt_psi_z_iff.mpr (Or.inl h)
      · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt (z_le B) hB'⟩)
    have hhigh : ¬ psi s' y z < psi (succ a) z z → ¬ psi s' y' z < psi (succ a) z z := by
      intro h h'; exact h (lt_theta_iff.mpr (lt_theta_iff.mp h'))
    by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s' y z) = true
    · have has : a ≤ s' := by
        have h2 : psi a z z < psi s' y z := ht.2
        rcases psi_lt_psi_z_iff.mp h2 with h | ⟨h, _⟩
        · exact le_of_lt h
        · rw [h]
      -- `y` and `y′` are not below `Ω_{s′}`: the rest of the argument is at least the child
      by_cases ht' : lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true
      · unfold step
        rw [if_pos ht', if_pos ht, H_eq hc', H_eq hc]
        rcases hcl with ⟨hhi, hlo'⟩ | ⟨hl0', hl0, _⟩ | hC
        · have hlo : (split y θs).2 ≠ z := by
            intro h0
            rw [h0, app_z_right] at ey
            have : (split y' θs).1 < y' := by
              have h := lt_app_of (x := (split y' θs).1) hlo'; rwa [ey'] at h
            rw [hhi, ey] at this
            exact absurd (lt_trans this hyy) (lt_irrefl' _)
          rw [if_neg hlo', if_neg hlo, hhi]
          apply cls_app_pair ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ (le_of_lt hpsi)
            (fun q hq => not_lt.mp (fun h => split_fst_ge _ y q hq
              (lt_trans h (lt_theta_iff.mpr (le_refl s'))))) hhigh
        · rw [if_pos hl0', if_pos hl0, app_z_right, app_z_right]
          right; left
          exact ⟨by rw [split_all_high _ (hi_all_high has y')],
            by rw [split_all_high _ (hi_all_high has y)]⟩
        · have hlo : (split y θs).2 ≠ z := by
            intro h0; rw [h0, app_z_right, ← hC] at ey; rw [ey] at hyy; exact absurd hyy (lt_irrefl' _)
          have hs' : split y' θs = (y', z) := by rw [hC]; exact split_hi_self θs y
          rw [hs', if_neg hlo]
          simp only [if_true, app_z_right]
          rw [← hC]
          have hy'h : ∀ q ∈ summands y', ¬ q < psi (succ a) z z := by
            rw [hC]; exact hi_all_high has y
          by_cases hlow : psi s' y z < psi (succ a) z z
          · right; right
            rw [split_app_low (Or.inr hlow), split_all_high y' hy'h]
          · right; left
            refine ⟨by rw [split_all_high y' hy'h], ?_⟩
            rw [split_all_high _ (by
              intro q hq; rw [summands_app] at hq
              rcases List.mem_append.mp hq with hq | hq
              · exact hy'h q hq
              · simp [summands] at hq; rw [hq]; exact hlow)]
      · -- only the old frame rewrites: class C with `B = y′`
        rcases hcl with ⟨hhi, hlo'⟩ | ⟨_, _, htr⟩ | hC
        · exfalso; apply ht'
          have hBhi : B ≤ (split y θs).1 := B_le_hi hc ht.1 hBc
          have hB' : lt B y' = true := by
            show B < y'
            rw [← hhi] at hBhi
            refine lt_of_le_of_lt hBhi ?_
            have h := lt_app_of (x := (split y' θs).1) hlo'; rwa [ey'] at h
          exact ⟨hB', hdown ht.2 hB'⟩
        · exact absurd ⟨htr ht, hdown ht.2 (htr ht)⟩ ht'
        · have hBhi : B ≤ y' := by rw [hC]; exact B_le_hi hc ht.1 hBc
          have hBy : B = y' := by
            rcases (le_iff _ _).mp hBhi with h | h
            · exact absurd ⟨h, hdown ht.2 h⟩ ht'
            · exact h
          have hlo : (split y θs).2 ≠ z := by
            intro h0; rw [h0, app_z_right, ← hC] at ey; rw [ey] at hyy; exact absurd hyy (lt_irrefl' _)
          unfold step
          rw [if_neg ht', if_pos ht, H_eq hc, if_neg hlo, ← hC, add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc', hBy]
          have hy'h : ∀ q ∈ summands y', ¬ q < psi s' y z := by
            intro q hq h
            rw [hC] at hq
            exact split_fst_ge _ y q hq (lt_trans h (lt_theta_iff.mpr (le_refl s')))
          exact cls_app_pair ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ (le_of_lt hpsi)
            (fun q hq => not_lt.mp (hy'h q hq)) hhigh
    · -- the old frame does not rewrite, so neither does the new one
      have ht' : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) := fun h =>
        ht ⟨lt_trans (show B < y' from h.1) hyy, lt_trans (show psi a z z < psi s' y' z from h.2) hpsi⟩
      unfold step
      rw [if_neg ht', if_neg ht, add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc, add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc']
      exact cls_app_pair ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ (le_of_lt hpsi) hBc hhigh
  · have hpsi : psi s' z z < psi s z z := (lhd_psi_sub hl).1
    have hn : ∀ s0, ¬ (lt B z = true ∧ lt (psi a z z) (psi s0 z z) = true) := by
      rintro s0 ⟨h, _⟩; exact T.not_lt_z _ h
    unfold step
    rw [if_neg (hn s'), if_neg (hn s), add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc,
      add_eq_app_of_ge ⟨_, _, rfl⟩ B (fun q hq => le_trans (le_of_lt hpsi) (hBc q hq))]
    exact cls_app_pair ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ (le_of_lt hpsi) hBc hhv

section
variable {M : Mat} {r L n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hn : 1 ≤ n)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (he1 : entry M 1 (r + L) = 0) (he2 : entry M 2 (r + L) = 0) (hn2 : 2 ≤ n)
  {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
  (hCN : Cons (TRIO.gexp M r L 0 0 n) σ)
include hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN

/-- `o_N_noc` with the standard `v(c)` only. -/
theorem o_N_noc' {c : Nat} (hc : c < r) (hcl : CL M c = []) (hvc : isOT (σ.v c) = true) :
    σ.o c = psi (σ.v c) z z := by
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hcN : c < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hclN : CL (TRIO.gexp M r L 0 0 n) c = [] := by
    rw [cl_N_eq hlen hL hp hn hR0 hZ2 he2 hn2 hc]
    · exact hcl
    · intro hg
      by_contra hb
      have hrc : r ∈ children M c := mem_children_iff.mpr ⟨by omega, hg⟩
      have : r ∈ CL M c := by
        unfold CL; rw [List.mem_filter]; refine ⟨hrc, ?_⟩
        simp only [decide_eq_true_eq]
        exact ⟨hb, by rw [not_topped_r hlen hL hp he2]; simp⟩
      rw [hcl] at this; simp at this
  exact o_of_no_counted hCN hcN hvc (no_cnt_of_cl_nil hclN)

omit hCN in
theorem cl_nil_of_depv' {c : Nat} (hc : c < r) (hv : DepX M (r + L) false c) : CL M c = [] := by
  unfold CL
  rw [List.filter_eq_nil_iff]
  intro d hd
  simp only [decide_eq_true_eq]
  exact uncnt_of_depv (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp
    (by omega) hv hd

/-- **The seed at `g` at the level of the arguments** (some middle copy root counts at `g`). -/
theorem t0_S1A {g : Nat} (hg : par M 0 r = some g) {ρ' : Valn} (hcnt : Counted M g r)
    (hσG : ∀ c, c < r → ¬ DepX M (r + L) true c → σ.o c = ρ.o c)
    (hσvg : σ.v g = ρ.v g)
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hLast : Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hl : Lhd z (ρ'.o r) (ρ.o r))
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hC1 : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hm1 : ∃ k, k + 1 < n ∧ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) :
    ∃ X X', ρ.o g = psi (ρ.v g) X z ∧ σ.o g = psi (ρ.v g) X' z ∧ Lhd z X' X ∧ isOT X' = true := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hgr : g < r := par_lt M 0 r g hg
  have hgM : g < M.length := by omega
  have hgN : g < (TRIO.gexp M r L 0 0 n).length := by rw [hlN]; omega
  have hrg : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
  -- the counted children in `M`
  set F := (children M g).filter (fun d => decide (d < r)) with hFdef
  have hchM : children M g = F ++ [r] := children_g_last hlen hL hp hg
  set Lc := F.filter (fun d => decide (Counted M g d)) with hLcdef
  have hclM : CL M g = Lc ++ [r] := by
    unfold CL; rw [hchM, List.filter_append]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hcnt]
    rfl
  -- the counted children in `N`
  set f : Nat → Nat := fun k => r + k * L with hfdef
  have hroots : [r] ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) =
      (List.range (n - 1)).map f ++ [r + (n - 1) * L] := by
    have e1 : (List.range n).map f = [r] ++ (List.range (n - 1)).map (fun k => r + (k + 1) * L) := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp [hfdef, Nat.add_sub_cancel]
    have e2 : (List.range n).map f = (List.range (n - 1)).map f ++ [r + (n - 1) * L] := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range_succ, List.map_append]; simp [hfdef]
    rw [← e1, e2]
  set Cm := ((List.range (n - 1)).map f).filter
    (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) g d)) with hCmdef
  have hclN : CL (TRIO.gexp M r L 0 0 n) g = Lc ++ Cm ++ [r + (n - 1) * L] := by
    unfold CL
    rw [children_g0 hlen hL hp hn hg, hchM, List.append_assoc, hroots, List.filter_append,
      List.filter_append]
    have hF' : F.filter (fun d => decide (Counted (TRIO.gexp M r L 0 0 n) g d)) = Lc := by
      apply List.filter_congr
      intro d hd
      have hdr : d < r := by simpa using (List.mem_filter.mp hd).2
      simp only [counted_lt0 hlen hL hp hn hR0 hZ2 he2 hn2 hgr hdr]
    rw [hF', List.append_assoc]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, if_pos hLast]
    rfl
  have hCmv : Cm.map σ.o = List.replicate Cm.length (omid M r L ρ) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hd).1
    exact hσmid k (by have := List.mem_range.mp hk; omega)
  have hσLc : ∀ d ∈ Lc, σ.o d = ρ.o d := by
    intro d hd
    have hdF := (List.mem_filter.mp hd).1
    have hdr : d < r := by simpa using (List.mem_filter.mp hdF).2
    have hdM := (List.mem_filter.mp hdF).1
    apply hσG d hdr
    intro hD
    exact p1_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hdM hrg hdr hD hcnt
  have hLcv : Lc.map σ.o = Lc.map ρ.o := List.map_congr_left hσLc
  -- the values
  obtain ⟨hsM, hpM⟩ := cl_vals hC hG hgM
  have hsO0 : Single (omid M r L ρ) :=
    ⟨isOT_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN, by
      rw [(o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG).2]; exact ⟨_, _, rfl⟩⟩
  have hsLr : Single (ρ'.o r) := single_o hC1 hGT (by rw [List.length_take]; omega)
  have hsCL : ∀ d ∈ CL (TRIO.gexp M r L 0 0 n) g, Single (σ.o d) := by
    intro d hd
    rw [hclN] at hd
    rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      · have hdF := (List.mem_filter.mp hd).1
        have hdr : d < r := by simpa using (List.mem_filter.mp hdF).2
        rw [hσLc d hd]
        exact single_o hC hG (by omega)
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hd).1
        rw [hσmid k (by have := List.mem_range.mp hk; omega)]; exact hsO0
    · simp at hd; rw [hd, hσlast]; exact hsLr
  have hsN : ∀ t ∈ (CL (TRIO.gexp M r L 0 0 n) g).map σ.o, Single t := by
    intro t ht; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht; exact hsCL d hd
  rw [hclM] at hsM hpM
  rw [hclN] at hsN
  simp only [List.map_append, List.map_singleton] at hsM hpM hsN
  rw [hLcv, hCmv, hσlast] at hsN
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG
  -- the decrease at `g` in `N`
  have hpN : (Lc.map ρ.o ++ List.replicate Cm.length (omid M r L ρ) ++ [ρ'.o r]).Pairwise
      (fun a b => b ≤ a) := by
    have hOr : omid M r L ρ < ρ.o r := by
      rw [hom, hor]; exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one _⟩)
    have hlo : ρ'.o r ≤ omid M r L ρ := by
      obtain ⟨_, s', y', hs'⟩ := hsN (ρ'.o r) (by simp)
      have h := hl.1
      rw [hs', hor] at h
      rw [hs', hom]
      rcases psi_lt_psi_z_iff.mp h with h1 | ⟨rfl, h2⟩
      · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h1))
      · exact psi_le_psi_arg ((lt_succ_iff (x := _)).mp h2)
    have hp1 := List.pairwise_append.mp hpM
    refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨hp1.1,
      List.pairwise_replicate.mpr (Or.inr (le_refl _)), fun a ha b hb => ?_⟩, by simp, fun a ha b hb => ?_⟩
    · rw [(List.mem_replicate.mp hb).2]
      exact le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp))
    · simp at hb; rw [hb]
      rcases List.mem_append.mp ha with ha | ha
      · exact le_trans hlo (le_trans (le_of_lt hOr) (hp1.2.2 a ha _ (by simp)))
      · rw [(List.mem_replicate.mp ha).2]; exact hlo
  have hpN0 : ((CL (TRIO.gexp M r L 0 0 n) g).map σ.o).Pairwise (fun a b => b ≤ a) := by
    rw [hclN]; simp only [List.map_append, List.map_singleton]; rw [hLcv, hCmv, hσlast]; exact hpN
  set Y0 := spArg (ρ.v r) z (sumN (((children M r).filter (fun c => decide (c < r + L))).map
    (cnt M ρ r))) with hY0
  set v := ρ.v r with hv
  set a := ρ.v g with ha
  set Lv := Lc.map ρ.o with hLv
  set m := Cm.length with hm
  have hOv : omid M r L ρ = psi v Y0 z := hom
  -- the sums
  have hsO : Single (omid M r L ρ) := by
    exact hsO0
  have hsumN : sumN (Lv ++ List.replicate m (omid M r L ρ) ++ [ρ'.o r]) =
      app (app (sumN Lv) (mulT (omid M r L ρ) m)) (ρ'.o r) := by
    have hp1 := List.pairwise_append.mp hpN
    rw [sumN_append_dec hsN hpN, sumN_append_dec (fun t ht => hsN t (List.mem_append_left _ ht)) hp1.1,
      sumN_replicate hsO m, sumN_singleton (hsN _ (by simp))]
  have hsumM : sumN (Lv ++ [ρ.o r]) = app (sumN Lv) (ρ.o r) := by
    rw [sumN_append_dec hsM hpM, sumN_singleton (hsM _ (by simp))]
  have hoN : σ.o g = psi a (spArg a (spArg a (spArg a z (sumN Lv)) (mulT (omid M r L ρ) m))
      (ρ'.o r)) z := by
    rw [o_cl_loc hCN hgN (by rw [hσvg]; exact hG.ot_v g hgM) hsCL hpN0, hclN]
    simp only [List.map_append, List.map_singleton]
    rw [hLcv, hCmv, hσlast, hsumN, spArg_app, spArg_app, hσvg]
  have hoM : ρ.o g = psi a (spArg a (spArg a z (sumN Lv)) (ρ.o r)) z := by
    rw [o_cl_eq hC hG hgM, hclM]
    simp only [List.map_append, List.map_singleton]
    rw [hsumM, spArg_app]
  have hLs := sumN_dec Lv (fun t ht => hsM t (List.mem_append_left _ ht)) (List.pairwise_append.mp hpM).1
  have hm : 1 ≤ m := by
    obtain ⟨k, hk, hkc⟩ := hm1
    have : r + k * L ∈ Cm := List.mem_filter.mpr ⟨List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩,
      by simpa using hkc⟩
    rw [hm]; exact List.length_pos_of_mem this
  have hXot : isOT (ρ.o r) = true := hG.ot_o r (by omega)
  rw [hor] at hoM hl hXot
  have hOld : isOT (psi a (spArg a (spArg a z (sumN Lv)) (psi v (app Y0 one) z)) z) = true := by
    rw [← hoM]; exact hG.ot_o g hgM
  refine ⟨_, spArg a (spArg a (spArg a z (sumN Lv)) (mulT (psi v Y0 z) m)) (ρ'.o r), hoM,
    by rw [hoN, hOv], ?_, ?_⟩
  rotate_left
  · exact isOT_spArg a _ _ (isOT_spArg a _ _ (isOT_spArg a _ _ rfl hLs.1)
      (isOT_mulT (by rw [← hOv]; exact hsO.1) ⟨_, _, rfl⟩ m)) hsLr.1
  apply s1_core_arg hm hOld hXot (by rw [← hOv]; exact hsO.1)
  · apply spArg_summands_ge ⟨v, _, rfl⟩ (sumN Lv) z hLs.1
    · rw [hLs.2]; intro q hq
      have := (List.pairwise_append.mp hpM).2.2 q hq (ρ.o r) (by simp)
      rwa [hor] at this
    · simp [summands]
  · exact hsLr
  · exact hl
  · have hp1 := List.pairwise_append.mp hpN
    rw [← hOv]
    exact hp1.2.2 (omid M r L ρ) (List.mem_append_right _ (List.mem_replicate.mpr ⟨by omega, rfl⟩))
      (ρ'.o r) (by simp)
  · exact hy'


/-- **The `D` columns before `r` are standard and drop by `◁`** in `N = M[n]` (`t = 0`, `n ≥ 2`, `r` has a
parent `g`), proved together by the ranking. The `o` calls also drop by `◁` in their arguments.
Residual hypotheses on `N`: `hShape` (the class of the argument pair of the last counted child at each
frame before `r`) and `hG0` (the frame of `g` when no middle copy root counts). -/
theorem t0_dep_ot {g : Nat} (hg : par M 0 r = some g) {rk : Bool → Nat → Nat} (hRM : Rk M rk)
    {ρ' : Valn} (hC1 : Cons (M.take (r + L)) ρ') (hGT : Good3 (M.take (r + L)) ρ')
    (hσB : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i)
    (hσBv : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i)
    (hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i))
    (hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ)
    (hσlast : σ.o (r + (n - 1) * L) = ρ'.o r)
    (hFO : FrameOT M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ) (hAbs : BumpAbsC M (r + L) ρ)
    (hl : Lhd z (ρ'.o r) (ρ.o r))
    (hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z)
    (hLastC : Counted M g r → Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hS3 : ∀ p, par M 0 g = some p → entry M 1 p ≠ 0 → entry M 2 p ≠ 0 → col M g = bump M p →
      Lhd z (σ.v p) (ρ.v p))
    (hS2 : col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → Lhd z (σ.v g) (ρ.v g))
    (hTrigB : ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → Lhd z y' y →
      (split y' (psi (succ s) z z)).2 = z → (split y (psi (succ s) z z)).2 = z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true)
    (hVchg : ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      σ.v c ≠ ρ.v c → ¬ psi (ρ.v c) z z < psi (succ (ρ.v i)) z z →
      ¬ psi (σ.v c) z z < psi (succ (ρ.v i)) z z)
    (hClsG : Counted M g r → ∀ X X', ρ.o g = psi (ρ.v g) X z → σ.o g = psi (ρ.v g) X' z →
      ClsNode (ρ.v g) X' X)
    (hG0 : Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      ∃ X X', ρ.o g = psi (ρ.v g) X z ∧ σ.o g = psi (ρ.v g) X' z ∧ Lhd z X' X ∧ isOT X' = true) :
    ∀ b i, i < r → isOT (valB σ b i) = true ∧
      (DepX M (r + L) b i → Lhd z (valB σ b i) (valB ρ b i)) ∧
      (b = true → DepX M (r + L) true i → σ.v i = ρ.v i →
        ∃ X X', ρ.o i = psi (ρ.v i) X z ∧ σ.o i = psi (ρ.v i) X' z ∧ Lhd z X' X ∧
          ClsNode (ρ.v i) X' X) := by
  have hx : r + L + 1 = M.length := hlen
  have hlN := lenN0 hlen hn (M := M) (L := L)
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hiN : ∀ i, i < r → i < (TRIO.gexp M r L 0 0 n).length := fun i hi => by rw [hlN]; omega
  have hAgx : Anc0 M g (r + L) := Anc0.step hp (Anc0.step hg (Anc0.refl g))
  have hgr : g < r := par_lt M 0 r g hg
  -- the copies are standard
  have hOTc : ∀ i, r ≤ i → i < (TRIO.gexp M r L 0 0 n).length →
      isOT (σ.o i) = true ∧ isOT (σ.v i) = true := by
    intro i hri hiN'
    have hph : phi0 r L i < r + L := by
      unfold phi0; rw [if_neg (by omega)]; have := Nat.mod_lt (i - r) hL; omega
    rw [hσB i hri hiN', hσBv i hri hiN']
    unfold tauN
    simp only [if_neg (show ¬ i < r by omega)]
    refine ⟨?_, ?_⟩
    · split_ifs
      · exact isOT_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN
      · exact hG.ot_o _ (by omega)
      · exact hGT.ot_o _ (by rw [List.length_take]; omega)
    · split_ifs
      · exact hG.ot_v _ (by omega)
      · exact hGT.ot_v _ (by rw [List.length_take]; omega)
  -- the claim, by the ranking
  have key : ∀ K, ∀ b i, rk b i ≤ K → i < r →
      isOT (valB σ b i) = true ∧ (DepX M (r + L) b i → Lhd z (valB σ b i) (valB ρ b i)) ∧
      (b = true → DepX M (r + L) true i → σ.v i = ρ.v i →
        ∃ X X', ρ.o i = psi (ρ.v i) X z ∧ σ.o i = psi (ρ.v i) X' z ∧ Lhd z X' X ∧
          ClsNode (ρ.v i) X' X) := by
    intro K
    induction K using Nat.strongRecOn with
    | _ K ih =>
      intro b i hK hi
      have hiM : i < M.length := by omega
      obtain ⟨hRv, hRc, hRr⟩ := hRM i hiM
      -- standard values of lower rank
      have hOTo : ∀ j, j < (TRIO.gexp M r L 0 0 n).length → (j < r → rk true j < K) →
          isOT (σ.o j) = true := by
        intro j hj hjK
        rcases Nat.lt_or_ge j r with hjr | hjr
        · exact (ih _ (hjK hjr) true j (le_refl _) hjr).1
        · exact (hOTc j hjr hj).1
      have hOTv : ∀ j, j < (TRIO.gexp M r L 0 0 n).length → (j < r → rk false j < K) →
          isOT (σ.v j) = true := by
        intro j hj hjK
        rcases Nat.lt_or_ge j r with hjr | hjr
        · exact (ih _ (hjK hjr) false j (le_refl _) hjr).1
        · exact (hOTc j hjr hj).2
      cases b with
      | false =>
        -- `v` calls
        have hot : isOT (σ.v i) = true := by
          apply ot_v_at hCN (hiN i hi)
          · intro h1
            rw [entry_pre0 hlen hn 1 (by omega)] at h1
            rw [par1_pre0 hlen hL hp hn hi]
            cases hpm : par M 1 i with
            | none => rfl
            | some m =>
              have hmi := par_lt M 1 i m hpm
              exact hOTv m (by rw [hlN]; omega) (fun _ => by have := (hRr h1).1 m hpm; omega)
          · intro h1 h2 k hu
            rw [entry_pre0 hlen hn 1 (by omega)] at h1
            rw [entry_pre0 hlen hn 2 (by omega)] at h2
            rw [upg_pre0 hlen hL hp hn (by omega)] at hu
            have hkN := upg_lt (hiN i hi) (by rw [upg_pre0 hlen hL hp hn (by omega)]; exact hu)
            exact hOTv k hkN (fun _ => by have := (hRr h1).2.1 h2 k hu; omega)
          · intro h1 h2 j hj hjb k hk
            rw [entry_pre0 hlen hn 1 (by omega)] at h1
            rw [entry_pre0 hlen hn 2 (by omega)] at h2
            have hkN := (mem_children hk).2
            apply hOTo k hkN
            intro hkr
            have hjk := (mem_children hk).1
            have hjr : j < r := by omega
            have hjM : j ∈ children M i := child_lt_r hlen hL hp hn hi hj hjr
            have hkM : k ∈ children M j := child_lt_r hlen hL hp hn hjr hk hkr
            have hjb' : col M j = bump M i := by
              rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)] at hjb; exact hjb
            have := (hRr h1).2.2 h2 j hjM hjb' k hkM; omega
        refine ⟨hot, ?_, fun h => absurd h (by simp)⟩
        intro hD
        show Lhd z (σ.v i) (ρ.v i)
        cases hD with
        | vpar h1 hpm hdm =>
          exfalso
          have hm := par_lt M 1 i _ hpm
          exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB (depX_chgX hdm)).1 rfl (by omega) |>.2.2 i
            (by omega) hpm
        | @vupg _ k h1 h2 hu hdk =>
          obtain ⟨_, _, _, _, hcase⟩ := upg_spec hu
          have hkr : k < r := by
            have hkle : k ≤ r := by rcases hcase with h | ⟨_, h⟩ <;> omega
            rcases Nat.lt_or_ge k r with h | h
            · exact h
            · exfalso
              have : k = r := by omega
              rw [this] at hdk
              exact not_depX_v_r hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB he1 hdk
          have hkK : rk false k < K := by have := (hRr h1).2.1 h2 k hu; omega
          have hIH : Lhd z (σ.v k) (ρ.v k) := (ih _ hkK false k (le_refl _) hkr).2.1 hdk
          have hVot : isOT (vOpt ρ (par M 1 i)) = true := by
            cases hpp : par M 1 i with
            | none => rfl
            | some m => exact hG.ot_v m (by have := par_lt M 1 i m hpp; omega)
          have hVot' : isOT (vOpt σ (par (TRIO.gexp M r L 0 0 n) 1 i)) = true := by
            rw [par1_pre0 hlen hL hp hn hi]
            cases hpp : par M 1 i with
            | none => rfl
            | some m =>
              have hmi := par_lt M 1 i m hpp
              exact hOTv m (by rw [hlN]; omega) (fun _ => by have := (hRr h1).1 m hpp; omega)
          have ek : ρ.v i = ρ.v k :=
            v_upg_eq hC hiM h1 h2 hu hVot (fun _ _ _ k' hk' => hG.ot_o k' (mem_children hk').2)
          have huN : upg (TRIO.gexp M r L 0 0 n) i = some k := by
            rw [upg_pre0 hlen hL hp hn (by omega)]; exact hu
          have hkM : k < M.length := by omega
          obtain ⟨_, _, hRrk⟩ := hRM k hkM
          have ek' : σ.v i = σ.v k :=
            v_upg_eq hCN (hiN i hi) (by rw [entry_pre0 hlen hn 1 (by omega)]; exact h1)
              (by rw [entry_pre0 hlen hn 2 (by omega)]; exact h2) huN hVot'
              (fun j hj hjb k' hk' => by
                apply hOTo k' (mem_children hk').2
                intro hk'r
                have hjk := (mem_children hk').1
                have hjr : j < r := by omega
                have hjM : j ∈ children M k := child_lt_r hlen hL hp hn hkr hj hjr
                have hk'M : k' ∈ children M j := child_lt_r hlen hL hp hn hjr hk' hk'r
                have hjb' : col M j = bump M k := by
                  rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)] at hjb
                  exact hjb
                obtain ⟨m, _, _, hcol, _⟩ := upg_spec hu
                have h1k : entry M 1 k ≠ 0 := by rw [e1_of_col hcol]; exact (upg_e12 hu).1
                have h2k : entry M 2 k ≠ 0 := by rw [e2_of_col hcol]; omega
                have := (hRrk h1k).2.2 h2k j hjM hjb' k' hk'M
                omega)
          rw [ek, ek']; exact hIH
        | @vbump _ j k h1 h2 hj hjb hk hdk =>
          have hij := (mem_children hj).1
          have hjk := (mem_children hk).1
          have hkl := (mem_children hk).2
          by_cases hkr : r ≤ k
          · by_cases hjr : r ≤ j
            · have hjr' : j = r := by
                by_contra hne
                by_cases hig : par M 0 r = some i
                · have := children_g_le hlen hL hp hig hj; omega
                · have := children_lt_r hlen hL hp hi hig hj; omega
              have hig : par M 0 r = some i := by rw [← hjr']; exact (mem_children_iff.mp hj).2
              have hgi : g = i := Option.some.inj (hg.symm.trans hig)
              have hkx : k = r + L := by
                by_contra hne
                have := nodep_B hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB he1 true k hdk (by omega) (by omega)
                omega
              rw [hjr'] at hjb
              rw [← hgi] at hjb h1 h2 ⊢
              exact hS2 hjb h1 h2
            · have hjg : par M 0 r = some j := by
                by_contra hne
                have := children_lt_r hlen hL hp (by omega) hne hk; omega
              have hgj : g = j := Option.some.inj (hg.symm.trans hjg)
              subst hgj
              exact hS3 i (mem_children_iff.mp hj).2 h1 h2 hjb
          · have hkr' : k < r := by omega
            obtain ⟨_, hpnd, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega)
              (DepX.vbump h1 h2 hj hjb hk hdk)
            rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j', k', hch, _, hchj, _, hKnd, hLnd⟩
            · exact absurd h2' h2
            · have hjj : j = j' := by
                rw [hch] at hj
                rcases List.mem_append.mp hj with h | h
                · exact absurd hdk (hLnd j h k hk).2
                · exact List.mem_singleton.mp h
              subst hjj
              have hkk : k = k' := by
                rw [hchj] at hk
                rcases List.mem_append.mp hk with h | h
                · exact absurd hdk (hKnd k h)
                · exact List.mem_singleton.mp h
              subst hkk
              have hLj : ∀ d ∈ Lb, d < j := (sib_order (children_sorted M i) (R := []) (by rw [hch])).1
              have hKk : ∀ d ∈ Kb, d < k := (sib_order (children_sorted M j) (R := []) (by rw [hchj])).1
              have hig : par M 0 r ≠ some i := by
                intro hig
                have hri : r ∈ children M i := mem_children_iff.mpr ⟨by omega, hig⟩
                rw [hch] at hri
                rcases List.mem_append.mp hri with h | h
                · have := hLj r h; omega
                · simp at h; omega
              have hjg : par M 0 r ≠ some j := by
                intro hjg
                -- the last child of `P_0(r)` is `r`, not `k < r`
                have hl := children_g_last hlen hL hp hjg
                rw [hchj] at hl
                have := congrArg List.getLast? hl
                simp at this
                omega
              have hchN : children (TRIO.gexp M r L 0 0 n) i = Lb ++ [j] := by
                rw [children_pre0 hlen hL hp hn hi hig, hch]
              have hchjN : children (TRIO.gexp M r L 0 0 n) j = Kb ++ [k] := by
                rw [children_pre0 hlen hL hp hn (by omega) hjg, hchj]
              have hbL : ∀ d ∈ Lb, bumpTerm (TRIO.gexp M r L 0 0 n) σ i d = bumpTerm M ρ i d := by
                intro d hd
                have hdj := hLj d hd
                have hdM : d ∈ children M i := by rw [hch]; simp [hd]
                have hdg : par M 0 r ≠ some d := by
                  intro hdg
                  have hgd : g = d := Option.some.inj (hg.symm.trans hdg)
                  have hAj : Anc0 M g j := anc_between hAgx j (by omega) (by omega)
                  have hAi := anc0_par hAj (by omega) (mem_children_iff.mp (show j ∈ children M i by
                    rw [hch]; simp)).2
                  have := hAi.le
                  have := (mem_children hdM).1
                  omega
                apply bumpTerm_eq_of
                · rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
                · intro _
                  rw [children_pre0 hlen hL hp hn (by omega) hdg]
                  apply List.map_congr_left
                  intro e he
                  have her := children_lt_r hlen hL hp (by omega) hdg he
                  exact (hoffD e her).1 (hLnd d hd e he).2
              have hKv : Kb.map σ.o = Kb.map ρ.o := List.map_congr_left (fun d hd => by
                have := hKk d hd; exact (hoffD d (by omega)).1 (hKnd d hd))
              have hbjM : bumpTerm M ρ i j = omega (sumN (Kb.map ρ.o ++ [ρ.o k])) := by
                unfold bumpTerm; rw [if_pos hjb, hchj, List.map_append, List.map_singleton]
              have hbjN : bumpTerm (TRIO.gexp M r L 0 0 n) σ i j = omega (sumN (Kb.map ρ.o ++ [σ.o k])) := by
                unfold bumpTerm
                rw [if_pos (by rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]; exact hjb),
                  hchjN, List.map_append, List.map_singleton, hKv]
              have hIH : Lhd z (σ.o k) (ρ.o k) :=
                (ih _ (by have := (hRr h1).2.2 h2 j hj hjb k hk; omega) true k (le_refl _) hkr').2.1 hdk
              have hdec := hKD i h1 h2 j hj hjb
              rw [hchj, List.map_append, List.map_singleton] at hdec
              have hsK : ∀ u ∈ Kb.map ρ.o, Single u := fun u hu => by
                obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hu
                exact single_o hC hG (by have := hKk d hd; omega)
              have hform : (∃ s y y', ρ.o k = psi s y z ∧ σ.o k = psi s y' z) ∨
                  (∃ w' w Y, σ.o k = psi w' z z ∧ ρ.o k = psi w Y z ∧ LhdE w' w ∧ one ≤ w') := by
                obtain ⟨y1, hy1⟩ := o_psi_sub hC (show k < M.length by omega)
                rw [sf_ot (hG.ot_v k (by omega))] at hy1
                by_cases hvk : σ.v k = ρ.v k
                · obtain ⟨y0, hy0⟩ := o_psi_sub hCN (hiN k hkr')
                  rw [sf_ot (hOTv k (hiN k hkr') (fun _ => by
                  have := (hRM k (by omega)).1; have := (hRr h1).2.2 h2 j hj hjb k hk; omega)), hvk] at hy0
                  exact Or.inl ⟨_, _, _, hy1, hy0⟩
                · have hdv : DepX M (r + L) false k := by
                    by_contra hn'; exact hvk ((hoffD k hkr').2 hn')
                  have ho0 := o_N_noc' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hkr'
                    (cl_nil_of_depv' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hkr' hdv)
                    (hOTv k (hiN k hkr') (fun _ => by
                      have := (hRM k (by omega)).1; have := (hRr h1).2.2 h2 j hj hjb k hk; omega))
                  have hvIH : Lhd z (σ.v k) (ρ.v k) :=
                    (ih _ (by have := (hRM k (by omega)).1; have := (hRr h1).2.2 h2 j hj hjb k hk; omega)
                      false k (le_refl _) hkr').2.1 hdv
                  have he1k : entry M 1 k ≠ 0 := by
                    intro he; apply hvk
                    rw [v_z_of_e1 hC (by omega) he, v_z_of_e1 hCN (hiN k hkr')
                      (by rw [entry_pre0 hlen hn 1 (by omega)]; exact he)]
                  have hv0 : σ.v k ≠ z := v_ne_z_of_e1 hCN (hiN k hkr')
                    (by rw [entry_pre0 hlen hn 1 (by omega)]; exact he1k)
                  exact Or.inr ⟨_, _, _, ho0, hy1, Or.inr hvIH, one_le_of_ne_z hv0⟩
              obtain ⟨hS, hlt, hG'ot⟩ := g_brel hsK hdec (single_o hC hG (by omega))
                ⟨hOTo k (hiN k hkr') (fun _ => by have := (hRr h1).2.2 h2 j hj hjb k hk; omega),
                o_psi_form hCN (hiN k hkr')⟩ hIH hform
              have hGot : isOT (sumN (Kb.map ρ.o ++ [ρ.o k])) = true := isOT_sumN _ (fun u hu => by
                rcases List.mem_append.mp hu with h | h
                · exact (hsK u h).1
                · simp at h; rw [h]; exact hG.ot_o k (by omega))
              have hV : vOpt σ (par (TRIO.gexp M r L 0 0 n) 1 i) = vOpt ρ (par M 1 i) := by
                rw [par1_pre0 hlen hL hp hn hi]
                cases hpp : par M 1 i with
                | none => rfl
                | some m =>
                  have := par_lt M 1 i m hpp
                  exact (hoffD m (by omega)).2 (hpnd m hpp)
              exact v_bump_lhd hC hG hCN hiM (hiN i hi) h1 h2 (entry_pre0 hlen hn 1 (by omega))
                (entry_pre0 hlen hn 2 (by omega)) hV hch hchN hbL hbjM hbjN hGot hG'ot hS hlt hTD
                (hAbs i h1 h2 (fun _ _ _ _ => v_z_of_e1 hC (by omega) he1) (Or.inr (Or.inr (v_z_of_e1 hC (by omega) he1))))
      | true =>
        by_cases hD : DepX M (r + L) true i
        swap
        · have he := (hoffD i hi).1 hD
          exact ⟨by show isOT (σ.o i) = true; rw [he]; exact hG.ot_o i hiM, fun h => absurd h hD,
            fun _ h => absurd h hD⟩
        suffices hmain : isOT (σ.o i) = true ∧ Lhd z (σ.o i) (ρ.o i) ∧ (σ.v i = ρ.v i →
            ∃ X X', ρ.o i = psi (ρ.v i) X z ∧ σ.o i = psi (ρ.v i) X' z ∧ Lhd z X' X ∧
              ClsNode (ρ.v i) X' X) by
          exact ⟨hmain.1, fun _ => hmain.2.1, fun _ _ hv => hmain.2.2 hv⟩
        have hvot : isOT (ρ.v i) = true := hG.ot_v i hiM
        cases hD with
        | leaf => omega
        | ov hv =>
          have hvIH := ih _ (by omega) false i (le_refl _) hi
          have hclM := cl_nil_of_depv' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hi hv
          have hoN := o_N_noc' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hi hclM hvIH.1
          have hoM := o_of_no_counted hC hiM hvot (no_cnt_of_cl_nil hclM)
          have hl' : Lhd z (σ.v i) (ρ.v i) := hvIH.2.1 hv
          refine ⟨by rw [hoN]; exact isOT_psi_zz hvIH.1, by rw [hoN, hoM]; exact lhd_psi_sub hl', ?_⟩
          intro he; rw [he] at hl'; exact absurd hl'.1 (lt_irrefl' _)
        | @ochild _ c hc hcb hcu hdc =>
          have hcnt : Counted M i c := ⟨hcb, hcu⟩
          have hvD : ¬ DepX M (r + L) false i := fun hv =>
            uncnt_of_depv hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp (by omega) hv hc hcnt
          have hv' := (hoffD i hi).2 hvD
          have hci := (mem_children hc).1
          have hcl := (mem_children hc).2
          have hfin : (∃ X X', ρ.o i = psi (ρ.v i) X z ∧ σ.o i = psi (ρ.v i) X' z ∧ Lhd z X' X ∧
              isOT X' = true ∧ ClsNode (ρ.v i) X' X) → isOT (σ.o i) = true ∧ Lhd z (σ.o i) (ρ.o i) ∧
              (σ.v i = ρ.v i → ∃ X X', ρ.o i = psi (ρ.v i) X z ∧ σ.o i = psi (ρ.v i) X' z ∧ Lhd z X' X ∧
                ClsNode (ρ.v i) X' X) := by
            rintro ⟨X, X', hX, hX', hl', hXo, hcls⟩
            refine ⟨?_, by rw [hX, hX']; exact lhd_psi _ hl', fun _ => ⟨X, X', hX, hX', hl', hcls⟩⟩
            rw [hX']
            have hot := hG.ot_o i hiM
            rw [hX] at hot
            exact ot_parent_lhd hot hXo (Or.inr hl')
          apply hfin
          by_cases hcr : r ≤ c
          · have hcr' : c = r := by
              by_contra hne
              by_cases hig : par M 0 r = some i
              · have := children_g_le hlen hL hp hig hc; omega
              · have := children_lt_r hlen hL hp hi hig hc; omega
            rw [hcr'] at hc hcnt
            have hig : par M 0 r = some i := (mem_children_iff.mp hc).2
            have hgi : g = i := Option.some.inj (hg.symm.trans hig)
            rw [← hgi] at hcnt hv' ⊢
            obtain ⟨X, X', hX, hX', hl', hXo⟩ : ∃ X X', ρ.o g = psi (ρ.v g) X z ∧
                σ.o g = psi (ρ.v g) X' z ∧ Lhd z X' X ∧ isOT X' = true := by
              by_cases hm1 : ∃ k, k + 1 < n ∧ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)
              · exact t0_S1A hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hg hcnt
                  (fun c hc hd => (hoffD c hc).1 hd) hv' hσmid hσlast (hLastC hcnt) hl hy' hC1 hGT hm1
              · exact hG0 hcnt (fun k hk hk' => hm1 ⟨k, hk, hk'⟩)
            exact ⟨X, X', hX, hX', hl', hXo, hClsG hcnt X X' hX hX'⟩
          · have hcr : c < r := by omega
            rcases hOS_t1 hx hR0 hZ2 hSD hZ1 hUAT hUAB he2 hp i (by omega) (DepX.ochild hc hcb hcu hdc) with
              ⟨hv, _⟩ | ⟨_, Lp, c0, R, hch, _, _, hR, hLnd⟩
            · exact absurd hv hvD
            · have hcR : ∀ d ∈ R, ¬ Counted M i d := fun d h hd => by
                rcases hR d h with h' | h'
                · exact hd.1 h'
                · exact hd.2 h'
              have hcc0 : c = c0 := by
                have hc' := hc
                rw [hch] at hc'
                rcases List.mem_append.mp hc' with h | h
                · exact absurd hdc (hLnd c h hcnt)
                · rcases List.mem_cons.mp h with h | h
                  · exact h
                  · exact absurd hcnt (hcR c h)
              rw [← hcc0] at hch
              obtain ⟨hLs, hRs⟩ := sib_order (children_sorted M i) hch
              have hclM : CL M i = Lp.filter (fun d => decide (Counted M i d)) ++ [c] := by
                unfold CL
                rw [hch, List.filter_append, List.filter_cons, if_pos (by simpa using hcnt)]
                have : R.filter (fun d => decide (Counted M i d)) = [] := by
                  rw [List.filter_eq_nil_iff]; intro d hd; simpa using hcR d hd
                rw [this]
              set Lc := Lp.filter (fun d => decide (Counted M i d)) with hLc
              have hb : par M 0 r = some i → col M r = bump M i := by
                intro hig
                have hri : r ∈ children M i := mem_children_iff.mpr ⟨by omega, hig⟩
                have hrR : r ∈ R := by
                  rw [hch] at hri
                  rcases List.mem_append.mp hri with h | h
                  · have := hLs r h; omega
                  · rcases List.mem_cons.mp h with h | h
                    · omega
                    · exact h
                by_contra hb
                exact hcR r hrR ⟨hb, by rw [not_topped_r hlen hL hp he2]; simp⟩
              have hclN : CL (TRIO.gexp M r L 0 0 n) i = Lc ++ [c] := by
                rw [cl_N_eq hlen hL hp hn hR0 hZ2 he2 hn2 hi hb, hclM]
              have hsame : ∀ d ∈ Lc, σ.o d = ρ.o d := fun d hd => by
                have hd' := List.mem_filter.mp hd
                have hdc : Counted M i d := by simpa using hd'.2
                have := hLs d hd'.1
                exact (hoffD d (by omega)).1 (hLnd d hd'.1 hdc)
              have hcK : rk true c < K := by have := hRc c hc hcb hcu; omega
              have hIH := ih _ hcK true c (le_refl _) hcr
              have hcM : c < M.length := by omega
              have hcN := hiN c hcr
              have hOTc' : isOT (σ.o c) = true := hIH.1
              have hlc : Lhd z (σ.o c) (ρ.o c) := hIH.2.1 hdc
              -- the singles and the decrease at `i` in both
              obtain ⟨hsM, hpM⟩ := cl_vals hC hG hiM
              have hsMc : ∀ d ∈ CL M i, Single (ρ.o d) := fun d hd => single_o hC hG
                (mem_children (cl_mem_children hd)).2
              have hsNc : ∀ d ∈ CL (TRIO.gexp M r L 0 0 n) i, Single (σ.o d) := by
                intro d hd
                rw [hclN] at hd
                rcases List.mem_append.mp hd with hd | hd
                · rw [hsame d hd]; exact hsMc d (by rw [hclM]; exact List.mem_append_left _ hd)
                · simp at hd; rw [hd]; exact ⟨hOTc', o_psi_form hCN hcN⟩
              have hpN0 : ((CL (TRIO.gexp M r L 0 0 n) i).map σ.o).Pairwise (fun a b => b ≤ a) := by
                have hpM' := hpM
                rw [hclM] at hpM'
                rw [hclN, List.map_append, List.map_singleton, List.map_congr_left hsame]
                rw [List.map_append, List.map_singleton] at hpM'
                exact pairwise_snoc_le hpM' (le_of_lt hlc.1)
              obtain ⟨s, y, hsy⟩ := (single_o hC hG hcM).2
              obtain ⟨s', y', hs'y'⟩ := (show Single (σ.o c) from ⟨hOTc', o_psi_form hCN hcN⟩).2
              have hformM := o_last_form hC hiM hvot hclM hsMc hpM hsy
              have hformN := o_last_form hCN (hiN i hi) (by rw [hv']; exact hvot) hclN hsNc hpN0 hs'y'
              rw [List.map_congr_left hsame, hv'] at hformN
              set a := ρ.v i with ha
              set B := spArg a z (sumN (Lc.map ρ.o)) with hB
              have hBot : isOT B = true := isOT_arg (hFO i hiM Lc c [] (by rw [hclM]))
              have hc0 : isOT (psi s y z) = true := by rw [← hsy]; exact hG.ot_o c hcM
              have hc0' : isOT (psi s' y' z) = true := by rw [← hs'y']; exact hOTc'
              have hpL : ((Lc.map ρ.o) ++ [ρ.o c]).Pairwise (fun a b => b ≤ a) := by
                have := hpM; rw [hclM, List.map_append, List.map_singleton] at this; exact this
              have hBc : ∀ q ∈ summands B, psi s y z ≤ q := by
                have hLs := sumN_dec (Lc.map ρ.o) (fun t ht => by
                  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
                  exact hsMc d (by rw [hclM]; exact List.mem_append_left _ hd))
                  (List.pairwise_append.mp hpL).1
                apply spArg_summands_ge ⟨s, y, rfl⟩ (sumN (Lc.map ρ.o)) z hLs.1
                · rw [hLs.2]; intro q hq
                  have := (List.pairwise_append.mp hpL).2.2 q hq (ρ.o c) (by simp)
                  rwa [hsy] at this
                · simp [summands]
              -- the child: same `v` (argument relation) or a bare changed `v`
              have hchC : (s' = s ∧ Lhd z y' y ∧ ClsABC B s y' y (Trig a B s y)) ∨
                  (y = z ∧ y' = z ∧ Lhd z s' s ∧
                    (¬ psi s z z < psi (succ a) z z → ¬ psi s' z z < psi (succ a) z z)) := by
                by_cases hvc : σ.v c = ρ.v c
                · obtain ⟨X, X', hX, hX', hlX, hclsX⟩ := hIH.2.2 rfl hdc hvc
                  rw [hsy] at hX; rw [hs'y'] at hX'
                  simp only [psi.injEq] at hX hX'
                  obtain ⟨hs1, hy1, -⟩ := hX
                  obtain ⟨hs2, hy2, -⟩ := hX'
                  have es : s' = s := hs2.trans hs1.symm
                  subst es; subst hy1; subst hy2
                  refine Or.inl ⟨rfl, hlX, ?_⟩
                  rw [← hs1] at hclsX
                  rcases hclsX with hA | hB0 | hC
                  · exact Or.inl hA
                  · exact Or.inr (Or.inl ⟨hB0.1, hB0.2, hTrigB i c Lc hi hcr hclM hdc _ _ _
                      (by rw [hsy]) (by rw [hs'y']) hlX hB0.1 hB0.2⟩)
                  · exact Or.inr (Or.inr hC)
                · have hdv : DepX M (r + L) false c := by
                    by_contra hn'; exact hvc ((hoffD c hcr).2 hn')
                  have hvK : rk false c < K := by have := (hRM c hcM).1; omega
                  have hvIH := ih _ hvK false c (le_refl _) hcr
                  have hclc := cl_nil_of_depv' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hcr hdv
                  have hoN := o_N_noc' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 he2 hn2 hC hG hCN hcr hclc
                    hvIH.1
                  have hoM := o_of_no_counted hC hcM (hG.ot_v c hcM) (no_cnt_of_cl_nil hclc)
                  rw [hsy] at hoM; rw [hs'y'] at hoN
                  simp only [psi.injEq] at hoM hoN
                  obtain ⟨rfl, rfl, -⟩ := hoM
                  obtain ⟨rfl, rfl, -⟩ := hoN
                  exact Or.inr ⟨rfl, rfl, hvIH.2.1 hdv, hVchg i c Lc hi hcr hclM hdc hvc⟩
              have hch : (s' = s ∧ Lhd z y' y ∧ ClsABC B s y' y (Trig a B s y)) ∨
                  (y = z ∧ y' = z ∧ Lhd z s' s) := by
                rcases hchC with h | ⟨h1, h2, h3, _⟩
                · exact Or.inl h
                · exact Or.inr ⟨h1, h2, h3⟩
              have hA := node_arg_lhd (a := a) hc0 hc0' hBc hch
              exact ⟨_, _, hformM, hformN, hA, isOT_step hBot hc0', cls_node hc0 hc0' hBc hchC⟩
  intro b i hi
  exact key _ b i (le_refl _) hi

end

/-- **`hOTD` of `t0_core`** from the residuals: the rewrite agreement at class-B0 children (`hTrigBN`),
a changed `v` of a child stays at least `Ω_{a+1}` (`hVchgN`), the class at `g` (`hClsGN`), and `g` when
no middle copy root counts (`hG0N`). -/
theorem t0_otd {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (hp : par M 0 (r + L) = some r) (he1 : entry M 1 (r + L) = 0)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hVS : VSmallF M ρ) (hF : FrameClosed M ρ) (hFO : FrameOT M ρ)
    (hArgT : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL (M.take (r + L)) i = Lc ++ [cs] →
      ∀ s y, (drop1 M (r + L) rkM).o cs = psi s y z → ¬ lt s (ρ.v i) = true →
      ∀ g ∈ comps (ρ.v i) y, g ≤ step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y z)
    (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAbs : BumpAbsC M (r + L) ρ)
    (hWS : BumpWeakSrc M (r + L) ρ (drop1 M (r + L) rkM))
    (hVSt : VSmallNew M (r + L) ρ (drop1 M (r + L) rkM))
    (hUA : UpgAbsX M (r + L) ρ)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hLast : ∀ n, 2 ≤ n → ∀ g, par M 0 r = some g → Counted M g r →
      Counted (TRIO.gexp M r L 0 0 n) g (r + (n - 1) * L))
    (hTrigBN : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → Lhd z y' y →
      (split y' (psi (succ s) z z)).2 = z → (split y (psi (succ s) z z)).2 = z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true)
    (hVchgN : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      σ.v c ≠ ρ.v c → ¬ psi (ρ.v c) z z < psi (succ (ρ.v i)) z z →
      ¬ psi (σ.v c) z z < psi (succ (ρ.v i)) z z)
    (hClsGN : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → ∀ g, par M 0 r = some g →
      Counted M g r → ∀ X X', ρ.o g = psi (ρ.v g) X z → σ.o g = psi (ρ.v g) X' z → ClsNode (ρ.v g) X' X)
    (hG0N : ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ → ∀ g, par M 0 r = some g →
      Counted M g r → (∀ k, k + 1 < n → ¬ Counted (TRIO.gexp M r L 0 0 n) g (r + k * L)) →
      ∃ X X', ρ.o g = psi (ρ.v g) X z ∧ σ.o g = psi (ρ.v g) X' z ∧ Lhd z X' X ∧ isOT X' = true) :
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i, i < r → DepX M (r + L) true i → isOT (σ.o i) = true ∧ (σ.v i = ρ.v i →
        ∃ X X', ρ.o i = psi (ρ.v i) X z ∧ σ.o i = psi (ρ.v i) X' z ∧ Lhd z X' X) ∧
        (σ.v i ≠ ρ.v i → σ.o i = psi (σ.v i) z z) := by
  intro n hn2 σ hCN
  have hn : 1 ≤ n := by omega
  have hx : r + L + 1 = M.length := hlen
  have hx2 : entry M 2 (r + L) = 0 := hR12 _ he1
  -- the drop `M.take x`
  have hcnt := hcnt_t1 hlen hR0 hZ2 hSD hZ1 hUAT
  have hRk1 : Rk (M.take (r + L)) rkM := rk_take (by omega) hRM hcnt
  set ρ' := drop1 M (r + L) rkM with hρ'
  have hC1 : Cons (M.take (r + L)) ρ' := cons_of_rk hRk1
  have hdrop := drop_all (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hVS hVSt hF hFO hArgT
    (bump_drop (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hKD hTD hAbs hWS) hUA
  have hoff := chg_off (show r + L + 1 = M.length from hlen) hC hG hC1 hRk1
  have hVT : ValInv (M.take (r + L)) ρ' :=
    drop_pres (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC
      ⟨hG, hVS, hF, hFO, hKD, hTD⟩ ⟨hArgT, hVSt, hWS, hUA, hAbs⟩ hC1 hRk1
  have hnx : ¬ DepX M (r + L) false (r + L) := not_depX_v_x he1
  have hD := dep_strict0 (by omega) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop hx2 hp hnx
  -- the expansion `N`
  set N := TRIO.gexp M r L 0 0 n with hNdef
  have hlN : N.length = r + n * L := lenN0 hlen hn
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hnl : (n - 1) * L + L = n * L := by rw [← Nat.succ_mul]; congr 1; omega
  have hRN := rk_N0 hlen hL hp hn hR0 hZ2 hx2 hn2 hRM
  -- the values of `N`
  have hvC := t0_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hn2 (depLike_chgX M (r + L))
    (read_not_chg hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB) hC hG hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hvD := t0_vals hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hn2 (depLike_depX M (r + L))
    (read_not_dep hlen hL hp hR0 hZ2 hSD hZ1 hUAT hUAB) hC hG hC1
    (fun i hi h => (hoff i hi).2 h) hCN hRN
  have hoffD : ∀ i, i < r → (¬ DepX M (r + L) true i → σ.o i = ρ.o i) ∧
      (¬ DepX M (r + L) false i → σ.v i = ρ.v i) := by
    intro i hi
    have h := hvD i (by rw [hlN]; omega)
    exact ⟨fun hd => by rw [h.1 (fun h' => hd h'.2), tau_o_lt hi],
      fun hd => by rw [h.2 (fun h' => hd h'.2), tau_v_lt hi]⟩
  have hσB : ∀ i, r ≤ i → i < N.length → σ.o i = (tauN r L n ρ ρ' (omid M r L ρ)).o i :=
    fun i hri hiN => (hvC i hiN).1 (fun h => by omega)
  have hσmid : ∀ k, k + 1 < n → σ.o (r + k * L) = omid M r L ρ := by
    intro k hk
    have : k * L + L ≤ n * L := by
      have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this; exact this
    rw [hσB _ (by omega) (by rw [hlN]; omega)]
    exact tau_o_root hk hL
  have hσlast : σ.o (r + (n - 1) * L) = ρ'.o r := by
    rw [hσB _ (by omega) (by rw [hlN]; omega)]
    have := tau_o_last (r := r) (L := L) (n := n) (ρ := ρ) (ρ' := ρ') (oMid := omid M r L ρ) hL
    rwa [Nat.add_zero, Nat.add_zero] at this
  have hGT := good3_take (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hdrop
  obtain ⟨hor, hom⟩ := o_r_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG
  -- roots, frames
  have hOXle : omid M r L ρ ≤ ρ.o r := by
    rw [hor, hom]; exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one _⟩))
  have hlt0 : ρ'.o r < ρ.o r :=
    hD true r (depLike_r hlen hL hp hx2 (depLike_depX M (r + L))) (by omega)
  have hO'le : ρ'.o r ≤ omid M r L ρ := by
    obtain ⟨_, s', y', hs'⟩ := (hdrop r (by omega)).1.2
    have h := hlt0
    rw [hs', hor] at h
    rw [hs', hom]
    rcases psi_lt_psi_z_iff.mp h with h1 | ⟨rfl, h2⟩
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h1))
    · exact psi_le_psi_arg ((lt_succ_iff (x := _)).mp h2)
  have hσBv : ∀ i, r ≤ i → i < N.length → σ.v i = (tauN r L n ρ ρ' (omid M r L ρ)).v i :=
    fun i hri hiN => (hvC i hiN).2 (fun h => by omega)
  have hFOT : FrameOT (M.take (r + L)) ρ' :=
    frameOT_take (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hFO
  by_cases hrg : ∃ g, par M 0 r = some g
  · obtain ⟨g, hg⟩ := hrg
    have hgr : g < r := par_lt M 0 r g hg
    have hrc : r ∈ children M g := mem_children_iff.mpr ⟨by omega, hg⟩
    have hxr : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hp⟩
    -- the drop at `r`
    have hDr : DepX M (r + L) true r := depLike_r hlen hL hp hx2 (depLike_depX M (r + L))
    have hlt : ρ'.o r < ρ.o r := hD true r hDr (by omega)
    have hl : Lhd z (ρ'.o r) (ρ.o r) := by
      rcases (hdrop r (by omega)).1.1 with hE | ⟨_, w, hw⟩
      · exact lhd_of_lhdE_lt hE hlt
      · exfalso
        rw [hor] at hw; simp only [psi.injEq] at hw
        have := lt_app_one (spArg (ρ.v r) z
          (sumN (((children M r).filter (fun c => decide (c < r + L))).map (cnt M ρ r))))
        rw [hw.2.1] at this; exact T.not_lt_z _ this
    have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
    have hy' : ∀ s' y', ρ'.o r = psi s' y' z → s' ≠ ρ.v r → y' = z := by
      intro s' y' hs hne
      obtain ⟨y0, hy0⟩ := o_psi_sub hC1 hrT
      rw [hs] at hy0; simp only [psi.injEq] at hy0
      have hv'ot := (hdrop r (by omega)).2.2
      rw [sf_ot hv'ot] at hy0
      have hCv : ChgX M (r + L) false r := by
        by_contra hn'; apply hne; rw [hy0.1]; exact (hoff r (by omega)).2 hn'
      have hT := (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hCv).1 rfl (by omega)
      have ho := o_of_no_counted hC1 hrT hv'ot hT.2.1
      rw [hs] at ho; simp only [psi.injEq] at ho; exact ho.2.1
    have hG0le : ∀ g', par M 0 r = some g' → col M r = bump M g' → entry M 1 g' ≠ 0 → entry M 2 g' ≠ 0 →
        sumN ((children (M.take (r + L)) r).map ρ'.o) ≤ sumN ((children (M.take (r + L)) r).map ρ.o) := by
      intro g' hg' hjb h1 h2
      have hgg : g' = g := Option.some.inj (hg'.symm.trans hg)
      rw [hgg] at hjb h1 h2
      exact (brelS_lhdE (g0_drop_rel (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG
        hC1 hRk1 hKD hWS h1 h2 hrc hjb hxr (o_x_one hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG)
        (fun k _ hk => hdrop k hk)
        (fun k hk hkx _ => v_lhd_B (show r + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hp
          hC hG hC1 hRk1 hKD hTD hAbs hWS hUA hdrop k (mem_children hk).1 hkx)).2).le
    -- seed S2
    have hS2 : col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → Lhd z (σ.v g) (ρ.v g) := by
      intro hjb h1 h2
      have hgD : DepX M (r + L) false g := DepX.vbump h1 h2 hrc hjb hxr DepX.leaf
      obtain ⟨_, hpnd, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hp (by omega) hgD
      rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j', k', hch, _, hchj, _, hKnd, hLnd⟩
      · exact absurd h2' h2
      · have hchM := children_g_last hlen hL hp hg
        have hjr : j' = r := by
          have := congrArg List.getLast? (hch.symm.trans hchM)
          simpa using this
        subst hjr
        -- the children of `r` in `M.take x` and the last copy
        have hdropR : isOT (sumN ((children (M.take (j' + L)) j').map ρ'.o)) = true ∧
            BRelS (sumN ((children (M.take (j' + L)) j').map ρ'.o))
              (sumN ((children (M.take (j' + L)) j').map ρ.o)) :=
          g0_drop_rel (show j' + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1 hKD hWS
            h1 h2 hrc hjb hxr (o_x_one hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG)
            (fun k _ hk => hdrop k hk)
            (fun k hk hkx _ => v_lhd_B (show j' + L + 1 = M.length from hlen) hR0 hZ2 hSD hZ1 hUAT hUAB hp
              hC hG hC1 hRk1 hKD hTD hAbs hWS hUA hdrop k (mem_children hk).1 hkx)
        have hG0ot : isOT (sumN ((children (M.take (j' + L)) j').map ρ.o)) = true := isOT_sumN _ (fun t ht => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
          rw [children_take, List.mem_filter] at hc
          exact hG.ot_o c (mem_children hc.1).2)
        have hcopy : ∀ k, k < n → bumpTerm N σ g (j' + k * L) =
            omega (sumN (((children M j').filter (fun c => decide (c < j' + L))).map
              (σ.o ∘ shk j' (k * L)))) := by
          intro k hk
          have hcolk : col N (j' + k * L) = bump N g := by
            rw [col_root0 hlen hL hp hn hk, bump_pre0 hlen hL hp hn (by omega)]; exact hjb
          unfold bumpTerm
          rw [if_pos hcolk]
          have hch0 := children_copy0 hlen hL hp hn (k := k) (q := 0) hk hL
          rw [Nat.add_zero, Nat.add_zero] at hch0
          rw [hch0, List.map_map]
        apply t0_S2G (O' := omega (sumN ((children (M.take (j' + L)) j').map ρ'.o))) hlen hL hp hn hR0 hZ2
          hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hg hjb h1 h2 hTD hAbs
        · intro d hd hdr
          have hdL : d ∈ Lb := by
            rw [hch] at hd
            rcases List.mem_append.mp hd with h | h
            · exact h
            · simp at h; omega
          have hdg : par M 0 j' ≠ some d := by
            intro h'; rw [hg] at h'; cases h'; have := (mem_children hd).1; omega
          apply bumpTerm_eq_of
          · rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
          · intro _
            rw [children_pre0 hlen hL hp hn hdr hdg]
            apply List.map_congr_left
            intro e he
            have her := children_lt_r hlen hL hp hdr hdg he
            exact (hoffD e her).1 (hLnd d hdL e he).2
        · intro k hkn
          rw [hcopy k (by omega), children_take]
          congr 1; congr 1
          apply List.map_congr_left
          intro c hc
          rw [List.mem_filter] at hc
          have hcgt := (mem_children hc.1).1
          have hcx : c < j' + L := by simpa using hc.2
          obtain ⟨q', rfl⟩ : ∃ q', c = j' + q' := ⟨c - j', by omega⟩
          simp only [Function.comp]
          rw [shk_B, hσB _ (by omega) (by
            rw [hlN]; have : k * L + L ≤ n * L := by
              have := Nat.mul_le_mul_right L (show k + 1 ≤ n by omega); rw [Nat.succ_mul] at this
              exact this
            omega), tau_o_mid hkn (by omega) (by omega)]
        · rw [hcopy (n - 1) (by omega), children_take]
          congr 1; congr 1
          apply List.map_congr_left
          intro c hc
          rw [List.mem_filter] at hc
          have hcgt := (mem_children hc.1).1
          have hcx : c < j' + L := by simpa using hc.2
          obtain ⟨q', rfl⟩ : ∃ q', c = j' + q' := ⟨c - j', by omega⟩
          simp only [Function.comp]
          rw [shk_B, hσB _ (by omega) (by rw [hlN]; omega), tau_o_last (by omega)]
        · exact single_omega hdropR.1
        · exact brelS_lhdE (brelS_omega hdropR.1 hG0ot hdropR.2)
        · rw [par1_pre0 hlen hL hp hn hgr]
          cases hpp : par M 1 g with
          | none => rfl
          | some m =>
            have := par_lt M 1 g m hpp
            exact (hoffD m (by omega)).2 (hpnd m hpp)
    -- seed S3
    have hS3 : ∀ pp, par M 0 g = some pp → entry M 1 pp ≠ 0 → entry M 2 pp ≠ 0 → col M g = bump M pp →
        Lhd z (σ.v pp) (ρ.v pp) := by
      intro pp hpg h1 h2 hjb
      have hppg := par_lt M 0 g pp hpg
      have hgp : g ∈ children M pp := mem_children_iff.mpr ⟨by omega, hpg⟩
      have hpD : DepX M (r + L) false pp := DepX.vbump h1 h2 hgp hjb hrc hDr
      obtain ⟨_, hpnd, hcase⟩ := dv_shape hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hp (by omega) hpD
      rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j', k', hch, _, hchj, _, hKnd, hLnd⟩
      · exact absurd h2' h2
      · have hjg : j' = g := by
          by_contra hne
          have hgL : g ∈ Lb := by
            rw [hch] at hgp
            rcases List.mem_append.mp hgp with h | h
            · exact h
            · simp at h; exact absurd h.symm hne
          exact (hLnd g hgL r hrc).2 hDr
        subst hjg
        have hkr : k' = r := by
          have hchM := children_g_last hlen hL hp hg
          rw [hchj] at hchM
          have := congrArg List.getLast? hchM
          simpa using this
        rw [hkr] at hchj
        have hLj : ∀ d ∈ Lb, d < j' :=
          (sib_order (children_sorted M pp) (R := []) (by rw [hch])).1
        apply t0_S3 hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hg hpg hjb h1 h2
          hTD hKD hAbs hch
        · intro d hd
          have hdg : par M 0 r ≠ some d := fun h =>
            (hLnd d hd r (mem_children_iff.mpr ⟨by have := hLj d hd; omega, h⟩)).2 hDr
          have hdj := hLj d hd
          apply bumpTerm_eq_of
          · rw [col_pre0 hlen hL hp hn (by omega), bump_pre0 hlen hL hp hn (by omega)]
          · intro _
            rw [children_pre0 hlen hL hp hn (by omega) hdg]
            apply List.map_congr_left
            intro e he
            have her := children_lt_r hlen hL hp (by omega) hdg he
            exact (hoffD e her).1 (hLnd d hd e he).2
        · intro d hd hdr
          have hdK : d ∈ Kb := by
            rw [hchj] at hd
            rcases List.mem_append.mp hd with h | h
            · exact h
            · simp at h; omega
          exact (hoffD d hdr).1 (hKnd d hdK)
        · exact hor
        · intro k hk; rw [hσmid k hk, hom]
        · rw [hσlast]; exact hl
        · rw [par1_pre0 hlen hL hp hn (by omega)]
          cases hpp : par M 1 pp with
          | none => rfl
          | some m =>
            have := par_lt M 1 pp m hpp
            exact (hoffD m (by omega)).2 (hpnd m hpp)
        · intro k hk
          by_cases hkn : k + 1 < n
          · rw [hσmid k hkn]; exact isOT_omid hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN
          · rw [show k = n - 1 by omega, hσlast]; exact hGT.ot_o r (by rw [List.length_take]; omega)
    intro i hi hd
    exact (t0_dep_ot hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hg hRM hC1 hGT hσB hσBv
      hoffD hσmid hσlast hFO hTD hKD hAbs hl hy' (hLast n hn2 g hg) hS3 hS2 (hTrigBN n hn2 σ hCN)
      (hVchgN n hn2 σ hCN) (hClsGN n hn2 σ hCN g hg) (hG0N n hn2 σ hCN g hg) true i hi) |> fun h =>
      ⟨h.1, (fun hv => let ⟨X, X', a1, a2, a3, _⟩ := h.2.2 rfl hd hv; ⟨X, X', a1, a2, a3⟩), fun hne => by
        have hdv : DepX M (r + L) false i := by
          by_contra hn'; exact hne ((hoffD i hi).2 hn')
        have hvot := (t0_dep_ot hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hg hRM hC1 hGT
          hσB hσBv hoffD hσmid hσlast hFO hTD hKD hAbs hl hy' (hLast n hn2 g hg) hS3 hS2 (hTrigBN n hn2 σ hCN)
          (hVchgN n hn2 σ hCN) (hClsGN n hn2 σ hCN g hg) (hG0N n hn2 σ hCN g hg) false i hi).1
        exact o_N_noc' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hCN hi
          (cl_nil_of_depv' hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hx2 hn2 hC hG hi hdv) hvot⟩
  · have hrn : par M 0 r = none := by
      cases h : par M 0 r with
      | none => rfl
      | some g => exact absurd ⟨g, h⟩ hrg
    intro i hi hd
    have := nodep_G_root hlen hL hp hn hR0 hZ2 hSD hZ1 hUAT hUAB he1 hrn true i hd
    omega

end Ytosk
