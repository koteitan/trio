/-
**正規化 sp と基本列の交換（方針 B の項の部品）。**

経路の節点 h で、子の並びの最後の子の値 c を基本列 c[η] に置き換えると、h の正規化した値も基本列で置き換わる:
fs(ψ_a(spArg(a, b, c)), η) = ψ_a(spArg(a, b, c[η]))。ここでは c が書き換えを起こさない通過の場合（`spArg_fs_pass`）。
-/
import Ytosk.FS
import Ytosk.Chain

namespace Ytosk

open T

/-- The cofinality of a sum is that of its last summand. -/
theorem cof_app : ∀ (B : T) {c : T}, c ≠ z → cof (app B c) = cof c
  | z, _, _ => by simp
  | psi a b B', c, hc => by
    simp only [app_psi]
    cases hB : app B' c with
    | z => exact absurd (app_eq_z hB).2 hc
    | psi d e f =>
      show cof (psi a b (psi d e f)) = cof c
      rw [← hB, ← cof_app B' hc]
      simp only [cof, hB]

/-- The fundamental sequence of a sum acts on its last summand. -/
theorem fs_app : ∀ (B : T) {c : T}, c ≠ z → ∀ η, fs (app B c) η = app B (fs c η)
  | z, _, _, _ => by simp
  | psi a b B', c, hc, η => by
    simp only [app_psi]
    cases hB : app B' c with
    | z => exact absurd (app_eq_z hB).2 hc
    | psi d e f =>
      show fs (psi a b (psi d e f)) η = psi a b (app B' (fs c η))
      rw [← fs_app B' hc η, hB]
      rfl

theorem isSucc_psi_rest (a b c : T) (hc : c ≠ z) : isSucc (psi a b c) = isSucc c := by
  cases c with
  | z => exact absurd rfl hc
  | psi => rfl

theorem not_succ_of_cof_big : ∀ {c μ : T}, cof c = .big μ → isSucc c = false
  | z, _, h => by simp [cof] at h
  | psi a b (psi d e f), μ, h => by
    rw [isSucc_psi_rest _ _ _ (by simp)]
    exact not_succ_of_cof_big (by simpa [cof] using h)
  | psi a b z, μ, h => by
    simp only [isSucc, last, beq_eq_false_iff_ne]
    intro h1
    simp only [one, psi.injEq, and_true] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simp [cof] at h

/-- The fundamental sequence passes through `ψ_a` when the argument has cofinality `Ω_{μ+1}`, `μ < a`. -/
theorem fs_psi_pass {a X μ : T} (hX : X ≠ z) (hc : cof X = .big μ) (hμ : lt μ a = true) (η : T) :
    fs (psi a X z) η = psi a (fs X η) z := by
  conv => lhs; unfold fs
  rw [if_neg hX, if_neg (by rw [not_succ_of_cof_big hc]; simp), hc]
  simp only [if_pos hμ]

theorem cof_psi_pass {a X μ : T} (hX : X ≠ z) (hc : cof X = .big μ) (hμ : lt μ a = true) :
    cof (psi a X z) = .big μ := by
  have hs := not_succ_of_cof_big hc
  simp [cof, hX, hs, hc, hμ]

theorem summand_lev_lt {η a : T} (hη : isOT η = true) (h : η < psi a z z) :
    ∀ s y, psi s y z ∈ summands η → s < a := by
  intro s y hq
  have h1 : psi s y z < psi a z z := lt_of_le_of_lt (le_trans (summands_le_head hη _ hq)
    (head_le_self η)) h
  rw [psi_lt_psi_z_iff] at h1
  rcases h1 with h1 | ⟨_, h1⟩
  · exact h1
  · exact absurd h1 (T.not_lt_z _)

/-- After a non-rewriting last summand, its fundamental sequence does not rewrite either. -/
theorem notrig_fs {a b s y μ η : T} (hc : isOT (psi s y z) = true) (hcof : cof (psi s y z) = .big μ)
    (hμ : lt μ a = true) (hη : isOT η = true) (hηl : η < psi (succ μ) z z)
    (hno : y ≤ b ∨ s < a) :
    ∀ s' y', psi s' y' z ∈ summands (fs (psi s y z) η) → y' ≤ b ∨ s' < a := by
  have hv : Valid (psi s y z) η := ⟨hη, by rw [hcof]; exact hηl⟩
  obtain ⟨hfot, hflt⟩ := fs_ot_lt hc hv
  rcases hno with hyb | hsa
  · by_cases hsa : s < a
    · intro s' y' hq
      right
      have h1 : psi s' y' z ≤ psi s y z :=
        le_trans (summands_le_head hfot _ hq) (le_trans (head_le_of_lt hflt) (le_refl _))
      rcases (le_iff _ _).mp h1 with h1 | h1
      · rw [psi_lt_psi_z_iff] at h1
        rcases h1 with h1 | ⟨rfl, _⟩
        · exact lt_trans h1 hsa
        · exact hsa
      · simp only [psi.injEq] at h1; rw [h1.1]; exact hsa
    · unfold fs at hfot ⊢
      by_cases hy : y = z
      · subst hy
        rw [if_pos rfl]
        have hs : s ≠ z := by rintro rfl; simp [cof] at hcof
        rw [if_neg hs]
        have hc0 : cof (psi s z z) = (if isSucc s then Cof.big (init s) else cof s) := by
          simp [cof, hs]
        rw [hc0] at hcof
        by_cases hss : isSucc s = true
        · rw [if_pos hss]
          rw [if_pos hss] at hcof; cases hcof
          -- `μ < a ≤ s = μ + 1`, so `a = s`
          have hsa' : a ≤ s := le_of_not_gt hsa
          have has : a = s := by
            have h1 : succ (init s) ≤ a := succ_le_of_lt hμ
            unfold succ at h1; rw [init_app_one hss] at h1
            exact le_antisymm hsa' h1
          intro s' y' hq
          right
          rw [has]
          have : η < psi s z z := by unfold succ at hηl; rwa [init_app_one hss] at hηl
          exact summand_lev_lt hη this s' y' hq
        · rw [if_neg hss]
          intro s' y' hq
          simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hq
          left; rw [hq.2.1]; exact z_le _
      · rw [if_neg hy]
        have hys : isSucc y = false := by
          cases h' : isSucc y with
          | false => rfl
          | true =>
            exfalso
            have : cof (psi s y z) = .omega := by simp [cof, hy, h']
            rw [this] at hcof; cases hcof
        rw [if_neg (by rw [hys]; decide)]
        have hc0 : cof (psi s y z) = (match cof y with
            | .big μ => if lt μ s = true then Cof.big μ else Cof.omega
            | c => c) := by
          show (if y = z then _ else if isSucc y then Cof.omega else _) = _
          rw [if_neg hy, hys]; rfl
        rw [hc0] at hcof
        cases hcy : cof y with
        | big ν =>
          rw [hcy] at hcof; simp only at hcof ⊢
          by_cases hνs : lt ν s = true
          · rw [if_pos hνs] at hcof ⊢
            intro s' y' hq
            simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hq
            left; rw [hq.2.1]
            cases hcof
            exact le_of_lt (lt_of_lt_of_le (fs_lt (by unfold ValidLt; rw [hcy]; exact hηl)) hyb)
          · rw [if_neg hνs] at hcof; cases hcof
        | zero => rw [hcy] at hcof; cases hcof
        | succ => rw [hcy] at hcof; cases hcof
        | omega => rw [hcy] at hcof; cases hcof
  · intro s' y' hq
    right
    have h1 : psi s' y' z ≤ psi s y z :=
      le_trans (summands_le_head hfot _ hq) (le_trans (head_le_of_lt hflt) (le_refl _))
    rcases (le_iff _ _).mp h1 with h1 | h1
    · rw [psi_lt_psi_z_iff] at h1
      rcases h1 with h1 | ⟨rfl, _⟩
      · exact lt_trans h1 hsa
      · exact hsa
    · simp only [psi.injEq] at h1; rw [h1.1]; exact hsa

/-- **Commutation, pass case.** The last child `ψ_s(y)` does not rewrite, and its cofinality `Ω_{μ+1}`
passes through `ψ_a` (`μ < a`): replacing it by its fundamental sequence replaces the node's value by its
fundamental sequence. -/
theorem spArg_fs_pass {a b s y μ η : T} (hc : isOT (psi s y z) = true)
    (hcof : cof (psi s y z) = .big μ) (hμ : lt μ a = true) (hη : isOT η = true)
    (hηl : η < psi (succ μ) z z) (hno : y ≤ b ∨ s < a) (hbc : isOT (app b (psi s y z)) = true) :
    fs (psi a (spArg a b (psi s y z)) z) η = psi a (spArg a b (fs (psi s y z) η)) z := by
  have hv : Valid (psi s y z) η := ⟨hη, by rw [hcof]; exact hηl⟩
  obtain ⟨hfot, hflt⟩ := fs_ot_lt hc hv
  have hcz : psi s y z ≠ z := by simp
  have h1 : spArg a b (psi s y z) = app b (psi s y z) := by
    apply spArg_eq_app hbc
    intro s' y' hq
    simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hq
    obtain ⟨rfl, rfl, _⟩ := hq; exact hno
  have hXz : app b (psi s y z) ≠ z := fun h => hcz (app_eq_z h).2
  rw [h1, fs_psi_pass hXz (by rw [cof_app b hcz]; exact hcof) hμ, fs_app b hcz]
  have hbot : isOT b = true := isOT_app_left hbc
  have hbf : isOT (app b (fs (psi s y z) η)) = true := by
    apply isOT_app_of hbot hfot
    intro q hq
    exact le_trans (head_le_of_lt hflt) (summand_ge_of_app hbc hq)
  rw [spArg_eq_app hbf (notrig_fs hc hcof hμ hη hηl hno)]

/-- The comparison with `Ω_a` in a step does not depend on a nonzero argument. -/
theorem trig_cond {a s y y' : T} (hy : y ≠ z) (hy' : y' ≠ z) :
    lt (psi a z z) (psi s y z) = lt (psi a z z) (psi s y' z) := by
  cases y with
  | z => exact absurd rfl hy
  | psi =>
    cases y' with
    | z => exact absurd rfl hy'
    | psi => simp [lt]

/-- Inverting the cofinality of a collapse: `cof (ψ_s(y)) = Ω_{μ+1}` with `y ≠ 0` passes through `ψ_s`. -/
theorem cof_psi_inv {s y μ : T} (hy : y ≠ z) (h : cof (psi s y z) = .big μ) :
    cof y = .big μ ∧ lt μ s = true := by
  have hys : isSucc y = false := by
    cases h' : isSucc y with
    | false => rfl
    | true =>
      exfalso
      have : cof (psi s y z) = .omega := by simp [cof, hy, h']
      rw [this] at h; cases h
  have hc0 : cof (psi s y z) = (match cof y with
      | .big μ => if lt μ s = true then Cof.big μ else Cof.omega
      | c => c) := by
    show (if y = z then _ else if isSucc y then Cof.omega else _) = _
    rw [if_neg hy, hys]; rfl
  rw [hc0] at h
  cases hcy : cof y with
  | big ν =>
    rw [hcy] at h; simp only at h
    by_cases hν : lt ν s = true
    · rw [if_pos hν] at h; cases h; exact ⟨rfl, hν⟩
    · rw [if_neg hν] at h; cases h
  | zero => rw [hcy] at h; cases h
  | succ => rw [hcy] at h; cases h
  | omega => rw [hcy] at h; cases h

/-- **Commutation, rewriting case.** The last child `ψ_s(y)` rewrites to `H(s, y)` (with a lower part), the
fundamental sequence acts on the lower part of `y` and leaves it nonzero, and the state is still below the new
argument. -/
theorem spArg_fs_trig {a b s y μ η : T} (hc : isOT (psi s y z) = true)
    (hcof : cof (psi s y z) = .big μ) (hμ : lt μ a = true) (hη : isOT η = true)
    (hηl : η < psi (succ μ) z z)
    (htr : lt b y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hlo : (split y (psi (succ s) z z)).2 ≠ z)
    (hlo' : fs (split y (psi (succ s) z z)).2 η ≠ z)
    (hbη : lt b (fs y η) = true) :
    fs (psi a (spArg a b (psi s y z)) z) η = psi a (spArg a b (fs (psi s y z) η)) z := by
  have hy : y ≠ z := by rintro rfl; simp [lt] at htr
  obtain ⟨hcy, hμs⟩ := cof_psi_inv hy hcof
  have hyot := isOT_arg hc
  -- y = p ++ lo
  have hbpl := split_app (psi (succ s) z z) y
  have hpge := split_fst_ge (psi (succ s) z z) y
  have hlo1 := split_snd_head (psi (succ s) z z) y
  generalize hP : (split y (psi (succ s) z z)) = pr at hbpl hpge hlo1 hlo hlo'
  obtain ⟨p, lo⟩ := pr
  simp only at hbpl hpge hlo1 hlo hlo'
  have hloh : head lo < psi (succ s) z z := by rcases hlo1 with h | h; exact absurd h hlo; exact h
  -- the left side
  have hH : spArg a b (psi s y z) = app p (psi s y z) := by
    rw [spArg_cons]; show step a b s y z = _
    unfold step; rw [if_pos htr, H_eq hc, hP]; simp [hlo]
  have hcz : psi s y z ≠ z := by simp
  have hXz : app p (psi s y z) ≠ z := fun h => hcz (app_eq_z h).2
  rw [hH, fs_psi_pass hXz (by rw [cof_app p hcz]; exact hcof) hμ, fs_app p hcz,
    fs_psi_pass hy hcy hμs]
  -- the right side: `y[η] = p ++ lo[η]`, which splits at `p`
  have hfy : fs y η = app p (fs lo η) := by rw [← hbpl]; exact fs_app p hlo η
  have hlocof : cof lo = .big μ := by rw [← hcy, ← hbpl, cof_app p hlo]
  have hlolt : fs lo η < lo := fs_lt (by unfold ValidLt; rw [hlocof]; exact hηl)
  have hsp : split (fs y η) (psi (succ s) z z) = (p, fs lo η) := by
    rw [hfy]
    apply split_app_of hpge
    right; exact lt_of_le_of_lt (head_le_of_lt hlolt) hloh
  have hcη : isOT (psi s (fs y η) z) = true := by
    have := (fs_ot_lt hc ⟨hη, by rw [hcof]; exact hηl⟩).1
    rwa [fs_psi_pass hy hcy hμs] at this
  rw [spArg_cons]; show _ = psi a (step a b s (fs y η) z) z
  unfold step
  have hy' : fs y η ≠ z := by intro h; rw [h] at hbη; simp [lt] at hbη
  have htr' : lt b (fs y η) = true ∧ lt (psi a z z) (psi s (fs y η) z) = true :=
    ⟨hbη, by rw [← trig_cond hy hy']; exact htr.2⟩
  rw [if_pos htr', H_eq hcη, hsp]
  simp [hlo']

/-- **Commutation on the argument, non-rewriting case** (no condition on `ψ_a`). -/
theorem spArg_fs_arg_notrig {a b s y η : T} (hc : isOT (psi s y z) = true) (hv : Valid (psi s y z) η)
    (hno : y ≤ b ∨ s < a) (hbc : isOT (app b (psi s y z)) = true)
    (hno' : ∀ s' y', psi s' y' z ∈ summands (fs (psi s y z) η) → y' ≤ b ∨ s' < a) :
    fs (spArg a b (psi s y z)) η = spArg a b (fs (psi s y z) η) := by
  obtain ⟨hfot, hflt⟩ := fs_ot_lt hc hv
  have hcz : psi s y z ≠ z := by simp
  have h1 : spArg a b (psi s y z) = app b (psi s y z) := by
    apply spArg_eq_app hbc
    intro s' y' hq
    simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hq
    obtain ⟨rfl, rfl, _⟩ := hq; exact hno
  have hbot : isOT b = true := isOT_app_left hbc
  have hbf : isOT (app b (fs (psi s y z) η)) = true := by
    apply isOT_app_of hbot hfot
    intro q hq
    exact le_trans (head_le_of_lt hflt) (summand_ge_of_app hbc hq)
  rw [h1, fs_app b hcz, spArg_eq_app hbf hno']

/-- **Commutation on the argument, rewriting case.** -/
theorem spArg_fs_arg_trig {a b s y μ η : T} (hc : isOT (psi s y z) = true)
    (hcof : cof (psi s y z) = .big μ) (hη : isOT η = true) (hηl : η < psi (succ μ) z z)
    (htr : lt b y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hlo : (split y (psi (succ s) z z)).2 ≠ z)
    (hlo' : fs (split y (psi (succ s) z z)).2 η ≠ z)
    (hbη : lt b (fs y η) = true) :
    fs (spArg a b (psi s y z)) η = spArg a b (fs (psi s y z) η) := by
  have hy : y ≠ z := by rintro rfl; simp [lt] at htr
  obtain ⟨hcy, hμs⟩ := cof_psi_inv hy hcof
  have hbpl := split_app (psi (succ s) z z) y
  have hpge := split_fst_ge (psi (succ s) z z) y
  have hlo1 := split_snd_head (psi (succ s) z z) y
  generalize hP : (split y (psi (succ s) z z)) = pr at hbpl hpge hlo1 hlo hlo'
  obtain ⟨p, lo⟩ := pr
  simp only at hbpl hpge hlo1 hlo hlo'
  have hloh : head lo < psi (succ s) z z := by rcases hlo1 with h | h; exact absurd h hlo; exact h
  have hH : spArg a b (psi s y z) = app p (psi s y z) := by
    rw [spArg_cons]; show step a b s y z = _
    unfold step; rw [if_pos htr, H_eq hc, hP]; simp [hlo]
  have hcz : psi s y z ≠ z := by simp
  rw [hH, fs_app p hcz, fs_psi_pass hy hcy hμs]
  have hfy : fs y η = app p (fs lo η) := by rw [← hbpl]; exact fs_app p hlo η
  have hlocof : cof lo = .big μ := by rw [← hcy, ← hbpl, cof_app p hlo]
  have hlolt : fs lo η < lo := fs_lt (by unfold ValidLt; rw [hlocof]; exact hηl)
  have hsp : split (fs y η) (psi (succ s) z z) = (p, fs lo η) := by
    rw [hfy]
    apply split_app_of hpge
    right; exact lt_of_le_of_lt (head_le_of_lt hlolt) hloh
  have hcη : isOT (psi s (fs y η) z) = true := by
    have := (fs_ot_lt hc ⟨hη, by rw [hcof]; exact hηl⟩).1
    rwa [fs_psi_pass hy hcy hμs] at this
  rw [spArg_cons]; show _ = step a b s (fs y η) z
  unfold step
  have hy' : fs y η ≠ z := by intro h; rw [h] at hbη; simp [lt] at hbη
  have htr' : lt b (fs y η) = true ∧ lt (psi a z z) (psi s (fs y η) z) = true :=
    ⟨hbη, by rw [← trig_cond hy hy']; exact htr.2⟩
  rw [if_pos htr', H_eq hcη, hsp]
  simp [hlo']

theorem count_natT : ∀ n, count (natT n) = n
  | 0 => rfl
  | n + 1 => by simp [natT, count, count_natT n]

/-- The diagonal chain of `X` at `μ`: `γ_0 = 0`, `γ_{k+1} = ψ_μ(X[γ_k])`. -/
def gam (μ X : T) : Nat → T
  | 0 => z
  | k + 1 => psi μ (fs X (gam μ X k)) z

/-- **The diagonal node.** -/
theorem fs_psi_diag {a X μ : T} (hX : X ≠ z) (hc : cof X = .big μ) (hμ : ¬ lt μ a = true) (m : Nat) :
    fs (psi a X z) (natT m) = psi a (fs X (gam μ X m)) z := by
  conv => lhs; unfold fs
  rw [if_neg hX, if_neg (by rw [not_succ_of_cof_big hc]; simp), hc]
  simp only [if_neg hμ, count_natT]
  congr 2
  induction m with
  | zero => rfl
  | succ k ih => simp only [gam]; rw [← ih]

/-! ## 経路の文脈 -/

/-- Fill a path context (frames `(a, b)` from the hole upwards: subscript and state of the left siblings)
with the value `c` of the hole child. A missing child is the value `0` (`spArg a b z = b`). -/
def fillC : List (T × T) → T → T
  | [], c => c
  | (a, b) :: fr, c => fillC fr (psi a (spArg a b c) z)

/-- The commutation condition at one frame. -/
def FrameOK (a b c μ η : T) : Prop :=
  ∃ s y, c = psi s y z ∧ isOT c = true ∧ cof c = .big μ ∧ lt μ a = true ∧ isOT η = true ∧
    η < psi (succ μ) z z ∧
    (((y ≤ b ∨ s < a) ∧ isOT (app b c) = true) ∨
     ((lt b y = true ∧ lt (psi a z z) c = true) ∧ (split y (psi (succ s) z z)).2 ≠ z ∧
       fs (split y (psi (succ s) z z)).2 η ≠ z ∧ lt b (fs y η) = true))

theorem frame_fs {a b c μ η : T} (h : FrameOK a b c μ η) :
    fs (psi a (spArg a b c) z) η = psi a (spArg a b (fs c η)) z := by
  obtain ⟨s, y, rfl, hc, hcof, hμ, hη, hηl, h⟩ := h
  rcases h with ⟨hno, hbc⟩ | ⟨htr, hlo, hlo', hbη⟩
  · exact spArg_fs_pass hc hcof hμ hη hηl hno hbc
  · exact spArg_fs_trig hc hcof hμ hη hηl htr hlo hlo' hbη

/-- The conditions along a whole context. -/
def FramesOK : List (T × T) → T → T → T → Prop
  | [], _, _, _ => True
  | (a, b) :: fr, c, μ, η => FrameOK a b c μ η ∧ FramesOK fr (psi a (spArg a b c) z) μ η

/-- **The fundamental sequence goes down a context.** -/
theorem fillC_fs : ∀ (ctx : List (T × T)) {c μ η : T}, FramesOK ctx c μ η →
    fs (fillC ctx c) η = fillC ctx (fs c η)
  | [], _, _, _, _ => rfl
  | (a, b) :: fr, c, μ, η, ⟨h1, h2⟩ => by
    simp only [fillC]
    rw [fillC_fs fr h2, frame_fs h1]

end Ytosk
