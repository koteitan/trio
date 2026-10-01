/-
**3 行: 穴の追跡（Ω 型の共終数が通過するか、対角化の点 ψ_{a'}(b_r) が下にあるか）。**

t = 1・q ≠ r の展開で値が変わる列の値 t は、x の値 Ω_{μ+1}（μ = v(r)）を穴として
- r より下では共終数 Ω_{μ+1} が通過する（cof t = Ω_{μ+1}）、
- r と r より上では対角化の点 ψ_{a'}(b_r)（a' ≤ v(r)、b_r = o(r) の引数）が下にある（`DiagAt`）。
これを `HoleT` とおき、枠（o の最後の子・添字・ω 冪・和）で保たれることを示す。
`HoleT` と始点つきの鎖 ζ = γ_m から、fsD(t, ζ) は標準形で t より小さい（`hok_of_holeT`）。
-/
import Ytosk.V3Good

namespace Ytosk

open T

/-- The hole of `t`: passing cofinality, or a diagonal point at `ψ_{a'}(b_r)` with `a' ≤ v(r)`. -/
def HoleT (μ br vr t : T) : Prop := cof t = .big μ ∨ ∃ a', ¬ lt vr a' = true ∧ DiagAt a' br μ t

/-- **`fsD` with the seeded chain is standard and smaller.** -/
theorem hok_of_holeT {μ br vr seed t : T} (hrot : isOT (psi vr br z) = true)
    (hcb : cof br = .big μ) (hμ : ¬ lt μ vr = true)
    (hS : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ seed)
    (hot : isOT t = true) (hH : HoleT μ br vr t) (m : Nat) :
    isOT (fsD t (gamS μ br seed m)) = true ∧ fsD t (gamS μ br seed m) < t := by
  have hSr := hS vr (lt_irrefl' vr) hrot
  rcases hH with hc | ⟨a', ha', hD⟩
  · rw [fsD_eq_fs hc]
    exact fs_ot_lt hot ⟨gamS_ot hrot hcb hμ hSr m, by rw [hc]; exact gamS_lt_om hrot hcb hμ hSr m⟩
  · have hnode := DiagAt.ot_node hD hot
    obtain ⟨h1, h2⟩ := fsD_seed (hS a' ha' hnode) hD hot m
    exact ⟨h1, h2.1⟩

theorem holeT_app {μ br vr c : T} (B : T) (hc : c ≠ z) (h : HoleT μ br vr c) :
    HoleT μ br vr (app B c) := by
  rcases h with h | ⟨a', ha', hD⟩
  · left; rw [cof_app B hc, h]
  · right; exact ⟨a', ha', DiagAt.append B hc hD⟩

/-- Wrapping in `ψ_a`: the hole stays below (no new diagonal point when the cofinality passes). -/
theorem holeT_psi {μ br vr a X : T} (hX : X ≠ z) (hs : isSucc X = false) (h : HoleT μ br vr X)
    (hpass : cof X = .big μ → lt μ a = true) : HoleT μ br vr (psi a X z) := by
  rcases h with h | ⟨a', ha', hD⟩
  · left; exact cof_psi_pass hX h (hpass h)
  · right; exact ⟨a', ha', DiagAt.arg hX hs hD⟩

/-- A subscript hole: `Ω_v` with `v` limit. -/
theorem holeT_sub {μ br vr v : T} (hv : v ≠ z) (hs : isSucc v = false) (h : HoleT μ br vr v) :
    HoleT μ br vr (psi v z z) := by
  rcases h with h | ⟨a', ha', hD⟩
  · left
    unfold cof
    rw [if_pos rfl, if_neg hv, if_neg (by rw [hs]; simp), h]
  · right; exact ⟨a', ha', DiagAt.sub hv hs hD⟩

/-- A standard term with a passing cofinality is not below `ψ_0(Ω_1)`. -/
theorem not_lt_E0_of_cof_big : ∀ {t μ : T}, isOT t = true → cof t = .big μ → ¬ t < E0
  | z, _, _, h => by simp [cof] at h
  | psi a b (psi c d e), μ, hot, h => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    have ih := not_lt_E0_of_cof_big (isOT_rest hot) h'
    intro hlt
    obtain ⟨rfl, hb⟩ := below_E0 hlt
    apply ih
    have h4 := (isOT_psi_iff.mp hot).2.2.2.1
    have hhead : psi z b z < E0 := by
      unfold E0; rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, hb⟩)
    have hh : psi c d z < E0 := lt_of_le_of_lt h4 hhead
    obtain ⟨rfl, hd⟩ := below_E0 hh
    unfold E0; rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, hd⟩)
  | psi a b z, μ, _, h => by
    intro hlt
    obtain ⟨rfl, _⟩ := below_E0 hlt
    unfold cof at h
    by_cases hb : b = z
    · rw [if_pos hb, if_pos rfl] at h; cases h
    · rw [if_neg hb] at h
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h
        cases hcb : cof b with
        | big μ' =>
          rw [hcb] at h; simp only at h
          split at h
          · rename_i hlt'; exact absurd hlt' (by simp [lt])
          · cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- The hole of the rest of a sum. -/
theorem holeT_rest {μ br vr a b c : T} (hc : c ≠ z) (h : HoleT μ br vr (psi a b c)) :
    HoleT μ br vr c := by
  cases c with
  | z => exact absurd rfl hc
  | psi c1 c2 c3 =>
    rcases h with h | ⟨a', ha', hD⟩
    · left; simpa [cof] using h
    · right; refine ⟨a', ha', ?_⟩
      cases hD with
      | rest h' => exact h'

theorem holeT_ne_z {μ br vr t : T} (h : HoleT μ br vr t) : t ≠ z := by
  rcases h with h | ⟨_, _, hD⟩
  · intro he; subst he; simp [cof] at h
  · exact DiagAt.ne_z hD

theorem holeT_not_succ {μ br vr t : T} (h : HoleT μ br vr t) : isSucc t = false := by
  rcases h with h | ⟨_, _, hD⟩
  · exact not_succ_of_cof_big h
  · exact DiagAt.not_succ hD

/-- **The hole through an `o` frame.** Below `r` the cofinality passes; at `r` it becomes the diagonal
point `ψ_{v(r)}(b_r)`; above `r` the diagonal point stays below (a rewrite onto `b_r` gives a new
diagonal node `ψ_a(b_r)` with `a ≤ v(r)`). -/
theorem holeT_oframe {μ br vr a b s y : T} (hc : isOT (psi s y z) = true)
    (hH : HoleT μ br vr (psi s y z)) (hμ : μ = vr) (hbr : br ≠ z) (hcbr : cof br = .big μ)
    (hpass : cof (psi s y z) = .big μ → lt μ a = true ∨ (a = vr ∧ step a b s y z = br)) :
    HoleT μ br vr (psi a (step a b s y z) z) := by
  rcases hH with hcof | ⟨a', ha', hD⟩
  · have hstep := cof_step (a := a) (b := b) hc hcof
    have hne : step a b s y z ≠ z := by intro he; rw [he] at hstep; simp [cof] at hstep
    rcases hpass hcof with h | ⟨rfl, heq⟩
    · left; exact cof_psi_pass hne hstep h
    · right; refine ⟨a, lt_irrefl' a, ?_⟩
      rw [heq]; exact DiagAt.here hbr hcbr (by rw [hμ]; exact lt_irrefl' a)
  · right
    rcases step_cases (a := a) (b := b) hc with ⟨B, hB⟩ | ⟨hy, _, hyz, _, htr2⟩
    · rw [hB]
      have hD' := DiagAt.append B (by simp) hD
      exact ⟨a', ha', DiagAt.arg (DiagAt.ne_z hD') (DiagAt.not_succ hD') hD'⟩
    · rw [hy]
      by_cases hne : s = a' ∧ y = br
      · obtain ⟨rfl, rfl⟩ := hne
        refine ⟨a, ?_, DiagAt.here hbr hcbr ?_⟩
        · -- `a ≤ s ≤ v(r)`
          have has : ¬ lt s a = true := by
            intro h
            have : psi a z z < psi s y z := htr2
            rw [psi_lt_psi_z_iff] at this
            rcases this with h' | ⟨h', _⟩
            · exact lt_irrefl' _ (lt_trans h h')
            · rw [h'] at h; exact lt_irrefl' _ h
          intro h
          have h3 : s < a := lt_of_le_of_lt (le_of_not_gt ha') (show vr < a from h)
          exact has h3
        · have has : ¬ lt s a = true := by
            intro h
            have : psi a z z < psi s y z := htr2
            rw [psi_lt_psi_z_iff] at this
            rcases this with h' | ⟨h', _⟩
            · exact lt_irrefl' _ (lt_trans h h')
            · rw [h'] at h; exact lt_irrefl' _ h
          rw [hμ]; intro h
          have h3 : s < a := lt_of_le_of_lt (le_of_not_gt ha') (show vr < a from h)
          exact has h3
      · have hDy := DiagAt.arg_inv hD hyz hne
        exact ⟨a', ha', DiagAt.arg hyz (DiagAt.not_succ hDy) hDy⟩

/-- **The hole through `ω^G`**, when the cofinality passes the head subscript of `G`. -/
theorem holeT_omega {μ br vr G : T} (hot : isOT G = true) (hH : HoleT μ br vr G)
    (hpass : ∀ s b c, G = psi s b c → cof G = .big μ → lt μ s = true) :
    HoleT μ br vr (omega G) := by
  by_cases hE : G < E0
  · rw [omega_small hE]
    rcases hH with hc | ⟨a', ha', hD⟩
    · exact absurd hE (not_lt_E0_of_cof_big hot hc)
    · right; exact ⟨a', ha', DiagAt.arg (DiagAt.ne_z hD) (DiagAt.not_succ hD) hD⟩
  · cases G with
    | z => exact absurd (holeT_ne_z hH) (by simp)
    | psi s b c =>
      rw [omega_big' hot hE]
      have hps : cof (psi s b c) = .big μ → lt μ s = true := hpass s b c rfl
      by_cases hlo : loOf s b = z
      · rw [if_pos hlo]
        by_cases hcz : c = z
        · subst hcz
          have hb : hiOf s b = b := by
            have := split_app (psi (succ s) z z) b
            unfold hiOf; unfold loOf at hlo; rw [hlo, app_z_right] at this; exact this
          rw [app_z_right, hb]; exact hH
        · have hHc := holeT_rest hcz hH
          apply holeT_psi (by intro he; exact hcz (app_eq_z he).2)
            (by rw [isSucc_app _ hcz]; exact holeT_not_succ hHc) (holeT_app _ hcz hHc)
          intro hcc; rw [cof_app _ hcz] at hcc
          have hcs : cof (psi s b c) = cof c := by
            cases c with
            | z => exact absurd rfl hcz
            | psi => rfl
          exact hps (by rw [hcs]; exact hcc)
      · rw [if_neg hlo]
        apply holeT_psi (by intro he; have := (app_eq_z he).2; simp at this)
          (by rw [isSucc_app _ (by simp)]; exact holeT_not_succ hH) (holeT_app _ (by simp) hH)
        intro hcc; rw [cof_app _ (by simp)] at hcc; exact hps hcc

end Ytosk
