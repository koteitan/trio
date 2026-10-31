/-
**WfQrL2 (2026-11-01): the `ω` exchange for `DQ`** (step (2) of tmp/wf/WfQrE/notes.md).

The bump term of a bump frame is `ω^Y` with `Y` the sum of the children of `j`.  In `M[n]` the last child `k`
of `j` carries `o_N(k) = DQ(o(k))`, so `Y_N = DQ(Y)` (`Q = 0` at the top: `DQ.snoc`).  Here: `DQ` passes through
`ω` (`omega_DQ`), case by case on the shape of the `DQ` step:
  * small (`Y, Y_N < ε₀`): `ω^Y = ψ_0(Y)`, `DQ.arg`;
  * rest (`Y = ψ_s(b) + c`, `c ≠ 0`): the head is kept, `ω` moves `c` (or `Y`) under `ψ_s`;
  * subscript (`Y = Ω_a`): `Y` and `Y_N` are fixed points of `ω`;
  * argument (`Y = ψ_a(b)`): fixed points if no low part appears (`hLo`, the `(L)(ii)` condition, `TPLoQ`),
    otherwise the high part is kept (`hHi`);
  * base (`Y_N = fsD(Y, η)`): the old exchange `fsD(ω^Y, η) = ω^{fsD(Y, η)}` (`omega_fsD_hole_Q`) is the input.
-/
import Ytosk.WfQrL1
import Ytosk.V3QROmega

namespace Ytosk.WfQrL2
open T Ytosk

/-- The shape of a `DQ` step on a sum. -/
theorem DQ.true_inv {η t tN : T} (h : DQ η true t tN) :
    ∃ B l lN Q s y, t = app B l ∧ tN = app B (app Q lN) ∧ l = psi s y z ∧ DQ η false l lN ∧
      ∀ q ∈ summands Q, lN ≤ q ∧ q < l := by
  cases h with
  | mk hl hd hQ => exact ⟨_, _, _, _, _, _, rfl, rfl, hl, hd, hQ⟩

/-- A single step seen as a sum (`B = Q = 0`). -/
theorem DQ.single_true {η l lN : T} (hl : ∃ s y, l = psi s y z) (h : DQ η false l lN) : DQ η true l lN := by
  obtain ⟨s, y, rfl⟩ := hl
  have := DQ.mk (B := z) (Q := z) rfl h (by simp [summands])
  simpa [app] using this

/-- `DQ` on a sum is kept by a common prefix. -/
theorem DQ.pre {η t tN : T} (B : T) (h : DQ η true t tN) : DQ η true (app B t) (app B tN) := by
  obtain ⟨B', l, lN, Q, s, y, rfl, rfl, hl, hd, hQ⟩ := DQ.true_inv h
  rw [← app_assoc, ← app_assoc]
  exact DQ.mk hl hd hQ

/-- **The sum of the children of `j`**: the last child changes by `DQ`, the others are kept (`Q = 0`). -/
theorem DQ.snoc {η l lN : T} (B : T) (hl : ∃ s y, l = psi s y z) (h : DQ η false l lN) :
    DQ η true (app B l) (app B lN) :=
  DQ.pre B (DQ.single_true hl h)

/-- **Small case.** -/
theorem omega_DQ_small {η Y YN : T} (hY : Y < E0) (hYN : YN < E0) (h : DQ η true Y YN) :
    DQ η false (omega Y) (omega YN) := by
  rw [omega_small hY, omega_small hYN]
  exact DQ.arg h

/-- `app B l = ψ_s(b) + c` with `c ≠ 0` and `l` single: `B = ψ_s(b) + B'`, `c = B' ++ l`. -/
theorem app_eq_psi_rest {B l s b c : T} (hl : ∃ s' y', l = psi s' y' z) (hc : c ≠ z)
    (h : app B l = psi s b c) : ∃ B', B = psi s b B' ∧ c = app B' l := by
  cases B with
  | z =>
    obtain ⟨s', y', rfl⟩ := hl
    simp only [app] at h
    cases h; exact absurd rfl hc
  | psi a1 b1 c1 =>
    simp only [app_psi] at h
    cases h
    exact ⟨c1, rfl, rfl⟩

/-- **Rest case**: `Y = ψ_s(b) + c`, `c ≠ 0`. -/
theorem omega_DQ_rest {η s b c YN : T} (hc : c ≠ z) (hY : isOT (psi s b c) = true) (hYN : isOT YN = true)
    (hE : ¬ psi s b c < E0) (hEN : ¬ YN < E0) (h : DQ η true (psi s b c) YN) :
    DQ η false (omega (psi s b c)) (omega YN) := by
  obtain ⟨B, l, lN, Q, s', y', e, rfl, hl, hd, hQ⟩ := DQ.true_inv h
  obtain ⟨B', rfl, hcB⟩ := app_eq_psi_rest ⟨s', y', hl⟩ hc e.symm
  simp only [app_psi] at hYN hEN ⊢
  rw [omega_big' hY hE, omega_big' hYN hEN]
  have hcd : DQ η true c (app B' (app Q lN)) := by rw [hcB]; exact DQ.mk hl hd hQ
  by_cases hlo : loOf s b = z
  · rw [if_pos hlo, if_pos hlo]
    exact DQ.arg (DQ.pre _ hcd)
  · rw [if_neg hlo, if_neg hlo]
    have h' : DQ η true (psi s b c) (psi s b (app B' (app Q lN))) := by
      have := DQ.pre (psi s b z) hcd
      simpa [app] using this
    exact DQ.arg (DQ.pre _ h')

/-- **Subscript case**: `Ω_a` is a fixed point of `ω` (above `ε₀`). -/
theorem omega_DQ_sub {η a aN : T} (hY : isOT (psi a z z) = true) (hYN : isOT (psi aN z z) = true)
    (hE : ¬ psi a z z < E0) (hEN : ¬ psi aN z z < E0) (h : DQ η true a aN) :
    DQ η false (omega (psi a z z)) (omega (psi aN z z)) := by
  rw [omega_fix_nolo hY hE rfl, omega_fix_nolo hYN hEN rfl]
  exact DQ.sub h

/-- **Argument case**: `Y = ψ_a(b)`.  No low part in `b` → none in `b_N` (`hLo`, the `(L)(ii)` condition):
fixed points.  A low part in `b` → the high part is kept and a low part stays (`hHi`). -/
theorem omega_DQ_arg {η a b bN : T} (hY : isOT (psi a b z) = true) (hYN : isOT (psi a bN z) = true)
    (hE : ¬ psi a b z < E0) (hEN : ¬ psi a bN z < E0) (h : DQ η true b bN)
    (hLo : loOf a b = z → loOf a bN = z)
    (hHi : loOf a b ≠ z → hiOf a bN = hiOf a b ∧ loOf a bN ≠ z) :
    DQ η false (omega (psi a b z)) (omega (psi a bN z)) := by
  by_cases hlo : loOf a b = z
  · rw [omega_fix_nolo hY hE hlo, omega_fix_nolo hYN hEN (hLo hlo)]
    exact DQ.arg h
  · obtain ⟨hhi, hlo'⟩ := hHi hlo
    rw [omega_big' hY hE, omega_big' hYN hEN, if_neg hlo, if_neg hlo', hhi]
    exact DQ.arg (DQ.pre _ (DQ.single_true ⟨a, b, rfl⟩ (DQ.arg h)))

/-- **Base case**: given the old exchange at `Y` (`omega_fsD_hole_Q`) and the decrease of `ω^Y`. -/
theorem omega_DQ_base {η Y : T} (hx : fsD (omega Y) η = omega (fsD Y η)) (hlt : fsD (omega Y) η < omega Y) :
    DQ η false (omega Y) (omega (fsD Y η)) := by
  rw [← hx]; exact DQ.base hlt

/-- **The `ω` exchange for a single `DQ` step** (all shapes), with the side conditions of each shape. -/
theorem omega_DQ {η Y YN : T} (h : DQ η false Y YN) (hY : isOT Y = true) (hYN : isOT YN = true)
    (hE : ¬ Y < E0) (hEN : ¬ YN < E0)
    (hLo : ∀ a b bN, Y = psi a b z → YN = psi a bN z → b ≠ z →
      (loOf a b = z → loOf a bN = z) ∧ (loOf a b ≠ z → hiOf a bN = hiOf a b ∧ loOf a bN ≠ z))
    (hB : YN = fsD Y η → fsD (omega Y) η = omega (fsD Y η) ∧ fsD (omega Y) η < omega Y) :
    DQ η false (omega Y) (omega YN) := by
  cases h with
  | base hlt =>
    obtain ⟨hx, hl⟩ := hB rfl
    exact omega_DQ_base hx hl
  | sub h' => exact omega_DQ_sub hY hYN hE hEN h'
  | @arg a b bN h' =>
    have hbz : b ≠ z := by
      intro hb; subst hb
      obtain ⟨B, l, lN, Q, s, y, e, _, hl, _, _⟩ := DQ.true_inv h'
      subst hl
      cases B <;> simp [app] at e
    obtain ⟨h1, h2⟩ := hLo a b bN rfl rfl hbz
    exact omega_DQ_arg hY hYN hE hEN h' h1 h2

end Ytosk.WfQrL2

namespace Ytosk.WfQrL2
open T Ytosk

/-- **(L)(ii) for `DQ`** (analog of `lo_keep_Q` / `lo_z_keep`): if `y` has no summand below `θ`, then neither has
`y_N`, as soon as the new last summand `l_N` and its summands are not below `θ` (the re-exposed summands `Q` are
`≥ l_N`). -/
theorem lo_keep_DQ {η y yN θ : T} (h : DQ η true y yN) (hl : (split y θ).2 = z)
    (hlast : ∀ B l lN Q, y = app B l → yN = app B (app Q lN) → DQ η false l lN →
      ¬ lN < θ ∧ ∀ q ∈ summands lN, ¬ q < θ) :
    (split yN θ).2 = z := by
  have hyall : ∀ q ∈ summands y, ¬ q < θ := by
    intro q hq
    have e := split_app θ y
    rw [hl, app_z_right] at e
    rw [← e] at hq
    exact split_fst_ge θ y q hq
  obtain ⟨B, l, lN, Q, s, y', ey, eyN, _, hd, hQ⟩ := DQ.true_inv h
  obtain ⟨hlN, hlNs⟩ := hlast B l lN Q ey eyN hd
  rw [eyN]
  apply split_snd_z_of_ge
  intro q hq
  rw [summands_app, summands_app] at hq
  rcases List.mem_append.mp hq with hq | hq
  · apply hyall; rw [ey, summands_app]; exact List.mem_append_left _ hq
  · rcases List.mem_append.mp hq with hq | hq
    · intro hqt
      exact hlN (lt_of_le_of_lt (hQ q hq).1 hqt)
    · exact hlNs q hq

/-- **The last summand `Ω_{P + W'}` from `TPLoQ`**: the condition of `lo_keep_DQ` at a last summand
`l_N = Ω_{a_N}`, `a_N = P + W'` (the value of the `v` call in `M[n]`, `v_bumpQ` / `v_upgQ`). -/
theorem lastQ_of_tpLoQ {P W' s : T} (h : ¬ psi (add P W') z z < psi (succ s) z z) :
    ¬ psi (add P W') z z < psi (succ s) z z ∧
      ∀ q ∈ summands (psi (add P W') z z), ¬ q < psi (succ s) z z := by
  refine ⟨h, fun q hq => ?_⟩
  simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
  subst hq; exact h

/-- `PgeS` gives the `TPLoQ` condition at every `W'` (`tpLoQ_of_le`). -/
theorem lastQ_of_le {P s a b : T} (hP : s ≤ P) :
    ¬ psi (add P (psi a b z)) z z < psi (succ s) z z ∧
      ∀ q ∈ summands (psi (add P (psi a b z)) z z), ¬ q < psi (succ s) z z :=
  lastQ_of_tpLoQ (tpLoQ_of_le hP)

end Ytosk.WfQrL2
