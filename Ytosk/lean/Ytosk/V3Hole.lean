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

end Ytosk
