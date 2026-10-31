/-
**WfDrE2: the seed of `t = 1`, `q = r` without `SmallSelf` (2026-10-31).**

`qr_seedC_of` concludes `seed ◁ o(r) ∨ (seed = Ω_{w′} ∧ w′ < v(r) ∧ SmallSelf w′)`. On graftD it is false 741 times
(smallest standard witness 21 columns, tmp/wf/WfInvD/notes.md): `w′ = ψ_0(Ω_{Ω_{ψ(ψ(1))}}) + 1` has the component
`Ω_{Ω_{ψ(ψ(1))}} > Ω_{w′}`.

The consumer (`hS` of `qr_final3`, then `hok_of_holeT`) asks `SeedOK a′ b_r μ seed` at every diagonal point `a′`
for every index `γ_k = gamS μ b_r seed k`. Measured (tmp/wf/WfDrE/seedc.py, all 903 weak seeds of graftD):
- the diagonal points of the bad part (columns `≥ r`) are only `a′ = μ`, and `SeedOK μ b_r μ seed` holds;
- `γ_1 = ψ_μ(b + seed) ◁ o(r) = ψ_μ(b + Ω_{μ+1})` holds;
- `SeedOK a′ b_r μ seed` fails at the root (`a′ = 0`, 279 cases): there `ψ_0(Ω_{w′})` is not standard. The root
  receives `γ_k` with `k ≥ 1` (its index passes through the copy of `r`).
`SeedC2` is this form. From it: `SeedOK a′ b_r μ γ_1` at every `a′` (`seedOK1_of_lhd`, by `seedOK_of_lhd_top`), hence
`hok_of_holeT` at every index `k + 1` (`hok_of_holeT_succ`); at index `0` only the diagonal points of the column
itself are needed (`hok_of_holeT_loc`), and when they are all `μ` the single `SeedOK μ b_r μ seed` suffices
(`hok_of_holeT_mu`).
-/
import Ytosk.WfDrE1
import Ytosk.V3QRFinal3

namespace Ytosk

open T

/-- The seeded chain from `γ_1`. -/
theorem gamS_shift (μ b seed : T) : ∀ k, gamS μ b seed (k + 1) = gamS μ b (gamS μ b seed 1) k
  | 0 => rfl
  | k + 1 => by
    show psi μ (fs b (gamS μ b seed (k + 1))) z = psi μ (fs b (gamS μ b (gamS μ b seed 1) k)) z
    rw [gamS_shift μ b seed k]

/-- **The new seed condition of `t = 1`, `q = r`** (`b_r = b + Ω_{μ+1}`): `seed ◁ ψ_μ(b_r)`, or a weak seed
`Ω_{w′}` (`w′ < μ`) with `SeedOK μ b_r μ seed` and `γ_1 = ψ_μ(b + seed) ◁ ψ_μ(b_r)`. -/
def SeedC2 (μ b seed : T) : Prop :=
  Lhd z seed (psi μ (app b (psi (succ μ) z z)) z) ∨
    ∃ w', seed = psi w' z z ∧ w' < μ ∧ SeedOK μ (app b (psi (succ μ) z z)) μ seed ∧
      Lhd z (psi μ (app b seed) z) (psi μ (app b (psi (succ μ) z z)) z)

/-- `γ_1` is good at every diagonal point when `γ_1 ◁ ψ_μ(b_r)`. -/
theorem seedOK1_of_lhd {μ b seed a' : T} (hot : isOT (psi a' (app b (psi (succ μ) z z)) z) = true)
    (ha : ¬ lt μ a' = true) (hsot : isOT (psi μ (app b seed) z) = true)
    (hl : Lhd z (psi μ (app b seed) z) (psi μ (app b (psi (succ μ) z z)) z)) :
    SeedOK a' (app b (psi (succ μ) z z)) μ (gamS μ (app b (psi (succ μ) z z)) seed 1) := by
  show SeedOK _ _ _ (psi μ (fs (app b (psi (succ μ) z z)) seed) z)
  rw [fs_br]
  have hsb : app b seed < app b (psi (succ μ) z z) := by
    have := hl.1
    rw [psi_lt_psi_z_iff] at this
    rcases this with h | ⟨_, h⟩
    · exact absurd h (lt_irrefl' _)
    · exact h
  exact seedOK_of_lhd_top hot cof_br ha hsot hsb hl

/-- **`hok_of_holeT` at the indices `k + 1`** from the condition on `γ_1` alone. -/
theorem hok_of_holeT_succ {μ br vr seed t : T} (hrot : isOT (psi vr br z) = true)
    (hcb : cof br = .big μ) (hμ : ¬ lt μ vr = true)
    (hS1 : ∀ a', ¬ lt vr a' = true → isOT (psi a' br z) = true → SeedOK a' br μ (gamS μ br seed 1))
    (hot : isOT t = true) (hH : HoleT μ br vr t) (m : Nat) :
    isOT (fsD t (gamS μ br seed (m + 1))) = true ∧ fsD t (gamS μ br seed (m + 1)) < t := by
  rw [gamS_shift]
  exact hok_of_holeT hrot hcb hμ hS1 hot hH m

/-- **`hok_of_holeT` with the seed condition only at `v(r)` and at the diagonal points of `t`.** -/
theorem hok_of_holeT_loc {μ br vr seed t : T} (hrot : isOT (psi vr br z) = true)
    (hcb : cof br = .big μ) (hμ : ¬ lt μ vr = true) (hSr : SeedOK vr br μ seed)
    (hSt : ∀ a', ¬ lt vr a' = true → DiagAt a' br μ t → SeedOK a' br μ seed)
    (hot : isOT t = true) (hH : HoleT μ br vr t) (m : Nat) :
    isOT (fsD t (gamS μ br seed m)) = true ∧ fsD t (gamS μ br seed m) < t := by
  rcases hH with hc | ⟨a', ha', hD⟩
  · rw [fsD_eq_fs hc]
    exact fs_ot_lt hot ⟨gamS_ot hrot hcb hμ hSr m, by rw [hc]; exact gamS_lt_om hrot hcb hμ hSr m⟩
  · obtain ⟨h1, h2⟩ := fsD_seed (hSt a' ha' hD) hD hot m
    exact ⟨h1, h2.1⟩

/-- **Index `0` when every diagonal point of `t` is `v(r)`**: the single `SeedOK vr` suffices. -/
theorem hok_of_holeT_mu {μ br vr seed t : T} (hrot : isOT (psi vr br z) = true)
    (hcb : cof br = .big μ) (hμ : ¬ lt μ vr = true) (hSr : SeedOK vr br μ seed)
    (hDt : ∀ a', DiagAt a' br μ t → a' = vr)
    (hot : isOT t = true) (hH : HoleT μ br vr t) (m : Nat) :
    isOT (fsD t (gamS μ br seed m)) = true ∧ fsD t (gamS μ br seed m) < t :=
  hok_of_holeT_loc hrot hcb hμ hSr (fun a' _ hD => by rw [hDt a' hD]; exact hSr) hot hH m

/-- **From `SeedC2`, the `q = r` frame `ψ_μ(b_r)`** (`vr = μ`): either the old `hS` (the `◁` seed; the weak seed is
handled by the next two conclusions), or `SeedOK μ` at the seed and `SeedOK a′` at `γ_1` for every `a′ ≤ μ`. -/
theorem seedC2_cases {μ b seed : T} (h : SeedC2 μ b seed) :
    Lhd z seed (psi μ (app b (psi (succ μ) z z)) z) ∨
      (SeedOK μ (app b (psi (succ μ) z z)) μ seed ∧
        (isOT (psi μ (app b seed) z) = true →
          ∀ a', ¬ lt μ a' = true → isOT (psi a' (app b (psi (succ μ) z z)) z) = true →
            SeedOK a' (app b (psi (succ μ) z z)) μ (gamS μ (app b (psi (succ μ) z z)) seed 1))) := by
  rcases h with h | ⟨_, _, _, hS, hl⟩
  · exact Or.inl h
  · exact Or.inr ⟨hS, fun hsot a' ha hot => seedOK1_of_lhd hot ha hsot hl⟩

/-- **Every index from `SeedC2`'s weak branch**, for a column whose diagonal points are `μ` at index `0`. -/
theorem hok_of_seedC2 {μ b seed t : T}
    (hrot : isOT (psi μ (app b (psi (succ μ) z z)) z) = true)
    (hSr : SeedOK μ (app b (psi (succ μ) z z)) μ seed)
    (hl : Lhd z (psi μ (app b seed) z) (psi μ (app b (psi (succ μ) z z)) z))
    (hot : isOT t = true) (hH : HoleT μ (app b (psi (succ μ) z z)) μ t) (k : Nat)
    (h0 : k = 0 → ∀ a', DiagAt a' (app b (psi (succ μ) z z)) μ t → a' = μ) :
    isOT (fsD t (gamS μ (app b (psi (succ μ) z z)) seed k)) = true ∧
      fsD t (gamS μ (app b (psi (succ μ) z z)) seed k) < t := by
  have hμ : ¬ lt μ μ = true := lt_irrefl' μ
  cases k with
  | zero => exact hok_of_holeT_mu hrot cof_br hμ hSr (h0 rfl) hot hH 0
  | succ m =>
    have hs1 := gamS_ot hrot cof_br hμ hSr 1
    have hsot : isOT (psi μ (app b seed) z) = true := by
      have e : gamS μ (app b (psi (succ μ) z z)) seed 1 = psi μ (app b seed) z := by
        show psi μ (fs _ seed) z = _; rw [fs_br]
      rw [← e]; exact hs1
    exact hok_of_holeT_succ hrot cof_br hμ (fun a' ha hot' => seedOK1_of_lhd hot' ha hsot hl) hot hH m

end Ytosk
