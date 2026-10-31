/-
**WfQnE2 (2026-11-01): the replacement fields of `AbsDS` / `TPLoS` for the t = 1, q ≠ r engine.**
The only primary deviation of the true valuation of `M[n]` from the engine's glue (WfQnE1, tmp/wf/WfQnE/analyze.py)
is a bump call `i` of `D` with
  * the bad shape `BadShape1 M i`: `m = P₀ i = P₁ i`, `CL i = []`, `CL m = Lc ++ [i]`, no column upgrades to `i`
    (the `M`-part of WfAbsW.BadAbsShape), and
  * bump term `W = bumpW i` equal to the node `A = o(r)` itself,
  * a summand `q` of `v(P₁ i)` in the window `A[ζ] ≤ q < A`.
There the true value is `sf(add v(P₁ i) A[ζ])` (not absorbed), which is still below `A` (`bad_v_lt`).
`AbsDSX` / `TPLoSX` allow exactly this case; `AbsDS → AbsDSX`, `TPLoS → TPLoSX`.
-/
import Ytosk.V3SeedFields
import Ytosk.V3DropAsm
import Ytosk.WfSrcC2a

namespace Ytosk.WfQnE2
open T Ytosk

/-- **The bad shape on one matrix** (the `M`-part of `WfAbsW.BadAbsShape`). -/
def BadShape1 (M : Mat) (i : Nat) : Prop :=
  ∃ m Lc, par M 0 i = some m ∧ par M 1 i = some m ∧ CL M i = [] ∧ CL M m = Lc ++ [i] ∧
    ∀ j, j < M.length → upg M j ≠ some i

/-- **`AbsDS` or the bad shape with `W = o(r)`.** -/
def AbsDSX (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) ≠ some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ b z →
    ∀ i, i < M.length - 1 → DepX M (M.length - 1) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
    OHole (bumpW M ρ i) → holeLev (bumpW M ρ i) = μ →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
      q < fsD (bumpW M ρ i) ((drop1 M (M.length - 1) rk).o r) ∨
      (BadShape1 M i ∧ bumpW M ρ i = ρ.o r)

theorem absDSX_of_absDS {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (h : AbsDS M ρ rk) : AbsDSX M ρ rk :=
  fun r μ b h1 h0 h2 hro i hi hd he1 he2 hO hl q hq hlt =>
    Or.inl (h r μ b h1 h0 h2 hro i hi hd he1 he2 hO hl q hq hlt)

/-- `AbsDSX` at every index `ζ` above the seed (the `hADζ` of `vlocal_t1`, with the bad case left open). -/
theorem hADζX_of_absDSX {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (h : AbsDSX M ρ rk) {r : Nat} {μ b ζ : T}
    (h1 : par M 1 (M.length - 1) = some r) (h0 : par M 0 (M.length - 1) ≠ some r)
    (h2 : entry M 2 (M.length - 1) = 0) (hro : ρ.o r = psi μ b z)
    (hζ : (drop1 M (M.length - 1) rk).o r ≤ ζ) :
    ∀ i, i < M.length - 1 → DepX M (M.length - 1) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
      OHole (bumpW M ρ i) → holeLev (bumpW M ρ i) = μ → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
        q < bumpW M ρ i → q < fsD (bumpW M ρ i) ζ ∨ (BadShape1 M i ∧ bumpW M ρ i = ρ.o r) := by
  intro i hi hv he1 he2 hO hl q hq hlt
  rcases h r μ b h1 h0 h2 hro i hi hv he1 he2 hO hl q hq hlt with h' | h'
  · exact Or.inl (lt_of_lt_of_le h' (fsD_mono_eta hO hζ))
  · exact Or.inr h'

/-- **`TPLoS` or the bad case**: the comparison fails only when `Ω_a` is `o(i)`'s index for a bad column `i` below
`c` on row 0, with `a = W_i = o(r)` and `s ≤ v(P₁ i)`. -/
def TPLoSX (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) ≠ some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ b z →
    ∀ c, c < M.length - 1 → DepX M (M.length - 1) true c →
    ∀ s y, ρ.o c = psi s y z → (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a → holeLev y = μ →
      ¬ psi (fsD a ((drop1 M (M.length - 1) rk).o r)) z z < psi (succ s) z z ∨
      ∃ i m, i < M.length - 1 ∧ DepX M (M.length - 1) false i ∧ BadShape1 M i ∧ par M 0 i = some m ∧
        Anc0 M c m ∧ a = bumpW M ρ i ∧ bumpW M ρ i = ρ.o r ∧ ¬ vOpt ρ (par M 1 i) < s

theorem tpLoSX_of_tpLoS {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (h : TPLoS M ρ rk) : TPLoSX M ρ rk :=
  fun r μ b h1 h0 h2 hro c hc hd s y ho hy a hla hns hO hl =>
    Or.inl (h r μ b h1 h0 h2 hro c hc hd s y ho hy a hla hns hO hl)

/-- **The non-absorbed value stays below the node**: `v(P₁ i) + A[ζ] < A` when both parts are below `A`. -/
theorem bad_v_lt {V W' a b : T} (hV : isOT V = true) (hW : isOT W' = true)
    (hVl : V < psi a b z) (hWl : W' < psi a b z) : sf (add V W') < psi a b z := by
  rw [sf_ot (isOT_add hV hW)]
  exact WfSrcC2.add_lt_single hVl hWl

/-- **In `M` the node absorbs**: `add V A = A` when the head of `V` is below `A`. -/
theorem add_absorb {a b : T} : ∀ {V : T}, V < psi a b z → add V (psi a b z) = psi a b z
  | z, _ => rfl
  | psi c d e, h => by
    have h' : psi c d z < psi a b z := WfSrcC2.lt_single_rest h
    simp only [add]
    rw [if_pos (show lt (psi c d z) (psi a b z) = true from h')]

end Ytosk.WfQnE2
