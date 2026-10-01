/-
**落とす補題の組み立て（順位の帰納法）。**

M′ = M.take x の各列で、
- o: `DRelO`（⊴ か弱い関係）、弱いなら M 側の引数は 0、o′ は標準形の単一の項（`PO`）。
- v: `DRelV`、v′ は標準形、v′ の成分 ≤ Ω_{v′}（`VSmallV`）、弱いなら M で数える子なし（`PV`）。
値の不変条件（`VSmall`・`FrameClosed`・`FrameOT`）と、のりしろの枠（`hBump`）・x − 1 の吸収（`hX1`）を仮定にとる。
-/
import Ytosk.V3DropRel

namespace Ytosk

open T

/-- The components of a subscript are at most `Ω_v`. -/
def VSmallV (t : T) : Prop := ∀ u, ∀ g ∈ comps u t, g ≤ psi t z z

/-- **Value invariant**: every `v` is small in this sense. -/
def VSmall (M : Mat) (ρ : Valn) : Prop := ∀ i, i < M.length → VSmallV (ρ.v i)

/-- **Value invariant**: every state of every frame gives a standard `ψ`. -/
def FrameOT (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL M i = L ++ c :: R →
    isOT (psi (ρ.v i) (spArg (ρ.v i) z (sumN (L.map ρ.o))) z) = true

theorem VSmallV.subSmall {t : T} (h : VSmallV t) (a : T) : SubSmall a t := fun u _ g hg => h u g hg

/-- The claim at an `o` call. -/
def PO (ρ ρ' : Valn) (i : Nat) : Prop :=
  (LhdE (ρ'.o i) (ρ.o i) ∨ (WkO (ρ'.o i) (ρ.o i) ∧ ∃ w, ρ.o i = psi w z z)) ∧ Single (ρ'.o i)

/-- The claim at a `v` call. -/
def PV (M : Mat) (ρ ρ' : Valn) (i : Nat) : Prop :=
  (LhdE (ρ'.v i) (ρ.v i) ∨ (WkV (ρ'.v i) (ρ.v i) ∧ ∀ c ∈ children M i, ¬ Counted M i c)) ∧
    isOT (ρ'.v i) = true ∧ VSmallV (ρ'.v i)

/-- A changed `v` has row 1 nonzero. -/
theorem chgx_e1 {M : Mat} {x i : Nat} (h : ChgX M x false i) : entry M 1 i ≠ 0 := by
  cases h with
  | supg hne =>
    intro he; apply hne
    unfold upg; rw [if_pos (Or.inl he)]
  | snb h1 _ _ _ => exact h1
  | vpar h1 _ _ => exact h1
  | vupg h1 _ _ _ => exact h1
  | vbump h1 _ _ _ _ _ => exact h1

end Ytosk
