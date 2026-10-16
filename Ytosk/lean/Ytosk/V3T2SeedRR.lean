/-
**3 行・t = 2: 種での RClaimU と REr を、引数の形と閉じた条件から（2026-10-17、t2）。**

種 r の引数 X（M）と X′（M[n]）は、測定ではいつも（10 集合、4 つの場合）
- 類 B0: どちらも加数がすべて Ω_{V+1} 以上（下の部分がない）、
- 右端だけの変化 REr: X = P + ψ(…)（最後の加数）、X′ = P + T′（T′ ≠ 0）。
このとき RClaimU は、u ≤ V の段で X′ の成分が X′ より小さいか P・V の成分以下、という閉じた条件と
両方の標準形から出る（`rclaim_of_hiB0`）。u > V の段の成分は ψ_V(X′) の標準形で X′ より小さい。
-/
import Ytosk.V3RelRU
import Ytosk.V3SubstLev
import Ytosk.V3T0RE

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- `Ω_a < X′` when `X′ ≠ 0` has every summand at least `Ω_{a+1}`. -/
theorem om_lt_of_hi {a X : T} (hX : X ≠ z) (hall : ∀ q ∈ summands X, ¬ q < psi (succ a) z z) :
    psi a z z < X := by
  cases X with
  | z => exact absurd rfl hX
  | psi s y c =>
    have h1 : ¬ psi s y z < psi (succ a) z z := hall _ (by simp [summands])
    have h2 : psi a z z < psi (succ a) z z := psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self a))
    have h3 : psi (succ a) z z ≤ psi s y z := not_lt.mp h1
    exact lt_of_lt_of_le h2 (le_trans h3 (le_psi_rest (z_le c)))

/-- **`RClaimU` at a node whose arguments are all high (class B0) and differ after a common prefix `P`**,
from the standard forms and the closedness of `X′` at the levels `u ≤ a`. -/
theorem rclaim_of_hiB0 {U : T → Prop} {ρ σ : Valn} {i : Nat} {a X X' P : T}
    (hX : ρ.o i = psi a X z) (hX' : σ.o i = psi a X' z)
    (hot : isOT (psi a X z) = true) (hot' : isOT (psi a X' z) = true)
    (hall : ∀ q ∈ summands X, ¬ q < psi (succ a) z z) (hall' : ∀ q ∈ summands X', ¬ q < psi (succ a) z z)
    (hX'z : X' ≠ z) (hP : ∀ c, X' < c → c ≤ X → ∃ c0, c = app P c0)
    (hcl : ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u X', g < X' ∨ ∃ d ∈ comps u P ++ comps u a, g ≤ d) :
    RClaimU U ρ σ i := by
  intro p y y' q hy hy' _ hsub
  rw [hX] at hy; rw [hX'] at hy'
  simp only [psi.injEq] at hy hy'
  obtain ⟨rfl, rfl, -⟩ := hy
  obtain ⟨-, rfl, -⟩ := hy'
  rw [H_all_hi hot hall, H_all_hi hot' hall']
  have hΩ := om_lt_of_hi hX'z hall'
  intro u hU hqu c h1 h2 g hg
  by_cases hau : lt a u = true
  · -- above `a`: the components are components at `a`
    exact Or.inl (comps_lt hot' g (comps_anti (le_of_lt hau) hg))
  · obtain ⟨c0, rfl⟩ := hP c h1 h2
    rcases hcl u hU hau g hg with h | ⟨d, hd, hgd⟩
    · exact Or.inl h
    · rcases List.mem_append.mp hd with hd | hd
      · exact Or.inr ⟨d, List.mem_append_left _ (gc_app_left d hd), hgd⟩
      · rcases hsub u hU hqu d hd with h | h | ⟨e, he, hde⟩
        · exact Or.inl (lt_of_le_of_lt (le_trans hgd h) hΩ)
        · rw [H_all_hi hot' hall'] at h; exact Or.inl (lt_of_le_of_lt hgd h)
        · exact Or.inr ⟨e, List.mem_append_right _ he, le_trans hgd hde⟩

/-- **`REr` from the common prefix**: `X = P + ψ_b(x)` and `X′ = P + T′` with `T′ ≠ 0`. -/
theorem rEr_of_prefix {P b x T' : T} (hT : T' ≠ z) : REr (app P (psi b x z)) (app P T') :=
  ⟨P, b, x, T', rfl, rfl, hT⟩

end Ytosk
