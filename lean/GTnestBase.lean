import GxN
import GzD
import GxV

namespace TRIO
namespace GTnestBase

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GzD GxV

/-! Base case for GT_nest: the far-word head appended to arbitrary good L.
KEY POSITIVE FINDING: for `Q = rword 0 u L'` (row0≥1), the far-word head pair's cone is clean
for ARBITRARY good L (no context needed) — because Q has row0≥1, so the bad root (2,u+1,1)'s only
row0-ancestors are the two heads (1,u+1,1),(2,u+1,1), both row1=u+1>u. -/

/-- CONE holds for arbitrary good Q (row0≥1): appended far-word head pair (1,u+1,1)(2,u+1,1). -/
theorem cone_farhead (u : ℕ) (Q : TrioSeq) (hQ : ∀ x ∈ Q, 1 ≤ x.1) :
    coneV (Q ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)]) u (Q.length + 1) := by
  set A : TrioSeq := Q ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)] with hAdef
  have hAlen : A.length = Q.length + 2 := by rw [hAdef]; simp
  -- entry values
  have eQl : entry A 0 Q.length = 1 := by
    rw [hAdef, show Q.length = Q.length + 0 from rfl, entry_append_right]; rfl
  have eQl1 : entry A 1 Q.length = u + 1 := by
    rw [hAdef, show Q.length = Q.length + 0 from rfl, entry_append_right]; rfl
  have eQl2 : entry A 0 (Q.length + 1) = 2 := by
    rw [hAdef, entry_append_right]; rfl
  have eQl21 : entry A 1 (Q.length + 1) = u + 1 := by
    rw [hAdef, entry_append_right]; rfl
  have hQrow0 : ∀ w, w < Q.length → 1 ≤ entry A 0 w := by
    intro w hw
    rw [hAdef, Small.entry_append_left hw]
    have hmem : Q.getD w (0, 0, 0) ∈ Q := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]; exact List.getElem_mem hw
    exact hQ _ hmem
  intro y hy
  -- Show y = Q.length+1 or y = Q.length; both have row1 = u+1 > u.
  rcases Relation.ReflTransGen.cases_tail hy with h1 | ⟨z, hyz, hzj⟩
  · -- y = Q.length+1
    rw [← h1, eQl21]; omega
  · -- hzj : nextrel0 A z (Q.length+1); force z = Q.length
    obtain ⟨hz, hj, hzlt, hent, hmin⟩ := hzj
    have hzQl : z = Q.length := by
      by_contra hne
      have hzlt' : z < Q.length := by omega
      have := hmin Q.length ⟨by omega, by omega⟩
      rw [eQl2, eQl] at this; omega
    subst hzQl
    -- hyz : RTG y Q.length
    rcases Relation.ReflTransGen.cases_tail hyz with h2 | ⟨w, hyw, hwQl⟩
    · rw [← h2, eQl1]; omega
    · exfalso
      obtain ⟨hw, hQl, hwlt, hent2, hmin2⟩ := hwQl
      rw [eQl] at hent2
      have hwlt' : w < Q.length := by omega
      have := hQrow0 w hwlt'
      omega

end GTnestBase
end TRIO
