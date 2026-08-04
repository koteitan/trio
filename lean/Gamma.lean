/-
Gamma.lean: γ 装置のステップ合成。

`Lift1 ((0,v,z)::graft M y) t` の展開を、graft 三分法（Xbar）と
リフト同変性（Lcone / `liftInner_holds`）で義務レベルに落とす:

  inner   : (Lift1 N t)⟦n⟧ = Lift1 ((0,v,z)::graft M (y⟦n⟧)) t
  blocked : (Lift1 N t)⟦n⟧ = Lift1 ((0,v,z)::graft (M.take (p+1)) Y') t
            （文脈が厳密に短くなる）

N = (0,v,z)::graft M y。どちらも既証明補題の合成。
-/
import Lcone
import Xbar

namespace TRIO

open Wset

/-- **The (a)-branch step**: an inner parent lets the lifted obligation recurse
into the argument's expansion. -/
theorem lift_graft_inner_step {M y : TrioSeq} (v z t n : ℕ)
    (hM : M ≠ []) (hy : y ≠ []) (hyL : y.length - 1 ≠ 0)
    (hG : argOK (graft M y))
    (hp : hasParent y (srow y (y.length - 1)) (y.length - 1)) :
    (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t)⟦n⟧
      = Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M (y⟦n⟧)) t := by
  have hGne : graft M y ≠ [] :=
    List.length_pos_iff.mp (by
      rw [graft_length]
      have h1 : 0 < y.length := List.length_pos_iff.mpr hy
      omega)
  have hpG := hasParent_graft_inner hM hy hp
  rw [liftInner_holds v z t n (graft M y) hG hGne hpG,
    oper_cons_nat hG hGne hpG, oper_graft_inner n hM hy hyL hp]

/-- **The γ-branch step**: a blocked parent lets the lifted obligation recurse
onto a strictly shorter context. -/
theorem lift_graft_blocked_step {M y : TrioSeq} {p : ℕ} (v z t n : ℕ)
    (hM : M ≠ []) (hy : y ≠ [])
    (hG : argOK (graft M y))
    (hL : (graft M y).length - 1 ≠ 0)
    (hpG : hasParent (graft M y)
      (srow (graft M y) ((graft M y).length - 1)) ((graft M y).length - 1))
    (hpar : parent (graft M y) (srow (graft M y) ((graft M y).length - 1))
      ((graft M y).length - 1) = p)
    (hplt : p < M.length - 1) :
    (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t)⟦n⟧
      = Lift1 (((0, v, z) : ℕ × ℕ × ℕ)
          :: graft (M.take (p + 1))
            (shiftl0 (entry M 0 p)
              (gcopies (graft M y) p ((graft M y).length - 1 - p)
                (if 0 < srow (graft M y) ((graft M y).length - 1)
                  then entry (graft M y) 0 ((graft M y).length - 1)
                    - entry (graft M y) 0 p else 0)
                (if 1 < srow (graft M y) ((graft M y).length - 1)
                  then entry (graft M y) 1 ((graft M y).length - 1)
                    - entry (graft M y) 1 p else 0) n))) t := by
  have hGne : graft M y ≠ [] :=
    List.length_pos_iff.mp (by
      rw [graft_length]
      have h1 : 0 < y.length := List.length_pos_iff.mpr hy
      omega)
  rw [liftInner_holds v z t n (graft M y) hG hGne hpG,
    oper_cons_nat hG hGne hpG,
    oper_graft_blocked n hM hy hL hpG hpar hplt]

end TRIO
