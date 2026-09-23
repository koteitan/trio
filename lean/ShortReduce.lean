/-
ShortReduce.lean — the SHORT ⟸ units_base BRIDGE (own scratch, non-colliding).
Proves rigorously that the childLoad SHORT content [(1,u+1,1),(D,0,0)] (D≥2)
reduces to `units_base` = `∀n, GTC CQ u (fh u n)` (fh u n = flatMap of the head).
SHORT is Y=[(a,0,0)] (length≤1, lev0, based); content=(1,u+1,1)::shiftr01 2 0 [(a,0,0)]
= [(1,u+1,1),(a+2,0,0)], so D=a+2≥2 (a≥0, via Wg_shift). This confirms the
consolidated finding (SHORT is downstream of the h=2 far-word tower, NOT
independently closeable) as a CHECKED fact, and wires SHORT for the units_base
route: once units_base lands (towWAQ n-gen or GoodChtX), SHORT = one application.

Mechanism: GTC_oper on the flat (D,0,0) (srow=0, row-0 parent = the head, D>1);
oper_snoc00'' gives content⟦n⟧ = [(1,u+1,1)] repeated n = units_base word.
-/
import HbB
import GzD
import HdR

namespace TRIO
namespace ShortReduce

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GzD GzH GzJ HbB HdR

/-- SHORT content `[(1,u+1,1),(D,0,0)]` (D≥2) follows from units_base
    (`hUB n : GTC CQ u ([(1,u+1,1)] repeated n)`). -/
theorem short_of_unitsBase (u D : ℕ) (hD : 2 ≤ D)
    (hUB : ∀ n, GTC CQ u ((List.range n).flatMap (fun _ => [((1, u + 1, 1) : ℕ × ℕ × ℕ)]))) :
    GTC CQ u ([((1, u + 1, 1) : ℕ × ℕ × ℕ), ((D, 0, 0) : ℕ × ℕ × ℕ)]) := by
  have hMne : ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq) ≠ [] := by simp
  have econt : ([((1, u + 1, 1) : ℕ × ℕ × ℕ), ((D, 0, 0) : ℕ × ℕ × ℕ)])
      = [((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((D, 0, 0) : ℕ × ℕ × ℕ)] := rfl
  rw [econt]
  refine GTC_oper (by simp) ?_ (fun n hn => ?_)
  · -- hp: the flat (D,0,0) has srow 0 and a row-0 parent (the head, 1 < D)
    have hidx : ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((D, 0, 0) : ℕ × ℕ × ℕ)]).length - 1
        = ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq).length + 0 := by simp
    rw [hidx, srow_append_right]
    have hs : srow ([((D, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq) 0 = 0 := rfl
    rw [hs]
    refine (hasParent_zero_iff (by simp)).mpr ⟨0, by simp, ?_⟩
    rw [Small.entry_append_left (by simp), entry_append_right]
    show (1 : ℕ) < D; omega
  · -- content⟦n⟧ = [(1,u+1,1)] repeated n = units_base word
    have hh : entry ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq) 0 0 = 1 := rfl
    show GTC CQ u (([] ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((D, 0, 0) : ℕ × ℕ × ℕ)])⟦n⟧)
    rw [oper_snoc00'' (d := D) (M := [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) [] hMne (by rw [hh]; omega)
      (fun r hr1 hr => by simp only [List.length_singleton] at hr; omega) n]
    simpa using hUB n

end ShortReduce
end TRIO
