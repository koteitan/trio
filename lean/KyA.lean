/-
KyA.lean: 節点の上に明示した塔 ETW（追記534）。

    ETW c [] V            = V
    ETW c ((W, K) :: d) V = W ++ (1, c+1, 1) :: (K ++ (1, c+1, 0) :: (ETW (c+1) d V)↑1)↑1

c は節点の行 1（絶対値）。段ごとの語 W・中身 K。最内の節点（行 1 が c + d.length）の子の並びが V。
towF r n (m+1) は ETW (r−1) [(farR r n, [])] (towF (r+1) n m) の形。
-/
import KxH

namespace TRIO
namespace KyA

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG

def ETW : ℕ → List (TrioSeq × TrioSeq) → TrioSeq → TrioSeq
  | _, [], V => V
  | c, (W, K) :: d, V => W ++ ((1, c + 1, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (K ++ ((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (ETW (c + 1) d V))

theorem ETW_nil (c : ℕ) (V : TrioSeq) : ETW c [] V = V := rfl

theorem ETW_cons (c : ℕ) (W K : TrioSeq) (d : List (TrioSeq × TrioSeq)) (V : TrioSeq) :
    ETW c ((W, K) :: d) V = W ++ ((1, c + 1, 1) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (K ++ ((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (ETW (c + 1) d V)) := rfl

/-- 塔の段のデータが全て Fr（行 0 ≥ 1）。 -/
def FrD (d : List (TrioSeq × TrioSeq)) : Prop := ∀ p ∈ d, Fr p.1 ∧ Fr p.2

theorem FrD_tail {p : TrioSeq × TrioSeq} {d : List (TrioSeq × TrioSeq)} (h : FrD (p :: d)) :
    FrD d := fun q hq => h q (List.mem_cons_of_mem p hq)

theorem Fr_ETW : ∀ (c : ℕ) (d : List (TrioSeq × TrioSeq)) (V : TrioSeq), FrD d → Fr V →
    Fr (ETW c d V)
  | _, [], _, _, hV => hV
  | c, (W, K) :: d, V, hd, _ => by
      have h0 := hd (W, K) (by simp)
      rw [ETW_cons]
      exact Fr_append h0.1 (Fr_letter _ _)

/-- ★ 最内の子の並びの末尾に足した列は、塔全体の末尾に深さ 2·(段の数) だけずれて付く。 -/
theorem ETW_append : ∀ (c : ℕ) (d : List (TrioSeq × TrioSeq)) (V X : TrioSeq),
    ETW c d (V ++ X) = ETW c d V ++ shiftr01 (2 * d.length) 0 X
  | _, [], V, X => by
      rw [ETW_nil, ETW_nil, List.length_nil, Nat.mul_zero, shiftr01_zero']
  | c, (W, K) :: d, V, X => by
      rw [ETW_cons, ETW_cons, ETW_append (c + 1) d V X]
      simp only [shiftr01, List.map_append, List.map_cons, List.map_map, Function.comp_def,
        List.append_assoc, List.cons_append, List.length_cons]
      refine congrArg (W ++ ·) (congrArg (_ :: ·) ?_)
      refine congrArg (_ ++ ·) (congrArg (_ :: ·) ?_)
      refine congrArg (_ ++ ·) (List.map_congr_left fun p _ => ?_)
      rw [show p.1 + 2 * d.length + 1 + 1 = p.1 + 2 * (d.length + 1) by omega]

end KyA
end TRIO
