/-
HeU.lean: 深い葉の keystone (GoodChtX_deep) への背骨 — 一般段 q の深い葉の展開像。

深い葉を遠い語の子に積むと悪い根の段は遠い段 r。その展開の内側の再下降は段 r-1（段 0 でない）で、
また深い葉になる（HeT の一段木化 tow_dtree は最上段 r=1 専用）。よって GoodChtX_deep は段 q の整礎帰納:
段 q'+1 の深い葉の GpT を upleaf_deep_core（HeQ）で展開 → hrep = 段 q' の深い葉の塔 → IH。段 0 で木。

- dtreeQ q' j: 外段 q'+1、内側再下降 段 q' の深い葉の塔（dtreeQ 0 = HeT.dtree = 木）。
- tow_dtreeQ: tow (q'+1) 0 [(1,q'+2,0),(2,q'+2,0)] (j+1) = (0,q'+1,0) :: topTs 0 [dtreeQ q' j]。
  これが帰納の各段で「生の展開 tow」を「段 q' の深い葉を持つ topTs」に橋渡しする。
-/
import HeT

namespace TRIO
namespace HeU

open Wset Small HdA HdQ HeK
open GwS GxL GxP

/-- 外段 q'+1、内側再下降 段 q' の深い葉の塔（段 0 に達すると HeT.dtree = 木）。 -/
noncomputable def dtreeQ (q' : ℕ) : ℕ → HdA.UT
  | 0 => HdA.UT.tie (q'+1) []
  | j + 1 => HdA.UT.tie (q'+1) [HdA.UT.tie q' [dtreeQ q' j]]

/-- ★ 一般段 q'+1 の深い葉の展開像: tow (q'+1) 0 [(1,q'+2,0),(2,q'+2,0)] (j+1)
    = (0,q'+1,0) :: topTs 0 [dtreeQ q' j]。 -/
theorem tow_dtreeQ (q' j : ℕ) :
    (tow (q'+1) 0 [((1,q'+2,0):ℕ×ℕ×ℕ),((2,q'+2,0):ℕ×ℕ×ℕ)] (j+1) : TrioSeq)
      = ((0,q'+1,0):ℕ×ℕ×ℕ) :: topTs 0 [dtreeQ q' j] := by
  induction j with
  | zero =>
      simp only [dtreeQ, tow, graft_eq_shift, topTs, topT, shiftr01, entry, List.getD,
        List.dropLast, List.append_nil, List.map_nil, List.map_cons, Nat.add_zero]
      refine congrArg (List.cons _) ?_
      refine congrArg (fun z => [z]) ?_
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      simp; omega
  | succ j ih =>
    rw [tow, graft_eq_shift]
    simp only [show [((1,q'+2,0):ℕ×ℕ×ℕ),((2,q'+2,0):ℕ×ℕ×ℕ)].dropLast = [((1,q'+2,0):ℕ×ℕ×ℕ)] from rfl,
      show entry [((1,q'+2,0):ℕ×ℕ×ℕ),((2,q'+2,0):ℕ×ℕ×ℕ)] 0 ([((1,q'+2,0):ℕ×ℕ×ℕ),((2,q'+2,0):ℕ×ℕ×ℕ)].length - 1) = 2 from rfl]
    rw [ih]
    simp only [dtreeQ, topTs, topT, shiftr01, List.map_cons, List.map_nil, List.append_nil,
      List.cons_append, List.nil_append, Nat.add_zero, Nat.zero_add, List.map_map]
    rw [show 1 + (q' + 1) = q' + 2 from by omega, show 1 + q' = q' + 1 from by omega,
      show (1:ℕ) + 1 = 2 from rfl,
      show ((fun (p : ℕ×ℕ×ℕ) => (p.1 + 1, p.2.1, p.2.2)) ∘ fun p => (p.1 + 1, p.2.1, p.2.2))
        = (fun (p : ℕ×ℕ×ℕ) => (p.1 + 2, p.2.1, p.2.2)) from by funext p; simp [Function.comp]]

/-- 段 0 では深い葉の塔は HeT.dtree（木）に一致。 -/
theorem dtreeQ_zero (j : ℕ) : dtreeQ 0 j = HeT.dtree j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [dtreeQ, HeT.dtree, ih]

end HeU
end TRIO
