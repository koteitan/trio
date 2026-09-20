import HeU
namespace TRIO
namespace WltCheck
open Wset Small HdQ HdA
-- wLT with a ch-load renders WITH the FTL0 marker (1,1,0), so ≠ Trc4=(1,1,1)(2,1,0):
example : wLT 0 ([[HdA.UT.ch ([((0,1,0):ℕ×ℕ×ℕ)]:TrioSeq)]], ([]:List (Option TrioSeq)))
    = [((1,1,1):ℕ×ℕ×ℕ),((1,1,0):ℕ×ℕ×ℕ),((2,1,0):ℕ×ℕ×ℕ)] := by
  simp [wLT, HbP.FTL0, topTs, topT, shiftr01, GxL.unitsC]
-- ∴ it is NOT Trc4 (extra (1,1,0) marker col):
example : wLT 0 ([[HdA.UT.ch ([((0,1,0):ℕ×ℕ×ℕ)]:TrioSeq)]], ([]:List (Option TrioSeq)))
    ≠ [((1,1,1):ℕ×ℕ×ℕ),((2,1,0):ℕ×ℕ×ℕ)] := by
  rw [show wLT 0 ([[HdA.UT.ch ([((0,1,0):ℕ×ℕ×ℕ)]:TrioSeq)]], ([]:List (Option TrioSeq)))
    = [((1,1,1):ℕ×ℕ×ℕ),((1,1,0):ℕ×ℕ×ℕ),((2,1,0):ℕ×ℕ×ℕ)] from by
    simp [wLT, HbP.FTL0, topTs, topT, shiftr01, GxL.unitsC]]
  decide
end WltCheck
end TRIO
