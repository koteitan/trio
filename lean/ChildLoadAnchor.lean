/-
ChildLoadAnchor.lean: childLoad の ch-Z route の基盤 anchor(coordinator lead 検証)。
childLoad の load 部 shiftr01 2 0 Z (Z∈Wg(2c) based) は GoodChtX の `ch (shiftr01 1 0 Z)` 葉で扱える:
- (a) okLowS c (shiftr01 1 0 Z) が成立(okLowS_load, Wg-load を吸収)⟹ LRawT c (ch (shiftr01 1 0 Z))。
- (b) topT v (ch (shiftr01 1 0 Z)) = shiftr01 2 0 Z = childLoad の load 部そのもの。
∴ deep-leaf(upleaf_deep_coreD, row1≥m)でなく ch-Z(low load, row1≤c)で childLoad が既存機構で achievable。
-/
import HdP
import HdQ

namespace TRIO
namespace ChildLoadAnchor

open Wset Small Gw GwS HdA HdP HdQ

/-- (a) Wg-load Z を shiftr01 1 した low-load は okLowS(⟹ ch 葉として valid)。 -/
theorem okLowS_wgload {c : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg (2 * c)) (hb : based Z) :
    okLowS c (shiftr01 1 0 Z) := by
  have := okLowS_load (okLowS_nil c) hZ hb
  simpa using this

/-- (a') ∴ LRawTs c [ch (shiftr01 1 0 Z)](GoodChtX_snocL で append 可能)。 -/
theorem LRawTs_chZ {c : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg (2 * c)) (hb : based Z) :
    LRawTs c [HdA.UT.ch (shiftr01 1 0 Z)] := by
  refine ⟨?_, trivial⟩
  show okLowS c (shiftr01 1 0 Z)
  exact okLowS_wgload hZ hb

/-- (b) ch (shiftr01 1 0 Z) の rendering は shiftr01 2 0 Z = childLoad の load 部。 -/
theorem chZ_render (v : ℕ) (Z : TrioSeq) :
    topT v (HdA.UT.ch (shiftr01 1 0 Z)) = shiftr01 2 0 Z := by
  show shiftr01 1 0 (shiftr01 1 0 Z) = shiftr01 2 0 Z
  rw [shiftr01_add0]

end ChildLoadAnchor
end TRIO
