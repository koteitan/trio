/-
**各段で標準形に直す翻訳 eval′（段 1 の対象）。**

`Ytosk.Eval` の v, o と同じ再帰で、o と v を作るたびに標準形化 `sf` をかける。途中の値はすべて標準形になる。
Ytosk 氏の eval とはシートの全行で一致し、乱択の 11,385 行列中 11,383 で一致する（`tools/ytosk_eval2.py`）。
-/
import Ytosk.Eval

namespace Ytosk

open T

/-- Sum a list of optional terms (`none` if any is `none`). -/
def sumOptN (l : List (Option T)) : Option T :=
  l.foldl (fun s x => do let a ← s; let b ← x; pure (sf (add a b))) (some z)


mutual
/-- `val2 M f path n` = v(M, n), the subscript of column `n` (`0` for `none`).
`path` holds the calls in progress; a call already on it means v and o call each other in a cycle,
and the result is `none`. `f` only makes the recursion structural: the calls on a path are distinct,
so depth `2 * length + 2` is never reached. -/
def val2 (M : Mat) : Nat → List Call → Option Nat → Option T
  | _, _, none => some z
  | 0, _, some _ => none
  | f + 1, path, some n =>
    if (false, n) ∈ path then none
    else
    let path := (false, n) :: path
    if entry M 1 n = 0 then some z
    else if entry M 2 n = 0 then do
      let u ← match upg M n with
        | some k => (val2 M f path (some k)).map last
        | none => some one
      let b ← val2 M f path (par M 1 n)
      pure (sf (add b u))
    else do
      let p ← sumOptN (some one :: (children M n).map fun j =>
        if col M j = bump M n then
          (sumOptN ((children M j).map fun k => ord2 M f path k)).map (fun q => omega q)
        else some z)
      let b ← val2 M f path (par M 1 n)
      pure (sf (add b (omega p)))

/-- `ord2 M f path n` = o(M, n) before the standard form: ψ_(v(n)) of the sum of the counted
children. -/
def ord2 (M : Mat) : Nat → List Call → Nat → Option T
  | 0, _, _ => none
  | f + 1, path, n =>
    if (true, n) ∈ path then none
    else
    let path := (true, n) :: path
    do
    let S ← sumOptN ((children M n).map fun i =>
      if col M i = bump M n then some z
      else if isUpg M i ∧ topped M i then some z
      else ord2 M f path i)
    let v ← val2 M f path (some n)
    pure (sf (psi v S z))
end

/-- The ordinal of a matrix: the standard form of the sum of `o` over its `(0,0,0)` columns.
`none` if v and o call each other in a cycle at some column (as at SRO); such matrices are outside
the evaluator's range. -/
def eval2 (M : Mat) : Option T :=
  let f := 2 * M.length + 2
  if (List.range M.length).all (fun i => (ord2 M f [] i).isSome) then
    (sumOptN ((List.range M.length).map fun i =>
      if col M i = (0, 0, 0) then ord2 M f [] i else some z))
  else none

end Ytosk
