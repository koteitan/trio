/-
**行列 → 拡張 Buchholz の項（Ytosk 氏の評価器）。**

Ytosk 氏のブログ記事 "Algorithm that changes BMS matrices into ordinals up to SRO"
(https://googology.fandom.com/wiki/User_blog:Ytosk/Algorithm_that_changes_BMS_matrices_into_ordinals_up_to_SRO)
の関数 v（列の添字）, o（列の値）を 3 行の行列の上で定義する。標準形 SF は `Ytosk.Term`。
実行できる読みは https://github.com/hemisemidemipresent/bms（src/lib）の JavaScript 版に合わせた。
ブログとの違いは 1 か所: 行 2 が 1 の列の添字の土台を P_2 でなく P_1 の親から取る。
v と o は前後の列を呼び合うので、呼び出し中の列の道を持ち、循環したら `none` を返す。
-/
import Ytosk.Term

namespace Ytosk

open T

/-- A matrix of three rows, as a list of columns. -/
abbrev Mat := List (Nat × Nat × Nat)

/-- `entry M i j` = the `i`-th row of the `j`-th column (`0` outside). -/
def entry (M : Mat) (i j : Nat) : Nat :=
  let c := M.getD j (0, 0, 0)
  if i = 0 then c.1 else if i = 1 then c.2.1 else c.2.2

/-! ## 行列の関数 -/

/-- The column `n`. -/
def col (M : Mat) (n : Nat) : Nat × Nat × Nat := M.getD n (0, 0, 0)

/-- `(M_n,0 + 1, M_n,1, 1)`: the column that sits right on top of `n` in the subscript. -/
def bump (M : Mat) (n : Nat) : Nat × Nat × Nat := (entry M 0 n + 1, entry M 1 n, 1)

def prev : Nat → Option Nat
  | 0 => none
  | n + 1 => some n

/-- From `q`, walk with `step` until `ok` holds (at most `fuel` steps). -/
def climb (step : Nat → Option Nat) (ok : Nat → Bool) : Nat → Option Nat → Option Nat
  | 0, _ => none
  | _, none => none
  | f + 1, some q => if ok q then some q else climb step ok f (step q)

/-- `par M r n` = P_r(n): the nearest ancestor of `n` in the row-(r-1) tree whose row-r entry is
smaller (row -1: the previous column). -/
def par (M : Mat) : Nat → Nat → Option Nat
  | 0, n => climb prev (fun q => entry M 0 q < entry M 0 n) (n + 1) (prev n)
  | r + 1, n => climb (par M r) (fun q => entry M (r + 1) q < entry M (r + 1) n) (n + 1) (par M r n)

/-- The column that upgrades `n` (the "upgrade effect"): the next column, or an ancestor in row 0,
equal to `(M_m,0 + 1, M_n,1, M_m,2 + 1)` with `m = P_1(n)` and the same row-1 parent. -/
def upg (M : Mat) (n : Nat) : Option Nat :=
  if entry M 1 n = 0 ∨ entry M 2 n = 1 ∨ n + 1 = M.length then none else
  match par M 1 n with
  | none => none
  | some m =>
    let L : Nat × Nat × Nat := (entry M 0 m + 1, entry M 1 n, entry M 2 m + 1)
    if par M 1 (n + 1) = some m ∧ col M (n + 1) = L then some (n + 1)
    else climb (par M 0)
      (fun q => par M 1 q = some m ∧ col M q = L ∧ entry M 0 q < entry M 0 (n + 1))
      (n + 1) (par M 0 n)

/-- Does some column upgrade to `i`? -/
def isUpg (M : Mat) (i : Nat) : Bool := (List.range M.length).any (fun k => upg M k = some i)

/-- The row-0 children of `n`, left to right. -/
def children (M : Mat) (n : Nat) : List Nat :=
  (List.range M.length).filter (fun i => par M 0 i = some n)

/-- `i` has no children, or its last child is `bump M i`. -/
def topped (M : Mat) (i : Nat) : Bool :=
  match (children M i).getLast? with
  | none => true
  | some c => col M c = bump M i

/-- Sum a list of optional terms (`none` if any is `none`). -/
def sumOpt (l : List (Option T)) : Option T :=
  l.foldl (fun s x => do let a ← s; let b ← x; pure (add a b)) (some z)

/-- A call on the path: `(false, n)` is v(n), `(true, n)` is o(n). -/
abbrev Call := Bool × Nat

mutual
/-- `val M f path n` = v(M, n), the subscript of column `n` (`0` for `none`).
`path` holds the calls in progress; a call already on it means v and o call each other in a cycle,
and the result is `none`. `f` only makes the recursion structural: the calls on a path are distinct,
so depth `2 * length + 2` is never reached. -/
def val (M : Mat) : Nat → List Call → Option Nat → Option T
  | _, _, none => some z
  | 0, _, some _ => none
  | f + 1, path, some n =>
    if (false, n) ∈ path then none
    else
    let path := (false, n) :: path
    if entry M 1 n = 0 then some z
    else if entry M 2 n = 0 then do
      let u ← match upg M n with
        | some k => (val M f path (some k)).map last
        | none => some one
      let b ← val M f path (par M 1 n)
      pure (add b u)
    else do
      let p ← sumOpt (some one :: (children M n).map fun j =>
        if col M j = bump M n then
          (sumOpt ((children M j).map fun k => ord M f path k)).map (fun q => omega q)
        else some z)
      let b ← val M f path (par M 1 n)
      pure (add b (omega p))

/-- `ord M f path n` = o(M, n) before the standard form: ψ_(v(n)) of the sum of the counted
children. -/
def ord (M : Mat) : Nat → List Call → Nat → Option T
  | 0, _, _ => none
  | f + 1, path, n =>
    if (true, n) ∈ path then none
    else
    let path := (true, n) :: path
    do
    let S ← sumOpt ((children M n).map fun i =>
      if col M i = bump M n then some z
      else if isUpg M i ∧ topped M i then some z
      else ord M f path i)
    let v ← val M f path (some n)
    pure (psi v S z)
end

/-- The ordinal of a matrix: the standard form of the sum of `o` over its `(0,0,0)` columns.
`none` if v and o call each other in a cycle at some column (as at SRO); such matrices are outside
the evaluator's range. -/
def eval (M : Mat) : Option T :=
  let f := 2 * M.length + 2
  if (List.range M.length).all (fun i => (ord M f [] i).isSome) then
    (sumOpt ((List.range M.length).map fun i =>
      if col M i = (0, 0, 0) then ord M f [] i else some z)).map sf
  else none

/-! ## 例（ブログの表から） -/

/-- `ω = ψ_0(1)`. -/
def w : T := psi z one z

/-- `(0,0,0)(1,1,1) = ψ_0(ψ_ω(0))`. -/
example : eval [(0,0,0), (1,1,1)] = some (psi z (psi w z z) z) := by decide

/-- `(0,0,0)(1,1,1)(2,1,0)(1,1,1) = ψ_0(ψ_ω(ψ_ω(0)))`: the last column upgrades `(2,1,0)` and is
not counted again. -/
example : eval [(0,0,0), (1,1,1), (2,1,0), (1,1,1)] =
    some (psi z (psi w (psi w z z) z) z) := by decide

/-- `(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0) = ψ_0(ψ_(ψ_(ψ_1(0))(0))(0))`. -/
example : eval [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (1,1,1), (2,1,1), (3,1,0)] =
    some (psi z (psi (psi (psi one z z) z z) z z) z) := by decide

/-- SRO = `(0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0)` (the sheet's psi(I)) is outside the range:
v(1) → v(2) → o(3) → v(3) → v(1) is a cycle. -/
example : eval [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (2,0,0)] = none := by decide

end Ytosk
