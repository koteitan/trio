/-
**拡張 Buchholz の項とその演算（Ytosk 氏の評価器の項の側）。**

Ytosk 氏の評価器（`Ytosk.Eval`）が値として返す項の型と、その上の演算（和、ω 冪、標準形 SF）。

項は `psi a b c` = ψ_a(b) + c（和は左から大きい順）、`z` = 0。
順序 `lt` は (添字, 引数, 残り) の辞書式。
-/
namespace Ytosk

/-- Extended Buchholz terms in list form: `psi a b c` is ψ_a(b) + c. -/
inductive T : Type where
  | z : T
  | psi : T → T → T → T
  deriving DecidableEq, Repr, Inhabited

open T

/-! ## 項の演算 -/

/-- `1 = ψ_0(0)`. -/
def one : T := psi z z z

/-- Lexicographic order on (subscript, argument, rest), `0` least. -/
def lt : T → T → Bool
  | _, z => false
  | z, psi _ _ _ => true
  | psi a b c, psi d e f =>
      if a = d then (if b = e then lt c f else lt b e) else lt a d

/-- The leading summand. -/
def head : T → T
  | z => z
  | psi a b _ => psi a b z

/-- Ordinal addition: summands of `x` below the head of `y` are absorbed. -/
def add : T → T → T
  | z, y => y
  | psi a b c, y =>
      match y with
      | z => psi a b c
      | psi d e _ => if lt (psi a b z) (psi d e z) then y else psi a b (add c y)

/-- `sub x y`: drop from `x` the summands it shares with `y` at the front. -/
def sub : T → T → T
  | z, _ => z
  | psi a b c, y =>
      match y with
      | z => psi a b c
      | psi d e f => if lt (psi d e z) (psi a b z) then psi a b c else sub c f

/-- `split x t` = (the leading summands of `x` that are `≥ t`, the rest). -/
def split : T → T → T × T
  | z, _ => (z, z)
  | psi a b c, t =>
      if lt (psi a b z) t then (z, psi a b c)
      else let r := split c t; (psi a b r.1, r.2)

/-- `ω^x`. Below `ψ_0(Ω_1)` it is `ψ_0(x)`; above, the head's argument keeps its part
`≥ Ω_(s+1)` and takes the rest of `x`. -/
def omega (x : T) : T :=
  if lt x (psi z (psi one z z) z) then psi z x z
  else match x with
    | z => one
    | psi s b _ =>
        let p := (split b (psi (add s one) z z)).1
        psi s (add p (sub x (psi s p z))) z

/-- The last summand. -/
def last : T → T
  | z => z
  | psi a b z => psi a b z
  | psi _ _ c => last c

/-- `cut x w`: drop the trailing summands of `x` below `Ω_w`. -/
def cut (w : T) : T → T
  | z => z
  | psi s b c =>
      let r := cut w c
      if r = z ∧ lt (psi s b z) (psi w z z) then z else psi s b r

/-- Build the standard argument of `ψ_a`: summands of `x` are added to `b` one by one; a summand
`ψ_s(y)` with `b < y` and `ψ_s(y) > Ω_a` is replaced by its part of size `≥ Ω_(s+1)`. -/
def sp (a : T) : T → T → T
  | b, z => psi a b z
  | b, psi s y c =>
      if lt b y ∧ lt (psi a z z) (psi s y c) then
        let t := cut (add s one) y
        sp a (add t (sub (psi s y z) (psi s t z))) c
      else sp a (add b (psi s y z)) c

/-- Standard form. -/
def sf : T → T
  | z => z
  | psi a b c => add (sp (sf a) z (sf b)) (sf c)

/-! ## 表示 -/

mutual
/-- `p_{a}(b)+c` in the notation of the sheet check (`1` = `p(0)`, subscript `0` omitted). -/
def str : T → String
  | z => "0"
  | psi a b c => String.intercalate "+" (strTerms (psi a b c))

def strTerms : T → List String
  | z => []
  | psi a b c =>
    (if a = z ∧ b = z then "1"
     else "p" ++ (if a = z then "" else "_{" ++ str a ++ "}") ++ "(" ++ str b ++ ")")
      :: strTerms c
end

end Ytosk
