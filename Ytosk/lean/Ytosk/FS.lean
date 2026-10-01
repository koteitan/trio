/-
**拡張 Buchholz の項の基本列（Denis 氏の規則、対角化の始点 γ[0] = 0）。**

googology wiki "Extended Buchholz's function" の基本列。共終数は 0・後続・ω・Ω_{μ+1} の 4 種類。
対角化（ψ_ν(β)、β の共終数が Ω_{μ+1}、μ ≥ ν）は γ[0] = 0、γ[k+1] = ψ_μ(β[γ[k]]) から始める（BM4 の展開に合う版、
`tools/ebocf_fs.py` の `G0 = "zero"`）。

目標: 標準形 t について t[η] は標準形で t[η] < t（乱択の 22,460 項・61,791 回で例外なし）。
-/
import Ytosk.SP

namespace Ytosk

open T

/-- All summands but the last. -/
def init : T → T
  | z => z
  | psi _ _ z => z
  | psi a b c => psi a b (init c)

/-- The number of summands. -/
def count : T → Nat
  | z => 0
  | psi _ _ c => count c + 1

/-- The finite ordinal `n = 1 + ... + 1`. -/
def natT : Nat → T
  | 0 => z
  | n + 1 => psi z z (natT n)

/-- `t` is a successor: its last summand is `1`. -/
def isSucc (t : T) : Bool := last t == one

/-- Cofinality: `0`, successor, `ω`, or `Ω_{μ+1}` (stored as `μ`). -/
inductive Cof where
  | zero | succ | omega | big (μ : T)
  deriving DecidableEq

/-- The cofinality of a term (by its last summand). -/
def cof : T → Cof
  | z => .zero
  | psi a b (psi c d e) => cof (psi c d e)
  | psi a b z =>
    if b = z then
      (if a = z then .succ else if isSucc a then .big (init a) else cof a)
    else if isSucc b then .omega
    else match cof b with
      | .big μ => if lt μ a then .big μ else .omega
      | c => c

/-- `ψ_ν(β) · n`. -/
def mulT (t : T) : Nat → T
  | 0 => z
  | n + 1 => app t (mulT t n)

/-- The fundamental sequence `t[η]` (for cofinality `ω` the index is `count η`). -/
def fs : T → T → T
  | z, _ => z
  | psi a b (psi c d e), η => psi a b (fs (psi c d e) η)
  | psi a b z, η =>
    if b = z then
      (if a = z then z else if isSucc a then η else psi (fs a η) z z)
    else if isSucc b then mulT (psi a (init b) z) (count η)
    else match cof b with
      | .big μ =>
        if lt μ a then psi a (fs b η) z
        else psi a (fs b (Nat.rec z (fun _ g => psi μ (fs b g) z) (count η))) z
      | _ => psi a (fs b η) z

#eval [psi z (psi z one z) z, psi z (psi (psi one z z) z z) z].map fun t =>
  ((List.range 3).map fun n => str (fs t (natT n)))

end Ytosk
