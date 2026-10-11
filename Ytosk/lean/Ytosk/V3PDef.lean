/-
**閉性の候補 P = S1 ∧ S3 ∧ S4 ∧ PH3c ∧ FC3 の定義（closure、2026-10-11）。**

`tools/probe_close_ph3.py`・`tools/probe_close_inv.py` の python の定義をそのまま写したもの。
実測（C′・deep2・deep3 の 65.6 万個の標準形）で P は真、P ∧ 構造 ∧ Inv3 は M[n]（n = 1..3）と 1 列落としで閉じる。

- S1: 兄弟の部分木（列の並び）は辞書式で増えない。
- S3: 行 1 は行 0 の親より高々 1 大きい（`R1S` と同じ、`sInvXJ_std` で証明済み）。
- S4: 行 2 が 1 の列 c で、q = P_1(c) が c の行 0 の真の祖先のとき、q の子で c の祖先（または c）の d が c でなければ、
  d の行 2 は 1、d と c の間の列の行 1 は c の行 1 より大きい。
- PH3c: 書き換えが起きる B ≠ 0 の数える子の枠（B = 前の数える子までの状態、o(c) = ψ_s(y)、
  y を Ω_{s+1} で hi・lo に分ける）で、(eq) hi = B かつ lo ≠ 0、(pre) B は hi の真の先頭部分、
  (cut) s ≠ 0 で B は hi のある位置 π（添字 k ≥ s の項）を Ω_s に替え π より右をすべて落とした項。
  π は hi の最上位の項そのものではなく、ある項の添字か引数の中（`cutsNS`: 添字の側は添字の鎖だけ、引数の側は高い道（引数に入る項の添字は s 以上）。
  python の cuts より狭い。2026-10-11: この形でも C′・deep2・deep3 で真、閉性も同じ。tools/probe_close_nt.py NARROW=S）。
- FC3: 最初の数える子（B = 0）で書き換えが起き hi ≠ 0 のとき、v(i) = s なら s は極限（0 でも後続でもない）、
  v(i) < s なら hi の先頭の添字は s + X（X ≠ 0、和としての連結）。
-/
import Ytosk.V3InvJ
import Ytosk.V3DropAsm

namespace Ytosk

open T

/-! ## 構造の部分 -/

/-- Strict lexicographic order on columns (python tuple order). -/
def colLtB (a b : Nat × Nat × Nat) : Bool :=
  decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2))))

/-- Strict lexicographic order on column lists (python list order: a proper prefix is smaller). -/
def seqLtB : Mat → Mat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | p :: A, q :: B => colLtB p q || (p == q && seqLtB A B)

/-- The row-0 subtree of `a` as a list of columns: `a` and the following columns with larger row 0. -/
def subT (M : Mat) (a : Nat) : Mat :=
  col M a :: (M.drop (a + 1)).takeWhile (fun q => decide (entry M 0 a < q.1))

/-- **S1**: consecutive sibling subtrees do not increase lexicographically. -/
def S1 (M : Mat) : Prop :=
  ∀ p (l₁ l₂ : List Nat) (a b : Nat), children M p = l₁ ++ a :: b :: l₂ →
    seqLtB (subT M a) (subT M b) = false

/-- **S3** = `R1S`. -/
abbrev S3 (M : Mat) : Prop := R1S M

/-- **S4**: for a row-2-one column `c` whose `P_1` parent `q` is a strict row-0 ancestor, the child `d` of `q`
on the path to `c`, if not `c`, has row 2 one, and the columns strictly between `d` and `c` have row 1 above `c`'s. -/
def S4 (M : Mat) : Prop :=
  ∀ c q d, entry M 2 c = 1 → par M 1 c = some q → par M 0 d = some q → Anc0 M d c → d ≠ c →
    entry M 2 d = 1 ∧
    ∀ t, Anc0 M d t → Anc0 M t c → t ≠ d → t ≠ c → entry M 1 c < entry M 1 t

/-! ## 値の部分 -/

/-- The positions `π` of `h` holding a summand `ψ_k(γ)` with `k ≥ s`: replace the summand (with what follows it
in its sum) by `Ω_s` and drop everything to the right of `π` (order: subscript, argument, rest). The path to `π`
enters the argument of a summand only when its subscript is at least `s`, and never a subscript (high path; 2026-10-11 実測: 標準形の
cut の枠 28.8 万件はすべてこの形。添字が s より小さい項の引数の中の位置は、t = 2 の置き換え σ で保たれない）。 -/
def cutsH (s : T) : T → List T
  | z => []
  | psi a x c =>
      (if le s a then [psi s z z] else []) ++
        (if le s a then (cutsH s x).map (fun t => psi a t z) else []) ++ (cutsH s c).map (fun t => psi a x t)

/-- The chain of subscripts: replace the head summand of `h` (`k ≥ s`) by `Ω_s`, or recurse into the subscript of the
head summand (`Ω_s`, `Ω_{Ω_s}`, … along the subscripts). -/
def scuts (s : T) : T → List T
  | z => []
  | psi a _ _ => (if le s a then [psi s z z] else []) ++ (scuts s a).map (fun t => psi t z z)

/-- The cut positions allowed in `PH3c`: inside a summand of `h`, either along the subscript chain of the summand
(`scuts`) or in its argument along a high path (`cutsH`); the summands before it are kept. A top-level summand itself is never
the position. -/
def cutsNS (s : T) : T → List T
  | z => []
  | psi a x c =>
      (scuts s a).map (fun t => psi t z z) ++ (cutsH s x).map (fun t => psi a t z) ++
        (cutsNS s c).map (fun t => psi a x t)

/-- The kinds `eq`・`pre`・`cut` of a rewriting frame with state `B ≠ 0`, `y = hi + lo` split at `Ω_{s+1}`.
The `cut` position is never a top-level summand of `hi` (`cutsNS`; 2026-10-11 実測: 標準形の cut の枠 9.7 万で、
位置は先頭の項の添字の鎖 S…S T か、ある項の引数の中。最上位の項そのものを Ω_s に替える位置は 0 件）。 -/
def PH3cKind (B hi lo s : T) : Prop :=
  (hi = B ∧ lo ≠ z) ∨ (hi ≠ B ∧ ((∃ R, R ≠ z ∧ hi = app B R) ∨ (s ≠ z ∧ B ∈ cutsNS s hi)))

/-- The state before the counted children `L` of `i`. -/
def stB (ρ : Valn) (i : Nat) (L : List Nat) : T := spArg (ρ.v i) z (sumN (L.map ρ.o))

/-- **PH3c**: every rewriting frame with nonzero state is of kind `eq`, `pre` or `cut`. -/
def PH3c (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL M i = L ++ c :: R → ∀ s y,
    ρ.o c = psi s y z → stB ρ i L ≠ z →
    lt (stB ρ i L) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
    PH3cKind (stB ρ i L) (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s

/-- The conclusion of `FC3` at a frame. -/
def FC3c (a s y : T) : Prop :=
  (s = a → s ≠ z ∧ last s ≠ one) ∧ (s ≠ a → ∃ X, X ≠ z ∧ lev (split y (psi (succ s) z z)).1 = app s X)

/-- **FC3**: in the frame of the first counted child, when it rewrites and `hi ≠ 0`: `v(i) = s` forces `s` to be a
limit; `v(i) < s` forces the head subscript of `hi` to be `s + X` with `X ≠ 0`. -/
def FC3 (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ∀ (c : Nat) (R : List Nat), CL M i = c :: R → ∀ s y,
    ρ.o c = psi s y z → y ≠ z → lt (psi (ρ.v i) z z) (psi s y z) = true →
    (split y (psi (succ s) z z)).1 ≠ z →
    (s = ρ.v i → s ≠ z ∧ last s ≠ one) ∧
    (s ≠ ρ.v i → ∃ X, X ≠ z ∧ lev (split y (psi (succ s) z z)).1 = app s X)

/-- **The closure candidate** `P = S1 ∧ S3 ∧ S4 ∧ PH3c ∧ FC3`. -/
structure PInv (M : Mat) (ρ : Valn) : Prop where
  s1 : S1 M
  s3 : S3 M
  s4 : S4 M
  ph3c : PH3c M ρ
  fc3 : FC3 M ρ

/-! ## G3: 広げた切り口の文法（2026-10-12、closure）

`cutsNS`・`cutsH` は標準形で偽だった（ext1 の t = 2 の行列の M[2]・M[3] で 153 枠。例:
M = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,1,0)(5,1,0)(1,1,1) の M[2] の枠で
B = Ω_{ψ_ω(ψ_ω(Ω_1))}、hi = Ω_{ψ_ω(ψ_ω(Ω_2))}、s = 1。位置は添字に入ってから引数の高い道を進む）。
G3: 添字には自由に入る、引数と後ろには添字が s 以上の項からだけ入る、最上位の項そのものは位置にしない。
ext1 の展開の t = 0・1・2 の cut の枠 119607 件と 5 集合の cut の枠はすべて G3。 -/

/-- G3 の位置（項の中）: 添字に入る。添字が s 以上の項では、その項を `Ω_s` に替える・引数に入る・後ろへ進む
（標準形の項では、位置を含む後ろの項は Ω_s 以上なので前の項も添字 ≥ s。この条件で切り口は s より大きい）。 -/
def cutsHG (s : T) : T → List T
  | z => []
  | psi a x c =>
      (cutsHG s a).map (fun t => psi t z z) ++
        (if le s a then [psi s z z] ++ (cutsHG s x).map (fun t => psi a t z) ++
          (cutsHG s c).map (fun t => psi a x t) else [])

/-- G3 の位置（状態の段）: 最上位の項そのものは除く。 -/
def cutsNSG (s : T) : T → List T
  | z => []
  | psi a x c =>
      (cutsHG s a).map (fun t => psi t z z) ++ (cutsHG s x).map (fun t => psi a t z) ++
        (cutsNSG s c).map (fun t => psi a x t)

/-- The kinds with the G3 cut. -/
def PH3cKindG (B hi lo s : T) : Prop :=
  (hi = B ∧ lo ≠ z) ∨ (hi ≠ B ∧ ((∃ R, R ≠ z ∧ hi = app B R) ∨ (s ≠ z ∧ B ∈ cutsNSG s hi)))

/-- **PH3c** with the G3 cut. -/
def PH3cG (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ∀ (L : List Nat) (c : Nat) (R : List Nat), CL M i = L ++ c :: R → ∀ s y,
    ρ.o c = psi s y z → stB ρ i L ≠ z →
    lt (stB ρ i L) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
    PH3cKindG (stB ρ i L) (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s

/-- **The closure candidate** with the G3 cut. -/
structure PInvG (M : Mat) (ρ : Valn) : Prop where
  s1 : S1 M
  s3 : S3 M
  s4 : S4 M
  ph3c : PH3cG M ρ
  fc3 : FC3 M ρ

end Ytosk
