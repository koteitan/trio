/-
**行 2 が 0 の行列（2 行、PSS）の評価器を、燃料なしの再帰で書いた版。**

行 2 が 0 なら上げも上に乗る子もないので、v(n) は行 1 の親の鎖の長さ、o(n) は子の値の和を引数にした ψ_{v(n)}。
`eval2` と同じく各段で sf をかける。子の番号は親より大きいので、`M.length - n` についての帰納で定義できる。
-/
import Ytosk.Bridge
import Ytosk.Eval2

namespace Ytosk

open T

/-- Sum with the standard form after each addition (as `sumOptN`). -/
def sumN (l : List T) : T := l.foldl (fun a b => sf (add a b)) z

/-- `v(n)` for a matrix whose row 2 is zero: `v(P_1 n) + 1`, and `0` when row 1 is `0`. -/
def vr (M : Mat) (n : Nat) : T :=
  if entry M 1 n = 0 then z
  else
    match h : par M 1 n with
    | none => sf (add z one)
    | some m =>
      have : m < n := par_lt M 1 n m h
      sf (add (vr M m) one)
termination_by n

theorem mem_children {M : Mat} {n i : Nat} (h : i ∈ children M n) : n < i ∧ i < M.length := by
  unfold children at h
  rw [List.mem_filter] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨par_lt M 0 i n (by simpa using h2), List.mem_range.mp h1⟩

/-- The normalized value `o′(n)` of a column (row 2 zero). -/
def o2r (M : Mat) (n : Nat) : T :=
  sf (psi (vr M n) (sumN ((children M n).attach.map fun ⟨i, hi⟩ =>
    have : M.length - i < M.length - n := by
      have := mem_children hi; omega
    o2r M i)) z)
termination_by M.length - n

/-- The ordinal of a matrix whose row 2 is zero. -/
def ev2r (M : Mat) : T :=
  sumN ((List.range M.length).filter (fun i => col M i = (0, 0, 0)) |>.map (o2r M))

/-- The defining equation of `o2r` without `attach`. -/
theorem o2r_eq (M : Mat) (n : Nat) :
    o2r M n = sf (psi (vr M n) (sumN ((children M n).map (o2r M))) z) := by
  rw [o2r]
  congr 3
  simp [List.map_attach_eq_pmap]

/-- **Congruence.** Equal subscripts and equal lists of child values give equal values. -/
theorem o2r_congr {M M' : Mat} {n n' : Nat} (hv : vr M n = vr M' n')
    (hc : (children M n).map (o2r M) = (children M' n').map (o2r M')) : o2r M n = o2r M' n' := by
  rw [o2r_eq, o2r_eq, hv, hc]

#eval [[(0,0,0), (1,1,0), (2,2,0)], [(0,0,0), (1,1,0), (2,2,0), (2,0,0)],
    [(0,0,0), (1,1,0), (2,1,0), (1,1,0), (2,1,0), (1,1,0), (2,0,0), (3,1,0), (4,1,0), (3,1,0), (4,1,0), (3,1,0)]].map
  fun (M : Mat) => (str (ev2r M), (eval2 M).map str)

end Ytosk
