/-
**hLast（1 列落とし M → M.take x）の部品。**

- `rootP_take_root`: x が根（列が (0,0,0)）なら、x より前の値は変わらない（`take_root_agree`）ので、根の値の
  並び RootP は M のものの先頭部分。
-/
import Ytosk.V3IndV
import Ytosk.V3N0T1

namespace Ytosk

open T

/-- The roots of `M` are those of the prefix and then the root `x` (the last column). -/
theorem roots_take_root {M : Mat} {x : Nat} (hx : x + 1 = M.length) (hk : col M x = (0, 0, 0)) :
    roots M = roots (M.take x) ++ [x] := by
  unfold roots
  have hlen : (M.take x).length = x := by rw [List.length_take]; omega
  rw [← hx, List.range_succ, List.filter_append, hlen]
  congr 1
  · apply List.filter_congr
    intro i hi
    have hix : i < x := List.mem_range.mp hi
    rw [col_take M hix]
  · simp [hk]

/-- **RootP of the prefix before a root column.** -/
theorem rootP_take_root {M : Mat} {x : Nat} (hx : x + 1 = M.length) (hk : col M x = (0, 0, 0))
    {ρ ρ' : Valn} {rk' : Bool → Nat → Nat} (hC : Cons M ρ) (hC' : Cons (M.take x) ρ')
    (hR' : Rk (M.take x) rk') (hp : RootP M ρ) : RootP (M.take x) ρ' := by
  have hag := take_root_agree hk (by omega) hC hC' hR'
  unfold RootP at hp ⊢
  rw [roots_take_root hx hk, List.map_append] at hp
  have h1 := (List.pairwise_append.mp hp).1
  have hmap : (roots (M.take x)).map ρ'.o = (roots (M.take x)).map ρ.o := by
    apply List.map_congr_left
    intro i hi
    have hil : i < (M.take x).length := List.mem_range.mp (List.mem_filter.mp hi).1
    rw [List.length_take] at hil
    exact (hag i (by omega)).1
  rw [hmap]; exact h1

/-- `entry M 0 x = 0` makes `x` a root column (`R01`, `R12`). -/
theorem col_root_of_e0 {M : Mat} {x : Nat} (hR01 : R01 M) (hR12 : R12 M) (h0 : entry M 0 x = 0) :
    col M x = (0, 0, 0) := by
  have h1 := hR01 x h0
  have h2 := hR12 x h1
  rw [col_eq_entries, h0, h1, h2]

end Ytosk
