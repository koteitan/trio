/-
**Ytosk の展開を trio 本体の `gexp`（先頭 ++ コピー）の形で書く。**
これで trio 本体のコピーの親の補題（`gexp_nextrel0_mir` など）が使える。
-/
import Ytosk.Bridge
import Gtrans

namespace Ytosk

theorem parent_eq_of_par {M : Mat} {t r x : Nat} (ht : t ≤ 2) (hx : x < M.length)
    (hp : par M t x = some r) : TRIO.parent M t x = r := by
  have hn : TRIO.nextR M t r x := (nextR_iff M ht hx).mp hp
  have h1 : TRIO.nextR M t (TRIO.parent M t x) x := by
    unfold TRIO.parent; exact Classical.epsilon_spec (p := fun j0 => TRIO.nextR M t j0 x) ⟨r, hn⟩
  have := (nextR_iff M ht hx).mpr h1; rw [hp] at this; exact (Option.some.inj this).symm

theorem hasParent_of_par {M : Mat} {t r x : Nat} (ht : t ≤ 2) (hx : x < M.length)
    (hp : par M t x = some r) : TRIO.hasParent M t x :=
  ⟨r, (nextR_iff M ht hx).mp hp, fun j hj => by
    have := (nextR_iff M ht hx).mpr hj; rw [hp] at this; exact (Option.some.inj this).symm⟩

/-- **The expansion as `gexp`.** -/
theorem expand_eq_gexp (M : Mat) (n : Nat) (hM : 2 ≤ M.length)
    (hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0))
    {r : Nat} (hp : par M (TRIO.srow M (M.length - 1)) (M.length - 1) = some r) :
    expand M n = TRIO.gexp M r (M.length - 1 - r)
      (if 0 < TRIO.srow M (M.length - 1) then TRIO.entry M 0 (M.length - 1) - TRIO.entry M 0 r else 0)
      (if 1 < TRIO.srow M (M.length - 1) then TRIO.entry M 1 (M.length - 1) - TRIO.entry M 1 r else 0)
      n := by
  have ht : TRIO.srow M (M.length - 1) ≤ 2 := by unfold TRIO.srow; split_ifs <;> omega
  have hx : M.length - 1 < M.length := by omega
  rw [expand_eq_oper M n hM, TRIO.oper_gcopies n (by omega) hz (hasParent_of_par ht hx hp),
    parent_eq_of_par ht hx hp]
  rfl

end Ytosk
