/-
**WfQnA17 (2026-11-01): the closure of the bad calls lies before `r` when the bad calls do.**
- `db_lt_r`: if every bad call is before `r` (`hBr`), every call of the closure `DepXB M B` is before `r`
  (`vpar` never fires in the closure: the row-1 parent of a `v` call of `D` is not in `D` (`dv_shape`);
  `vupg` goes to `i + 1`; `ochild`/`vbump` go to larger columns).
- `hrB_of`: `o(r)` is off the closure (the `hrB` of `WfQnA16.t1_main_vlocSX2`).
- `hnest_of`: no nested bad call, if the bump grandchildren in `D` of a bad call are at or after `r` (`hKr`;
  measured: the last bump grandchild of a bad call is `r` itself).
-/
import Ytosk.WfQnA16

namespace Ytosk.WfQnA17
open T Ytosk Ytosk.WfQnE3

section
variable {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r)
  {q : Nat} (hq : par M 0 (r + L) = some q)
  {B : Nat → Prop} (hB : ∀ i, B i → DepX M (r + L) false i)
include hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr hq hB

theorem db_lt_r (hBr : ∀ i, B i → i < r) : ∀ {b j}, DepXB M B b j → j < r := by
  have hnx := WfQnA2.hnx_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr
  intro b j h
  induction h with
  | leaf h => exact hBr _ h
  | ochild hc _ _ _ ih => have := (mem_children hc).1; omega
  | ov _ ih => exact ih
  | @vpar i m h1i hm hdm _ =>
    exfalso
    have hdi : DepX M (r + L) false i := DepXB.sub hB (DepXB.vpar h1i hm hdm)
    have hiM := lt_of_entry_ne h1i
    rcases Nat.lt_or_ge i (r + L) with hi | hi
    · exact (dv_shape hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hdi).2.1 m hm (DepXB.sub hB hdm)
    · have : i = r + L := by omega
      subst this
      exact hnx hdi
  | @vupg i k h1i h2i hk hdk ih =>
    have hdi : DepX M (r + L) false i := DepXB.sub hB (DepXB.vupg h1i h2i hk hdk)
    have := upg_succ_lt hk
    have hi : i < r + L := by omega
    rcases (dv_shape hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hdi).2.2 with ⟨_, hu, _, _⟩ | ⟨h2', _⟩
    · rw [hu] at hk; cases hk; omega
    · exact absurd h2i h2'
  | vbump _ _ hj _ hk _ ih =>
    have := (mem_children hj).1; have := (mem_children hk).1; omega

/-- **`o(r)` is off the closure.** -/
theorem hrB_of (hBr : ∀ i, B i → i < r) : ¬ DepXB M B true r := fun h =>
  lt_irrefl _ (db_lt_r hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr hq hB hBr h)

/-- **No nested bad call.** -/
theorem hnest_of (hBr : ∀ i, B i → i < r)
    (hKr : ∀ i, B i → ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, DepX M (r + L) true k →
      r ≤ k) :
    ∀ i, B i → ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, ¬ DepXB M B true k := by
  intro i hi j hj hjb k hk hdk
  have h1' := db_lt_r hlen hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hqr hq hB hBr hdk
  have h2' := hKr i hi j hj hjb k hk (DepXB.sub hB hdk)
  omega

end

end Ytosk.WfQnA17
