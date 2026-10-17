/-
**t = 1・q = r: x − 1 が上げを失う場合の始点の添字（2026-10-17、t1）。**

r = x − 1 は M.take x の最後の列なので上げがなく、v′(r) = v′(P_1 r) + 1。P_1 r の v は 1 列落としで
変わらない（変わる v の列には P_1 で指す列がない、chg_struct の TopC）。よって v′(r) = v(P_1 r) + 1。
-/
import Ytosk.V3SeedWeak
import Ytosk.V3StrictR
import Ytosk.V3DropPres

namespace Ytosk

open T

/-- **`v′(x − 1) = v(P_1(x − 1)) + 1`** in `M.take x`. -/
theorem v_last_take {M : Mat} {x : Nat} (hx : x + 1 = M.length)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
    {r : Nat} (hr : r + 1 = x) (h1r : entry M 1 r ≠ 0) (h2r : entry M 2 r = 0) :
    ρ'.v r = sf (add (vOpt ρ (par M 1 r)) one) := by
  have hrT : r < (M.take x).length := by rw [List.length_take]; omega
  rw [(hC' r hrT).2]
  unfold vRhs
  rw [entry_take M 1 (show r < x by omega), if_neg h1r, entry_take M 2 (show r < x by omega), if_pos h2r,
    upg_last_none (show r + 1 = (M.take x).length by rw [List.length_take]; omega),
    par_take M 1 r (show r < x by omega)]
  congr 2
  cases hm : par M 1 r with
  | none => rfl
  | some m =>
    show ρ'.v m = ρ.v m
    have hmr := par_lt M 1 r m hm
    apply ((chg_off hx hC hG hC' hRk' m (by omega)).2)
    intro hch
    exact (chg_struct hx hR0 hZ2 hSD hZ1 hUAT hUAB hch).1 rfl (by omega) |>.2.2 r (by omega) hm

end Ytosk
