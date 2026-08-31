/-
**R2 の検算用ファイル（測定側）。**

`L105Cap.lean:1350` の注釈:

    「`X ∈ W m` から `X ∈ W (lev X 0)` は**出ない**（`W_mono` は逆向き）ので、
      これは真の弱化である。」

⚠ これは `Wset.W_root_stage`（`Wset.lean:2304`）と矛盾する。実際に逆向きが引ける。
⟹ **`LiftTieSelf` は `LiftTie` の弱化ではなく、同値**。
-/
import L105Cap

namespace TRIO
namespace R2LT

open Wset

/-- **`LiftTieSelf ⟹ LiftTie`**（逆は `L105.liftTieSelf_of_liftTie` で既にある）。
⟹ 2 つは同値であり、「自己段への制限」は債務を減らさない。 -/
theorem liftTie_of_liftTieSelf (h : L105.LiftTieSelf) : L53.LiftTie := by
  intro m d v z R hR ht hX
  have hne : (((0, v, z) : ℕ × ℕ × ℕ) :: R) ≠ [] := by simp
  have hlev : lev (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 = 2 * v + z :=
    L105.lev_cons_root v z R
  have hself : (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z) := by
    have hr := W_root_stage hX hne
    rwa [hlev] at hr
  have hle : 2 * v + z ≤ m := by
    have hr := lev_root_le_of_mem_W hX hne
    rwa [hlev] at hr
  exact W_mono (by omega) (h d v z R hR ht hself)

/-- ⟹ **同値**。 -/
theorem liftTie_iff_liftTieSelf : L53.LiftTie ↔ L105.LiftTieSelf :=
  ⟨L105.liftTieSelf_of_liftTie, liftTie_of_liftTieSelf⟩

end R2LT
end TRIO
