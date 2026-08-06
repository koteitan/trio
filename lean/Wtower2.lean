/-
Wtower2.lean: **行 2 塔をリフト無し `Wstar` のまま解く** — (WL) を法として。

`towerGraft2_holds`（Wset.lean）は塔の帰納を「すべてのリフト量 `s` について」
強めて回している。そのために `Wstar2`（リフト閉）が要り、そこから `GraftAll`
→ `GX` → `CoreCap` の全体が生えた。

しかし塔が実際に消費するのは **1 つの具体的なリフト `d1 = 行1(末尾) - v`** だけ
であり、段の勘定は

```
prev ∈ W (2v+z)  --(WL)-->  Lift1 prev d1 ∈ W (2v+z+2*d1) = W (2w+z) ⊆ W m
                              （w = 行1(末尾), z < 行2(末尾) ⟹ 2w+z ≤ m）
```

でちょうど閉じる。したがって **(WL) さえあれば `Wstar`（リフト無し）のままで
`TowerGraft2` が証明でき、`Wstar2` / `GX` / `CoreCap` は不要**になる。

(WL) は `tools/probe_lift.py` で 18300 例すべて**等号**で成立
（`minstage (Lift1 X d) = minstage X + 2d`）。階段リフト版
（`Wslift.slift_mem_W_tight` / `mlift_mem_W`）は核なしで証明済み。
-/
import Wset
import Wslift

namespace TRIO

open Wset
open Classical

/-- **(WL)**: the ambient root lift costs exactly `2 * d` stages.  Measured with
equality on 18300 instances (`tools/probe_lift.py`); the staircase-lift version
is proved (`Wslift.mlift_mem_W`). -/
def LiftStage : Prop :=
  ∀ (m d : ℕ) (X : TrioSeq), X ∈ W m → Lift1 X d ∈ W (m + 2 * d)

/-- **The row-2 tower falls to (WL) over the LIFT-FREE `Wstar`.**  The tower's
induction only ever needs the single lift `d1`, so the `∀ s` strengthening (and
with it `Wstar2`, `GraftAll`, `GX`) is unnecessary once the stage law is
available. -/
theorem towerGraft2_of_liftStage (hWL : LiftStage) : Wset.TowerGraft2 := by
  classical
  intro v z m a R hR hRne hz1 hva hd hi1 hgr hpM n _
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set M : TrioSeq := p0 :: R with hMdef
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : M.length - 1 = R.length := by rw [hMdef]; simp
  have hE : ∀ i, entry M i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  have hL : M.length - 1 ≠ 0 := by rw [hMlen]; omega
  have hzz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -, -⟩; rw [hE 0] at h1; omega
  have hsrM : srow M (M.length - 1) = 2 := by
    rw [hMlen, hMdef, srow_cons_last hRne, hi1]
  have hpM' : hasParent M (srow M (M.length - 1)) (M.length - 1) := by
    rw [hsrM, hMlen, hMdef, ← hi1]; exact hpM
  have hpar0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0 := by
    rw [hsrM, hMlen]
    have := parent_cons_eq_zero (v := v) (z := z) hRne hd hpM
    rwa [hi1] at this
  have hroot1 : entry M 1 0 = v := by rw [hMdef]; simp [entry, hp0]
  have hroot2 : entry M 2 0 = z := by rw [hMdef]; simp [entry, hp0]
  have hnr := parent_nextR hpM'
  rw [hpar0, hsrM] at hnr
  have hn2 : nextrel2 M 0 (M.length - 1) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_neg (by omega)] at hnr
    exact hnr
  have hle1lp : le1 M 0 (M.length - 1) := hn2.2.2.2.2.1
  have hwv : v < entry R 1 (R.length - 1) := by
    have := le1_entry1_lt hle1lp (by omega)
    rw [hroot1, hMlen, hE 1] at this
    exact this
  have hz2 : z < entry R 2 (R.length - 1) := by
    have := hn2.2.2.2.1
    rw [hroot2, hMlen, hE 2] at this
    exact this
  set d1 : ℕ := entry R 1 (R.length - 1) - v with hd1
  have hlev := hd.1
  unfold lev at hlev
  have hbound : 2 * v + z + 2 * d1 ≤ m := by rw [hd1]; omega
  have hM0 : M⟦0⟧ = [] := by
    rw [oper_bad_unfold 0 hL hzz hpM', hpar0]
    simp
  have hstep : ∀ j, M⟦j + 1⟧ = p0 :: graft R (Lift1 (M⟦j⟧) d1) := by
    intro j
    rw [hd1]
    exact oper_cons_tower2 hR hRne hd hi1 hpM
  have hbased : ∀ j, based (M⟦j⟧) := by
    intro j
    cases j with
    | zero => rw [hM0]; exact based_nil
    | succ j => rw [hstep j]; exact based_cons v z _
  have key : ∀ j : ℕ, M⟦j⟧ ∈ W (2 * v + z) := by
    intro j
    induction j with
    | zero => rw [hM0]; exact W_nil _
    | succ j ih =>
        have hmem : Lift1 (M⟦j⟧) d1 ∈ W (2 * v + z + 2 * d1) := hWL _ _ _ ih
        have hmem' : Lift1 (M⟦j⟧) d1 ∈ W m := W_mono hbound hmem
        have hb : based (Lift1 (M⟦j⟧) d1) := based_Lift1 _ (hbased j)
        rw [hstep j]
        exact hgr _ hmem' hb (argOK_graft hRne hR _) v z (2 * v + z) hz1
          (le_refl _)
  exact W_mono hva (key n)

end TRIO
