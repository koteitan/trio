/-
**落とす補題の関係: ◁ と弱い関係。**

崩れの節点の値 w′ は、成分がすべて Ω_1 より下（`CS`）で 1 以上。
- v の関係 `DRelV`: w′ ⊴ w か、弱い関係 `WkV`（w′ < w、`CS w′`、1 ≤ w′）。
- o の関係 `DRelO`: ⊴ か、ψ_{w′}(0) と ψ_w(X) で `WkV w′ w`。
弱い子 ψ_{w′}(0) は自分の成分を自分で押さえる（`self_small_weak`）ので、親で ⊴ に戻る（`lhd_weak_child`）。
-/
import Ytosk.V3DropAsm

namespace Ytosk

open T

/-- All components are countable. -/
def CS (t : T) : Prop := ∀ g ∈ comps z t, g < Om one

/-- The weak relation of subscripts. -/
def WkV (w' w : T) : Prop := w' < w ∧ CS w' ∧ one ≤ w' ∧ isOT w' = true

def DRelV (w' w : T) : Prop := LhdE w' w ∨ WkV w' w

def WkO (t' t : T) : Prop := ∃ w' w X, t' = psi w' z z ∧ t = psi w X z ∧ WkV w' w

def DRelO (t' t : T) : Prop := LhdE t' t ∨ WkO t' t

/-- Components at a level are among the components at level `0`. -/
theorem comps_sub_z (u : T) : ∀ t, ∀ g ∈ comps u t, g ∈ comps z t
  | z, g, hg => by simp [comps] at hg
  | psi v b c, g, hg => by
    simp only [comps, List.mem_append] at hg ⊢
    rcases hg with hg | hg
    · left
      split at hg
      · simp at hg
      · rw [if_neg (by simp [lt])]
        simp only [List.mem_cons, List.mem_append] at hg ⊢
        rcases hg with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (comps_sub_z u b g h))
        · exact Or.inr (Or.inr (comps_sub_z u v g h))
    · exact Or.inr (comps_sub_z u c g hg)

theorem Om_one_le_psi {w : T} (hw : one ≤ w) : Om one ≤ psi w z z := by
  unfold Om
  rcases (le_iff _ _).mp hw with h | h
  · left
    show psi one z z < psi w z z
    rw [psi_lt_psi_z_iff]; exact Or.inl h
  · right; rw [h]

/-- **A weak child dominates its own components.** -/
theorem self_small_weak {w' : T} (hcs : CS w') (h1 : one ≤ w') :
    ∀ u, ∀ g ∈ comps u (psi w' z z), g ≤ psi w' z z := by
  intro u g hg
  have hg0 := comps_sub_z u _ g hg
  simp only [comps, List.mem_append] at hg0
  rw [if_neg (by simp [lt])] at hg0
  simp only [List.mem_cons, List.mem_append] at hg0
  rcases hg0 with (rfl | h | h) | h
  · exact z_le _
  · simp at h
  · exact le_of_lt (lt_of_lt_of_le (hcs g h) (Om_one_le_psi h1))
  · simp at h

/-- **`o` from `v`**: `ψ_{v′}(0)` against `ψ_v(X)`. -/
theorem drelO_of_v {v' v X : T} (h : DRelV v' v) : DRelO (psi v' z z) (psi v X z) := by
  rcases h with h | h
  · exact Or.inl (lhdE_oq_v h)
  · exact Or.inr ⟨v', v, X, rfl, rfl, h⟩

end Ytosk
