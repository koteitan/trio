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

/-- A single summand is at most a sum ending with it, when the earlier summands are at least it. -/
theorem le_app_of_ge {s y : T} : ∀ (B : T), (∀ q ∈ summands B, psi s y z ≤ q) → psi s y z ≤ app B (psi s y z)
  | z, _ => by simp
  | psi a b c, h => by
    have hh := h (psi a b z) (by simp [summands])
    rcases (le_iff _ _).mp hh with hlt | heq
    · left
      rw [psi_lt_psi_z_iff] at hlt
      show psi s y z < psi a b (app c (psi s y z))
      rw [T.psi_lt_psi]
      rcases hlt with h1 | ⟨rfl, h1⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨rfl, h1⟩)
    · simp only [psi.injEq] at heq
      obtain ⟨rfl, rfl, -⟩ := heq
      exact psi_le_psi_rest (z_le _)

/-- **The `o` frame with a weak last child**: the new child is `ψ_{w′}(0)` (no rewrite), the relation
of the old side to the state without the child (`hdrop`) is a hypothesis. -/
theorem o_frame_weak {a w' w F : T} {L : List T}
    (hs' : ∀ t ∈ L ++ [psi w' z z], Single t) (hp' : (L ++ [psi w' z z]).Pairwise (fun a b => b ≤ a))
    (hW : WkV w' w) (hdrop : LhdE (psi a (spArg a z (sumN L)) z) (psi a F z))
    (hlt : app (spArg a z (sumN L)) (psi w' z z) < F) :
    LhdE (psi a (spArg a z (sumN (L ++ [psi w' z z]))) z) (psi a F z) := by
  set B := spArg a z (sumN L) with hB
  have hc : Single (psi w' z z) := hs' _ (by simp)
  have e2 : sumN (L ++ [psi w' z z]) = app (sumN L) (psi w' z z) := by
    rw [sumN_append_dec hs' hp']
    congr 1
    show sf (add z (psi w' z z)) = psi w' z z
    rw [add_z_left]; exact sf_ot hc.1
  have hL := sumN_dec L (fun t ht => hs' t (List.mem_append_left _ ht)) (List.pairwise_append.mp hp').1
  have hBge : ∀ q ∈ summands B, psi w' z z ≤ q := by
    apply spArg_summands_ge ⟨w', z, rfl⟩ (sumN L) z hL.1
    · rw [hL.2]; intro q hq
      exact (List.pairwise_append.mp hp').2.2 q hq _ (by simp)
    · simp [summands]
  have estep : spArg a z (sumN (L ++ [psi w' z z])) = app B (psi w' z z) := by
    rw [e2, spArg_app, spArg_single, step_leaf, ← hB]
    exact add_eq_app_of_ge ⟨w', z, rfl⟩ B hBge
  have hBlt : B < app B (psi w' z z) := by
    have := app_lt_app_left B (show z < psi w' z z from T.z_lt_psi _ _ _)
    rwa [app_z_right] at this
  rw [estep]
  right
  rcases hdrop with he | hl
  · exfalso
    simp only [psi.injEq] at he
    have := lt_trans hBlt hlt
    rw [he.2.1] at this; exact lt_irrefl' _ this
  · exact lhd_weak_child hl (by simp)
      (fun u g hg => le_trans (self_small_weak hW.2.1 hW.2.2.1 u g hg) (le_app_of_ge B hBge)) hlt

/-! ## 評価器の段の o の枠 (1): v が変わる列 -/

theorem sumN_all_z : ∀ (l : List T), (∀ t ∈ l, t = z) → sumN l = z := by
  intro l h
  unfold sumN
  suffices ∀ acc, acc = z → l.foldl (fun a b => sf (add a b)) acc = z by exact this z rfl
  induction l with
  | nil => intro acc h0; simpa using h0
  | cons t l ih =>
    intro acc h0
    simp only [List.foldl_cons]
    apply ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
    rw [h0, h t List.mem_cons_self]; rfl

/-- **A column with no counted child**: `o = ψ_v(0)`. -/
theorem o_of_no_counted {M : Mat} {ρ : Valn} {i : Nat} (hC : Cons M ρ) (hi : i < M.length)
    (hv : isOT (ρ.v i) = true) (hn : ∀ c ∈ children M i, ¬ Counted M i c) : ρ.o i = psi (ρ.v i) z z := by
  classical
  rw [(hC i hi).1]
  unfold oRhs
  rw [sumN_all_z _ (fun t ht => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    rw [cnt_eq_ite, if_neg (hn c hc)])]
  rw [sf_psi_spArg hv rfl]
  rfl

/-- **The `o` frame where `v` changes**: no counted child in `M.take x`, so `o′ = ψ_{v′}(0)`. -/
theorem o_frame_vchg {M : Mat} {x : Nat} {ρ ρ' : Valn} {i : Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hC' : Cons (M.take x) ρ') (hix : i < (M.take x).length) (hiM : i < M.length)
    (hv' : isOT (ρ'.v i) = true) (hT : ∀ c ∈ children (M.take x) i, ¬ Counted (M.take x) i c)
    (hrel : DRelV (ρ'.v i) (ρ.v i)) : DRelO (ρ'.o i) (ρ.o i) := by
  rw [o_of_no_counted hC' hix hv' hT, o_spArg hC hG hiM]
  exact drelO_of_v hrel

end Ytosk
