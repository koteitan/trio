/-
**PH3c・FC3 は 1 列落とし M → M.take x で保たれる（closure、2026-10-11）。**

`frameClosed_take`（V3DropPres）と同じ形: M.take x の枠は v(i) と前の数える子の値が M と同じで（`frame_take`）、
書き換える新しい子は添字が同じで引数が下がる（`rewrite_take`・`new_rewrite_same_v`・PO）。引数が y から
y′ ≤ y に下がり B < y′ なので、PH3c の種類と FC3 の結論は V3PKind の挟み込みで保たれる。
仮定 `hdrop`（i < x で PO・PV）は落とす補題 `drop_all` の結論。
-/
import Ytosk.V3PKind
import Ytosk.V3DropPres
import Ytosk.V3StrictR

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop

/-- A counted child of `M.take x` with a nonzero new argument keeps its subscript, and the argument drops. -/
theorem new_arg_le {c : Nat} (hcx : c < x) {s' y' s y : T} (hc' : ρ'.o c = psi s' y' z)
    (hsy : ρ.o c = psi s y z) (hy' : y' ≠ z) : s' = s ∧ y' ≤ y := by
  have hvs := new_rewrite_same_v hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hcx hc' hy'
  obtain ⟨y0, hy0⟩ := o_psi_sub hC' (show c < (M.take x).length by rw [lenT hx]; exact hcx)
  rw [hc'] at hy0; simp only [psi.injEq] at hy0
  obtain ⟨y1, hy1⟩ := o_psi_sub hC (show c < M.length by omega)
  rw [hsy] at hy1; simp only [psi.injEq] at hy1
  have hss : s' = s := by rw [hy0.1, hy1.1, hvs]
  subst hss
  refine ⟨rfl, ?_⟩
  have hle : psi s' y' z ≤ psi s' y z := by
    rw [← hc', ← hsy]
    exact DRelOA.le ((hdrop c hcx).1.1.elim (fun h => Or.inl h) (fun h => Or.inr h.1))
  rcases (le_iff _ _).mp hle with h | h
  · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
    · exact absurd h (lt_irrefl' _)
    · exact le_of_lt h
  · simp only [psi.injEq] at h; rw [h.2.1]

/-- **PH3c passes to `M.take x`.** -/
theorem ph3c_take (hP : PH3c M ρ) : PH3c (M.take x) ρ' := by
  intro i hi L c R h s' y' hc' hB ht'
  rw [lenT hx] at hi
  have hiM : i < M.length := by omega
  obtain ⟨hv, hL, Tl, hM⟩ := frame_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi h
  have hst : stB ρ' i L = stB ρ i L := by unfold stB; rw [hv, hL]
  rw [hst] at hB ht' ⊢
  rw [hv] at ht'
  obtain ⟨hsM, _⟩ := cl_vals hC hG hiM
  rw [hM] at hsM
  obtain ⟨s, y, hsy⟩ := (hsM (ρ.o c) (by simp)).2
  have hcT : c ∈ CL (M.take x) i := by rw [h]; simp
  have hcx : c < x := by have := (mem_children (cl_mem_children hcT)).2; rw [lenT hx] at this; exact this
  have hK := hP i hiM L c (R ++ Tl) hM s y hsy hB
    (rewrite_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hi h hc' ht' hsy)
  obtain ⟨rfl, hyy⟩ := new_arg_le hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hcx hc' hsy
    (ne_z_of_lt ht'.1)
  exact ph3cKind_squeeze hK ht'.1 hyy

/-- **FC3 passes to `M.take x`.** -/
theorem fc3_take (hP : FC3 M ρ) : FC3 (M.take x) ρ' := by
  intro i hi c R h s' y' hc' hy' ht' hhi
  rw [lenT hx] at hi
  have hiM : i < M.length := by omega
  obtain ⟨hv, -, Tl, hM⟩ := frame_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi
    (L := []) (by simpa using h)
  rw [hv] at ht' ⊢
  obtain ⟨hsM, _⟩ := cl_vals hC hG hiM
  rw [hM] at hsM
  obtain ⟨s, y, hsy⟩ := (hsM (ρ.o c) (by simp)).2
  have hcT : c ∈ CL (M.take x) i := by rw [h]; simp
  have hcx : c < x := by have := (mem_children (cl_mem_children hcT)).2; rw [lenT hx] at this; exact this
  obtain ⟨rfl, hyy⟩ := new_arg_le hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hcx hc' hsy hy'
  exact fc3_squeeze (hP i hiM c (R ++ Tl) (by simpa using hM) s' y hsy) hyy ht' hhi

end

end Ytosk
