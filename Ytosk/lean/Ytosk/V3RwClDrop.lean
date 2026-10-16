/-
**RwClosed は基底 SRO[n] と 1 列落とし M → M.take x で成り立つ（2026-10-17、t0）。**

closure の `G.base_ph3c`・`G.ph3c_take`（V3PBaseG・V3PDropG）と同じ形:
- 基底の枠は書き換えない（no_trig）。
- M.take x の枠は v(i) と前の数える子の値（状態 B）が M と同じで、書き換える新しい子は添字が同じで引数が
  下がる（rewrite_take・new_arg_le）。hi は単調なので、B < hi(y′) ≤ hi(y) で M の RwClosed が使える。
-/
import Ytosk.V3RwClT0
import Ytosk.V3PBaseG
import Ytosk.V3PDropG

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem base_rwClosed {L : Nat} {β : T} (hF : BaseFit L β) : RwClosed (Mlen L) (bval L β) := by
  intro i hi L' c R h s y ho htr
  obtain ⟨_, hc, _⟩ := CL_split hF h
  exact absurd (no_trig hF (by simpa using hi) hc ho htr.1 htr.2) id

section
variable {M : Mat} {x : Nat} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ' : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take x) ρ') (hRk' : Rk (M.take x) rk)
  (hdrop : ∀ i, i < x → PO ρ ρ' i ∧ PV M ρ ρ' i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop

/-- **RwClosed passes to `M.take x`.** -/
theorem rwClosed_take (hP : RwClosed M ρ) : RwClosed (M.take x) ρ' := by
  intro i hi L c R h s' y' hc' ht' hB hnp
  rw [lenT hx] at hi
  have hiM : i < M.length := by omega
  obtain ⟨hv, hL, Tl, hM⟩ := frame_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hi h
  have hst : spArg (ρ'.v i) z (sumN (L.map ρ'.o)) = spArg (ρ.v i) z (sumN (L.map ρ.o)) := by
    rw [hv, hL]
  rw [hst] at hB ht' hnp ⊢
  rw [hv] at ht' ⊢
  obtain ⟨hsM, _⟩ := cl_vals hC hG hiM
  rw [hM] at hsM
  obtain ⟨s, y, hsy⟩ := (hsM (ρ.o c) (by simp)).2
  have hcT : c ∈ CL (M.take x) i := by rw [h]; simp
  have hcx : c < x := by have := (mem_children (cl_mem_children hcT)).2; rw [lenT hx] at this; exact this
  have ht := rewrite_take hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hi h hc' ht' hsy
  obtain ⟨rfl, hyy⟩ := G.new_arg_le hx hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC' hRk' hdrop hcx hc' hsy
    (ne_z_of_lt ht'.1)
  exact hP i hiM L c (R ++ Tl) hM s' y hsy ht (lt_of_lt_of_le hB (hi_le_of_le hyy))
    (notpre_back hB (hi_le_of_le hyy) hnp)

end

end Ytosk
