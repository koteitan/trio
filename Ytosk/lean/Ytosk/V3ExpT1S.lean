/-
**3 行・t = 1・q = r: 種が ψ_{v(r)}(1) より小さいときの種の形。**

種 = M.take x での o(r)。r + 1 < x なら種 ≥ ψ_{v(r)}(1)（qr_seed_big）。よって種が小さいのは L = 1（x = r + 1）のときだけで、
M.take x では r は最後の列なので子がなく上げもない。r の行 2 は 0（x は行 1 が r より大きい子なので Z1C）。
よって 種 = Ω_{v(P_1 r) + 1}（v(P_1 r) は M と M.take x で同じ、base_v_read）。
-/
import Ytosk.V3ExpT1W
import Ytosk.V3QRSmall
import Ytosk.V3BaseDrop

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The small seed is `Ω_{v(P_1 r)+1}`** (`t = 1`, `q = r`). -/
theorem seed_shape_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hq : par M 0 (r + L) = some r) (hμ : ρ.v r ≠ z)
    {ρ1 : Valn} (hC1 : Cons (M.take (r + L)) ρ1)
    (hlow : ¬ psi (ρ.v r) one z ≤ ρ1.o r) :
    L = 1 ∧ ρ1.o r = psi (succ (vOpt ρ (par M 1 r))) z z := by
  have hrx : r < r + L := par_lt M 1 _ r h1
  have hcntG := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcntG
  have hL1 : L = 1 := by
    by_contra hne
    exact hlow (qr_seed_big (x := r + L) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 I.cons I.good hC1 hRk1
      (by omega))
  subst hL1
  refine ⟨rfl, ?_⟩
  have hrM : r < M.length := by omega
  have hrT : r < (M.take (r + 1)).length := by rw [List.length_take]; omega
  have hch : children (M.take (r + 1)) r = [] := by
    rw [children_take, List.eq_nil_iff_forall_not_mem]
    intro c hc
    have h' := List.mem_filter.mp hc
    have hrc := (mem_children h'.1).1
    have := of_decide_eq_true h'.2
    omega
  have he1 : entry M 1 r ≠ 0 := fun h => hμ (v_z_of_e1L I.cons hrM h)
  have he2 : entry M 2 r = 0 := by
    have hz2 := I.z2 r
    by_contra hne
    have h21 : entry M 2 r = 1 := by omega
    have hxc : r + 1 ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
    have := I.z1 r (r + 1) h21 hxc
    have := par1_entry_lt h1
    omega
  have hvp : vOpt ρ1 (par M 1 r) = vOpt ρ (par M 1 r) := by
    cases hp : par M 1 r with
    | none => rfl
    | some g =>
      have hgr : g < r := par_lt M 1 r g hp
      have hpT : par (M.take (r + 1)) 1 (r + 0) = some g := by
        have := par_take M (k := r + 1) 1 r (by omega)
        simpa [this] using hp
      exact (base_v_read hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 (le_of_lt hgr)
        (by omega) (Or.inl hpT)).symm
  have hVot : isOT (vOpt ρ (par M 1 r)) = true := vOpt_ot I.good hrM
  have hv1 : ρ1.v r = succ (vOpt ρ (par M 1 r)) := by
    rw [(hC1 r hrT).2]
    unfold vRhs
    rw [entry_take M 1 (by omega), if_neg he1, entry_take M 2 (by omega), if_pos he2,
      upg_last_none (by rw [List.length_take]; omega), par_take M 1 r (by omega), hvp]
    show sf (add (vOpt ρ (par M 1 r)) one) = _
    rw [add_one_eq_succ hVot, sf_ot (isOT_succ hVot)]
  rw [(hC1 r hrT).1]
  unfold oRhs
  rw [hch, hv1]
  show sf (psi (succ (vOpt ρ (par M 1 r))) (sumN []) z) = _
  rw [sf_psi_spArg (isOT_succ hVot) rfl]
  rfl

end Ytosk
