/-
The t=1 branch of the repaired induction, using the existing DQ and bad-closure engines.
The input records name their separate residual fields; grouping is not a reduction
in the number of open mathematical obligations. The old top is not modified.
-/
import Ytosk.V3QRCarrierV3
import Ytosk.V3QNCarrierV3

namespace Ytosk.V3Main
open T WfExQ1 WfExQ2 WfExQ10 WfQnE3 WfBad

/-- The three still-open q=r inputs. -/
structure QrInputsV3 (M : Mat) (ρ : Valn) (r L d0 : Nat) : Prop where
  ua : UAwRA M ρ (r + L)
  loc : QrLocV3 M ρ r L d0
  vsf : VSFResQ M r L d0 ρ

/-- The seven still-open q!=r inputs of WfQnA18, with PnV3 as the carried property. -/
structure QnInputsV3 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L d0 : Nat) (br : T) : Prop where
  inn : ∀ m, WfQnH3.TPLoSXIn M ρ r (ρ.v r) (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) m)
  vlt : ∀ m i, BadSet M (r + L) ρ r (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) m) i → vOpt ρ (par M 1 i) < ρ.o r
  before : ∀ m i, BadSet M (r + L) ρ r (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) m) i → i < r
  kids : ∀ m i, BadSet M (r + L) ρ r (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) m) i → ∀ j ∈ children M i,
      col M j = bump M i → ∀ k ∈ children M j, DepX M (r + L) true k → r ≤ k
  window : ∀ m i, BadSet M (r + L) ρ r (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) m) i →
      ∀ q ∈ summands (vOpt ρ (par M 1 i)), ¬ q < fsD (ρ.o r) (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) m) → q < ρ.o r →
        Lhd z q (ρ.o r)
  rest : WfQnA15.ResT1Bv M r L d0 ρ (ρ.v r) br ((drop1 M (r + L) rk).o r)
      (fun n => BadSet M (r + L) ρ r (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) (n - 2)))
  step : WfQnA8.StepT1B PnV3 M r L d0 ρ (ρ.v r) br ((drop1 M (r + L) rk).o r)
      (fun n => BadSet M (r + L) ρ r (gamS (ρ.v r) br ((drop1 M (r + L) rk).o r) (n - 2)))

/-- q=r local inputs at every actual t=1 frame of the new context. -/
def HQRInputsV3 : Prop :=
  ∀ M ρ rk, StepCtx3 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 1 (r + L) = some r → entry M 2 (r + L) = 0 → par M 0 (r + L) = some r →
      QrInputsV3 M ρ r L (entry M 0 (r + L) - entry M 0 r)

/-- q!=r local inputs at every actual t=1 frame of the new context. -/
def HQNInputsV3 : Prop :=
  ∀ M ρ rk, StepCtx3 M ρ rk → ∀ r L, r + L + 1 = M.length → 0 < L →
    par M 1 (r + L) = some r → entry M 2 (r + L) = 0 → par M 0 (r + L) ≠ some r →
      ∀ br, ρ.o r = psi (ρ.v r) br z →
        QnInputsV3 M ρ rk r L (entry M 0 (r + L) - entry M 0 r) br

/-- The actual repaired t=1 engines, with their local residuals still explicit. -/
theorem expOut1_of_inputs (hF : HFrameV3) (hQR : HQRInputsV3) (hQN : HQNInputsV3) : ExpOutV3 1 := by
  intro M ρ rk C hz hs n hn
  obtain ⟨r, hr⟩ := parLast_of C.S.e00 C.S.r01 C.S.r12 hz
  rw [hs] at hr
  have hrx := par_lt M 1 (M.length - 1) r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  have hx2 : entry M 2 (r + L) = 0 := by
    unfold TRIO.srow at hs
    split_ifs at hs with he2 he1
    · cases hs
    · show entry M 2 (r + L) = 0
      have : ¬ 0 < entry M 2 (M.length - 1) := he2
      rw [hL] at this; omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp := expand_eq_gexp_t1 M n (by omega) hzT (by rw [hs]; exact hr) hs
  rw [hL] at hexp hr
  simp only [Nat.add_sub_cancel_left] at hexp
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  rw [hexp]
  by_cases hq : par M 0 (r + L) = some r
  · have F := hQR M ρ rk C r L hlen hL0 hr hx2 hq
    exact qr_carrierV3 hF C hlen hL0 hd0e hr hx2 hq F.ua F.loc F.vsf n hn
  · obtain ⟨br, hro⟩ := o_psi_sub C.I.cons (show r < M.length from by omega)
    rw [sf_ot (C.I.good.ot_v r (by omega))] at hro
    have F := hQN M ρ rk C r L hlen hL0 hr hx2 hq br hro
    exact qn_carrierV3 C hlen hL0 hd0e hr hx2 hq hro F.inn F.vlt F.before F.kids F.window F.rest F.step n hn

end Ytosk.V3Main
