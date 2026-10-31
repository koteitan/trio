/-
**`WfT2Src.T2AbsNSrcW` from the three narrowed parts (2026-10-31).**

- (a): `WfSrcA.SrcARem2` (via `WfSrcA.not_dropFail_of_case_a`) gives `WfSrcB.SrcA`.
- (b): `WfSrcB.SrcBNonlost2`.
- (c): `WfSrcC.SrcCRes` (with `WfSrcC.o_psi_form` and `WfSrcC.lt_bnd_of_lt_psi`) gives `WfSrcB.SrcC`.
-/
import Ytosk.WfSrcA
import Ytosk.WfSrcB2
import Ytosk.WfSrcC1

namespace Ytosk.WfSrcABC

open T

set_option linter.unusedSectionVars false

/-- Part (a) in the form of `WfSrcB.SrcA`. -/
theorem srcA_of_rem2 (h : WfSrcA.SrcARem2) : WfSrcB.SrcA := by
  intro M ρ rk C hB2 hz hs r L hlen hr τ hτ i hi h1 h2 ha _
  exact WfSrcA.not_dropFail_of_case_a (WfSrcA.srcARem_of_rem2 h) C hB2 hz hs hlen hr ha hi h1 h2 hτ

/-- Part (c) in the form of `WfSrcB.SrcC`. -/
theorem srcC_of_res (h : WfSrcC.SrcCRes) : WfSrcB.SrcC := by
  intro M ρ rk C hB2 hz hs r hlen hr _ _ τ hτ p i hp hpi h1 h2 hfail hfacts s hsm hs2 hlt hnl
  have hpr := par_lt M 0 r p hp
  have hip := par_lt M 0 p i hpi
  obtain ⟨hso, harg⟩ := h M ρ rk C hB2 hz hs r hlen hr τ hτ i (by omega) h1 h2 hfail hfacts p hp hpi
    s hsm hs2 hlt hnl
  have hrM : r < M.length := by omega
  obtain ⟨Y, hY⟩ := WfSrcC.o_psi_form C.I.cons hrM (C.I.good.ot_v r hrM)
  exact WfSrcC.lt_bnd_of_lt_psi (mem_summands hsm) (hY ▸ hso) harg

/-- **Bridge**: `T2AbsNSrcW` from (a) `SrcARem2`, (b) `SrcBNonlost2`, (c) `SrcCRes`. -/
theorem t2AbsNSrcW_of (hA : WfSrcA.SrcARem2) (hB : WfSrcB.SrcBNonlost2) (hC : WfSrcC.SrcCRes) :
    WfT2Src.T2AbsNSrcW :=
  WfSrcB.t2AbsNSrcW_of (srcA_of_rem2 hA) (WfSrcB.srcBNonlost_of_2 hB) (srcC_of_res hC)

end Ytosk.WfSrcABC
