/-
**WfT2R1: the `VRA` consumers of `T2BelowXResAt` with `T2BelowXResAtX` (2026-11-01, t = 2 Bad2 route).**

Copies (suffix `XR`) of `t2VRAPre_of` (V3T2VRAPre), `t2VRASeed_of`・`t2VRASeedG_of` (V3T2VRASeed), the seed
lemmas of V3T2VRASV and `vsmallRAll_expand_t2`・`t2VRAV2_of` (V3T2VRA), with `t2BelowXS_of` replaced by
`WfT2X.t2BelowXS_ofX` (frame shape `FrameShapeX`) and the frame-shape readers replaced by their X versions
(WfT2X5・WfT2X6・WfT2X7). `pathLv_of_shapeXR`: `pathLv_of_shape` with `FrameShapeX`.
-/
import Ytosk.WfT2X8
import Ytosk.V3T2VRASV
import Ytosk.V3T2VRA
import Ytosk.V3T2VRAPre
import Ytosk.V3T2VRASeed

namespace Ytosk

open T Classical

/-- **`pathLv_of_shape` (V3T2VRASeed) with `FrameShapeX`.** -/
theorem pathLv_of_shapeXR {M N : Mat} {ρ σ : Valn} (hC : Cons M ρ) (hCN : Cons N σ) {c : Nat}
    (hS : ∀ k, par N 0 c = some k → WfAbsW.FrameShapeX M N ρ σ k)
    (hup : ∀ k u, par N 0 c = some k → PathLvAll N σ k u → PathLvAll M ρ k u) :
    ∀ u, PathLvAll N σ c u → PathLvAll M ρ c u := by
  intro u h
  have hpar : ∀ {k : Nat} {Lc R : List Nat}, CL N k = Lc ++ c :: R → par N 0 c = some k := by
    intro k Lc R hcl
    exact (mem_children_iff.mp (cl_mem_children (show c ∈ CL N k by rw [hcl]; simp))).2
  cases h with
  | top hcl hsy ht =>
    obtain ⟨y', hclM, hv, hLc, hy', ht'⟩ := WfT2X.rw_frame_of_shapeX hC hCN (hS _ (hpar hcl)) hcl hsy ht
    rw [← hv]
    exact PathLvAll.top hclM hy' ht'
  | step hcl hsy ht hk =>
    obtain ⟨y', hclM, hv, hLc, hy', ht'⟩ := WfT2X.rw_frame_of_shapeX hC hCN (hS _ (hpar hcl)) hcl hsy ht
    exact PathLvAll.step hclM hy' ht' (hup _ u (hpar hcl) hk)

end Ytosk
