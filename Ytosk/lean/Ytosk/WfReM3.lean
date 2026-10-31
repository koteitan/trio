/-
**The `ua` field of `HDropU` is false (2026-10-31, WfReM).** N (35 columns, standard: 487-step `Std.exp` trace
from SRO; from the graft family graftM36 of WfReM), not Bad2 (Python). x = 34 = (8,5,1), i = x − 1 = 33 = (7,4,0)
upgrades to k = 30 = (6,4,1) = P₀ i. V = v(P₁ i) = v(29) = r₀ + 1 with r₀ = ψ_{ψ(1)}(ψ_{ψ_{ψ(2)}(0)}(0)),
v(k) = ψ_{r₀}(0) = V + W with W = v(k) (V is absorbed). Both disjuncts of `DropResHB.ua` fail:
- r₀ < W but not r₀ ◁ W: c = ψ_{ψ(1)+1}(0) has r₀ < c ≤ W and the u = 0 component ψ_{ψ_{ψ(2)}(0)}(0) of r₀ is above
  every u = 0 component of c;
- the component ψ_{ψ_{ψ(2)}(0)}(0) of V + 1 is not below ψ_{V+1}(0).
- `ua_core_false`: the `ua` clause for standard matrices with `Cons` only is false (axioms propext / Quot.sound).
- `not_HDropU_of_inv`: `HDropU` is false if N has an `Inv3V2` valuation (Python: all fields hold on N and its prefixes).
- `not_HDropU_of`: the hypotheses of `hInvV2_all` are inconsistent (independently of `WfReM1`).
-/
import Ytosk.V3MainV2

namespace Ytosk.WfReM3
open T
set_option maxRecDepth 200000
set_option maxHeartbeats 80000000

def N : Mat := [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 1), (4, 2, 1), (5, 1, 0), (6, 2, 1), (7, 2, 1), (8, 2, 0), (6, 2, 1), (7, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (7, 2, 0), (6, 3, 0), (7, 4, 1), (8, 4, 1), (9, 2, 0), (7, 2, 0), (5, 3, 0), (6, 4, 1), (7, 4, 1), (8, 2, 0), (7, 4, 0), (8, 5, 1)]
def trace : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1]
def ρO : List T := [(psi z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) (psi z z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi z (psi z z z) z)) z z) z))) z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z z) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) (psi z z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi z (psi z z z) z)) z z) z))) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) (psi z z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi z (psi z z z) z)) z z) z))) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) (psi z z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi z (psi z z z) z)) z z) z))) z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z), (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi z (psi z z (psi z z z)) z) z z) z), (psi (psi z (psi z z (psi z z z)) z) z z), (psi (psi z (psi z z (psi z z z)) z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) (psi z z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi z (psi z z z) z)) z z) z))) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z)) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)) z z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) (psi z z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi z (psi z z z) z)) z z) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi z (psi z z z) z)) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi z (psi z z z) z)) z z) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi z (psi z z z) z)) z z)]
def ρV : List T := [z, (psi (psi (psi z (psi z z z) z) z z) z z), (psi z (psi z z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) z z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi z (psi z z z) z), (psi (psi z (psi z z (psi z z z)) z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi z (psi z z (psi z z z)) z), (psi z (psi z z (psi z z z)) z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z)), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) (psi z z z)), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z) z (psi z (psi z z z) z))]
def r0 : T := (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z (psi z z z)) z) z z) z z) z)

def ρ : Valn := ⟨fun i => ρO.getD i z, fun i => ρV.getD i z⟩

/-- The witness `c = ψ_{ψ(1)+1}(0)`. -/
def cw : T := psi (psi z one one) z z

private theorem std_fold : ∀ (ns : List Nat) (N : Mat), Std N → Std (ns.foldl expand N)
  | [], _, h => h
  | n :: ns, N, h => std_fold ns (expand N n) (Std.exp n h)

theorem standard : Std N := by
  have h : trace.foldl expand SRO = N := by decide
  rw [← h]
  exact std_fold trace SRO Std.sro

theorem ne_sro : N ≠ SRO := by decide

theorem cons : Cons N ρ := by unfold Cons; decide

theorem r0_mem : r0 ∈ summands (ρ.v 29) := by decide

theorem r0_lt : r0 < ρ.v 30 := by decide

theorem r0_not_lhd : ¬ Lhd z r0 (ρ.v 30) := by
  intro h
  have hd := h.2 z cw (by decide) (by decide)
  have hno : ¬ ∀ g ∈ comps z r0, ∃ y ∈ comps z cw ++ Gc z z, g ≤ y := by decide
  exact hno hd

theorem comp_bad : ¬ ∀ g ∈ comps z (add (ρ.v 29) one), g < psi (add (ρ.v 29) one) z z := by decide

/-- The `ua` clause at N fails for every valuation agreeing with `ρ` at 29 and 30. -/
theorem not_ua (ρ' : Valn) (h29 : ρ'.v 29 = ρ.v 29) (h30 : ρ'.v 30 = ρ.v 30) :
    ¬ (∀ i k W, i + 1 = 34 → upg N i = some k → ρ'.v k = add (vOpt ρ' (par N 1 i)) W → W ≠ z →
      (∀ r ∈ summands (vOpt ρ' (par N 1 i)), r < W → Lhd z r W) ∨
        (WCSP N ρ' i (add (vOpt ρ' (par N 1 i)) one) ∧
          (∀ g ∈ comps z (add (vOpt ρ' (par N 1 i)) one), g < psi (add (vOpt ρ' (par N 1 i)) one) z z))) := by
  intro h
  have hp : par N 1 33 = some 29 := by decide
  have hk : upg N 33 = some 30 := by decide
  have hadd : ρ.v 30 = add (ρ.v 29) (ρ.v 30) := by decide
  have hW : ρ.v 30 ≠ z := by decide
  have h1 := h 33 30 (ρ'.v 30) rfl hk (by rw [hp]; simp only [vOpt]; rw [h29, h30]; exact hadd) (by rw [h30]; exact hW)
  rw [hp] at h1
  simp only [vOpt] at h1
  rw [h29, h30] at h1
  rcases h1 with h1 | h1
  · exact r0_not_lhd (h1 r0 r0_mem r0_lt)
  · exact comp_bad h1.2

/-- **The `ua` clause of `DropResHB` for standard matrices with only `Cons` is false.** -/
theorem ua_core_false :
    ¬ (∀ M ρ, Std M → M ≠ SRO → Cons M ρ →
      ∀ i k W, i + 1 = M.length - 1 → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
        (∀ r ∈ summands (vOpt ρ (par M 1 i)), r < W → Lhd z r W) ∨
          (WCSP M ρ i (add (vOpt ρ (par M 1 i)) one) ∧
            (∀ g ∈ comps z (add (vOpt ρ (par M 1 i)) one), g < psi (add (vOpt ρ (par M 1 i)) one) z z))) := by
  intro h
  exact not_ua ρ rfl rfl (h N ρ standard ne_sro cons)

/-- **`HDropU` is false as soon as N has an `Inv3V2` valuation.** -/
theorem not_HDropU_of_inv (hI : ∃ ρ' rk, Inv3V2 N ρ' rk) : ¬ HDropU := by
  intro hU
  obtain ⟨ρ', rk, I⟩ := hI
  have hu := cons_unique I.cons cons I.rank
  exact not_ua ρ' (hu 29 (by decide)).2 (hu 30 (by decide)).2 (hU N ρ' rk standard ne_sro (by decide) I).1.ua

/-- **The hypotheses of `hInvV2_all` are inconsistent** (via `ua`). -/
theorem not_HDropU_of (hU : HDropU) (hD : HDropV2) (hT : HTakeV2) (hTB : TakeBadV2) (hBO : BadOutV2)
    (h0 : ExpT0OutV2) (h1 : ExpT1OutV2) (h2 : ExpT2V2) (hCB : T2CBadOut) : False :=
  not_HDropU_of_inv (hInvV2_all hU hD hT hTB hBO h0 h1 h2 hCB N standard ne_sro (by decide)) hU

#print axioms ua_core_false
#print axioms not_HDropU_of

end Ytosk.WfReM3
