/-
**The invariant field `AbsDN` is false on a standard matrix (2026-10-31, WfReM).** N (38 columns, standard:
150-step `Std.exp` trace from SRO; an expansion prefix in the WfReM family graftM36x):
…(12,0,0)(13,1,1)(14,1,1)(10,2,0)(11,3,1)(12,3,1)(13,1,0)(14,0,0)(15,1,1)(16,1,1)(17,1,0).
At i = 31 = (11,3,1): W = bumpW(31) = ψ_{ψ(1)}(ψ_{ψ(1)}(ψ_{ψ(1)}(ψ(Ω_{Ω_1})))) has a hole, cof W = ω, W is not a node,
and the summand q₀ = ψ_{ψ(1)}(ψ_{ψ(1)}(ψ_{ψ(1)}(ψ(Ω_{ψ(2)})))) of v(P₁ 31) = v(30) has q₀ < W but not q₀ < W[1].
So no valuation of N satisfies `Inv3V2` (field `adn`) nor `TakeFrameV2` (field `adn`):
- `not_absDN`: `¬ AbsDN N ρ` (ρ = the valuation of `Cons`).
- `no_inv3V2`: `¬ ∃ ρ' rk, Inv3V2 N ρ' rk`.
- `not_HFrameV2`: `HFrameV2` is false (its premises Std, Cons, Rk, Good3 hold at N).
- `not_hInvV2_all_hyps`: the hypotheses of `hInvV2_all` are inconsistent.
-/
import Ytosk.V3MainV2
import Ytosk.V3GlobV2
import Ytosk.V3Total

namespace Ytosk.WfReM4
open T
set_option maxRecDepth 200000
set_option maxHeartbeats 80000000

def N : Mat := [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 1), (4, 2, 1), (5, 1, 0), (6, 2, 1), (7, 2, 1), (8, 2, 0), (6, 2, 1), (7, 2, 1), (8, 1, 0), (9, 2, 1), (10, 2, 1), (11, 2, 0), (9, 2, 1), (10, 2, 1), (11, 1, 0), (12, 0, 0), (13, 1, 1), (14, 1, 1), (10, 2, 0), (11, 3, 1), (12, 3, 1), (13, 1, 0), (14, 0, 0), (15, 1, 1), (16, 1, 1), (17, 1, 0)]
def trace : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def ρO : List T := [(psi z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z) z) z z) z z) z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z z) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z) z) z z) z z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z) z) z z) z z) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z) z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z) z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z) z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z), (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z), (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z), (psi (psi z (psi z z (psi z z z)) z) z z), (psi (psi z (psi z z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z), (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z), (psi z (psi (psi (psi z z z) z z) z z) z), (psi (psi (psi z z z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi z z z) z z) z), (psi (psi z z z) z z)]
def ρV : List T := [z, (psi (psi (psi z (psi z z z) z) z z) z z), (psi z (psi z z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) z z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z) z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z) z z) z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi z (psi z z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z) z z) z)) z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi z (psi z z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi z (psi z z z) z), z, (psi z (psi z z (psi z z z)) z), (psi z (psi z z z) z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) (psi z (psi z z z) z)), (psi z (psi z z z) z), z, (psi (psi z z z) z z), (psi z (psi z z z) z), (psi z z z)]
def Wl : T := (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi (psi z z z) z z) z z) z) z) z) z)
def q0 : T := (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z (psi z z z)) z) z z) z) z) z) z)

def ρ : Valn := ⟨fun i => ρO.getD i z, fun i => ρV.getD i z⟩

private theorem std_fold : ∀ (ns : List Nat) (N : Mat), Std N → Std (ns.foldl expand N)
  | [], _, h => h
  | n :: ns, N, h => std_fold ns (expand N n) (Std.exp n h)

theorem standard : Std N := by
  have h : trace.foldl expand SRO = N := by decide
  rw [← h]
  exact std_fold trace SRO Std.sro

theorem ne_sro : N ≠ SRO := by decide

theorem cons : Cons N ρ := by unfold Cons; decide

theorem good : Good3 N ρ := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · unfold cvals nzs
    decide

theorem hW : bumpW N ρ 31 = Wl := by decide

theorem ohole_gen (a b : T) (hb : b ≠ z) (hs : isSucc b = false) (h : (∃ μ, cof b = .big μ) ∨ OHole b) :
    OHole (psi a b z) := by
  rcases h with ⟨μ, hμ⟩ | h
  · simp [OHole, hb, hs, hμ]
  · cases hcb : cof b <;> simp_all [OHole]

theorem ohole_a (a : T) (ha : a ≠ z) (h : isSucc a = true ∨ OHole a) : OHole (psi a z z) := by
  simp [OHole, ha]; exact h

theorem cof_ne {b : T} (h : cof b = .omega) : ∀ μ, cof b ≠ .big μ := by
  intro μ hc; rw [h] at hc; cases hc

private def A1 : T := psi z (psi z z z) z
private def B4 : T := psi (psi (psi z z z) z z) z z
private def B3 : T := psi z B4 z
private def B2 : T := psi A1 B3 z
private def B1 : T := psi A1 B2 z

theorem wl_eq : Wl = psi A1 B1 z := by decide

theorem hole : OHole Wl := by
  have h4 : OHole B4 := ohole_a _ (by decide) (Or.inr (ohole_a _ (by decide) (Or.inl (by decide))))
  have step : ∀ a b, b ≠ z → isSucc b = false → ((∃ μ, cof b = .big μ) ∨ OHole b) → OHole (psi a b z) :=
    fun a b hb hs h => ohole_gen a b hb hs h
  have h3 : OHole B3 := step _ _ (by decide) (by decide) (Or.inr h4)
  have h2 : OHole B2 := step _ _ (by decide) (by decide) (Or.inr h3)
  have h1 : OHole B1 := step _ _ (by decide) (by decide) (Or.inr h2)
  rw [wl_eq]
  exact step _ _ (by decide) (by decide) (Or.inr h1)

theorem cofW : cof Wl = .omega := by decide

theorem notNode : NotNode Wl := by
  intro a b h μ
  rw [wl_eq] at h
  injection h with h1 h2 h3
  have hc : cof b = .omega := by rw [← h2]; decide
  rw [hc]; intro h'; cases h'

theorem q0_mem : q0 ∈ summands (vOpt ρ (par N 1 31)) := by decide

theorem q0_lt : q0 < Wl := by decide

theorem q0_not : ¬ q0 < fsD Wl one := by decide

theorem absDN_fails (ρ' : Valn) (h30 : ρ'.v 30 = ρ.v 30) (hW' : bumpW N ρ' 31 = Wl) : ¬ AbsDN N ρ' := by
  intro h
  have hp : par N 1 31 = some 30 := by decide
  have h1 := h 31 (by decide) (by decide) (by decide) (hW' ▸ hole) (hW' ▸ cofW) (hW' ▸ notNode) q0
    (by rw [hp]; simp only [vOpt]; rw [h30]; have := q0_mem; rw [hp] at this; exact this) (hW' ▸ q0_lt)
  rw [hW'] at h1
  exact q0_not h1

theorem not_absDN : ¬ AbsDN N ρ := absDN_fails ρ rfl hW

/-- bumpW at 31 only reads `o` of columns of N. -/
theorem bumpW_congr (ρ' : Valn) (hu : ∀ i, i < N.length → ρ'.o i = ρ.o i ∧ ρ'.v i = ρ.v i) :
    bumpW N ρ' 31 = bumpW N ρ 31 := by
  unfold bumpW
  congr 2
  congr 1
  apply List.map_congr_left
  intro j hj
  unfold bumpTerm
  split
  · congr 2
    apply List.map_congr_left
    intro c hc
    exact (hu c (mem_children hc).2).1
  · rfl

/-- **No valuation of the standard matrix N has `Inv3V2`.** -/
theorem no_inv3V2 : ¬ ∃ ρ' rk, Inv3V2 N ρ' rk := by
  rintro ⟨ρ', rk, I⟩
  have hu := cons_unique I.cons cons I.rank
  exact absDN_fails ρ' (hu 30 (by decide)).2 ((bumpW_congr ρ' hu).trans hW) I.adn

/-- **`HFrameV2` is false.** -/
theorem not_HFrameV2 : ¬ HFrameV2 := by
  intro h
  obtain ⟨rk, hrk⟩ := rk_std standard ne_sro
  exact not_absDN (h N ρ rk standard ne_sro (by decide) cons hrk good).adn

/-- **The hypotheses of `hInvV2_all` are inconsistent** (its conclusion fails at N). -/
theorem not_hInvV2_all_hyps (hU : HDropU) (hD : HDropV2) (hT : HTakeV2) (hTB : TakeBadV2) (hBO : BadOutV2)
    (h0 : ExpT0OutV2) (h1 : ExpT1OutV2) (h2 : ExpT2V2) (hCB : T2CBadOut) : False :=
  no_inv3V2 (hInvV2_all hU hD hT hTB hBO h0 h1 h2 hCB N standard ne_sro (by decide))

#print axioms not_HFrameV2
#print axioms no_inv3V2
#print axioms not_hInvV2_all_hyps

end Ytosk.WfReM4
