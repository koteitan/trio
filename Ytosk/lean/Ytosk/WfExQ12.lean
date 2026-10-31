/-
**WfExQ12 (2026-11-01): the Inv3V2 field `AbsUWL` is false on a standard 39-column matrix (below SRO).**
Found by the WfExQ audit (tmp/wf/WfExQ/audit3.py) in graftE (tmp/wf/WfDrE/graftE.pkl; 5 matrices, 39-42 columns).
N = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)
    (7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(9,2,1)(10,2,1)(11,2,0)(9,2,1)(10,2,1)(11,1,0)(12,0,0)(13,1,1)(10,2,0)(11,3,1)
    (12,3,1)(13,1,0)(14,2,1)(12,3,0)(11,3,1)(12,3,1)(13,1,0)(14,2,0)   (Std: 340-step trace from SRO).
Last column x = 38: r = P_1 x = P_0 x = 37 (t = 1, q = r), o(r) = A = ψ_{ψ(1)}(Ω_{ψ(1)+1}).
At the v call i = 34 = (12,3,0) (D, upgrade to k = 35, d_i = 2): W = last v(35) = A itself, and the summand
q0 = ψ_{ψ(1)}(ψ_{ψ(1)}(ψ_{ψ(1)}(ψ(ψ_{ψ(1)}(0))))) of v(P_1 34) has q0 < W but not q0 < W[gamS μ b_r 1 2].
It is the upgrade-frame instance of the bad call (WfBad.BadCall: W = A, a summand of v(P1 i) re-exposed), like the
dropped `AbsDWs`; the DQ engine (WfQrE1.v_upgDQ) needs no absorption.  So `auwl` is dropped from the bundle
(WfExQ1.Inv3V3).
Theorems: `not_absUWL` (the Cons valuation), `no_inv3V2`, `no_inv3V2A` (no valuation of N has Inv3V2 / Inv3V2A).
The first version of WfExQ1.Inv3V3 (commit aad2270f) had `auwl`; it was removed after this refutation.
-/
import Ytosk.WfInvA1
import Ytosk.V3Total
import Ytosk.V3QRIdx
import Ytosk.V3StructT1
import Ytosk.V3VLocT1
import Ytosk.V3QRShape
import Ytosk.V3InvExpand

namespace Ytosk.WfExQ12
open T Ytosk
set_option maxRecDepth 200000
set_option maxHeartbeats 80000000

-- trace 340 x 38 r 37 q 37 i 34 k 35 d_i 2 o r p_{p(1)}(p_{p(1)+1}(0))
-- W p_{p(1)}(p_{p(1)+1}(0)) q p_{p(1)}(p_{p(1)}(p_{p(1)}(p(p_{p(1)}(0))))) eta p_{p(1)}(p_{p(1)}(1)) fsD p_{p(1)}(p_{p(1)}(p_{p(1)}(1))) cof ('omega',) ohole True
-- steps [('lb', 35, 36, 37, 2), ('lo', 37, 38, 0)]
def N : Mat := [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 1), (4, 2, 1), (5, 1, 0), (6, 2, 1), (7, 2, 1), (8, 2, 0), (6, 2, 1), (7, 2, 1), (8, 1, 0), (9, 2, 1), (10, 2, 1), (11, 2, 0), (9, 2, 1), (10, 2, 1), (11, 1, 0), (12, 0, 0), (13, 1, 1), (10, 2, 0), (11, 3, 1), (12, 3, 1), (13, 1, 0), (14, 2, 1), (12, 3, 0), (11, 3, 1), (12, 3, 1), (13, 1, 0), (14, 2, 0)]
def trace : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2]
def ρO : List T := [(psi z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z) z) z z) z z) z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z z) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z) z) z z) z z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z) z) z z) z z) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z) z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z) z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z) z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z), (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z), (psi z (psi (psi z (psi z z z) z) z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z), (psi (psi z (psi z z z) (psi z z z)) z z)]
def ρV : List T := [z, (psi (psi (psi z (psi z z z) z) z z) z z), (psi z (psi z z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) z z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z) z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z) z z) z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi z (psi z z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z) z (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z) (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z) z z) z) z)) z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi z (psi z z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi z (psi z z z) z), z, (psi z (psi z z z) z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z (psi z z z) z)) z z) z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) (psi z (psi z z z) z)), (psi z (psi z z z) z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) (psi z (psi z z z) z)), (psi z (psi z z z) z), (psi z (psi z z z) (psi z z z))]
def Wl : T := (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) (psi z z z)) z z) z)
def q0 : T := (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z (psi (psi z (psi z z z) z) z z) z) z) z) z)
def μ0 : T := (psi z (psi z z z) z)
def b0 : T := z
def η0 : T := (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) (psi z z z) z) z)

def ρ : Valn := ⟨fun i => ρO.getD i z, fun i => ρV.getD i z⟩

private theorem std_fold : ∀ (ns : List Nat) (N : Mat), Std N → Std (ns.foldl expand N)
  | [], _, h => h
  | n :: ns, N, h => std_fold ns (expand N n) (Std.exp n h)

theorem standard : Std N := by
  have h : trace.foldl expand SRO = N := by decide
  rw [← h]
  exact std_fold trace SRO Std.sro

theorem ne_sro : N ≠ SRO := by decide

theorem below_sro : N.length = 39 ∧ N.take 5 ≠ SRO := by decide

theorem cons : Cons N ρ := by unfold Cons; decide

theorem S : SInv N := sInv_std standard ne_sro

theorem hx : 38 + 1 = N.length := by decide
theorem h1 : par N 1 38 = some 37 := by decide
theorem hq : par N 0 38 = some 37 := by decide
theorem hx2 : entry N 2 38 = 0 := by decide

theorem hxv : ¬ DepX N 38 false 38 := by
  intro h
  have hdep := qr_dep hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2 hq
  cases h with
  | vpar _ hp hdm =>
    rw [h1] at hp; cases hp
    exact hdep.2.1 hdm
  | vupg _ _ hu _ =>
    have h0 : upg N 38 = none := by decide
    rw [h0] at hu; cases hu
  | vbump _ h2 _ _ _ _ => exact h2 (by decide)

noncomputable abbrev lo := loQ N ρ μ0 b0
noncomputable abbrev lb := lbQ N ρ μ0 b0

theorem depL34 : DepL N 38 lo lb false 34 (0 + lo 37 38 + lb 35 36 37) := (DepL.vupg (k := 35) (by decide) (by decide) (by decide) (DepL.vbump (j := 36) (k := 37) (by decide) (by decide) (by decide) (by decide) (by decide) (DepL.ochild (c := 38) (by decide) (by decide) (by decide) DepL.leaf)))

theorem lo_37_38 : lo 37 38 = 0 := by
  show loQ N ρ μ0 b0 37 38 = 0
  unfold loQ
  rw [if_neg (by decide)]

theorem lb_35 : lb 35 36 37 = 2 := by
  show lbQ N ρ μ0 b0 35 36 37 = 2
  unfold lbQ
  rw [if_pos (by decide), if_pos (by decide)]

theorem dOf34 : dOf N 38 lo lb 34 = 2 := by
  have h := dOf_v hx hxv (hOS_t1 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq)
    (fun i hi hv => dv_shape hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq hi hv) (by decide) depL34
  rw [h, lo_37_38, lb_35]

theorem hole : OHole Wl := by
  have hc : cof (psi (succ μ0) z z) = .big μ0 := cof_omega_succ μ0
  show OHole (psi μ0 (psi (succ μ0) z z) z)
  have hs : isSucc (psi (succ μ0) z z) = false := by decide
  simp only [OHole, hc, hs]
  simp

section
variable {ρ' : Valn} (hu : ∀ i, i < N.length → ρ'.o i = ρ.o i ∧ ρ'.v i = ρ.v i)
include hu

theorem cnt_eq {i c : Nat} (hc : c < N.length) : cnt N ρ' i c = cnt N ρ i c := by
  unfold cnt; rw [(hu c hc).1]

theorem preState_eq {i : Nat} (hi : i < N.length) {L : List Nat} (hL : ∀ c ∈ L, c < N.length) :
    preState N ρ' i L = preState N ρ i L := by
  unfold preState
  rw [(hu i hi).2, List.map_congr_left (fun c hc => cnt_eq hu (hL c hc))]

theorem bumpTerm_eq {i j : Nat} : bumpTerm N ρ' i j = bumpTerm N ρ i j := by
  unfold bumpTerm
  split
  · congr 2
    apply List.map_congr_left
    intro c hc
    exact (hu c (mem_children hc).2).1
  · rfl

theorem lo_eq : loQ N ρ' μ0 b0 37 38 = lo 37 38 := by
  have hp : preState N ρ' 37 ((children N 37).filter (fun d => decide (d < 38))) =
      preState N ρ 37 ((children N 37).filter (fun d => decide (d < 38))) :=
    preState_eq hu (by decide) (fun c hc => (mem_children (List.mem_filter.mp hc).1).2)
  show loQ N ρ' μ0 b0 37 38 = loQ N ρ μ0 b0 37 38
  unfold loQ
  simp only [(hu 38 (by decide)).1, (hu 37 (by decide)).2, hp]

theorem lb_eq : lbQ N ρ' μ0 b0 35 36 37 = lb 35 36 37 := by
  show lbQ N ρ' μ0 b0 35 36 37 = lbQ N ρ μ0 b0 35 36 37
  have hb : bumpTerm N ρ' 35 = bumpTerm N ρ 35 := funext (fun j => bumpTerm_eq hu)
  unfold lbQ
  simp only [(hu 37 (by decide)).1, hb]

end

theorem depL34g (lo' : Nat → Nat → Nat) (lb' : Nat → Nat → Nat → Nat) :
    DepL N 38 lo' lb' false 34 (0 + lo' 37 38 + lb' 35 36 37) := (DepL.vupg (k := 35) (by decide) (by decide) (by decide) (DepL.vbump (j := 36) (k := 37) (by decide) (by decide) (by decide) (by decide) (by decide) (DepL.ochild (c := 38) (by decide) (by decide) (by decide) DepL.leaf)))

theorem absUWL_fails (ρ' : Valn) (rk : Bool → Nat → Nat) (hR : Rk N rk) (hC : Cons N ρ') : ¬ AbsUWL N ρ' := by
  intro h
  have hu := cons_unique hC cons hR
  have ho : ρ'.o 37 = psi μ0 (app b0 (psi (succ μ0) z z)) z := (hu 37 (by decide)).1.trans (by decide)
  have hk : last (ρ'.v 35) = Wl := by rw [(hu 35 (by decide)).2]; decide
  have hp : par N 1 34 = some 29 := by decide
  have hv : vOpt ρ' (par N 1 34) = ρ.v 29 := by rw [hp]; exact (hu 29 (by decide)).2
  have hd : dOf N 38 (loQ N ρ' μ0 b0) (lbQ N ρ' μ0 b0) 34 = 2 := by
    have h := dOf_v hx hxv (hOS_t1 hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq)
      (fun i hi hv => dv_shape hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq hi hv) (by decide)
      (depL34g (loQ N ρ' μ0 b0) (lbQ N ρ' μ0 b0))
    rw [h, lo_eq hu, lb_eq hu, lo_37_38, lb_35]
  have h34 : DepX N 38 false 34 := depX_of_depL (depL34g lo lb)
  have hup : upg N 34 = some 35 := by decide
  have h1' := h 37 μ0 b0 h1 hq hx2 ho 34 35 (by decide) h34 hup (by rw [hk]; exact hole) (by rw [hk]; decide)
    q0 (by rw [hv]; decide) (by rw [hk]; decide)
  rw [show List.length N - 1 = 38 from rfl, hd, hk] at h1'
  exact (by decide : ¬ q0 < fsD Wl (gamS μ0 (app b0 (psi (succ μ0) z z)) one (max 1 2))) h1'

theorem not_absUWL (rk : Bool → Nat → Nat) (hR : Rk N rk) : ¬ AbsUWL N ρ :=
  absUWL_fails ρ rk hR cons

/-- **No valuation of the standard matrix N has `Inv3V2`** (field `auwl`). -/
theorem no_inv3V2 : ¬ ∃ ρ' rk, Inv3V2 N ρ' rk := by
  rintro ⟨ρ', rk, I⟩
  exact absUWL_fails ρ' rk I.rank I.cons I.auwl

/-- **No valuation of N has `Inv3V2A`** (WfInvA1; field `auwl`). -/
theorem no_inv3V2A : ¬ ∃ ρ' rk, Inv3V2A N ρ' rk := by
  rintro ⟨ρ', rk, I⟩
  exact absUWL_fails ρ' rk I.rank I.cons I.auwl

theorem main : Std N ∧ N ≠ SRO ∧ (¬ ∃ ρ' rk, Inv3V2 N ρ' rk) ∧ ¬ ∃ ρ' rk, Inv3V2A N ρ' rk :=
  ⟨standard, ne_sro, no_inv3V2, no_inv3V2A⟩

end Ytosk.WfExQ12
