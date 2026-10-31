"""probe_hframe with TPLoW / AbsDW at the actual seed (TPLoWs / AbsDWs of Inv3V2 / TakeFrameV2):
gamS mu b_r (o_{M.take x}(r)) (max 1 d) instead of gamS mu b_r 1 (max 1 d). fsD is monotone in k, so k = max 1 d suffices."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import probe_hframe as H
ORIG=H.gamS
def measure_s(M):
    from probe_inv3_prefix import Ctx
    x=len(M)-1
    seed=None
    try:
        T=Ctx(M[:x]);C=Ctx(M);r=C.e.par(1,x)
        if r is not None:seed=T.o(r)
    except Exception:pass
    def g(mu,b,s,k):return ORIG(mu,b,seed if (s==H.ONE and seed is not None) else s,k)
    H.gamS=g
    try:cc,ee=H.measure(M)
    finally:H.gamS=ORIG
    return cc,ee
