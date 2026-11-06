"""Detail of a T2VRAK KAG (KG) failure: V, s, y, the failing component g, B."""
import sys, json
for p in ['/home/koteitan/proofs/trio/tools', '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b']:
    sys.path.insert(0, p)
import probe_t2vrak as K
from probe_inv3_prefix import Ctx, Z, lt, le, comps
from vracopy import sh, shf, frames
import trio, ytosk_eval as Y
T = Y.tstr

def detail(M, nlist=(2, 3), stop=3):
    M = [tuple(c) for c in M]; x = len(M) - 1
    C = Ctx(M); r = C.e.par(2, x); L = x - r
    out = []
    for n in nlist:
        N = trio.expand(M, n); P = trio.expand(M, n - 1)
        CN, CP = Ctx(N), Ctx(P)
        _, pP = frames(CP)
        V = CP.v(r); V2 = CN.v(r + L)
        for i in range(r, len(P)):
            if not K.le1(CP, r, i): continue
            a = CP.v(i); cl = CP.CL(i)
            for idx, c in enumerate(cl):
                s, y, tail = CP.o(c); B = CP.pre(i, cl[:idx])
                for u in pP[i] | {a}:
                    if not le(u, V) or not lt(V, s): continue
                    bad = [g for g in K.compsA(V, u, Y.sub(s, V)) if not (le(g, (s, Z, Z)) or le(g, B))]
                    if bad:
                        out.append(dict(n=n, i=i, c=c, P_i=P[i], P_c=P[c], u=T(u), V=T(V), V2=T(V2), a=T(a),
                                        o_c=T(CP.o(c)), tail_z=(tail == Z), s=T(s), y=T(y), subsV=T(Y.sub(s, V)),
                                        B=T(B), bad=[T(g) for g in bad], lenP=len(P), r=r, L=L))
                        if len(out) >= stop: return out
    return out

if __name__ == '__main__':
    M = json.loads(sys.argv[1])
    for d in detail(M): print(json.dumps(d))
