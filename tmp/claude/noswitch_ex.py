"""Print small Bpos (B' > 0) trigger examples at qr frames where o_T(c) != o_M(c)."""
import sys, json, collections
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, lt, sumN, spa
import ytosk_eval as Y
from pv2 import load
f = sys.argv[1]; K = int(sys.argv[2])
best = []
for m in load(f):
    M = list(map(tuple, m))
    if not M < SRO: continue
    x = len(M) - 1
    if x < 1 or M[x][2] == 0: continue
    C = Ctx(M)
    if not C.ok: continue
    r = C.e.par(2, x)
    if r is None or C.e.par(0, x) != r: continue
    if any(C.upg(i) == x for i in range(x)): continue
    cl = C.CL(r)
    if not cl or len(cl) < 2 or cl[-1] != x: continue
    T = Ctx(M[:-1])
    if not T.ok: continue
    c = cl[-2]; oT, oM = T.o(c), C.o(c); a = C.v(r)
    Bp = spa(a, sumN([C.o(d) for d in cl[:-2]]))
    trig = lambda o: lt(Bp, o[1]) and lt((a, Z, Z), (o[0], o[1], Z))
    if Bp == Z or not trig(oM) or oT == oM: continue
    best.append((len(M), M, r, c, cl, C.upg(x - 1), Bp, oT, oM, C, T))
    best.sort(key=lambda t: t[0]); best = best[:K]
for n, M, r, c, cl, u, Bp, oT, oM, C, T in best:
    print('M =', ''.join('(%d,%d,%d)' % t for t in M))
    print(' x=%d r=%d c=%d CL_M(r)=%s upg(x-1)=%s V=%s' % (len(M) - 1, r, c, cl, u, Y.tstr(C.v(r))))
    print(' CL(c)=%s' % C.CL(c))
    for d in cl[:-1]: print('  o(%d) = %s' % (d, Y.tstr(C.o(d))))
    print(' B\' =', Y.tstr(Bp)); print(' oT(c) =', Y.tstr(oT)); print(' oM(c) =', Y.tstr(oM))
    print(' trigT =', lt(Bp, oT[1]))
