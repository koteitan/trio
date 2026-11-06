"""The copy/VRA residuals of hN_of2 (V3SeedVFAll2.lean) on all 86 sets, t = 2 matrices strictly below SRO, n = 2, 3.
N = M[n], P = M[n-1], x = last column, r = P_2(x), L = x - r, V = v_P(r), V' = v_N(r + L), f = shf V V', sigma = sh V V'.
  T2VRAPre, T2VRACopyEsc, T2VRASeed : as tmp/claude/probe_t2vra_esc.py (V3T2VRA.lean).
  FDshAt (T2CopyK FDshAt, V3T2VSFC.lean): at the copy frames of P (r <= i, le1 P r i, counted child c, o(c) = psi s y 0,
    V < s, B < y, psi_a(0) < psi_s(y)):  FrameDom a B s (H s y) -> FrameDom (f a) (sigma B) (f s) (H (f s) (sigma y)).
  VDK (T2CopyK CopyVDomK): VDomF V V' a at the copy frames of P with a counted child.
FrameDom is decided exactly by tools/fdom_exact.py."""
import sys, json, collections
from multiprocessing import Pool
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
          '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, lt, le, comps, split, succ
from vracopy import sh, shf, frames
from fdom_exact import frame_dom
from probe_fdsh import H
from lhd_exact import indices
import probe_t2vra_esc as E
import trio, ytosk_eval as Y
from pv2 import load


def keep(ex, key, M, info):
    if key not in ex or len(M) < len(ex[key]['matrix']): ex[key] = dict(matrix=M, **info)


def measure(matrix):
    M = list(matrix); cnt = collections.Counter(input=1); ex = {}
    if not M < SRO: cnt['outside_SRO'] += 1; return cnt, ex
    x = len(M) - 1
    if x < 1 or M[x][2] == 0: return cnt, ex
    C = Ctx(M)
    if not C.ok: cnt['eval_failed'] += 1; return cnt, ex
    r = C.e.par(2, x)
    if r is None: return cnt, ex
    cnt['t2'] += 1
    L = x - r; q = C.e.par(0, x)
    seed = {r} if q == r else {q, C.e.par(0, q)}
    fM, pM = frames(C)
    for n in (2, 3):
        N = trio.expand(M, n); P = trio.expand(M, n - 1)
        CN, CP = Ctx(N), Ctx(P)
        if not (CN.ok and CP.ok): cnt['eval_failed_N'] += 1; continue
        fN, pN = frames(CN); fP, pP = frames(CP)
        V = CP.v(r); V2 = CN.v(r + L)
        for k in range(x):
            if k in seed: continue
            for u in pN[k]:
                cnt['Pre.cases'] += 1
                if u not in pM[k]:
                    cnt['Pre.failures'] += 1; keep(ex, 'Pre', M, dict(n=n, k=k, u=Y.tstr(u)))
        for (k, c, B, s, y) in fN:
            i = k - L
            if i < r or i >= len(P): continue
            if split(y, (succ(s), Z, Z))[0] == Z: continue
            aN = CN.v(k); UP = pP[i] | {CP.v(i)}
            for u in pN[k] | {aN}:
                if lt(aN, u): continue
                if any(lt((s, Z, Z), g) and lt(B, g) for g in comps(u, s)):
                    cnt['CopyEsc.cases'] += 1
                    if not (u in UP and le(u, V)):
                        cnt['CopyEsc.failures'] += 1; keep(ex, 'CopyEsc', M, dict(n=n, i=i, u=Y.tstr(u)))
        for i in seed:
            cl = CN.CL(i); a = CN.v(i)
            for idx, c in enumerate(cl):
                B = CN.pre(i, cl[:idx]); cv = CN.o(c)
                for u in pN[i] | {a}:
                    cnt['Seed.cases'] += 1
                    if not E.qvrat(a, B, cv, u):
                        cnt['Seed.failures'] += 1; keep(ex, 'Seed', M, dict(n=n, i=i, c=c, u=Y.tstr(u)))
        for i in range(r, len(P)):
            if not E.le1(CP, r, i): continue
            cl = CP.CL(i)
            if not cl: continue
            a = CP.v(i); fa = shf(V, V2, a)
            # VDK
            us = {Z}; indices(V2, us); indices(fa, us)
            cnt['VDK.cases'] += 1
            for u in us:
                if lt(fa, u): continue
                cfa = comps(u, fa)
                if not all(le(g, (fa, Z, Z)) or any(le(g, d) for d in cfa) for g in comps(u, V2)):
                    cnt['VDK.failures'] += 1; keep(ex, 'VDK', M, dict(n=n, i=i, u=Y.tstr(u))); break
            # FDshAt
            for idx, c in enumerate(cl):
                s, y, tail = CP.o(c)
                if tail != Z or not lt(V, s): continue
                B = CP.pre(i, cl[:idx])
                if not (lt(B, y) and lt((a, Z, Z), (s, y, Z))): continue
                if not frame_dom(a, B, s, H(s, y)): cnt['FDshAt.vacuous'] += 1; continue
                cnt['FDshAt.cases'] += 1
                fs = shf(V, V2, s); sB = sh(V, V2, B); sy = sh(V, V2, y)
                if not frame_dom(fa, sB, fs, H(fs, sy)):
                    cnt['FDshAt.failures'] += 1; keep(ex, 'FDshAt', M, dict(n=n, i=i, c=c))
    return cnt, ex


if __name__ == '__main__':
    sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
    if len(sys.argv) > 1: sets = [f for f in sets if f.split('/')[-1] in sys.argv[1:]]
    tot = collections.Counter(); exs = {}
    with Pool(4) as pool:
        for f in sets:
            for c, e in pool.imap_unordered(measure, load(f), chunksize=100):
                tot.update(c)
                for k, v in e.items():
                    if k not in exs or len(v['matrix']) < len(exs[k]['matrix']): exs[k] = v
            print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', json.dumps(exs, default=str))
