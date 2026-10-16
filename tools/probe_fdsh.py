"""FDsh: FrameDom a B s (H s y) ⟹ FrameDom (f a) (σ B) (f s) (H (f s) (σ y)),  σ = sh V V', f = shf V V',
for V < V', V ≤ a, V < s, at real rewriting frames (a, B, s, y) of the set, V ranging over the values
v(j) ≤ a of the matrix, V' in {V+1, V+ω, V+ω^2, V + v-values > V of the matrix}.
Also measures FrameDom itself at every rewriting frame (FrameClosed in Lean form).
"""
import sys, pickle, random
from collections import Counter
from multiprocessing import Pool
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_inv3_prefix import Ctx, Y
from fdom_exact import frame_dom

SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]
SETD = '/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/'


def rwframes(C):
    """Rewriting frames (k, c, a, B, s, y) of the evaluation C (FrameClosed's frames)."""
    for k in range(len(C.M)):
        cl = C.CL(k); a = C.v(k)
        for idx, c in enumerate(cl):
            s, y, _ = C.o(c)
            B = C.pre(k, cl[:idx])
            if lt(B, y) and lt((a, Z, Z), (s, y, Z)):
                yield k, c, a, B, s, y
from lhd_exact import lt, le, Z

ONE = (Z, Z, Z); OMEGA = (Z, ONE, Z); OM2 = (Z, (Z, Z, ONE), Z)

def sh(V, V2, t):
    if not t: return Z
    s, y, c = t
    if lt(V, s): return (Y.add(V2, sh(V, V2, Y.sub(s, V))), sh(V, V2, y), sh(V, V2, c))
    return (s, y, sh(V, V2, c))
def shf(V, V2, s): return Y.add(V2, sh(V, V2, Y.sub(s, V)))
def H(s, y): return Y.add(Y.cut(Y.add(s, ONE), y), Y.sub((s, y, Z), (s, Y.cut(Y.add(s, ONE), y), Z)))

def go(m):
    cnt = Counter(); ex = {}
    M = list(m)
    if not M < SRO: return cnt, ex
    C = Ctx(M)
    if not C.ok: return cnt, ex
    vals = sorted(set(C.v(i) for i in range(len(M))), key=lambda t: Y.tstr(t))
    for (k, c, a, B, s, y) in rwframes(C):
        X = H(s, y)
        ok = frame_dom(a, B, s, X)
        cnt[('FD', ok)] += 1
        if not ok:
            ex.setdefault('FDfail', (M, k, c)); continue
        for V in vals:
            if not le(V, a) or not lt(V, s): continue
            V2s = [Y.add(V, ONE), Y.add(V, OMEGA), Y.add(V, OM2)] + [w for w in vals if lt(V, w)]
            for V2 in V2s:
                if not lt(V, V2): continue
                a2, B2, s2, y2 = shf(V, V2, a), sh(V, V2, B), shf(V, V2, s), sh(V, V2, y)
                ok2 = frame_dom(a2, B2, s2, H(s2, y2), why=True)
                cnt[('FDsh', ok2[0])] += 1
                if not ok2[0]:
                    ex.setdefault('FDsh', (M, k, c, Y.tstr(V), Y.tstr(V2), Y.tstr(a), Y.tstr(B), Y.tstr(s), Y.tstr(y), Y.tstr(ok2[1]), Y.tstr(ok2[2])))
    return cnt, ex

if __name__ == '__main__':
    nm, lim = sys.argv[1], int(sys.argv[2])
    mats = [tuple(map(tuple, mm)) for mm in pickle.load(open(SETD + nm + '.pkl', 'rb'))]
    mats = [mm for mm in mats if len(mm) > 1 and list(mm) < SRO]
    random.seed(4); random.shuffle(mats); mats = mats[:lim]
    tot = Counter(); exs = {}
    with Pool(4) as p:
        for c, e in p.imap_unordered(go, mats, chunksize=10):
            tot.update(c)
            for k, v in e.items(): exs.setdefault(k, v)
    print(nm, len(mats))
    for k, v in sorted(tot.items(), key=lambda kv: str(kv[0])): print(k, v)
    for k, v in exs.items(): print('EX', k, v)
