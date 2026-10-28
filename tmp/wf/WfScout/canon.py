"""HCanonV2 (CanonicalNeed) antecedent shapes.
p, a < b adjacent children of p, both e1 = e1 p + 1, e2 = 1, P1 = p; upg(a-1) = a, topped a;
upg(b-1) != b; b counted at p.  Conclusion v(b) <= v(a).
Records: conclusion, bumpW(b) vs bumpW(a), a has children, b has a bump child, subtree shapes."""
import sys, pickle, json, time
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfScout')
from probe_inv3_prefix import Ctx, Z, ONE, lt
from qndom import load, mt
SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]
def le(x, y): return x == y or lt(x, y)
def sub(C, i):
    out = [i]; k = 0
    while k < len(out):
        out += C.ch(out[k]); k += 1
    return sorted(out)
def go(m):
    cnt = Counter(); ex = []
    M = [tuple(c) for c in m]
    if not M < SRO or len(M) < 3: return cnt, ex
    C = Ctx(M)
    if not C.ok: return cnt, ex
    n = len(M)
    for p in range(n):
        ch = C.ch(p)
        for ia in range(len(ch) - 1):
            a, b = ch[ia], ch[ia + 1]
            ok = True
            for d in (a, b):
                if not (M[d][1] == M[p][1] + 1 and M[d][2] == 1 and C.e.par(1, d) == p): ok = False
            if not ok: continue
            if not (a >= 1 and C.upg(a - 1) == a and C.e.topped(a)): continue
            if C.upg(b - 1) == b: continue
            if not C.counted(p, b): continue
            cnt['ante'] += 1
            concl = le(C.v(b), C.v(a))
            wa, wb = C.bumpW(a), C.bumpW(b)
            sa = [tuple(x - y for x, y in zip(M[i], M[a])) for i in sub(C, a)]
            sb = [tuple(x - y for x, y in zip(M[i], M[b])) for i in sub(C, b)]
            key = ('concl', concl, 'Wle', le(wb, wa), 'Weq', wb == wa, 'achild', bool(C.ch(a)),
                   'sb_le_sa', sb <= sa,
                   'bbump', any(M[j] == C.e.bump(b) for j in C.ch(b)),
                   'aallbump', all(M[j] == C.e.bump(a) for j in C.ch(a)))
            cnt[key] += 1
            if len(ex) < 2 and any(M[j] == C.e.bump(b) for j in C.ch(b)): ex.append((mt(M), p, a, b))
    return cnt, ex
if __name__ == '__main__':
    out = {}
    for nm in sys.argv[1:]:
        t = time.time(); mats = load(nm)
        tot = Counter(); exs = []
        with Pool(4) as pl:
            for c, ex in pl.imap_unordered(go, mats, chunksize=200):
                tot.update(c); exs += ex[:max(0, 5 - len(exs))]
        res = {'n': len(mats), 'counts': {str(k): v for k, v in tot.items()}, 'examples': exs, 'sec': time.time() - t}
        print(nm, json.dumps(res), flush=True)
