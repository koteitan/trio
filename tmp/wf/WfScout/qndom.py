"""T2QNDomBad / T2QNDomBad2 on graft and expansion families.
For every matrix M (< SRO) whose last column x has row 2 != 0, q = P0(x) != r = P2(x), q the last counted child of r:
 weak := not lhdE(v_T(q), v_M(q))  (T = M.take x)
 simple := filter(children q, < x) = [p], children p = [x-1], col p = bump q, upg(x-1) = k < x-1
 form := v_T(q) = V + last(v_T(q)) with V = v_M(r)
 dom := for all u, comps u omegaT dominated by comps u qnS ++ [0]
Bad2 itself is not checked (superset of the antecedent).
Usage: qndom.py SET...   SET = pkl name in sets/, or shape_d3s, kbump, ufam, deepfam, grow."""
import sys, pickle, json, time
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfT2Abs')
from probe_inv3_prefix import Ctx, Z, ONE, lt, sumN
from lhd_exact import comps, indices, le, lhdE
import ytosk_eval as Y
SETD = '/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/'
SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]
def last(t):
    while t[2]: t = t[2]
    return (t[0], t[1], Z)
def mt(M): return ''.join('(%d,%d,%d)' % tuple(c) for c in M)
def go(m):
    cnt = Counter(); ex = []
    M = [tuple(c) for c in m]
    if not M < SRO or len(M) < 3 or M[-1][2] == 0: return cnt, ex
    x = len(M) - 1
    C = Ctx(M)
    if not C.ok: return cnt, ex
    r = C.e.par(2, x); q = C.e.par(0, x)
    if r is None or q is None or q == r: return cnt, ex
    cl = [d for d in C.ch(r) if C.counted(r, d)]
    if not cl or cl[-1] != q: return cnt, ex
    T = Ctx(M[:-1])
    if not T.ok: return cnt, ex
    cnt['qn'] += 1
    vT = T.v(q); vM = C.v(q)
    if lhdE(vT, vM): return cnt, ex
    cnt['weak'] += 1
    chq = [d for d in C.ch(q) if d < x]
    simple = False
    if len(chq) == 1:
        p = chq[0]
        k = C.upg(x - 1)
        simple = (C.ch(p) == [x - 1] and M[p] == C.e.bump(q) and k is not None and k < x - 1)
    V = C.v(r); wT = last(vT)
    form = Y.add(V, wT) == vT
    S = sumN([ONE] + [C.bumpTerm(q, d) for d in chq]); qnS = Y.add(V, Y.omega(S))
    I = {Z}; indices(wT, I); indices(qnS, I)
    dom = all(g == Z or any(le(g, d) for d in comps(u, qnS)) for u in I for g in comps(u, wT))
    cnt[('simple', simple, 'form', form, 'dom', dom)] += 1
    if not simple and len(ex) < 3: ex.append((mt(M), simple, form, dom))
    return cnt, ex
def load(nm):
    if nm == 'shape_d3s': return pickle.load(open('/home/koteitan/proofs/trio/tmp/wf/WfH10/shape_d3s.pkl', 'rb'))
    if nm == 'kbump':
        d = json.load(open('/home/koteitan/proofs/trio/tmp/wf/WfH10/kbump_d3s.json'))
        return [eval('[' + c['matrix'].replace(')(', '),(') + ']') for c in d['cases']]
    if nm == 'ufam': return pickle.load(open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC2/ufam.pkl', 'rb'))
    if nm == 'deepfam': return pickle.load(open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC/deepfam.pkl', 'rb'))
    if nm == 'grow':
        import probe_sets
        return probe_sets.grow()
    return pickle.load(open(SETD + nm + '.pkl', 'rb'))
if __name__ == '__main__':
    out = {}
    for nm in sys.argv[1:]:
        t = time.time()
        mats = load(nm)
        tot = Counter(); exs = []
        with Pool(4) as pl:
            for c, ex in pl.imap_unordered(go, mats, chunksize=200):
                tot.update(c); exs += ex[:max(0, 5 - len(exs))]
        res = {'n': len(mats), 'counts': {str(k): v for k, v in tot.items()}, 'examples': exs, 'sec': time.time() - t}
        print(nm, json.dumps(res), flush=True)
        out[nm] = res
        json.dump(out, open('/home/koteitan/proofs/trio/tmp/wf/WfScout/qndom_%s.json' % '_'.join(sys.argv[1:]), 'w'), indent=1)
