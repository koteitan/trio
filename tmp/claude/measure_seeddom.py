"""Measure T2SeedQNDom (qn frames) and T2SeedCDom (C1 frames) on all t = 2 source frames below SRO.
∀ u ≤ v(r) is checked at u ∈ {0} ∪ (subscripts of the terms involved) — comps u t is constant between them."""
import sys, json, collections
from multiprocessing import Pool
R = '/home/koteitan/proofs/trio'
sys.path.insert(0, R + '/tmp/claude')
import measure_seedpf as S
from lhd_exact import lt, le, comps, indices, Z

SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]


def levels(vr, *terms):
    us = {Z}
    for t in terms: indices(t, us)
    return [u for u in us if not lt(vr, u)]


def prefB(s, w):
    while s:
        if not w or s[0] != w[0] or s[1] != w[1]: return False
        s, w = s[2], w[2]
    return True


def work(mats):
    cnt = collections.Counter(); ex = {}
    def bad(key, M):
        cnt[key + '.false'] += 1
        if key not in ex or len(M) < len(ex[key]): ex[key] = M
    for raw in mats:
        M = list(map(tuple, raw)); x = len(M) - 1
        if x < 1 or M[x][1] == 0 or M[x][2] == 0 or not M < SRO: continue
        try:
            C = S.Aud.A.ctx(M); T = S.Aud.A.ctx(M[:x])
            if not (C.ok and T.ok): cnt['unresolved'] += 1; continue
            r = C.e.par(2, x); q = C.e.par(0, x)
            if r is None or q is None or q == r: continue
            vr = C.v(r); clM = C.CL(r)
            Sq = S.Y.add(vr, S.Y.omega(S.sumN([S.ONE] + [C.bumpTerm(q, d) for d in C.ch(q) if d < x])))
            PS = (Sq, Z, Z)
            if clM and clM[-1] == q:
                cnt['qn.frames'] += 1
                Lc = clM[:-1]
                B = S.spa(vr, S.sumN([C.o(d) for d in Lc]))
                if Lc:
                    ok = True
                    for u in levels(vr, Sq, B, vr):
                        cB, cV = comps(u, B), comps(u, vr)
                        for g in comps(u, Sq):
                            if not (g == Z or le(g, B) or le(g, PS) or any(le(g, d) for d in cB) or any(le(g, d) for d in cV)):
                                ok = False; break
                        if not ok: break
                    if not ok: bad('qnDom.1', M)
                if not all(le(g, PS) or le(g, B) for g in comps(vr, Sq)): bad('qnDom.2', M)
                continue
            if C.upg(x - 1) is not None: continue
            cnt['C1.frames'] += 1
            X1 = S.spa(T.v(r), S.sumN([T.o(d) for d in T.CL(r)]))
            if X1 != Z and not prefB(Sq, S.shf(vr, Sq, Sq)): bad('cDom.1', M)
            if not all(le(g, PS) or le(g, X1) for g in comps(vr, Sq)): bad('cDom.2', M)
        except Exception as e:
            cnt['exception'] += 1
            if 'exception' not in ex: ex['exception'] = [M, repr(e)]
    return cnt, ex


if __name__ == '__main__':
    sets = json.loads(open(R + '/tmp/codex/inv3v3_inputs_sets_20261101.json').read())
    tot = collections.Counter(); exs = {}
    with Pool(4) as pool:
        for f in sets:
            try: ms = S.Aud.A.load(f)
            except Exception: tot['load_fail'] += 1; continue
            for c, e in pool.imap_unordered(work, [ms[i:i + 2000] for i in range(0, len(ms), 2000)]):
                tot.update(c)
                for k, v in e.items(): exs.setdefault(k, v)
            print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', json.dumps(exs))
