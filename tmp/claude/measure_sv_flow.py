"""Simulate the visibility flow for T2SVStrict (sv: q = r, upg(x-1) = x) in T = M.take x, sigma = sigma_{V,V+1}.
Rules (checked):
  base: l = x-1, v(l) = V + 1, S(l).
  C: cur is the last counted child of p: P(cur) := vis(cur) and (not trig or low) or A(cur)  ==>  A(p).
  B: p = par0(cur) is bump(pp), cur is p's last child: vis(cur) ==> SW(pp) and S(pp) (needs V <= v(P1 pp)).
  U: cur is upgraded & topped at p = par0(cur), cur reached by B (SW(cur)): k = upgrader of cur, k = cur - 1,
     SW(cur) ==> S(k) (needs V <= v(P1 k)); continue from k.
  final at r: cur is the last counted child c of r: P(c)."""
import sys, json, collections
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
          '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, ONE, lt, le, sumN, spa, summ, succ
from vracopy import sh
import ytosk_eval as Y
from pv2 import load

def measure(m):
    M = list(map(tuple, m)); cnt = collections.Counter()
    if not M < SRO: return cnt, None
    x = len(M) - 1
    if x < 1 or M[x][2] == 0: return cnt, None
    C = Ctx(M)
    if not C.ok: return cnt, None
    r = C.e.par(2, x); q = C.e.par(0, x)
    if r is None or q != r or C.upg(x - 1) != x: return cnt, None
    T = Ctx(M[:-1])
    if not T.ok: return cnt, None
    V = C.v(r); W = succ(V)
    sg = lambda t: sh(V, W, t)
    shf = lambda s: Y.add(W, sg(Y.sub(s, V)))
    def vis(a): return lt(T.o(a), sg(T.o(a)))
    def S(a): return lt(V, T.v(a)) and lt(T.v(a), shf(T.v(a)))
    def A(a): y = T.o(a)[1]; return lt(y, sg(y))
    def Wt(a): return sumN([ONE] + [T.bumpTerm(a, j) for j in T.ch(a)])
    def SW(a): w = Wt(a); return lt(w, sg(w))
    def P(c, p):
        cl = T.CL(p); i = cl.index(c)
        B = spa(T.v(p), sumN([T.o(d) for d in cl[:i]]))
        s, y, _ = T.o(c)
        trig = lt(B, y) and lt((T.v(p), Z, Z), (s, y, Z))
        low = lt(Y.cut(Y.add(s, ONE), y), y)
        return (vis(c) and (not trig or low)) or A(c)
    def P1v(a):
        p1 = T.e.par(1, a); return T.v(p1) if p1 is not None else Z
    fail = []
    l = x - 1
    cnt['cases'] += 1
    if T.v(l) != succ(V): fail.append('base_v')
    if not S(l): fail.append('base_S')
    cur = l; viaB = False; steps = []
    for _ in range(10 * len(M)):
        p = T.e.par(0, cur)
        if p is None: fail.append('no_parent'); break
        if p == r:
            cl = T.CL(r)
            if cl and cl[-1] == cur:
                steps.append('F')
                if not P(cur, r): fail.append('final_P')
                break
            if T.counted(r, cur): fail.append('final_not_lastCL'); break
            if M[cur] == T.e.bump(r): fail.append('final_bump'); break
            # U at r: jump
            steps.append('U')
            ks = [k for k in range(len(M) - 1) if T.upg(k) == cur]
            if ks != [cur - 1]: fail.append('U_upgrader:%s' % ks); break
            if not viaB: fail.append('U_not_viaB')
            if not SW(cur): fail.append('U_SW')
            k = cur - 1
            if not le(V, P1v(k)): fail.append('U_P1k')
            if not S(k): fail.append('U_Sk')
            cur = k; viaB = False; continue
        pp = T.e.par(0, p)
        if M[p] == T.e.bump(pp):
            steps.append('B')
            if T.ch(p)[-1] != cur: fail.append('B_not_last')
            if not vis(cur): fail.append('B_vis')
            if M[pp][2] == 0: fail.append('B_e2pp0')
            if not le(V, P1v(pp)): fail.append('B_P1pp')
            if not SW(pp): fail.append('B_SW')
            if not S(pp): fail.append('B_S')
            cur = pp; viaB = True; continue
        if T.counted(p, cur):
            steps.append('C')
            if T.CL(p)[-1] != cur: fail.append('C_not_lastCL')
            if P(cur, p) and not A(p): fail.append('C_A')
            if not P(cur, p): fail.append('C_noP')
            cur = p; viaB = False; continue
        if M[cur] == T.e.bump(p): fail.append('bump_edge_unexpected'); break
        steps.append('U')
        ks = [k for k in range(len(M) - 1) if T.upg(k) == cur]
        if ks != [cur - 1]: fail.append('U_upgrader:%s' % ks); break
        if not viaB: fail.append('U_not_viaB')
        if not SW(cur): fail.append('U_SW')
        k = cur - 1
        if not le(V, P1v(k)): fail.append('U_P1k')
        if not S(k): fail.append('U_Sk')
        cur = k; viaB = False
    else:
        fail.append('loop')
    for f in fail: cnt['fail.' + f] += 1
    if not fail: cnt['ok'] += 1
    cnt['steps.' + ''.join(steps)] += 1
    return cnt, (M if fail else None)

if __name__ == '__main__':
    sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
    lo = int(sys.argv[1]); hi = int(sys.argv[2])
    tot = collections.Counter(); ex = {}
    from multiprocessing import Pool
    pool = Pool(4)
    for f in sets[lo:hi]:
        for c, Mf in pool.imap_unordered(measure, load(f), chunksize=200):
            tot.update(c)
            if Mf is not None:
                k = tuple(sorted(x for x in c if x.startswith('fail.')))
                if k not in ex or len(Mf) < len(ex[k]): ex[k] = Mf
        print(f.split('/')[-1], json.dumps({k: v for k, v in tot.items() if not k.startswith('steps.')}), flush=True)
    for k in sorted(tot): print(k, tot[k])
    for k, v in ex.items(): print('EX', k, v)
