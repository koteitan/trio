"""WfExQ: audit of Inv3V3 (Ytosk/lean/Ytosk/WfExQ1.lean), 2026-11-01.

usage: nice -n 15 python3 audit3.py MODE OUT.jsonl NPROC PKL...
  MODE = full : every Inv3V2 field (WfInvX/audit.py) + the four new fields
  MODE = new  : only the four new fields (adn0, tploq, adsx, tplosx)
New fields, Lean form (WfExQ1 / WfInvA1 / WfQnE2):
  adn0   AbsDN0 : q = r frame, o(r) = psi_mu(b + Om_{mu+1}), D v call i, e1 e2 != 0, dOf i = 0, OHole W, cof W = omega,
                  NotNode W, q in summands v(P1 i), q < W  ->  q < W[seed]
  tploq  TPLoQ  : TPLoWAt pattern at c, for m = 0..3 with m + d_c >= 1:
                  not psi(a[g(m + d_c)]) < Om_{s+1}  or  (a source exists and at every source i (D v call, e1 i != 0,
                  v(i) = a, W = bumpW i (e2 != 0) or last v(upg i) (e2 = 0)):
                  not psi(P + W[g(max 1 (m + d_i))]) < Om_{s+1}, P = v(P1 i))
  adsx   AbsDSX : q != r frame (P1 x = r, P0 x != r, e2 x = 0, o(r) = psi_mu(b)), D v call i, e1 e2 != 0, OHole W,
                  holeLev W = mu, q < W  ->  q < W[seed]  or  (BadShape1 i and W = o(r))
  tplosx TPLoSX : q != r frame, D o call c, o(c) = psi_s(y), split(y, Om_{s+1}).2 = 0, last y = Om_a, a not succ,
                  OHole a, holeLev y = mu  ->  not psi(a[seed]) < Om_{s+1}  or  exists i < x, D v call, BadShape1 i,
                  c anc0 P0 i, a = bumpW i = o(r), not v(P1 i) < s
Also the plain old forms on the same frames for comparison: AbsDS, TPLoS (old), TPLoWs (old, k = max 1 d_c).
Each matrix records whether M < SRO.
"""
import sys, os, json, pickle, collections, time
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfInvX')
import audit as A
from audit import ctx
import probe_inv2 as I
from probe_trigs0 import lift_counts
from probe_inv3_prefix import Z, ONE, lt, le, fs, fsD, summ, ohole, holelev, cof, notNode, split, succ, last, isSucc
import ytosk_eval as Y
from multiprocessing import Pool

SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]

def gamS(mu, b, seed, k):
    t = seed
    for _ in range(k): t = (mu, fs(b, t), Z)
    return t

def bad_shape(C, i):
    m = C.e.par(0, i)
    if m is None or C.e.par(1, i) != m: return False
    if C.CL(i) != []: return False
    cl = C.CL(m)
    if not cl or cl[-1] != i: return False
    if any(C.upg(j) == i for j in range(len(C.M))): return False
    return True

def anc0(C, c, b):
    while b is not None:
        if b == c: return True
        b = C.e.par(0, b)
    return False

def newfields(M, note):
    C = ctx(M)
    if not C.ok: return
    x = len(M) - 1
    if x < 1 or M[x][2] != 0: return
    r = C.e.par(1, x)
    if r is None: return
    q0 = C.e.par(0, x)
    Aor = C.o(r)
    if Aor == Z or Aor[2] != Z: return
    T = ctx(M[:x])
    if not T.ok: note('internal.seed_eval', False, ()); return
    seed = T.o(r)
    mu, br, _ = Aor
    D = A._dep(C, x)
    if q0 == r:
        if not br or last(br) != (succ(mu), Z, Z): return
        d = lift_counts(C, x, Aor)
        for i in range(x):
            if (False, i) in D and C.e12(i) and d[i] == 0:
                W = C.bumpW(i)
                if ohole(W) and cof(W)[0] == 'omega' and notNode(W):
                    F = fsD(W, seed)
                    for t in summ(C.vOpt1(i)):
                        if lt(t, W): note('adn0', lt(t, F), (i, 'q', t))
        srcs_by_a = {}
        for c in range(x):
            if (True, c) not in D: continue
            s, y, _ = C.o(c)
            if y == br or split(y, (succ(s), Z, Z))[1] != Z: continue
            l = last(y)
            if not l or l[1] != Z: continue
            a = l[0]
            if isSucc(a) or not ohole(a) or cof(a)[0] != 'omega': continue
            th = (succ(s), Z, Z)
            if a not in srcs_by_a:
                S = []
                for i in range(x):
                    if (False, i) in D and M[i][1] != 0 and C.v(i) == a:
                        if M[i][2] != 0: W = C.bumpW(i)
                        else:
                            k = C.upg(i)
                            if k is None: continue
                            W = last(C.v(k))
                        S.append((i, C.vOpt1(i), W))
                srcs_by_a[a] = S
            S = srcs_by_a[a]
            for m in range(4):
                if m + d[c] < 1: continue
                old = not lt((fsD(a, gamS(mu, br, seed, m + d[c])), Z, Z), th)
                if m == 0 or (m == 1 and d[c] == 0): note('tplow.old', old, (c, m))
                qok = bool(S) and all(
                    not lt((Y.sf(Y.add(P, fsD(W, gamS(mu, br, seed, max(1, m + d[i]))))), Z, Z), th)
                    for (i, P, W) in S)
                note('tploq', old or qok, (c, m, d[c], [(i, d[i]) for (i, _, _) in S]))
    else:
        for i in range(x):
            if (False, i) in D and C.e12(i):
                W = C.bumpW(i)
                if not (ohole(W) and holelev(W) == mu): continue
                F = fsD(W, seed); bs = None
                for t in summ(C.vOpt1(i)):
                    if lt(t, W):
                        ok = lt(t, F)
                        note('ads.old', ok, (i,))
                        if not ok:
                            if bs is None: bs = bad_shape(C, i)
                            ok = bs and W == Aor
                        note('adsx', ok, (i, 't', t))
        bad = None
        for c in range(x):
            if (True, c) not in D: continue
            o = C.o(c)
            if o == Z: continue
            s, y, _ = o
            l = last(y)
            if not (l and l[1] == Z and not isSucc(l[0]) and ohole(l[0]) and holelev(y) == mu
                    and split(y, (succ(s), Z, Z))[1] == Z): continue
            a = l[0]
            ok = not lt((fsD(a, seed), Z, Z), (succ(s), Z, Z))
            note('tplos.old', ok, (c,))
            if not ok:
                if bad is None:
                    bad = [i for i in range(x) if (False, i) in D and C.e12(i) and bad_shape(C, i)
                           and C.bumpW(i) == Aor]
                ok = any(anc0(C, c, C.e.par(0, i)) and a == Aor and not lt(C.vOpt1(i), s) for i in bad)
            note('tplosx', ok, (c,))

def audit3(M, mode):
    M = [tuple(c) for c in M]
    if mode == 'full':
        cnt, ex = A.audit(M)
    else:
        cnt, ex = collections.Counter(), {}
        cnt['input'] += 1
    seen = set(); fseen = set()
    below = list(M) < SRO
    def note(f, ok, info):
        cnt[f + '.cases'] += 1
        if f not in seen: seen.add(f); cnt[f + '.mats'] += 1
        if not ok:
            cnt[f + '.fail'] += 1
            if below: cnt[f + '.failSRO'] += 1
            if f not in fseen:
                fseen.add(f); cnt[f + '.fmats'] += 1; ex[f] = (len(M), M, repr(info)[:300])
    try:
        newfields(M, note)
    except Exception as e:
        cnt['new_exception'] += 1; ex.setdefault('new_exception', (len(M), M, repr(e)[:300]))
    return cnt, ex

MODE = 'full'
def work(batch):
    cnt = collections.Counter(); ex = {}
    for M in batch:
        try: c, e = audit3(M, MODE)
        except Exception as err:
            c = collections.Counter(harness_exception=1); e = {'harness_exception': (len(M), [tuple(x) for x in M], repr(err)[:300])}
        cnt.update(c); A.merge(ex, e)
    return cnt, ex

def init(mode):
    global MODE; MODE = mode

SHARD = 50000
if __name__ == '__main__':
    mode = sys.argv[1]; out = sys.argv[2]; npr = int(sys.argv[3])
    MODE = mode
    done = set()
    if os.path.exists(out):
        for line in open(out): r = json.loads(line); done.add((r['set'], r['shard']))
    for f in sys.argv[4:]:
        mats = A.load(f)
        for sh in range(0, max(1, len(mats)), SHARD):
            if (f, sh) in done: continue
            t = time.time(); part = mats[sh:sh + SHARD]
            cnt = collections.Counter(); ex = {}
            with Pool(npr, initializer=init, initargs=(mode,)) as pool:
                for c, e in pool.imap_unordered(work, (part[i:i + 25] for i in range(0, len(part), 25))):
                    cnt.update(c); A.merge(ex, e)
            rec = {'set': f, 'shard': sh, 'mode': mode, 'n': len(part), 'total': len(mats), 'sec': round(time.time() - t),
                   'cnt': dict(sorted(cnt.items())),
                   'ex': {k: [(w[0], A.ms(w[1]), w[2]) for w in L] for k, L in ex.items()}}
            with open(out, 'a') as fo: fo.write(json.dumps(rec) + '\n')
            print(json.dumps({'set': os.path.basename(f), 'shard': sh, 'n': len(part), 'sec': rec['sec'],
                              'fails': {k: v for k, v in cnt.items() if k.endswith('.fail') or 'exception' in k or 'internal' in k or 'eval_failed' in k}}), flush=True)
        del mats
