"""WfInvX: one checker for every field of Inv3V2 (V3Inv2.lean) and of SInv / SInvX / RowJ / UAT / UAB
(V3InvExpand.lean, V3InvJ.lean, V3Take.lean, V3ChgS.lean), in the Lean form (2026-10-31).

usage: nice -n 15 python3 audit.py OUT.jsonl NPROC PKL...   (NPROC <= 4)

Per matrix M (rho = Ctx(M) = the evaluator value, rho' = Ctx(M.take x), x = |M| - 1). Each field below reports
'<F>.cases' (innermost instances checked) and '<F>.fail' (failed instances), '<F>.mats' (matrices with >= 1 case),
'<F>.fmats' (matrices with >= 1 failure); per field the smallest failing matrix (len, then lex).

Structural (exact; own implementation of Eval.lean par / upg / children / topped / bump, compared with Ev):
  R0P R1S Z2 R12 R01 E00 SibDec Z1C BumpE2 BumpLeaf UAT UAB RowJ   (SInv = R0P Z2 SibDec Z1C UAT UAB R12 BumpE2 R01 E00;
  SInvX = R0P R1S Z2 R12 R01 E00 LocInv, LocInv = SibDec Z1C BumpE2 BumpLeaf)
Value (Inv3V2 fields, Lean name : this checker):
  cons  : Cons  -- o(i) = sf(psi(v i, sumN(children.map cnt), 0)), v(i) = vRhs (Val.lean), with ytosk_eval ops
  rank  : Rk    -- exists rk iff the Rk constraint graph (Val.lean Rk) is acyclic (finite graph, exact)
  good  : Good3 -- isOT o, isOT v, cvals pairwise >=
  vs    : VSmallF (V3DropMain)            -- WfReM/vsmallf.py form
  fc    : FrameClosed (V3DropRel)         -- FrameDom (v i) B s (H s y) decided by tools/fdom_exact.frame_dom
  fo    : FrameOT
  kd/td : BumpKidsDec / BumpTermDec
  ph    : PH3cG (V3PDef; cutsNSG, prefix)  -- fdshcopy.kind
  fc3   : FC3
  vra   : VSmallRAll (probe_inv2)
  ads   : AbsDS (probe_frame7);  aus : AbsUS (probe_inv2);  tplos : TPLoS (probe_inv2)
  tp1   : TP1C  (counted children only, preState over all earlier children)
  tp1w  : TP1WC (same frames, cof y = omega)
  tplow : TPLoWs = TPLoWAt with sd = seed (WfReM/hframe_s.py; worst k = max 1 d by gamS_mono + fsD_mono_eta)
  auwl  : AbsUWL (probe_frame7);  auw0 : AbsUW0 (probe_frame7)
  adw   : AbsDWs (hframe_s)
  trigs : TrigS0 (probe_trigs0)
  tplon : TPLoN (probe_frame7);  adn : AbsDN (probe_frame7)
  rootS / rootP
The probes' 'M < SRO' filter is disabled (the Lean fields do not depend on SRO).
"""
import sys, os, json, pickle, collections, time, functools
from multiprocessing import Pool
for p in ['/home/koteitan/proofs/trio/tools', '/home/koteitan/proofs/trio/tmp/wf/WfReM', '/home/koteitan/proofs/trio/tmp/codex',
          '/home/koteitan/proofs/trio/tmp/t0/probes']:
    if p not in sys.path: sys.path.append(p)
import ytosk_eval as Y
import probe_inv3_prefix as P
from probe_inv3_prefix import Z, ONE, lt, le, isOT, comps, sumN, spa, split, succ, last, dec, single, cof, ohole, holelev, fsD
import probe_inv2 as I, probe_frame7 as R, probe_trigs0 as G, probe_hframe as HF
import hframe_s
from vsmallf import vsmallf
from fdom_exact import frame_dom
from probe_fdsh import H

Y.sf = functools.lru_cache(maxsize=1 << 18)(Y.sf)   # pure; the recursion goes through the module global
P.isOT = functools.lru_cache(maxsize=1 << 18)(P.isOT)
isOT = P.isOT
P_Ctx = P.Ctx
_CL0 = P_Ctx.CL
def _CL(s, i):
    c = s.__dict__.setdefault('_clc', {})
    if i not in c: c[i] = _CL0(s, i)
    return c[i]
P_Ctx.CL = _CL
@functools.lru_cache(maxsize=64)
def _ctx(key): return P_Ctx(list(key))
def ctx(M): return _ctx(tuple(tuple(c) for c in M))
BIG = [(10 ** 9, 0, 0)]
_dep0 = I.dependencies
def _dep(C, x):
    c = C.__dict__.setdefault('_depc', {})
    if x not in c: c[x] = frozenset(_dep0(C, x))
    return c[x]
for m in (I, R, G, HF):
    m.Ctx = ctx; m.SRO = BIG; m.dependencies = _dep
P.Ctx = ctx   # hframe_s imports Ctx from probe_inv3_prefix at call time

# ---------- structural, literally from Eval.lean ----------
class S:
    def __init__(s, M):
        s.M = M; s.n = len(M); s._p = {}
        s.children = [[] for _ in M]
        for i in range(s.n):
            q = s.par(0, i)
            if q is not None: s.children[q].append(i)
        s.up = [s.upg(i) for i in range(s.n)]
        s.upgs = set(u for u in s.up if u is not None)
    def e(s, r, i): return s.M[i][r] if 0 <= i < s.n else 0
    def col(s, i): return tuple(s.M[i]) if 0 <= i < s.n else (0, 0, 0)
    def par(s, r, n):
        k = (r, n)
        if k in s._p: return s._p[k]
        stepf = (lambda q: q - 1 if q > 0 else None) if r == 0 else (lambda q: s.par(r - 1, q))
        q = stepf(n); fuel = n + 1
        res = None
        while fuel > 0 and q is not None:
            if s.e(r, q) < s.e(r, n): res = q; break
            q = stepf(q); fuel -= 1
        s._p[k] = res; return res
    def bump(s, n): return (s.e(0, n) + 1, s.e(1, n), 1)
    def upg(s, n):
        if s.e(1, n) == 0 or s.e(2, n) == 1 or n + 1 == s.n: return None
        m = s.par(1, n)
        if m is None: return None
        L = (s.e(0, m) + 1, s.e(1, n), s.e(2, m) + 1)
        if s.par(1, n + 1) == m and s.col(n + 1) == L: return n + 1
        q = s.par(0, n); fuel = n + 1
        while fuel > 0 and q is not None:
            if s.par(1, q) == m and s.col(q) == L and s.e(0, q) < s.e(0, n + 1): return q
            q = s.par(0, q); fuel -= 1
        return None
    def topped(s, i):
        ch = s.children[i]
        return (not ch) or s.col(ch[-1]) == s.bump(i)
    def anc0(s, a, b):  # Anc0 M a b : a is b or a row-0 ancestor of b
        while b is not None:
            if a == b: return True
            b = s.par(0, b)
        return False

def colLe(a, b): return tuple(a) <= tuple(b)

def structural(M, note):
    St = S(M); n = len(M)
    note('E00', n == 0 or M[0][0] == 0, ())
    for c in range(n):
        note('Z2', M[c][2] <= 1, c)
        note('R12', M[c][1] != 0 or M[c][2] == 0, c)
        note('R01', M[c][0] != 0 or M[c][1] == 0, c)
        p = St.par(0, c)
        if p is not None:
            note('R0P', M[c][0] == M[p][0] + 1, c)
            note('R1S', M[c][1] <= M[p][1] + 1, c)
            if M[c][2] != 0: note('RowJ', M[p][1] <= M[c][1], c)
    for p in range(n):
        ch = St.children[p]
        for a, b in zip(ch, ch[1:]): note('SibDec', colLe(M[b], M[a]), (p, a, b))
        if M[p][2] == 1:
            for c in ch: note('Z1C', M[c][1] <= M[p][1], (p, c))
        for c in ch:
            if St.col(c) == St.bump(p): note('BumpE2', M[p][2] == 1, (p, c))
        for j in ch:
            if St.col(j) != St.bump(p): continue
            for c in St.children[j]:
                if M[p][1] <= M[c][1]:
                    note('BumpLeaf', M[c][2] == 0 and not St.children[c] and St.children[j][-1] == c and ch[-1] == j, (p, j, c))
    for i in range(n):
        k = St.up[i]
        if k is not None and k != i + 1:
            note('UAT', not St.topped(k), (i, k))
            for j in St.children[k]:
                if St.col(j) == St.bump(k): note('UAB', not St.anc0(j, i), (i, k, j))
    return St

# ---------- Rk: acyclicity of the constraint graph ----------
def rank_ok(St):
    n = St.n; E = collections.defaultdict(list)   # edge u -> w means rk u < rk w  (u must be ranked below w)
    isUpg = St.upgs
    for i in range(n):
        E[(False, i)].append((True, i))
        for c in St.children[i]:
            if St.col(c) != St.bump(i) and not (c in isUpg and St.topped(c)): E[(True, c)].append((True, i))
        if St.e(1, i) != 0:
            m = St.par(1, i)
            if m is not None: E[(False, m)].append((False, i))
            if St.e(2, i) == 0:
                k = St.up[i]
                if k is not None: E[(False, k)].append((False, i))
            else:
                for j in St.children[i]:
                    if St.col(j) == St.bump(i):
                        for k in St.children[j]: E[(True, k)].append((False, i))
    color = {}
    nodes = [(b, i) for i in range(n) for b in (False, True)]
    for s0 in nodes:
        if s0 in color: continue
        stack = [(s0, iter(E[s0]))]; color[s0] = 1
        while stack:
            u, it = stack[-1]
            w = next(it, None)
            if w is None: color[u] = 2; stack.pop(); continue
            cw = color.get(w)
            if cw == 1: return False
            if cw is None: color[w] = 1; stack.append((w, iter(E[w])))
    return True

def lev(t): return t[0] if t else Z

def isprefix(B, h):
    while B:
        if not h or (B[0], B[1]) != (h[0], h[1]): return False
        B = B[2]; h = h[2]
    return True

@functools.lru_cache(maxsize=20000)
def cutsHG(s, t):
    if not t: return ()
    a, x, c = t
    out = [(v, Z, Z) for v in cutsHG(s, a)]
    if le(s, a): out += [(s, Z, Z)] + [(a, v, Z) for v in cutsHG(s, x)] + [(a, x, v) for v in cutsHG(s, c)]
    return tuple(out)
@functools.lru_cache(maxsize=20000)
def cutsNSG(s, t):
    if not t: return ()
    a, x, c = t
    return tuple([(v, Z, Z) for v in cutsHG(s, a)] + [(a, v, Z) for v in cutsHG(s, x)] + [(a, x, v) for v in cutsNSG(s, c)])
def ph3cKindG(B, hi, lo, s):
    if hi == B: return lo != Z
    return isprefix(B, hi) or (s != Z and B in cutsNSG(s, hi))

def value_fields(M, St, C, note):
    n = len(M)
    # Cons, with the Lean right-hand sides
    for i in range(n):
        cs = [C.cnt(i, c) for c in C.ch(i)]
        orhs = Y.sf((C.v(i), sumN(cs), Z))
        if M[i][1] == 0: vr = Z
        else:
            p = St.par(1, i); vp = C.v(p) if p is not None else Z
            if M[i][2] == 0:
                k = St.up[i]
                vr = Y.sf(Y.add(vp, Y.last(C.v(k)) if k is not None else ONE))
            else:
                vr = Y.sf(Y.add(vp, Y.omega(sumN([ONE] + [C.bumpTerm(i, j) for j in C.ch(i)]))))
        note('cons', C.o(i) == orhs and C.v(i) == vr, i)
    # Good3
    for i in range(n):
        note('good', isOT(C.o(i)) and isOT(C.v(i)) and dec([t for t in (C.cnt(i, d) for d in C.ch(i)) if t != Z]), i)
    # VSmallF (Lean form)
    for i in range(n):
        cl = C.CL(i); vi = C.v(i)
        for idx, c in enumerate(cl):
            B = spa(vi, sumN([C.o(d) for d in cl[:idx]])); vc = C.v(c)
            note('vs', all(le(g, (vc, Z, Z)) or le(g, B) for g in comps(vi, vc)), (i, c))
            s, y, _ = C.o(c)
            note('fo', isOT((vi, B, Z)), (i, c))
            trig = lt(B, y) and lt((vi, Z, Z), (s, y, Z))
            if trig:
                note('fc', frame_dom(vi, B, s, H(s, y)), (i, c))
                hi, lo = split(y, (succ(s), Z, Z))
                if B != Z: note('ph', ph3cKindG(B, hi, lo, s), (i, c))
                if idx == 0 and y != Z and hi != Z:
                    if s == vi: ok = s != Z and last(s) != ONE
                    else:
                        L = lev(hi); ok = False; t = L
                        while t:
                            if P.app(s, t) == L: ok = True
                            t = t[2]
                    note('fc3', ok, (i, c))
        # TP1C / TP1WC: every counted child, state over all earlier children
        chs = C.ch(i)
        for idx, c in enumerate(chs):
            if not C.counted(i, c): continue
            Pst = C.pre(i, chs[:idx]); s, y, _ = C.o(c)
            if not (lt(Pst, y) and lt((vi, Z, Z), (s, y, Z))): continue
            if ohole(y):
                note('tp1', lt(Pst, fsD(y, (holelev(y), ONE, Z))), (i, c))
                if cof(y)[0] == 'omega': note('tp1w', lt(Pst, fsD(y, ONE)), (i, c))
        if C.e12(i):
            for j in chs:
                if tuple(M[j]) == C.e.bump(i): note('kd', dec([C.o(k) for k in C.ch(j)]), (i, j))
            note('td', dec([t for t in (C.bumpTerm(i, j) for j in chs) if t != Z]), i)
    roots = [i for i in range(n) if tuple(M[i]) == (0, 0, 0)]
    for r in roots: note('rootS', single(C.o(r)), r)
    note('rootP', dec([C.o(r) for r in roots]), ())

# probe counters -> field names
MAP7 = {'AbsDS': 'ads', 'AbsUWL': 'auwl', 'AbsUW0': 'auw0', 'TPLoN': 'tplon', 'AbsDN': 'adn'}
MAP2 = {'AbsUS': 'aus', 'TPLoS': 'tplos', 'VSmallRAll': 'vra'}
MAPS = {'TPLoW': 'tplow', 'AbsDW': 'adw'}
def from_probe(cc, ee, mp, note_bulk, M):
    for k, f in mp.items():
        c = cc.get(k + '.cases', 0); fl = cc.get(k + '.failures', 0)
        if c: note_bulk(f, c, fl, ee.get(k))

def audit(M):
    M = [tuple(c) for c in M]
    cnt = collections.Counter(); ex = {}
    seen = set(); fseen = set()
    def note(f, ok, info):
        cnt[f + '.cases'] += 1
        if f not in seen: seen.add(f); cnt[f + '.mats'] += 1
        if not ok:
            cnt[f + '.fail'] += 1
            if f not in fseen:
                fseen.add(f); cnt[f + '.fmats'] += 1; ex[f] = (len(M), M, repr(info)[:300])
    def note_bulk(f, c, fl, e):
        cnt[f + '.cases'] += c
        if f not in seen: seen.add(f); cnt[f + '.mats'] += 1
        if fl:
            cnt[f + '.fail'] += fl
            if f not in fseen: fseen.add(f); cnt[f + '.fmats'] += 1; ex[f] = (len(M), M, repr(e)[:300])
    cnt['input'] += 1
    St = structural(M, note)
    rk = rank_ok(St); note('rank', rk, ())
    C = ctx(M)
    if C.ok != rk: cnt['internal.rank_vs_eval'] += 1
    for i in range(len(M)):
        if St.par(0, i) != C.e.par(0, i) or St.par(1, i) != C.e.par(1, i) or St.up[i] != C.upg(i) or \
           St.children[i] != C.ch(i):
            cnt['internal.struct_mismatch'] += 1; break
    if not C.ok:
        cnt['eval_failed'] += 1; return cnt, ex
    value_fields(M, St, C, note)
    try:
        cc, ee = R.measure(M); from_probe(cc, ee, MAP7, note_bulk, M)
        for k, v in cc.items():
            if 'internal' in k or 'seed_eval_failed' in k: cnt['frame7.' + k] += v
        cc, ee = I.measure(M); from_probe(cc, ee, MAP2, note_bulk, M)
        cc, ee = G.measure_trigS0(M)
        if cc.get('TrigS0.cases'): note_bulk('trigs', cc['TrigS0.cases'], cc.get('TrigS0.failures', 0), ee.get('TrigS0'))
        cc, ee = hframe_s.measure_s(M); from_probe(cc, ee, MAPS, note_bulk, M)
    except Exception as e:
        cnt['harness_exception'] += 1; ex.setdefault('harness_exception', (len(M), M, repr(e)[:300]))
    return cnt, ex

KEEP = 20
def merge(ex, e):
    """ex[k] = sorted list of the KEEP smallest (len, M, info) failing instances (one per matrix)."""
    for k, v in e.items():
        L = ex.setdefault(k, [])
        for w in (v if isinstance(v, list) else [v]):
            if all(w[1] != u[1] for u in L): L.append(w)
        L.sort(key=lambda w: (w[0], w[1])); del L[KEEP:]

def work(batch):
    cnt = collections.Counter(); ex = {}
    for M in batch:
        try: c, e = audit(M)
        except Exception as err:
            c = collections.Counter(harness_exception=1); e = {'harness_exception': (len(M), [tuple(x) for x in M], repr(err)[:300])}
        cnt.update(c); merge(ex, e)
    return cnt, ex

def load(f):
    d = pickle.load(open(f, 'rb'))
    if isinstance(d, dict): d = d['seeds'] + d['ext'] if 'seeds' in d else list(d.values())
    return d

def ms(M): return ''.join('(%d,%d,%d)' % tuple(c) for c in M)
SHARD = 200000
if __name__ == '__main__':
    out = sys.argv[1]; npr = int(sys.argv[2])
    done = set()
    if os.path.exists(out):
        for line in open(out): r = json.loads(line); done.add((r['set'], r['shard']))
    for f in sys.argv[3:]:
        mats = load(f)
        for sh in range(0, max(1, len(mats)), SHARD):
            if (f, sh) in done: continue
            t = time.time(); part = mats[sh:sh + SHARD]
            cnt = collections.Counter(); ex = {}
            with Pool(npr) as pool:
                for c, e in pool.imap_unordered(work, (part[i:i + 50] for i in range(0, len(part), 50))):
                    cnt.update(c); merge(ex, e)
            rec = {'set': f, 'shard': sh, 'n': len(part), 'total': len(mats), 'sec': round(time.time() - t),
                   'cnt': dict(sorted(cnt.items())),
                   'ex': {k: [(w[0], ms(w[1]), w[2]) for w in L] for k, L in ex.items()}}
            with open(out, 'a') as fo: fo.write(json.dumps(rec) + '\n')
            print(json.dumps({'set': os.path.basename(f), 'shard': sh, 'n': len(part), 'sec': rec['sec'],
                              'fails': {k: v for k, v in cnt.items() if k.endswith('.fail') or 'exception' in k or 'internal' in k or 'eval_failed' in k}}), flush=True)
        del mats
