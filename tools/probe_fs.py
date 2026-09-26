# -*- coding: utf-8 -*-
"""Fundamental sequences of the Buchholz-style D-terms against BM4 expansion.

Every summand w^e of a (lowered) label is a D-term D_v(a): v is its level (lvl, psi_{Omega_{u+1}}
at level u) and a = strip(e) is the argument its column's children spell. So a label is a D-tree:
a tuple of units (v, a) with v and a D-trees again, and () = 0, ((),()) = D_0 0 = 1.

  python3 tools/probe_fs.py calib      does gamma[n] (on the D side) equal S(gamma)[m] (BM4 on the
                                       sheet matrix) for sheet rows gamma, gamma[n]; which m - n
  python3 tools/probe_fs.py gen [N]    build every gap row by descending from the pure row above it
                                       with the same steps on both sides, and compare with the sheet
                                       (env OFF = m - n used for every step, ROWMAX = last row)

Status (notes 781): the FS needs four BM4-specific rules to mesh with expansion (g_0 = 0 for a
regular Omega, Omega_0 = 0, D_x(P + Omega_w)[m] = D_x(P + D_(x+m-1)(P)), results lowered); then
the sheet pairs below row ~421 all mesh. But m - n is not uniform, and gen loses its target on
most rows past 269, so gen matches only a few dozen gap rows. Work in progress.
"""
import os, re, sys
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.setrecursionlimit(20000)
import probe_eps_range as P
import trio

Z = ()
G0 = os.environ.get('G0', 'zero')
ITER_SHIFT = os.environ.get('ITER_SHIFT', '0') == '1'
AUTO = os.environ.get('AUTO', '0') == '1'
ONEU = (Z, Z)                                   # the unit D_0 0 = 1

# ---- labels -> D-trees ----
def from_ord(x):
    out = []
    for e, c in x:
        u = to_unit(e)
        out += [u] * c
    return tuple(out)

def to_unit(e):
    eo = P.ato(e)
    if eo == P.ZERO:
        return ONEU
    L = P._true_level(e)
    v = from_ord(L) if L else Z
    return (v, from_ord(P.strip(e)))

def to_ord(t):
    """The label a D-tree stands for (D_0 a = psi_0(a), D_v 0 = Omega_v, D_v a = psi_v(a))."""
    out = P.ZERO
    for v, a in t:
        if not v and not a: x = P.nat(1)
        elif not a: x = P.ato(P.Om(to_ord(v)))
        elif not v and P.lvl(to_ord(a)) is None:
            x = ((to_ord(a), 1),)                # D_0 a = w^a below the first Omega
        else: x = P.ato(P.Psi(to_ord(v), to_ord(a)))
        out = P.add(out, x) if out else x
    return out

def fsl(t, x):
    """t[x], lowered to the form a matrix writes (psi_1(Omega_3) is D_1 D_2 D_3 0)."""
    r = fs(t, x)
    try:
        return from_ord(P.lower(to_ord(r)))
    except Exception:
        return r

# ---- order ----
def cmp(a, b):
    for ua, ub in zip(a, b):
        c = cmp_u(ua, ub)
        if c: return c
    return (len(a) > len(b)) - (len(a) < len(b))

def cmp_u(u, w):
    c = cmp(u[0], w[0])
    return c if c else cmp(u[1], w[1])

# ---- successors, cofinality, fundamental sequences ----
def is_succ(t):
    return bool(t) and t[-1] == ONEU

def pred(t):
    return t[:-1]

def cof(t):
    """0, 1 (successor), 'w', or ('R', mu): Omega_mu regular (mu a successor)."""
    if not t: return 0
    return cof_u(t[-1])

def cof_u(u):
    v, a = u
    if not a:
        if not v: return 1
        if is_succ(v): return ('R', v)
        return cof(v)                           # Omega_v, v a limit: cof(v)
    c = cof(a)
    if c == 1 or c == 'w': return 'w'
    if cmp(c[1], v) <= 0: return c              # the argument's cofinality is at most Omega_v
    return 'w'

def fs(t, x):
    """t[x]: x an int for cofinality w, a D-tree for a regular Omega."""
    return t[:-1] + fs_u(t[-1], x)

def neg_add(x, v):
    """-x + v on labels (x <= v)."""
    while x:
        if P.cmp_exp(x[0][0], v[0][0]) < 0: return v
        if x[0][1] < v[0][1]: return ((v[0][0], v[0][1] - x[0][1]),) + v[1:]
        x, v = x[1:], v[1:]
    return v

def omega_limit_step(x, P_, v, n):
    """D_x(P + Omega_v)[n] for a limit v of cofinality w, as BM4 expands it:
    D_x(P + D_(x + (-x+v)[n])(P)), the inner collapse dropped when its level is <= x
    (D_1(Omega_w)[m] = D_1 D_2 .. D_m 0, D_0(Omega_w*2)[2] = D_0(Omega_w + D_1(Omega_w)))."""
    xo, vo = to_ord(x), to_ord(v)
    k = from_ord(neg_add(xo, vo)) if xo else v
    if not k or cof(k) != 'w':                  # v at the context's own level: Buchholz
        vx = fs(v, n)                           # Omega_v[n] = Omega_(v[n])
        return ((x, P_ + (((vx, Z),) if vx else Z)),)
    lv = from_ord(P.add(xo, to_ord(fs(k, n)))) if xo else fs(k, n)
    if cmp(lv, x) <= 0:
        return ((x, P_),)
    return ((x, P_ + ((lv, P_),)),)

BR = []

def fs_u(u, x):
    v, a = u
    if (a and not a[-1][1] and a[-1][0] and not is_succ(a[-1][0])
            and cof(a[-1][0]) == 'w' and isinstance(x, int)):
        BR.append('Wlim'); return omega_limit_step(v, a[:-1], a[-1][0], x)
    if not a:                                   # Omega_v
        if is_succ(v): BR.append('Rz'); return x     # Omega_(mu+1)[zeta] = zeta
        vx = fs(v, x)                           # Omega_v[x] = Omega_(v[x]), Omega_0 = 0
        return ((vx, Z),) if vx else Z
    c = cof(a)
    if c == 1: BR.append('succ'); return ((v, pred(a)),) * x   # D_v(a+1)[n] = D_v(a)*n
    if c == 'w' or cmp(c[1], v) <= 0: return ((v, fs(a, x)),)
    BR.append('iter')
    mu0 = pred(c[1])                            # cofinality Omega_(mu0+1) above Omega_v:
    g = ((mu0, Z),) if G0 == 'omega' else Z     # g_0 = Omega_mu0 (or 0), g_(n+1) = D_mu0 a[g_n]
    for _ in range(x - 1 if ITER_SHIFT and x > 0 else x):
        g = ((mu0, fs(a, g)),)
    return ((v, fs(a, g)),)

# ---- sheet ----
def cols(mat):
    cs = [tuple(int(v) for v in c.split(',')) for c in re.findall(r'\((\d+(?:,\d+)*)\)', mat)]
    return [c + (0,) * (3 - len(c)) for c in cs]

def smat(m): return ''.join('(%d,%d,%d)' % c for c in m)

def sheet():
    rows = []
    for L in open(os.path.join(HERE, '..', 'tmp', 'fixed-sheet', 'to-psi-I.tsv')):
        p = L.rstrip('\n').split('\t')
        if not p[0].isdigit() or not p[1].startswith('('): continue
        O = P.parse(p[3])
        if O is None: continue
        try:
            D = from_ord(P.lower(O))
        except Exception:
            continue
        rows.append((int(p[0]), p[3], O, D, cols(p[1])))
    return rows

def calib():
    rows = sheet()
    bykey = {r[3]: r for r in rows}
    off = Counter(); bad = []
    for r, lab, O, D, S in rows:
        if cof(D) != 'w': continue
        for n in range(0, 5):
            BR.clear()
            try: d = fsl(D, n)
            except Exception: continue
            if d not in bykey: continue
            T = bykey[d][4]
            ms = [m for m in range(0, 8) if trio.expand(S, m) == T]
            if ms: off[(BR[0] if BR else '?', ms[0] - n)] += 1
            else: bad.append((r, lab, n, bykey[d][0], bykey[d][1]))
    print('m - n:', dict(off), ' no m:', len(bad))
    for b in bad[:12]: print('  row %d %s  [%d] = row %d %s' % b)

def gen(nshow=10, off=int(os.environ.get('OFF', '1'))):
    rows = sheet()
    pure = set(int(l.split('\t')[0]) for l in open(os.path.join(HERE, 'omega_alpha_rows.tsv')) if l[0].isdigit())
    prow = sorted((r for r in rows if r[0] in pure), key=lambda r: r[0])
    cnt = Counter(); fails = []
    lim = int(os.environ.get('ROWMAX', '99999'))
    for r, lab, O, D, S in rows:
        if r in pure or r > lim: continue
        Q = next((q for q in prow if q[0] >= r), None)
        if Q is None: cnt['no pure above'] += 1; continue
        g, X = Q[3], P.block(P.lower(Q[2]), 0, 0, False)
        ok = None
        try:
          for _ in range(400):
              c = cmp(g, D)
              if c == 0: ok = X == S; break
              if c < 0: break
              k = cof(g)
              if k == 1:
                  g, X = pred(g), X[:-1]
              elif k == 'w':
                  n = next((n for n in range(0, 64) if cmp(fsl(g, n), D) >= 0), None)
                  if n is None: break
                  h = fsl(g, n)
                  m = n + off
                  if AUTO:                      # pick m by reading X[m] (here: the builder's
                      try:                      # matrix of h), only to choose among m's
                          want = P.block(P.lower(to_ord(h)), 0, 0, False)
                          m = next((k for k in (n, n + 1, n - 1, n + 2) if k >= 0
                                    and trio.expand(X, k) == want), m)
                      except Exception:
                          pass
                  g, X = h, trio.expand(X, m)
              else:
                  break
        except Exception:
            ok = None
        key = 'ok' if ok else ('ng' if ok is False else 'lost')
        cnt[key] += 1
        if key != 'ok': fails.append((r, lab, key, smat(S), smat(X)))
    print(dict(cnt))
    for f in fails[:nshow]:
        print(f[0], f[1], f[2]); print('   sheet', f[3][:170]); print('   got  ', f[4][:170])

if __name__ == '__main__':
    if sys.argv[1] == 'calib': calib()
    else: gen(int(sys.argv[2]) if len(sys.argv) > 2 else 10)
