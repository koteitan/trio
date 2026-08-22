# -*- coding: utf-8 -*-
"""The eps_0 <= alpha range: ordinal arithmetic with the atom E = eps_0, plus M(alpha).

This replaces build_omega_alpha.py's PrSS by `block`, which copies the Buchholz OT term of
the exponent verbatim, and adds the uncollapse in the argument position of psi_0 (a leading
E becomes an Omega_1 leaf). Of the 135 sheet rows whose alpha is w-CNF plus the E atom, 131
match (the other 4 are the known mismatch rows 1947 / 2113 / 2131 / 2133). This module is
also the builder the build_omega_alpha.py CLI delegates to above eps_0. Its own CLI mirrors
build_omega_alpha.py:

  python3 probe_eps_range.py 'psi_0(W)^psi_0(W)'  print psi_0(W_alpha)
  python3 probe_eps_range.py 'psi_0(W)+w^2' 2     also print the expansion
  python3 probe_eps_range.py                      validation mode
"""
import re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trio import expand

# Ord = tuple((exp, coeff), ...) in decreasing order; exp is an Ord or 'E'.
ZERO = ()
E_EXP = 'E'
E = ((E_EXP, 1),)

def has_E(x):
    if x == E_EXP: return True
    if x == ZERO: return False
    return any(has_E(e) for e, _ in x)

def cmp_exp(a, b):
    if a == E_EXP and b == E_EXP: return 0
    if a == E_EXP:
        if not has_E(b): return 1
        return 0 if b == E else -1
    if b == E_EXP:
        if not has_E(a): return -1
        return 0 if a == E else 1
    return cmp_ord(a, b)

def cmp_ord(a, b):
    for (ea, ca), (eb, cb) in zip(a, b):
        c = cmp_exp(ea, eb)
        if c: return c
        if ca != cb: return -1 if ca < cb else 1
    return (len(a) > len(b)) - (len(a) < len(b))

def add(a, b):
    if not b: return a
    lead = b[0][0]
    keep = [t for t in a if cmp_exp(t[0], lead) > 0]
    same = [t for t in a if cmp_exp(t[0], lead) == 0]
    if same:
        return tuple(keep) + ((lead, same[0][1] + b[0][1]),) + b[1:]
    return tuple(keep) + b

def wpow(x):
    return ((x, 1),)

def nat(n):
    return ((ZERO, n),) if n else ZERO

def mul(a, b):
    if not a or not b: return ZERO
    e1 = a[0][0]
    out = ZERO
    for e, c in b:
        if e == ZERO:
            out = add(out, ((e1, a[0][1] * c),) + a[1:])
        else:
            out = add(out, ((add_exp(e1, e), c),))
    return out

def add_exp(x, y):
    xo = E if x == E_EXP else x
    yo = E if y == E_EXP else y
    return add(xo, yo)

def power(a, b):
    if b == ZERO: return nat(1)
    if a == nat(1): return nat(1)
    if b == nat(1): return a
    # a finite exponent is repeated multiplication
    if len(b) == 1 and b[0][0] == ZERO:
        r = a
        for _ in range(b[0][1] - 1): r = mul(r, a)
        return r
    e1 = a[0][0]
    if e1 == ZERO:                       # a finite base
        return wpow(b_pred(b))
    return wpow(mul(E if e1 == E_EXP else e1, b))

def b_pred(b):
    return b

# ---- Parser: w, digits, E (= psi(W)), + * ^ ( ) ----
TOK = re.compile(r'psi\(W\)|w|\d+|[+*^()]')
def parse(s):
    s = canon(s.replace(' ', ''))
    toks = TOK.findall(s)
    if ''.join(toks) != s: return None
    pos = 0
    def peek(): return toks[pos] if pos < len(toks) else None
    def eat():
        nonlocal pos; t = toks[pos]; pos += 1; return t
    def atom():
        t = eat()
        if t == '(':
            e = expr(); assert eat() == ')'; return e
        if t == 'w': return wpow(nat(1))
        if t == 'psi(W)': return E
        return nat(int(t))
    def pw():
        b = atom()
        if peek() == '^': eat(); return power(b, pw())
        return b
    def term():
        f = pw()
        while peek() == '*' or (peek() and re.fullmatch(r'\d+', peek())):
            if peek() == '*': eat()
            f = mul(f, pw())
        return f
    def expr():
        e = term()
        while peek() == '+':
            eat(); e = add(e, term())
        return e
    try:
        e = expr()
        return e if pos == len(toks) else None
    except Exception:
        return None

# ---- The builder ----
def units(a):
    return [e for e, c in a for _ in range(c)]

def pred_beta(beta):
    """The beta' with 1 + beta' = beta."""
    if beta == ZERO: return ZERO
    if beta[0][0] == ZERO:
        k = beta[0][1]
        return nat(k - 1)
    return beta

def block(gamma, x):
    """Copy the Buchholz OT term of gamma into columns verbatim.

    For each summand w^delta place a psi_0 node (x,0,0) and write its argument arg(delta)
    at x+1 as its children. arg carries the uncollapse:
      delta = E*c + rest -> the Omega_1 leaf (x,1,0) ++ block(E*(c-1)+rest)
      otherwise          -> block(delta)
    Why: for delta < eps_0 we have w^delta = psi_0(delta), so the copy is direct. For
    delta >= eps_0 the leading E turns back into Omega_1 (the uncollapse).
    """
    if gamma == ZERO: return []
    cols = []
    for e, c in gamma:
        for _ in range(c):
            cols.append((x, 0, 0))
            cols += arg(e, x + 1)
    return cols

def arg(delta, x):
    """How the argument of psi_0 is written (uncollapse included). delta is an exp."""
    if delta == E_EXP:
        return [(x, 1, 0)]
    if delta == ZERO:
        return []
    if delta[0][0] == E_EXP:
        c = delta[0][1]
        rest = ((E_EXP, c - 1),) + delta[1:] if c > 1 else delta[1:]
        return [(x, 1, 0)] + block(rest, x)
    return block(delta, x)

def body(beta, x0, y):
    cols = [(x0, y, 1)]
    for e, c in pred_beta(beta):
        for _ in range(c):
            cols.append((x0 + 1, y, 1))
            cols += block(E if e == E_EXP else e, x0 + 2)   # a digit's children = gamma
    return cols

def M(alpha):
    us = units(alpha)
    cols = []; level = 0; root_x = -1; prev0 = False
    for b in us:
        beta = E if b == E_EXP else b
        if beta == ZERO and prev0:
            tx, ty, _ = cols[-1]; cols.append((tx + 1, ty + 1, 0))
        elif beta == ZERO:
            cols.append((root_x + 1, level, 0)); cols.append((root_x + 2, level + 1, 0))
        else:
            ax = root_x + 1
            cols.append((ax, level, 0))
            cols += body(beta, ax + 1, level + 1)
            root_x = ax + 1
        level += 1
        prev0 = (beta == ZERO)
    return cols

# ---- Validation ----
def mat(s):
    cs = [tuple(int(v) for v in x.split(',')) for x in re.findall(r'\((\d+(?:,\d+)*)\)', s)]
    return [c + (0,) * (3 - len(c)) for c in cs]

# ---- Large alpha: the psi_0(X) and Omega_v atoms ----
def _toplevel_ops(t):
    d = 0
    for ch in t:
        d += (ch == '(') - (ch == ')')
        if d == 0 and ch in '+*^': return True
    return False

def canon(t):
    """Rewrite the input sugar into the canonical psi(...) form.

    psi_0( / p_0( / p(  ->  psi(   (psi_1( and other v>0 collapses are left alone)
    """
    return (t.replace('psi_0(', 'psi(')
             .replace('p_0(', 'psi(')
             .replace('p(', 'psi('))

def big_parse(t):
    """'psi(W)' / 'psi(W_X)' / 'W' / 'W_X' -> ('psi'|'om', the X string).

    Returns None when an operator sits outside the subscript X, as in W_2^2 = (Omega_2)^2.
    """
    t = canon(t.strip())
    while t.startswith('(') and t.endswith(')') and not _toplevel_ops(t[1:-1]):
        inner = t[1:-1]
        d = 0; ok = True
        for ch in inner:
            d += (ch == '(') - (ch == ')')
            if d < 0: ok = False; break
        if not ok or d != 0: break
        t = inner
    if _toplevel_ops(t): return None
    if t == 'W': return ('om', '1')
    if t == 'psi(W)': return ('psi', '1')
    if t.startswith('W_') and not _toplevel_ops(t[2:]):
        return ('om', t[2:])
    if t.startswith('psi(W_') and t.endswith(')') and not _toplevel_ops(t[6:-1]):
        return ('psi', t[6:-1])          # W_X^2 is arithmetic on Omega_X, not a subscript
    return None

def Many(t):
    """M(alpha) for the string t; accepts both the large atoms and w-CNF plus E."""
    b = big_parse(t)
    if b:
        kind, v = b
        if kind == 'om':
            return M_Omega(v)
        vm = Many(v)
        if vm is None: return None
        # M(psi_0(Omega_X)) = (0,0,0)(1,1,1)(2,1,1) ++ shift(M(X), 3)。
        # the shifted anchor of M(X) is the psi_0 node (3,0,0) itself.
        return [(0, 0, 0), (1, 1, 1), (2, 1, 1)] + [(c[0] + 3, c[1], c[2]) for c in vm]
    a = parse(t)
    if a in (None, ZERO): return None
    return M(a)

# ---- alpha = Omega_v: a second storey built out of B ----
BASE_B = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0)]   # = M(Omega_1)

def lift(cols, k=1):
    return [(c[0] + k, c[1] + k, c[2]) for c in cols]

def _forest(cols):
    par = [None] * len(cols); kids = [[] for _ in cols]
    for i in range(len(cols)):
        for j in range(i - 1, -1, -1):
            if cols[j][0] < cols[i][0]:
                par[i] = j; kids[j].append(i); break
    return par, kids

def _is_level(cols, par, i):
    """Is this a level column (an anchor or a +1 marker)? Omega leaves and psi_0 nodes
    are excluded."""
    x, y, z = cols[i]
    if z != 0 or y < 1: return False
    p = par[i]
    if p is None: return True
    if cols[p][2] == 0:
        # a parent that is a psi_0 node (a z0 column with y=0, other than the root
        return not (p != 0 and cols[p][1] == 0)
    gp = par[p]
    return gp is None or cols[gp][2] == 0           # parent is a root -> level; a digit -> leaf

def M_Omega(v):
    """M(Omega_v): insert B's tail below every level column of M(v) and drop a trailing
    level column."""
    cols = Many(v)
    if cols is None: return None
    par, kids = _forest(cols)
    lev = {i for i in range(len(cols)) if _is_level(cols, par, i)}
    drop = len(cols) - 1 if (len(cols) - 1) in lev else None
    out = []
    def dfs(i, d):
        if i == drop: return
        out.append((d, cols[i][1], cols[i][2]))
        if i in lev or i == 0:                       # the root anchor also takes a B
            y0 = cols[i][1]
            for k, (dy, z) in enumerate(((1, 1), (1, 1), (1, 0))):
                out.append((d + 1 + k, y0 + dy, z))
        for c in kids[i]: dfs(c, d + 1)
    dfs(0, 0)
    return out

def M_Omega_fin(v):
    """The closed form for finite v (agrees with M_Omega): B ++ L(B) ++ ... ++ L^{v-1}(B)."""
    out = []
    for k in range(v): out += lift(BASE_B, k)
    return out

def run_omega():
    tsv = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'omega_alpha_rows.tsv')
    ok = ng = skip = 0; bad = []
    for L in open(tsv):
        p = L.rstrip('\n').split('\t')
        if p[0] == 'row': continue
        b = big_parse(p[1])
        if not b or b[0] != 'om': continue
        got = M_Omega(b[1])
        if got is None: skip += 1; continue
        if got == mat(p[3]): ok += 1
        else:
            ng += 1
            if len(bad) < 6: bad.append((p[0], b[1], p[3], got))
    print('alpha = Omega_v: %d match / %d mismatch / %d subscript unsupported' % (ok, ng, skip))
    for r, v, w, g in bad:
        print(' NG row %s v=%s' % (r, v))
        print('   sheet:', w)
        print('   built:', ''.join('(%d,%d,%d)' % c for c in g))
    # finite v also agrees with the closed form
    for v in range(1, 7):
        assert M_Omega(str(v)) == M_Omega_fin(v), v
    return ng

def run_big():
    tsv = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'omega_alpha_rows.tsv')
    ok = ng = skip = 0; bad = []
    for L in open(tsv):
        p = L.rstrip('\n').split('\t')
        if p[0] == 'row': continue
        if not big_parse(p[1]): continue
        got = Many(p[1])
        if got is None: skip += 1; continue
        kind, _ = big_parse(p[1])
        if kind == 'om' and p[1].strip() not in ('W', '(W)'):
            skip += 1; continue          # Omega_v (v>=2) is a different regime
        want = mat(p[3])
        if got == want: ok += 1
        else:
            ng += 1
            if len(bad) < 8: bad.append((p[0], p[1], want, got))
    print('large atoms (psi(W_X) / W_X): %d match / %d mismatch / %d subscript unsupported'
          % (ok, ng, skip))
    for r, t, w, g in bad:
        print(' row %s a=%s' % (r, t))
        print('   sheet:', ''.join('(%d,%d,%d)' % c for c in w))
        print('   built:', ''.join('(%d,%d,%d)' % c for c in g))
    return ng

KNOWN_MISMATCH = {'1947', '2113', '2131', '2133'}

USAGE = """\
usage: python3 probe_eps_range.py [alpha] [n]

  alpha  the notation of build_omega_alpha.py (w / digits / + * ^ / parentheses)
         plus the atom psi_0(W) = eps_0. Example: 'psi_0(W)^psi_0(W)+w^2'
         Sugar: psi( , p( and p_0( may be written for psi_0( .
  n      optional; also print the expansion psi_0(W_alpha)[n].
  (none) validation mode (check against the sheet).
"""

def run_check():
    ok = ng = skip = known = 0; bad = []
    tsv = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'omega_alpha_rows.tsv')
    for L in open(tsv):
        p = L.rstrip('\n').split('\t')
        if p[0] == 'row': continue
        a = parse(p[1])
        if a in (None, ZERO): skip += 1; continue
        want = mat(p[3]); got = M(a)
        if got == want: ok += 1
        elif p[0] in KNOWN_MISMATCH: known += 1
        else:
            ng += 1
            if len(bad) < 8: bad.append((p[0], p[1], want, got))
    print('alpha in w-CNF + E: %d match / %d unexpected mismatch / %d known mismatch'
          ' / %d unparsed'
          % (ok, ng, known, skip))
    for r, t, w, g in bad:
        print(' row %s a=%s' % (r, t))
        print('   sheet:', ''.join('(%d,%d,%d)' % c for c in w))
        print('   built:', ''.join('(%d,%d,%d)' % c for c in g))
    assert ng == 0
    assert run_big() == 0
    run_omega()

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] in ('-h', '--help'):
        print(USAGE)
    elif len(sys.argv) > 1:
        cols = Many(sys.argv[1])
        if cols is None:
            print('parse error; run --help for the accepted notation.'); sys.exit(1)
        head = 'psi_0(W_{%s})' % sys.argv[1]
        print('%s = %s' % (head, ''.join('(%d,%d,%d)' % c for c in cols)))
        if len(sys.argv) > 2:
            n = int(sys.argv[2])
            print('%s[%d] = %s' % (head, n, ''.join('(%d,%d,%d)' % tuple(c)
                                                    for c in expand(cols, n))))
    else:
        run_check()
