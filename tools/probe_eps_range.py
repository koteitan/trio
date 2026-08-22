# -*- coding: utf-8 -*-
"""M(alpha) = the standard form of psi_0(Omega_alpha), for alpha up to the Omega arithmetic.

Ordinals are ordinary base-w CNFs over two families of atoms, both of them fixed points of
x -> w^x that the CNF cannot decompose:

  Omega_v   the v-th uncountable cardinal    ('W', v)
  psi_v(X)  a collapse                       ('psi', v, X)   (E = eps_0 = psi_0(Omega_1))

The matrix side has three rules:

  unit_loop  alpha = w^{beta_1} + ... + w^{beta_m}: one add unit per summand, each an
             anchor plus a body (a z1 root and one digit per summand of beta_i').
  block      a summand w^delta becomes ONE column whose children spell out delta. Its row-1
             entry names the level: 0 for a countable psi_0 node, v for Omega_v. Row 1
             repeats row 0 one storey up, with Omega_v in the place of 1.
  M          alpha >= Omega_v is built on top of M(Omega_v): the units are laid out one
             storey higher, starting at the base's last z1 root.

The level a column names is its position in the chain of z0 ancestors, not the bare entry,
so a unit's leaf names it in one column while a collapse argument spells the whole subscript
out (the "emergent address"). A leaf that ends the matrix takes a suffix that says which
limit level it was -- the upgrade effect. Of the sheet's 813 rows the builder reproduces
603; dom.md lists what the other 210 need. The CLI mirrors build_omega_alpha.py:

  python3 probe_eps_range.py 'psi_0(W)^psi_0(W)'  print psi_0(W_alpha)
  python3 probe_eps_range.py 'W_2+W*w' 2          also print the expansion
  python3 probe_eps_range.py                      validation mode
"""
import re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trio import expand

class Unsupported(Exception):
    """A shape the builder does not write yet (an infinite Omega subscript in a place where
    the surrounding chain does not already spell it out)."""

# ---- Ord = tuple((exp, coeff), ...) in decreasing order; exp is an Ord or an atom ----
ZERO = ()

def is_atom(x):
    return bool(x) and isinstance(x[0], str)

def nat(n):
    return ((ZERO, n),) if n else ZERO

ONE = nat(1)
def Om(v): return ('W', v)                     # Omega_v
def Psi(v, X): return ('psi', v, X)            # psi_v(X)

OM_EXP = Om(ONE)
OM = ((OM_EXP, 1),)                            # Omega_1
E_EXP = Psi(ZERO, OM)
E = ((E_EXP, 1),)                              # eps_0 = psi_0(Omega_1)

def ato(x):
    """The Ord an exponent denotes. w^atom = atom, so an atom is its own w-power."""
    return ((x, 1),) if is_atom(x) else x

def cmp_atom(a, b):
    if a[0] == 'W' and b[0] == 'W': return cmp_ord(a[1], b[1])
    if a[0] == 'W':                            # Omega_v vs psi_u(X): Omega_u < psi_u(X)
        return 1 if cmp_ord(a[1], b[1]) > 0 else -1
    if b[0] == 'W':
        return -cmp_atom(b, a)
    c = cmp_ord(a[1], b[1])                    # psi_v vs psi_u: the level decides first
    return c if c else cmp_ord(a[2], b[2])

def cmp_exp(a, b):
    if is_atom(a) and is_atom(b): return cmp_atom(a, b)
    return cmp_ord(ato(a), ato(b))

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
    return add(ato(x), ato(y))

def power(a, b):
    if b == ZERO: return ONE
    if a == ONE: return ONE
    if b == ONE: return a
    # a finite exponent is repeated multiplication
    if len(b) == 1 and b[0][0] == ZERO:
        r = a
        for _ in range(b[0][1] - 1): r = mul(r, a)
        return r
    e1 = a[0][0]
    if e1 == ZERO:                             # a finite base
        return wpow(b)
    return wpow(mul(ato(e1), b))

# ---- Parser: w, digits, W[_sub], psi[_sub]( ), + * ^ ( ) ----
TOK = re.compile(r'psi|w|W|\d+|[+*^()_]')

def canon(t):
    """Rewrite the input sugar into the canonical psi form: p( / p_ -> psi( / psi_ ."""
    return re.sub(r'(?<![A-Za-z])p(?=[_(])', 'psi', t)

def parse(s):
    s = canon(s.replace(' ', ''))
    toks = TOK.findall(s)
    if ''.join(toks) != s: return None
    pos = 0
    def peek(): return toks[pos] if pos < len(toks) else None
    def eat():
        nonlocal pos; t = toks[pos]; pos += 1; return t
    def sub():
        """A subscript binds tight: W_w*2 is (Omega_w)*2, W_W_w is Omega_{Omega_w}."""
        assert eat() == '_'
        return atom()
    def atom():
        t = eat()
        if t == '(':
            e = expr(); assert eat() == ')'; return e
        if t == 'w': return wpow(ONE)
        if t == 'W': return ato(Om(sub() if peek() == '_' else ONE))
        if t == 'psi':
            v = sub() if peek() == '_' else ZERO
            assert eat() == '('
            x = expr(); assert eat() == ')'
            return ato(Psi(v, x))
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

def lvl(x):
    """The Omega level of x as an Ord (Omega_v <= x < Omega_{v+1}), None when x is
    countable. The leading exponent decides it, since a CNF is decreasing."""
    if is_atom(x):
        if x[0] == 'W': return x[1]
        return x[1] if x[1] != ZERO else None      # psi_v(X) sits in [Omega_v, Omega_{v+1})
    if x == ZERO: return None
    return lvl(x[0][0])

def fin(v):
    """v as a natural number, or None when it is infinite."""
    if v == ZERO: return 0
    return v[0][1] if len(v) == 1 and v[0][0] == ZERO else None

def strip(delta):
    """The ordinal the children of delta's column spell out.

    The column already names delta's leading atom, so the children carry what is left:
      psi_v(X)*c + rest -> X + psi_v(X)*(c-1) + rest   (the uncollapse: the argument of the
                           collapse takes the place of the collapse itself)
      Omega_v*c + rest  -> Omega_v*(c-1) + rest        (the level is cancelled)
      anything else     -> delta itself                (nothing to cancel: either delta is
                           below eps_0, or its head absorbs the level)
    """
    d = ato(delta)
    if d == ZERO: return ZERO
    h, c = d[0]
    rest = (((h, c - 1),) if c > 1 else ()) + d[1:]
    if is_atom(h) and h[0] == 'psi': return add(h[2], rest)
    if is_atom(h) and h[0] == 'W': return rest
    return d

def write_level(v, x, d, arg=False):
    """The columns that name the level Omega_v at x, for a column at chain depth d.

    A unit's leaf (arg=False) only names the level, and one column does that: the row-1
    entry of M(v)'s last column. What that loses -- Omega_w and Omega_1 both leave a leaf
    at y=1 -- the suffix in append_suffix puts back.

    In the argument of a collapse (arg=True) the level is spelt out instead, by M(v)
    itself: the chain of z0 ancestors already provides M(v)'s first 1+k columns (k = how
    far the plain staircase of anchors agrees with M(v)), so only M(v)[1+k:] is written.
    The d-k ancestor levels the context spends on something else push the copy that much
    deeper, so every entry whose row-1 value tracks the unit level is raised by d-k; the
    ones naming an absolute level (Omega leaves, psi nodes) keep theirs.
    """
    base = M(v)
    if not arg:
        # A unit's leaf only has to name the level, and one column does that: the row-1
        # entry of M(v)'s last column, with z=0 (the level itself, not its spelling).
        return [(x, base[-1][1], 0)]
    k = 0
    while k < d and k + 1 < len(base) and base[k + 1] == (k + 1, k + 1, 0): k += 1
    tail = base[1 + k:]
    if not tail:                                 # the chain already spells v out
        return [(x, base[-1][1], 0)]
    par, _ = _forest(base)
    bump = d - k
    return [(c[0] + x - 1 - k, c[1] + (bump if _relative(base, par, 1 + k + i) else 0), c[2])
            for i, c in enumerate(tail)]

def block(gamma, x, d=0, arg=False):
    """Copy the ordinal gamma into columns: one column per summand w^delta of gamma, and
    the children of that column spell out strip(delta).

    d is the level the surrounding chain of z0 ancestors already reaches, and arg says the
    columns are the argument of a collapse (the uncollapse). A countable summand is the
    single psi_0 node (x,0,0); an uncountable one names its level through write_level.
    """
    cols = []
    for e, c in gamma:
        eo = ato(e)
        h = eo[0][0] if eo else None
        for _ in range(c):
            v = lvl(e)
            run = [(x, 0, 0)] if v is None else write_level(v, x, d, arg)
            cols += run
            # the children of a collapse are its argument, written one level up
            cols += block(strip(e), run[-1][0] + 1, run[-1][1],
                          is_atom(h) and h[0] == 'psi')
    return cols

def body(beta, x0, y):
    """The body of an add unit w^beta at level y: the z1 root and one digit per summand of
    beta', each digit followed by the block of that summand's exponent."""
    cols = [(x0, y, 1)]
    for e, c in pred_beta(beta):
        for _ in range(c):
            cols.append((x0 + 1, y, 1))
            cols += block(ato(e), x0 + 2, y - 1)     # the anchor's level is y-1
    return cols

def suffix(v):
    """The trailing z1 columns of M(v) (the part after its last z0 column).

    A limit level is named by the same leaf as the level with the same last row-1 entry
    (Omega_w and Omega_1 both leave a leaf at y=1), and this suffix is what tells them
    apart. It only shows up when the leaf ends the matrix -- the upgrade effect: anything
    written after the leaf absorbs it.
    """
    cols = M(v)
    i = max(j for j in range(len(cols)) if cols[j][2] == 0)
    return cols[i + 1:]

def append_suffix(cols, v):
    """Append the upgrade suffix for level v, copied from where v is already spelt.

    The suffix repeats the marker run that names v, so it lands at the x of the run
    already in the matrix; M(v)'s own x is the fallback."""
    suf = suffix(v)
    if not suf: return cols
    n = len(suf)
    pat = [(c[1], c[2]) for c in suf]
    dx = [c[0] - suf[0][0] for c in suf]
    for i in range(len(cols) - n, -1, -1):
        seg = cols[i:i + n]
        if ([(c[1], c[2]) for c in seg] == pat
                and [c[0] - seg[0][0] for c in seg] == dx):
            return cols + seg
    return cols + suf

def tail_level(alpha):
    """The level named by the very last column of M(alpha), or None."""
    us = units(alpha)
    if not us: return None
    beta = ato(us[-1])
    bp = pred_beta(beta)
    if beta == ZERO or bp == ZERO: return None    # a +1 marker or a bare root ends it
    return _tail_block(ato(bp[-1][0]), False)

def _tail_block(gamma, arg):
    """The level of the last column block(gamma, .., arg) writes, or None. A column
    written inside a collapse argument spells its level out, so it takes no suffix."""
    if gamma == ZERO: return None
    e = gamma[-1][0]
    rest = strip(e)
    if rest != ZERO:                              # the children are written after it
        h = ato(e)[0][0]
        return _tail_block(rest, is_atom(h) and h[0] == 'psi')
    return None if arg else lvl(e)

def leaf_y(v):
    """The row-1 entry a leaf naming level v carries."""
    return M(v)[-1][1]

def storey(cols, y):
    """The lifted copy of cols that psi_0(Omega_b + psi_1(Omega_b)) puts on top of
    M(b) = cols: every column one level deeper, with the final leaf naming level y."""
    out = lift(cols)
    out[-1] = (out[-1][0], y, out[-1][2])
    return out

def unit_tail_level(beta):
    """The level named by the last column of the add unit w^beta, or None."""
    bp = pred_beta(beta)
    if beta == ZERO or bp == ZERO: return None
    return _tail_block(ato(bp[-1][0]), False)

def needs_storey(prev, regime):
    """Does a storey have to come before the next add unit?

    Under a limit regime the ladder of anchors reads Omega_regime, Omega_{regime+1}, ...,
    so a leaf there can only name the regime's own level or the bottom one. Once a unit has
    named anything else the ladder has to be laid again, and the lifted copy lays it.
    """
    return (regime is not None and prev is not None and cmp_ord(prev, regime) != 0
            and suffix(regime) and leaf_y(prev) == leaf_y(regime))

def place_units(cols, alpha, level, root_x, regime=None):
    """Lay alpha's add units out after cols, starting at the given level and root x.

    Three things interrupt the plain loop, all of them in a limit regime, and all of them
    storeys -- lifted copies of the matrix so far (of the last storey, once there is one):
      * a leaf only reaches as deep as the regime's own leaf, so naming a level whose leaf
        is deeper takes one storey per extra step;
      * once a leaf has named a level that shares the regime's leaf, the ladder is spent
        and the next add unit needs a fresh one;
      * the same holds between the digits of one add unit.
    """
    st = 0
    def add_storey(cols, st, y):
        return cols + storey(cols[st:], y), len(cols)
    def spent(u):
        return (regime is not None and u is not None and cmp_ord(u, regime) != 0
                and suffix(regime) and leaf_y(u) == leaf_y(regime))
    prev0 = False; prev = None; first = True
    for b in units(alpha):
        beta = ato(b)
        if not first and spent(prev):
            cols, st = add_storey(cols, st, cols[-1][1])
            level, root_x = last_root_plain(cols)
            prev0 = False
        if beta == ZERO and prev0:
            tx, ty, _ = cols[-1]; cols = cols + [(tx + 1, ty + 1, 0)]
        elif beta == ZERO:
            cols = cols + [(root_x + 1, level, 0), (root_x + 2, level + 1, 0)]
        else:
            ax = root_x + 1
            x0, y = ax + 1, level + 1
            cols = cols + [(ax, level, 0), (x0, y, 1)]        # anchor and z1 root
            digits = [e for e, c in pred_beta(beta) for _ in range(c)]
            for i, e in enumerate(digits):
                if i and spent(prev):                         # the ladder is spent mid-unit
                    cols, st = add_storey(cols, st, cols[-1][1])
                    y, x0 = last_root_plain(cols)
                cols = cols + [(x0 + 1, y, 1)] + block(ato(e), x0 + 2, y - 1)
                prev = _tail_block(ato(e), False)
            root_x = x0
        level += 1
        prev0 = (beta == ZERO)
        prev = unit_tail_level(beta)
        if prev is not None and regime is not None and cmp_ord(prev, regime) < 0:
            dy = leaf_y(prev) - leaf_y(regime)
            if dy > 0:                           # the leaf cannot reach that deep here
                cols[-1] = (cols[-1][0], leaf_y(regime), cols[-1][2])
                for k in range(1, dy + 1):
                    cols, st = add_storey(cols, st, leaf_y(regime) + k)
                level, root_x = last_root_plain(cols)
                prev0 = False
        first = False
    return cols

def last_root_plain(cols):
    """(level, root x) of the last add unit's z1 root, for a continuation that hangs one
    step below that root."""
    par, _ = _forest(cols)
    i = max(j for j in range(len(cols))
            if cols[j][2] == 1 and (par[j] is None or cols[par[j]][2] == 0))
    return cols[i][1], cols[i][0]

def last_root(cols):
    """(level, anchor x) for the add unit that continues the base matrix cols.

    The last add unit's z1 root is the last z1 column whose x parent is a z0 column (a
    digit's parent is the root, which is z1). The next anchor takes the root's own x when
    the root already carries children, and the next x when it does not.
    """
    par, _ = _forest(cols)
    i = max(j for j in range(len(cols))
            if cols[j][2] == 1 and (par[j] is None or cols[par[j]][2] == 0))
    kid = any(par[j] == i for j in range(i + 1, len(cols)))
    return cols[i][1], cols[i][0] + (0 if kid else 1)

def M(alpha):
    """alpha -> the standard form of psi_0(Omega_alpha).

    Below Omega_1 the add units are laid out from (0,0,0). Otherwise they are laid out on
    top of M(Omega_v), starting at its last z1 root. alpha = Omega_v itself is that base,
    which M_Omega builds by writing the subscript v as a chain of level columns.
    """
    v = lvl(alpha)
    if v is None:
        cols = place_units([], alpha, 0, -1)
    elif alpha == ato(Om(v)):                # alpha = Omega_v itself: the base
        return M_Omega(v)
    else:
        base = M_Omega(v)
        y, ax = last_root(base)
        cols = place_units(base, alpha, y, ax - 1, v)
    t = tail_level(alpha)                    # the upgrade effect, if a leaf ends the matrix
    return append_suffix(cols, t) if t is not None else cols

def Many(t):
    """M(alpha) for the string t; None when it does not parse."""
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
        # a parent that is a psi_0 node (a z0 column with y=0, other than the root)
        return not (p != 0 and cols[p][1] == 0)
    gp = par[p]
    return gp is None or cols[gp][2] == 0        # parent is a root -> level; a digit -> leaf

def _relative(cols, par, i):
    """Does this column's row-1 entry track the unit level (so that embedding the matrix
    one level deeper raises it), rather than name an absolute level?"""
    return cols[i][2] == 1 or _is_level(cols, par, i)

def M_Omega(v):
    """M(Omega_v): insert B's tail below every level column of M(v) and drop a trailing
    level column."""
    cols = M(v)
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

# ---- Validation ----
def mat(s):
    cs = [tuple(int(v) for v in x.split(',')) for x in re.findall(r'\((\d+(?:,\d+)*)\)', s)]
    return [c + (0,) * (3 - len(c)) for c in cs]

# Rows whose label and matrix do not agree. The orbit-law audit (M(alpha)[n] = M(alpha_n),
# expanding a trusted neighbouring row) sides with the builder on all of them, but the
# orbit law is itself empirical, so these are mismatches, not proven errata.
KNOWN_MISMATCH = {
    '1947': '(11,5,1) vs (11,6,1); M(w^3)[6] sides with the builder',
    '2113': 'the matrix has the shape of w^5*2; M(w^6)[3] sides with the builder',
    '2131': 'the content is a two-step +1 staircase, i.e. w^w+2 (label duplicated with 2133)',
    '2133': '(3,2,0)(4,3,1) vs (4,2,0)(5,3,1); M(w^w+w^2)[2] sides with the builder',
    '2532': 'the matrix is M(W^(w+1)); the label duplicates 2538, which is W^(W+1)',
    '2723': 'the matrix drops the trailing Omega leaf; the label duplicates 2724',
}

def rows():
    tsv = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'omega_alpha_rows.tsv')
    for L in open(tsv):
        p = L.rstrip('\n').split('\t')
        if p[0] != 'row': yield p

def group(alpha):
    return ('Omega_v arithmetic' if 'W_' in alpha else
            'Omega_1 arithmetic' if 'W' in alpha else 'alpha < Omega_1')

def run_check():
    from collections import Counter
    ok = Counter(); ng = Counter(); skip = Counter(); uns = Counter(); known = 0
    bad = []
    for p in rows():
        g = group(p[1])
        try:
            a = parse(p[1])
        except RecursionError:
            a = None
        if a in (None, ZERO): skip[g] += 1; continue
        try:
            got = M(a)
        except (Unsupported, RecursionError):
            uns[g] += 1; continue
        if got == mat(p[3]): ok[g] += 1
        elif p[0] in KNOWN_MISMATCH: known += 1
        else:
            ng[g] += 1
            if len(bad) < 8: bad.append((p[0], p[1], mat(p[3]), got))
    for g in ('alpha < Omega_1', 'Omega_1 arithmetic', 'Omega_v arithmetic'):
        print('%-20s %4d match / %3d mismatch / %3d unsupported / %3d unparsed'
              % (g, ok[g], ng[g], uns[g], skip[g]))
    print('%-20s %4d match / %3d mismatch / %3d unsupported / %3d unparsed'
          ' (+%d known mismatch)'
          % ('total', sum(ok.values()), sum(ng.values()), sum(uns.values()),
             sum(skip.values()), known))
    for r, t, w, g in bad:
        print(' row %s a=%s' % (r, t))
        print('   sheet:', ''.join('(%d,%d,%d)' % c for c in w))
        print('   built:', ''.join('(%d,%d,%d)' % c for c in g))
    for v in range(1, 7):                       # finite v agrees with the closed form
        assert M_Omega(nat(v)) == M_Omega_fin(v), v
    return sum(ng.values())

USAGE = """\
usage: python3 probe_eps_range.py [alpha] [n]

  alpha  the notation of build_omega_alpha.py (w / digits / + * ^ / parentheses) plus the
         atoms W_v = Omega_v and psi_v(X). Example: 'psi_0(W)^psi_0(W)+w^2', 'W_2+W*w'
         Sugar: p( and p_v( may be written for psi( and psi_v( .
  n      optional; also print the expansion psi_0(W_alpha)[n].
  (none) validation mode (check against the sheet).
"""

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
