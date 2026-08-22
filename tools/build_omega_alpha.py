# -*- coding: utf-8 -*-
"""The M(alpha) builder: the general term of the standard form for psi_0(Omega_alpha).

Domain of alpha: the terms of the extended Buchholz OT (< Lambda, the least Omega fixed
point). This file implements alpha < eps_0 first (what the CNF of w can write); the CLI
routes larger alpha through probe_eps_range.Many.

The grammar (induced from the 812 BM4-Analysis rows, cross-checked by the probe):
- alpha = w^{b_1} + ... + w^{b_m} (a non-increasing list of add units). Add unit i lives at
  level y = i.
- add unit w^b (b >= 1): the anchor column (root_prev+1, level, 0), then the body = the z1
  root (x0, y, 1) plus one digit per summand of b' (split as 1 + b' = b):
  a digit w^g is the z1 child (x0+1, y, 1) plus the closer forest prss(g).
- add unit w^0 = +1: an anchor plus a bare z0 column, climbing one level. Consecutive +1
  units share the anchor and continue as a chain.
- prss(g): a 1-row BM. A digit w^g is the node (x,0,0) plus the child forest prss(g).
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(__file__))

# ---- CNF representation: 0 | [(beta_cnf, count), ...], non-increasing ----

def cnf_cmp(a, b):
    """Compare two CNFs (-1/0/1)."""
    if a == b: return 0
    if a == 0: return -1
    if b == 0: return 1
    for (ba, ca), (bb, cb) in zip(a, b):
        c = cnf_cmp(ba, bb)
        if c: return c
        if ca != cb: return -1 if ca < cb else 1
    return -1 if len(a) < len(b) else 1

def units(cnf):
    return [b for b, c in cnf for _ in range(c)]

def pred(beta):
    """The b' with 1 + b' = beta (beta >= 1). A leading infinite term absorbs the 1."""
    if beta[0][0] != 0:
        return beta
    k = beta[0][1]
    return [(0, k - 1)] if k > 1 else 0

def prss(gamma, x0):
    """The 1-row BM forest of the exponent gamma. Closers are always z0 columns with
    y = 0; a node is (x,0,0) followed by its child forest."""
    cols = []
    if gamma == 0:
        return cols
    for g, d in gamma:
        for _ in range(d):
            cols.append((x0, 0, 0))
            cols += prss(g, x0 + 1)
    return cols

def body(beta, x0, y):
    """The body of an add unit w^beta: the z1 root followed by the digits."""
    cols = [(x0, y, 1)]
    bp = pred(beta)
    if bp != 0:
        for g, d in bp:
            for _ in range(d):
                cols.append((x0 + 1, y, 1))
                if g != 0:
                    cols += prss(g, x0 + 2)
    return cols

def M(alpha):
    """alpha (a CNF, >= w) -> the matrix of psi_0(Omega_alpha)."""
    us = units(alpha)
    assert us and us[0] != 0, 'alpha >= w only'
    cols = []
    level = 0                                   # add unit i has its anchor at y = i-1
    root_x = -1                                 # x of the previous add unit's z1 root
    prev_plus1 = False
    for b in us:
        if b == 0 and prev_plus1:               # a +1 chain: share the anchor, extend z0
            tx, ty, _ = cols[-1]
            cols.append((tx + 1, ty + 1, 0))
        elif b == 0:                            # the first +1: anchor plus a z0 column
            cols.append((root_x + 1, level, 0))
            cols.append((root_x + 2, level + 1, 0))
        else:                                   # a w^b add unit: anchor plus body
            ax = root_x + 1
            cols.append((ax, level, 0))         # for U_1 this is (0,0,0)
            cols += body(b, ax + 1, level + 1)
            root_x = ax + 1
        level += 1
        prev_plus1 = (b == 0)
    return cols

# ---- Validation: check every w-CNF row among the 812 taken from the sheet ----

tok_re = re.compile(r'w|\d+|[+*^()]')

def parse(s):
    toks = tok_re.findall(s)
    if ''.join(toks) != s.replace(' ', ''):
        return None
    pos = 0
    def peek(): return toks[pos] if pos < len(toks) else None
    def eat():
        nonlocal pos
        t = toks[pos]; pos += 1; return t
    def atom():
        t = eat()
        if t == '(':
            e = expr(); assert eat() == ')'
            return e
        if t == 'w':
            return [([(0, 1)], 1)]
        return [(0, int(t))] if int(t) > 0 else 0
    def power():
        b = atom()
        if peek() == '^':
            eat()
            return [(power(), 1)]
        return b
    def term():
        f = power()
        while peek() == '*' or (peek() and re.match(r'\d+$', peek() or '')):
            if peek() == '*': eat()
            k = int(eat())
            f = [(f[0][0], f[0][1] * k)] + f[1:]
        return f
    def expr():
        e = term()
        while peek() == '+':
            eat()
            t2 = term()
            if e == 0: e = t2
            elif t2 != 0:
                if cnf_cmp(e[-1][0], t2[0][0]) == 0:
                    e = e[:-1] + [(e[-1][0], e[-1][1] + t2[0][1])] + t2[1:]
                else:
                    e = e + t2
        return e
    try:
        e = expr()
        return e if pos == len(toks) else None
    except Exception:
        return None

# The 4 rows known to disagree with the sheet. The orbit-law audit
# (M(alpha)[n] = M(alpha_n), expanding a trusted neighbouring row) sides with the builder
# on all four, but the orbit law is itself empirical, so these are mismatches, not proven
# errata.
KNOWN_MISMATCH = {
    '1947': '(11,5,1) vs (11,6,1); M(w^3)[6] sides with the builder',
    '2113': 'the matrix has the shape of w^5*2; M(w^6)[3] sides with the builder',
    '2131': 'the content is a two-step +1 staircase, i.e. w^w+2 (label duplicated with 2133)',
    '2133': '(3,2,0)(4,3,1) vs (4,2,0)(5,3,1); M(w^w+w^2)[2] sides with the builder',
}

def main():
    tsv = os.path.join(os.path.dirname(__file__), 'omega_alpha_rows.tsv')
    ok = ng = nerr = 0
    bad = []
    for L in open(tsv):
        p = L.rstrip('\n').split('\t')
        if p[0] == 'row': continue
        c = parse(p[1])
        if c is None or c == 0 or c[0][0] == 0:   # skip non-w-CNF and finite alpha
            continue
        want = [tuple(int(v) for v in x.split(',')) for x in re.findall(r'\(([^)]*)\)', p[3])]
        want = [t + (0,) * (3 - len(t)) for t in want]
        got = M(c)
        if got == want:
            ok += 1
        elif p[0] in KNOWN_MISMATCH:
            nerr += 1
        else:
            ng += 1
            bad.append((p[0], p[1], want, got))
    print('w-CNF fragment: %d match / %d unexpected mismatch / %d known mismatch'
          % (ok, ng, nerr))
    for r, a, w, g in bad[:8]:
        print(' row %s a=%s' % (r, a))
        print('   sheet:', ''.join('(%d,%d,%d)' % t for t in w))
        print('   built:', ''.join('(%d,%d,%d)' % t for t in g))
    assert ng == 0

    # Self-check: the orbit law also holds for alpha that the sheet does not list
    from trio import expand
    SELF = [('w^9', 4, 'w^8*4'),
            ('w^8*4', 3, 'w^8*3+w^7*3'),
            ('w^3*2+w^2', 3, 'w^3*2+w3'),
            ('w^3*2+w3', 4, 'w^3*2+w2+3'),
            ('w^(w+2)', 3, 'w^(w+1)*3'),
            ('w^(w2)', 2, 'w^(w+2)'),
            ('w^w^3', 2, 'w^(w^2*2)'),
            ('w2+w^2', 2, 'w2+w2')]
    sok = 0
    for a, n, b in SELF:
        assert expand(M(parse(a)), n) == M(parse(b)), (a, n, b)
        sok += 1
    print('self-check (orbit law, off-sheet alpha): %d/%d ok' % (sok, len(SELF)))

USAGE = '''\
usage: python3 build_omega_alpha.py [alpha] [n]

  alpha        print the trio sequence standard form of psi_0(W_alpha) (W = Omega).
               The notation is the one used by the BM4-Analysis sheet:
                 w           omega
                 digits      a natural number (coefficient or finite ordinal)
                 + * ^       sum, product, power (^ is right associative)
                 ( )         parentheses
                 juxtaposed  w2 = w*2, w^w3 = w^w*3, and so on
                 W, W_X      Omega_1, Omega_X
                 psi_0(W)    eps_0 = psi_0(Omega_1)
                 psi_0(W_X)  psi_0(Omega_X) (X recursively in the same notation)
               Sugar: psi( , p( and p_0( may be written for psi_0( .
                 psi_0(W_w) = psi(W_w) = p(W_w) = p_0(W_w)
               Examples: 'w^2+w+1'  'w^(w+1)*2'  'psi_0(W)^psi_0(W)'
                         'psi_0(W_(w^2))'  'W_3'  'W_W_W'
               The domain is alpha < Lambda (the least Omega fixed point).
               M() in this file covers alpha < eps_0; probe_eps_range.Many()
               takes over above it (the two agree on every w-CNF row).
  n            optional; also print the expansion psi_0(W_alpha)[n].
  (no argument) validation mode: check every alpha < eps_0 row against the sheet
               and run the orbit-law self-check
               (validation above eps_0 lives in probe_eps_range.py).

examples:
  python3 build_omega_alpha.py 'w+1'
  python3 build_omega_alpha.py 'w^(w2)+w^2*3' 2
  python3 build_omega_alpha.py 'psi_0(W_(w^2))'
  python3 build_omega_alpha.py 'W_3'
  python3 build_omega_alpha.py
'''

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] in ('-h', '--help'):
        print(USAGE)
        sys.exit(0)
    if len(sys.argv) > 1:
        from probe_eps_range import Many     # the general builder, alpha < Lambda
        mat = Many(sys.argv[1])
        if mat is None:
            print('parse error; run --help for the accepted notation.')
            sys.exit(1)
        head = 'psi_0(W_{%s})' % sys.argv[1]
        print('%s = %s' % (head, ''.join('(%d,%d,%d)' % c for c in mat)))
        if len(sys.argv) > 2:
            from trio import expand
            n = int(sys.argv[2])
            print('%s[%d] = %s' % (head, n, ''.join('(%d,%d,%d)' % tuple(c)
                                                    for c in expand(mat, n))))
    else:
        main()
