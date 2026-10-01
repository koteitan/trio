# -*- coding: utf-8 -*-
"""Step 1 check for the Ytosk route: along BM4 expansion from SRO, does the evaluator decrease?

  python3 tools/probe_desc.py [walks] [maxlen] [nmax] [maxcols]

Random walks M -> M[n] (n <= nmax) from SRO = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0), keeping matrices with at
most maxcols columns. Every matrix met is evaluated by the Lean definition (Ytosk/lean/Run.lean); the
script reports pairs where eval(M[n]) < eval(M) fails, where eval is undefined, or where the value is
not a standard term (isOT).
"""
import os, sys, random, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import trio

SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]

def smat(m): return ''.join('(%d,%d,%d)' % tuple(c) for c in m)

def parse(s):
    pos = [0]
    def sum_():
        terms = []
        while True:
            terms.append(term())
            if pos[0] < len(s) and s[pos[0]] == '+': pos[0] += 1
            else: break
        t = ()
        for x in reversed([x for x in terms if x is not None]): t = (x[0], x[1], t)
        return t
    def term():
        if s[pos[0]] == '0': pos[0] += 1; return None
        if s[pos[0]] == '1': pos[0] += 1; return ((), ())
        pos[0] += 1; a = ()
        if s[pos[0]] == '_':
            pos[0] += 2; a = sum_(); pos[0] += 1
        pos[0] += 1; b = sum_(); pos[0] += 1
        return (a, b)
    return () if s == '0' else sum_()

def lt(x, y):
    if not y: return False
    if not x: return True
    if x[0] != y[0]: return lt(x[0], y[0])
    if x[1] != y[1]: return lt(x[1], y[1])
    return lt(x[2], y[2])

def evaluate(mats):
    keys = list(mats)
    inp = ''.join('%d\t%s\n' % (i, k) for i, k in enumerate(keys))
    out = subprocess.run(['lake', 'env', 'lean', '--run', 'Run.lean'], cwd=os.path.join(HERE, '..', 'Ytosk', 'lean'),
                         input=inp, capture_output=True, text=True).stdout
    res = {}
    for l in out.splitlines():
        i, v, ot = l.split('\t')
        res[keys[int(i)]] = (v, ot)
    return res

def main(walks=300, maxlen=40, nmax=3, maxcols=30, seed=1):
    random.seed(seed)
    pairs = set()
    for _ in range(walks):
        m = SRO
        for _ in range(maxlen):
            if not m: break
            n = random.randint(0, nmax)
            m2 = trio.expand(m, n)
            if len(m2) > maxcols or not m2: continue
            pairs.add((smat(m), n, smat(m2)))
            m = m2
    mats = {p[0] for p in pairs} | {p[2] for p in pairs}
    val = evaluate(mats)
    bad = [p for p in pairs if p[0] != smat(SRO) and
           (val[p[0]][0] == 'none' or val[p[2]][0] == 'none'
            or not lt(parse(val[p[2]][0]), parse(val[p[0]][0])))]
    notot = [k for k, (v, o) in val.items() if o == 'notOT']
    nonev = [k for k, (v, o) in val.items() if v == 'none' and k != smat(SRO)]
    print('pairs', len(pairs), 'matrices', len(mats), 'decrease fails', len(bad), 'undefined', len(nonev),
          'not OT', len(notot))
    for p in sorted(bad, key=lambda p: len(p[0]))[:10]:
        print(p[0], '[%d] ->' % p[1], p[2]); print('   ', val[p[0]][0][:120]); print('   ', val[p[2]][0][:120])
    for k in sorted(nonev, key=len)[:5]: print('undefined', k)
    return bad

if __name__ == '__main__':
    a = [int(x) for x in sys.argv[1:]]
    main(*a)
