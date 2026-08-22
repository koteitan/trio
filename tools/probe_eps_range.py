# -*- coding: utf-8 -*-
"""eps_0 <= alpha 領域の探索: E = eps_0 を原子に持つ順序数算術 + M(alpha) 拡張。

現状 11/13 一致。残り 2 件（塔のケース）は指数スロットの引数位置で
E -> Omega_1 の逆崩壊が起きており、その適用条件が未特定。詳細は ../dom.md。
未完なので build_omega_alpha.py には統合していない。
"""
import re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trio import expand

# Ord = tuple((exp, coeff), ...) 降順。exp は Ord または 'E'。
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
    # 有限指数は反復
    if len(b) == 1 and b[0][0] == ZERO:
        r = a
        for _ in range(b[0][1] - 1): r = mul(r, a)
        return r
    e1 = a[0][0]
    if e1 == ZERO:                       # 有限の底
        return wpow(b_pred(b))
    return wpow(mul(E if e1 == E_EXP else e1, b))

def b_pred(b):
    return b

# ---- パーサ: w, 数, E(=psi(W)), + * ^ ( ) ----
TOK = re.compile(r'psi\(W\)|w|\d+|[+*^()]')
def parse(s):
    s = s.replace(' ', '')
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

# ---- ビルダー拡張 ----
def units(a):
    return [e for e, c in a for _ in range(c)]

def pred_beta(beta):
    """1 + beta' = beta の beta'。"""
    if beta == ZERO: return ZERO
    if beta[0][0] == ZERO:
        k = beta[0][1]
        return nat(k - 1)
    return beta

def V(gamma, x):
    """指数 gamma の埋め込みブロック。gamma < eps_0 は原始数列、E は psi_0(Omega_1)。"""
    if gamma == ZERO: return []
    cols = []
    for e, c in gamma:
        for _ in range(c):
            if e == E_EXP:                       # w^E = E = psi_0(Omega_1)
                cols.append((x, 0, 0)); cols.append((x + 1, 1, 0))
            else:
                cols.append((x, 0, 0)); cols += V(e, x + 1)
    return cols

def body(beta, x0, y):
    cols = [(x0, y, 1)]
    for e, c in pred_beta(beta):
        for _ in range(c):
            cols.append((x0 + 1, y, 1))
            if e == E_EXP:
                cols.append((x0 + 2, 0, 0)); cols.append((x0 + 3, 1, 0))
            elif e != ZERO:
                cols += V(e, x0 + 2)
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

# ---- 検証 ----
def mat(s):
    cs = [tuple(int(v) for v in x.split(',')) for x in re.findall(r'\((\d+(?:,\d+)*)\)', s)]
    return [c + (0,) * (3 - len(c)) for c in cs]

ok = ng = skip = 0; bad = []
for L in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'omega_alpha_rows.tsv')):
    p = L.rstrip('\n').split('\t')
    if p[0] == 'row': continue
    a = parse(p[1])
    if a in (None, ZERO): skip += 1; continue
    if not has_E(a): continue          # w-CNF は既存で検証済み
    want = mat(p[3]); got = M(a)
    if got == want: ok += 1
    else:
        ng += 1
        if len(bad) < 8: bad.append((p[0], p[1], want, got))
print('E 原子を含む alpha: 一致 %d / 不一致 %d' % (ok, ng))
for r, s, w, g in bad:
    print(' row %s a=%s' % (r, s))
    print('   sheet:', ''.join('(%d,%d,%d)' % t for t in w))
    print('   built:', ''.join('(%d,%d,%d)' % t for t in g))
