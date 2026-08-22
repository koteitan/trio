# -*- coding: utf-8 -*-
"""eps_0 <= alpha 領域: E = eps_0 を原子に持つ順序数算術 + M(alpha)。

build_omega_alpha.py の PrSS を「Buchholz OT 項をそのまま写す block」に
置き換え、psi_0 の引数位置での逆崩壊（先頭の E -> Omega_1 葉）を入れた版。
シートの w-CNF + E 原子 135 行に対し 131 一致（残り 4 は既知の不一致行
1947 / 2113 / 2131 / 2133）。CLI は build_omega_alpha.py と同じ:

  python3 probe_eps_range.py 'psi(W)^psi(W)'     M(alpha) を表示
  python3 probe_eps_range.py 'psi(W)+w^2' 2      展開も表示
  python3 probe_eps_range.py                     検証モード
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

def block(gamma, x):
    """gamma の Buchholz OT 項をそのまま列に写す。

    加法項 w^delta ごとに psi_0 ノード (x,0,0) を置き、その子として
    引数 arg(delta) を x+1 に書く。arg は逆崩壊込み:
      delta = E*c + rest -> Omega_1 葉 (x,1,0) ++ block(E*(c-1)+rest)
      それ以外           -> block(delta)
    根拠: delta < eps_0 では w^delta = psi_0(delta) なので素直な写し。
    delta >= eps_0 では先頭の E が Omega_1 に戻る（逆崩壊）。
    """
    if gamma == ZERO: return []
    cols = []
    for e, c in gamma:
        for _ in range(c):
            cols.append((x, 0, 0))
            cols += arg(e, x + 1)
    return cols

def arg(delta, x):
    """psi_0 の引数位置の書き方（逆崩壊込み）。delta は exp（Ord または 'E'）。"""
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
            cols += block(E if e == E_EXP else e, x0 + 2)   # 桁の子 = 指数 gamma 自身
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

KNOWN_MISMATCH = {'1947', '2113', '2131', '2133'}

USAGE = """\
使い方: python3 probe_eps_range.py [alpha] [n]

  alpha  記法は build_omega_alpha.py と同じ（w / 数 / + * ^ / 括弧）に
         原子 psi(W) = eps_0 を加えたもの。例: 'psi(W)^psi(W)+w^2'
  n      省略可。与えると展開 M(alpha)[n] も表示。
  なし   検証モード（シート照合）。
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
    print('w-CNF + E 原子の alpha: 一致 %d / 想定外の不一致 %d / 既知の不一致 %d / パース外 %d'
          % (ok, ng, known, skip))
    for r, t, w, g in bad:
        print(' row %s a=%s' % (r, t))
        print('   sheet:', ''.join('(%d,%d,%d)' % c for c in w))
        print('   built:', ''.join('(%d,%d,%d)' % c for c in g))
    assert ng == 0

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] in ('-h', '--help'):
        print(USAGE)
    elif len(sys.argv) > 1:
        a = parse(sys.argv[1])
        if a in (None, ZERO):
            print('parse error（w / 数 / + * ^ / 括弧 / psi(W)）'); sys.exit(1)
        cols = M(a)
        print('M(%s) = %s' % (sys.argv[1], ''.join('(%d,%d,%d)' % c for c in cols)))
        if len(sys.argv) > 2:
            n = int(sys.argv[2])
            print('M[%d]   = %s' % (n, ''.join('(%d,%d,%d)' % tuple(c)
                                               for c in expand(cols, n))))
    else:
        run_check()
