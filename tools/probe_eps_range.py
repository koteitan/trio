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

# ---- 大きい alpha: psi_0(X) 原子と Omega_v 原子 ----
def _toplevel_ops(t):
    d = 0
    for ch in t:
        d += (ch == '(') - (ch == ')')
        if d == 0 and ch in '+*^': return True
    return False

def big_parse(t):
    """'psi(W)' / 'psi(W_X)' / 'W' / 'W_X' -> ('psi'|'om', X文字列)。

    添字 X の外側に演算子があるもの（W_2^2 = (Omega_2)^2 など）は None。
    """
    t = t.strip()
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
        return ('psi', t[6:-1])          # W_X^2 等は添字でなく Omega_X の演算
    return None

def Many(t):
    """t（文字列）の M(alpha)。大きい原子と w-CNF+E の両方を受ける。"""
    b = big_parse(t)
    if b:
        kind, v = b
        if kind == 'om':
            return M_Omega(v)
        vm = Many(v)
        if vm is None: return None
        # M(psi_0(Omega_X)) = (0,0,0)(1,1,1)(2,1,1) ++ shift(M(X), 3)。
        # shift された M(X) のアンカーがそのまま psi_0 ノード (3,0,0) になる。
        return [(0, 0, 0), (1, 1, 1), (2, 1, 1)] + [(c[0] + 3, c[1], c[2]) for c in vm]
    a = parse(t)
    if a in (None, ZERO): return None
    return M(a)

# ---- alpha = Omega_v （B を単位とする第 2 階層）----
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
    """レベル列（アンカー / +1 標識）か。Omega 葉・psi_0 ノードは除く。"""
    x, y, z = cols[i]
    if z != 0 or y < 1: return False
    p = par[i]
    if p is None: return True
    if cols[p][2] == 0:
        # 親が psi_0 ノード（y=0 の z0 列、ただし根のアンカーを除く）なら Omega 葉
        return not (p != 0 and cols[p][1] == 0)
    gp = par[p]
    return gp is None or cols[gp][2] == 0           # 親が「根」なら level、桁なら Omega 葉

def M_Omega(v):
    """M(Omega_v)。M(v) の各レベル列の下に B の尾を挿し、末尾のレベル列を落とす。"""
    cols = Many(v)
    if cols is None: return None
    par, kids = _forest(cols)
    lev = {i for i in range(len(cols)) if _is_level(cols, par, i)}
    drop = len(cols) - 1 if (len(cols) - 1) in lev else None
    out = []
    def dfs(i, d):
        if i == drop: return
        out.append((d, cols[i][1], cols[i][2]))
        if i in lev or i == 0:                       # 根のアンカーにも B を挿す
            y0 = cols[i][1]
            for k, (dy, z) in enumerate(((1, 1), (1, 1), (1, 0))):
                out.append((d + 1 + k, y0 + dy, z))
        for c in kids[i]: dfs(c, d + 1)
    dfs(0, 0)
    return out

def M_Omega_fin(v):
    """有限 v の閉じた形（M_Omega と一致する）: B ++ L(B) ++ ... ++ L^{v-1}(B)。"""
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
    print('alpha = Omega_v: 一致 %d / 不一致 %d / 添字未対応 %d' % (ok, ng, skip))
    for r, v, w, g in bad:
        print(' NG row %s v=%s' % (r, v))
        print('   sheet:', w)
        print('   built:', ''.join('(%d,%d,%d)' % c for c in g))
    # 有限 v は閉じた形とも一致
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
            skip += 1; continue          # Omega_v (v>=2) は別レジーム（未対応）
        want = mat(p[3])
        if got == want: ok += 1
        else:
            ng += 1
            if len(bad) < 8: bad.append((p[0], p[1], want, got))
    print('大きい原子 (psi(W_X) / W_X): 一致 %d / 不一致 %d / 添字が未対応 %d' % (ok, ng, skip))
    for r, t, w, g in bad:
        print(' row %s a=%s' % (r, t))
        print('   sheet:', ''.join('(%d,%d,%d)' % c for c in w))
        print('   built:', ''.join('(%d,%d,%d)' % c for c in g))
    return ng

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
    assert run_big() == 0
    run_omega()

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] in ('-h', '--help'):
        print(USAGE)
    elif len(sys.argv) > 1:
        cols = Many(sys.argv[1])
        if cols is None:
            print('parse error（w / 数 / + * ^ / 括弧 / psi(W) / psi(W_X) / W_X）'); sys.exit(1)
        print('M(%s) = %s' % (sys.argv[1], ''.join('(%d,%d,%d)' % c for c in cols)))
        if len(sys.argv) > 2:
            n = int(sys.argv[2])
            print('M[%d]   = %s' % (n, ''.join('(%d,%d,%d)' % tuple(c)
                                               for c in expand(cols, n))))
    else:
        run_check()
