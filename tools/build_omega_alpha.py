# -*- coding: utf-8 -*-
"""M(alpha) ビルダー: psi_0(Omega_alpha) の標準形行列の一般項（w-CNF 断片）。

alpha の定義域: 拡張ブーフホルツ OT の項（< Lambda = 最小 Omega 不動点）。
本ファイルはまず alpha < eps_0（w の CNF で書ける範囲）を実装する。

文法（BM4-Analysis 812 行からの帰納、probe で全数照合）:
- alpha = w^{b_1} + ... + w^{b_m}（単位の列、非増加）。単位 i はレベル y=i に住む。
- 単位 w^b（b>=1）: アンカー列 (root_prev+1, level, 0) の後、
  本体 = z1 根 (x0, y, 1) ＋ b の CNF 桁（1+b' = b と分解した b'）:
  桁 w^g は z1 子 (x0+1, y, 1) ＋ 閉包子森 prss(g)（y-1 レベル、z=0）。
- 単位 w^0 = +1: アンカー ＋ 素の z0 列でレベルを 1 段登る。連続する +1 は鎖で継ぐ。
- prss(g): 1 行 BM。桁 w^g は節 (x,y,0) ＋ 子森 prss(g)。
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(__file__))

# ---- CNF 表現: 0 | [(beta_cnf, count), ...] 非増加 ----

def cnf_cmp(a, b):
    """CNF の比較 (-1/0/1)。"""
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
    """1 + b' = beta となる b'（beta >= 1）。先頭項が無限なら 1 は吸収される。"""
    if beta[0][0] != 0:
        return beta
    k = beta[0][1]
    return [(0, k - 1)] if k > 1 else 0

def prss(gamma, x0):
    """指数 gamma の 1 行 BM 森。閉包子は常に y=0 の z0 列。節 = (x,0,0) + 子森。"""
    cols = []
    if gamma == 0:
        return cols
    for g, d in gamma:
        for _ in range(d):
            cols.append((x0, 0, 0))
            cols += prss(g, x0 + 1)
    return cols

def body(beta, x0, y):
    """単位 w^beta の本体。z1 根 + 桁。根の x を返す。"""
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
    """alpha (CNF, >= w) -> psi_0(Omega_alpha) の行列。"""
    us = units(alpha)
    assert us and us[0] != 0, 'alpha >= w のみ'
    cols = []
    level = 0                                   # 単位 i のアンカーは y = i-1
    root_x = -1                                 # 直前単位の z1 根の x（初期値 -1）
    prev_plus1 = False
    for b in us:
        if b == 0 and prev_plus1:               # +1 の連鎖: アンカー共有で z0 鎖
            tx, ty, _ = cols[-1]
            cols.append((tx + 1, ty + 1, 0))
        elif b == 0:                            # 最初の +1: アンカー + z0 列
            cols.append((root_x + 1, level, 0))
            cols.append((root_x + 2, level + 1, 0))
        else:                                   # w^b 単位: アンカー + 本体
            ax = root_x + 1
            cols.append((ax, level, 0))         # U_1 ではこれが (0,0,0)
            cols += body(b, ax + 1, level + 1)
            root_x = ax + 1
        level += 1
        prev_plus1 = (b == 0)
    return cols

# ---- 検証: シート由来の 812 行のうち w-CNF なものと全数照合 ----

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

# シートと一致しない既知の 4 行。軌道法則 M(alpha)[n] = M(alpha_n) による監査
# （信頼できる隣の行の展開との突合）ではビルダー側に一致するが、
# 軌道法則自体は経験則であり、シートの誤記だと証明できたわけではない。
KNOWN_MISMATCH = {
    '1947': '(11,5,1) vs (11,6,1)（M(w^3)[6] はビルダー側）',
    '2113': '行列は w^5*2 の形（M(w^6)[3] はビルダー側）',
    '2131': '内容は +1 の階段 2 段 = w^w+2 相当（2133 とラベル重複）',
    '2133': '(3,2,0)(4,3,1) vs (4,2,0)(5,3,1)（M(w^w+w^2)[2] はビルダー側）',
}

def main():
    tsv = os.path.join(os.path.dirname(__file__), 'omega_alpha_rows.tsv')
    ok = ng = nerr = 0
    bad = []
    for L in open(tsv):
        p = L.rstrip('\n').split('\t')
        if p[0] == 'row': continue
        c = parse(p[1])
        if c is None or c == 0 or c[0][0] == 0:   # w-CNF 外・有限は対象外
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
    print('w-CNF 断片: 一致 %d / 想定外の不一致 %d / 既知の不一致 %d（軌道法則の監査ではビルダー側）'
          % (ok, ng, nerr))
    for r, a, w, g in bad[:8]:
        print(' row %s a=%s' % (r, a))
        print('   sheet:', ''.join('(%d,%d,%d)' % t for t in w))
        print('   built:', ''.join('(%d,%d,%d)' % t for t in g))
    assert ng == 0

    # 自己検証: シートに無い alpha でも軌道法則が成り立つ
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
    print('自己検証（軌道法則、シート外 alpha）: %d/%d ok' % (sok, len(SELF)))

USAGE = '''\
使い方: python3 build_omega_alpha.py [alpha] [n]

  alpha        psi_0(W_alpha) のトリオ数列標準形を表示する（W = Omega）。
               記法は BM4-Analysis シートと同じ:
                 w           omega
                 数          自然数（係数・有限順序数）
                 + * ^       和・積・冪（^ は右結合）
                 ( )         括弧
                 併置数       w2 = w*2, w^w3 = w^w*3 など
                 W, W_X      Omega_1, Omega_X
                 psi_0(W)    eps_0 = psi_0(Omega_1)
                 psi_0(W_X)  psi_0(Omega_X)（X は再帰的に同じ記法）
               シュガーシンタクス: psi_0( の代わりに psi( / p( / p_0( も可。
                 psi_0(W_w) = psi(W_w) = p(W_w) = p_0(W_w)
               例: 'w^2+w+1'  'w^(w+1)*2'  'psi_0(W)^psi_0(W)'
                   'psi_0(W_(w^2))'  'W_3'  'W_W_W'
               定義域は alpha < Lambda（最小 Omega 不動点）。
               alpha < eps_0 は本ファイルの M() が、それ以上は
               probe_eps_range.Many() が担当する（w-CNF 上で両者は一致）。
  n            省略可。与えると展開 psi_0(W_alpha)[n] も表示する。
  （引数なし）  検証モード: alpha < eps_0 の全数照合と
               軌道法則による自己検証を走らせる
               （eps_0 以上の検証は probe_eps_range.py 側）。

例:
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
        from probe_eps_range import Many     # alpha < Lambda の一般ビルダー
        mat = Many(sys.argv[1])
        if mat is None:
            print('parse error。--help で対応記法を表示します。')
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
