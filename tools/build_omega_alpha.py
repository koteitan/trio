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
    cols = [(0, 0, 0)]
    level = 0
    root_x = 0
    prev_plus1 = False
    for i, b in enumerate(us):
        if i == 0:
            level = 1
            cols += body(b, 1, 1)
            root_x = 1
            prev_plus1 = False
            continue
        if b == 0:                              # +1 単位
            if prev_plus1:
                tx, ty, _ = cols[-1]
                cols.append((tx + 1, ty + 1, 0))
            else:
                cols.append((root_x + 1, level, 0))
                cols.append((root_x + 2, level + 1, 0))
            level += 1
            prev_plus1 = True
        else:
            ax = root_x + 1
            cols.append((ax, level, 0))
            cols += body(b, ax + 1, level + 1)
            root_x = ax + 1
            level += 1
            prev_plus1 = False
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

ERRATA = {
    '1947': '(11,5,1) は (11,6,1)（M(w^3)[6] で確認）',
    '2113': '行列は w^5*2 のもの（M(w^6)[3] で確認）',
    '2131': 'ラベルは w^w+2 が正（内容は +1 の階段 2 段）',
    '2133': '(3,2,0)(4,3,1) は (4,2,0)(5,3,1)（M(w^w+w^2)[2] で確認）',
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
        elif p[0] in ERRATA:
            nerr += 1
        else:
            ng += 1
            bad.append((p[0], p[1], want, got))
    print('w-CNF 断片: 一致 %d / 不一致 %d / シート誤記 %d' % (ok, ng, nerr))
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

if __name__ == '__main__':
    if len(sys.argv) > 1:
        # 使い方: python3 build_omega_alpha.py 'w^2+w+1' ['n']
        #   alpha (シートと同じ記法: w, 数, +, *, ^, 併置数 w2=w*2) の
        #   M(alpha) を表示。第 2 引数 n を与えると M(alpha)[n] も表示。
        a = parse(sys.argv[1])
        if a is None or a == 0:
            print('parse error（対応: w / 数 / + / * / ^ / 括弧。例: w^(w+1)*2+w3+1）')
            sys.exit(1)
        mat = M(a)
        print('M(%s) = %s' % (sys.argv[1], ''.join('(%d,%d,%d)' % c for c in mat)))
        if len(sys.argv) > 2:
            from trio import expand
            n = int(sys.argv[2])
            print('M[%d]   = %s' % (n, ''.join('(%d,%d,%d)' % tuple(c)
                                               for c in expand(mat, n))))
    else:
        main()
