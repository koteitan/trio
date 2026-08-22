# -*- coding: utf-8 -*-
"""ebp2bms の表セルを、加算/乗算ユニットの underbrace 付きで生成する。

入れ子:
  加算ユニット U_i
    アンカー / 根 / 乗算ユニット S_ij（= 桁 + 埋め込み）
  beta_i = 0 のときは アンカー / +1 列。

alpha = psi_0(Omega_X) と alpha = Omega_v は文法が別なので個別に扱う。
どの出力も列を平坦化すると probe_eps_range.Many(alpha) に一致することを assert する。

GitHub は 1 ページの数式ソースが 20000 字を超えると描画を止めるので、
ページの分割で収める（\\def によるマクロ化は GitHub の KaTeX が許可しない）。
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_eps_range import (Many, big_parse, parse, units, pred_beta, block,
                             E, E_EXP, ZERO, BASE_B, lift)

# GitHub の KaTeX は \def を許可しないので pmatrix をそのまま書く。
MDEF = ''

L = {
 'ja': dict(unit='加算ユニット', mult='乗算ユニット', anchor='アンカー',
            root='根', digit='桁', plus1='{+}1'),
 'en': dict(unit='add unit', mult='multiply unit', anchor='anchor',
            root='root', digit='digit', plus1='{+}1'),
}

def txt(s): return r'\text{%s}' % s
def ub(body, label): return r'\underbrace{%s}_{%s}' % (body, label)

def pmat(cols):
    r = [' & '.join(str(c[i]) for c in cols) for i in range(3)]
    return r'\begin{pmatrix}' + r'\cr '.join(r) + r'\end{pmatrix}'

ONE = ((ZERO, 1),)

def cnf_tex(c):
    if c == E_EXP: return r'\varepsilon_0'
    if c == ZERO: return '0'
    out = []
    for g, d in c:
        if g == ZERO:
            out.append(str(d)); continue
        b = (r'\varepsilon_0' if g == E_EXP else
             r'\omega' if g == ONE else r'\omega^{%s}' % cnf_tex(g))
        out.append(b + (r'\cdot %d' % d if d > 1 else ''))
    return '+'.join(out)

# ---- 一般の alpha（ユニットループ） ----

def tagged(alpha):
    out = []; level = 0; root_x = -1; prev0 = False; last = None
    for b in units(alpha):
        beta = E if b == E_EXP else b
        parts = []
        if beta == ZERO and prev0:
            tx, ty, _ = last
            parts.append(('plus1', [(tx + 1, ty + 1, 0)]))
        elif beta == ZERO:
            parts.append(('anchor', [(root_x + 1, level, 0)]))
            parts.append(('plus1', [(root_x + 2, level + 1, 0)]))
        else:
            ax = root_x + 1
            parts.append(('anchor', [(ax, level, 0)]))
            parts.append(('root', [(ax + 1, level + 1, 1)]))
            for e, c in pred_beta(beta):
                for _ in range(c):
                    parts.append(('mult', [(ax + 2, level + 1, 1)],
                                  block(E if e == E_EXP else e, ax + 3), e))
            root_x = ax + 1
        out.append(parts)
        for p in parts:
            last = (p[2][-1] if (p[0] == 'mult' and p[2]) else p[1][-1])
        level += 1; prev0 = (beta == ZERO)
    return out

def render_generic(alpha, lang, emb):
    lab = L[lang]; body = []; flat = []
    for parts in tagged(alpha):
        seg = ''
        for p in parts:
            if p[0] == 'mult':
                d, bl, e = p[1], p[2], p[3]
                inner = ub(pmat(d), txt(lab['digit']))
                if bl:
                    inner += ub(pmat(bl), r'\mathrm{%s}(%s)' % (emb, cnf_tex(e)))
                seg += ub(inner, txt(lab['mult']))
                flat += d + bl
            else:
                seg += ub(pmat(p[1]),
                          lab['plus1'] if p[0] == 'plus1' else txt(lab[p[0]]))
                flat += p[1]
        body.append(ub(seg, txt(lab['unit'])))
    return ''.join(body), flat

# ---- alpha = psi_0(Omega_X) ----

def render_psi(X, lang, emb):
    lab = L[lang]
    tail = [(c[0] + 3, c[1], c[2]) for c in Many(X)]
    seg = (ub(pmat([(0, 0, 0)]), txt(lab['anchor']))
           + ub(pmat([(1, 1, 1)]), txt(lab['root']))
           + ub(ub(pmat([(2, 1, 1)]), txt(lab['digit']))
                + ub(pmat(tail), r'\mathrm{%s}' % emb), txt(lab['mult'])))
    return ub(seg, txt(lab['unit'])), [(0, 0, 0), (1, 1, 1), (2, 1, 1)] + tail

# ---- alpha = Omega_v ----

def render_omega(v, lang):
    """先頭 B をアンカー/根/乗算ユニットに割り、残りは L^k(B) または B としてまとめる。"""
    lab = L[lang]
    full = Many('W' if v == '1' else 'W_' + v)
    b0 = BASE_B
    seg = (ub(pmat([b0[0]]), txt(lab['anchor']))
           + ub(pmat([b0[1]]), txt(lab['root']))
           + ub(ub(pmat([b0[2]]), txt(lab['digit']))
                + ub(pmat([b0[3]]), r'\Omega_1'), txt(lab['mult'])))
    rest = full[4:]
    if v.isdigit():
        k = 1
        while rest:
            blk = lift(b0, k)
            assert rest[:4] == blk, (v, rest[:4], blk)
            seg += ub(pmat(blk),
                      r'\mathrm{L}(B)' if k == 1 else r'\mathrm{L}^{%d}(B)' % k)
            rest = rest[4:]; k += 1
    elif rest:
        seg += ub(pmat(rest), 'B')
    return ub(seg, txt(lab['unit'])), full

def cell(alpha, lang, emb):
    b = big_parse(alpha)
    if b and b[0] == 'psi':
        tex, flat = render_psi(b[1], lang, emb)
    elif b and b[0] == 'om':
        tex, flat = render_omega(b[1], lang)
    else:
        tex, flat = render_generic(parse(alpha), lang, emb)
    assert flat == Many(alpha), alpha
    return MDEF + tex
