# -*- coding: utf-8 -*-
"""ebp2dbms の表のセルを作る。`render_examples.py` の DBMS 版。

BMS との違いは 2 つだけ。

1. 先頭のアンカー `(0,0,0)` の直後に**梯子** `(1,0,0)(2,1,0)` が入る。
2. 残りの柱は `(x,y,z) -> (x+2, y+1, z)`（ただし段が 0 の柱、すなわち
   原始数列埋め込み `P(γ)` の柱は `(x,0,0) -> (x+2,0,0)`）。

`Omega_v` の族だけはこれに従わない（縮約でブロックが 1 つ減る）。そこは
`render_omega_dbms` が別に扱う。出力はすべて `mrf3.b2d(Many(alpha))` と突き合わせる。
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', 'bms2dbms', 'tools'))
import mrf3
from probe_eps_range import Many, parse, BASE_B
from render_examples import tagged, ub, pmat, txt, cnf_tex, big_parse, MDEF

LAB = {
 'ja': dict(unit='加算ユニット', mult='乗算ユニット', anchor='アンカー',
            root='根', digit='桁', plus1='{+}1', ladder='梯子'),
 'en': dict(unit='add unit', mult='multiply unit', anchor='anchor',
            root='root', digit='digit', plus1='{+}1', ladder='ladder'),
}

LADDER = [(1, 0, 0), (2, 1, 0)]


def sh(c):
    """BMS の柱を DBMS の柱へ。段が 0 の柱（P(γ) の柱）は段を上げない。"""
    c = tuple(c)
    return (c[0] + 2, c[1] + 1, c[2]) if c[1] >= 1 else (c[0] + 2, 0, 0)


def shl(cols):
    return [sh(c) for c in cols]


def render_generic(alpha, lang, emb):
    """alpha < eps_0。最初のアンカーの直後に梯子を挟み、残りを平行移動する。"""
    lab = LAB[lang]
    body = []
    flat = []
    first = True
    for parts in tagged(alpha):
        seg = ''
        for p in parts:
            if p[0] == 'mult':
                d, bl, e = shl(p[1]), shl(p[2]), p[3]
                inner = ub(pmat(d), txt(lab['digit']))
                if bl:
                    inner += ub(pmat(bl), r'\mathrm{%s}(%s)' % (emb, cnf_tex(e)))
                seg += ub(inner, txt(lab['mult']))
                flat += d + bl
            elif p[0] == 'anchor' and first:
                seg += (ub(pmat(p[1]), txt(lab['anchor']))
                        + ub(pmat(LADDER), txt(lab['ladder'])))
                flat += list(p[1]) + LADDER
                first = False
            else:
                cs = shl(p[1])
                seg += ub(pmat(cs),
                          lab['plus1'] if p[0] == 'plus1' else txt(lab[p[0]]))
                flat += cs
        body.append(ub(seg, txt(lab['unit'])))
    return ''.join(body), flat


def render_psi(X, lang, emb):
    """alpha = psi_0(Omega_X)。BMS と同じ骨格を平行移動したもの。"""
    lab = LAB[lang]
    # 末尾の柱は段が上がらないことがある（縮約の効き目）ので、実際の像から切り出す。
    full = [tuple(c) for c in mrf3.b2d([tuple(c) for c in Many('psi_0(W_%s)' % X
                                                              if X != '1' else 'psi_0(W)')])]
    tail = full[5:]
    seg = (ub(pmat([(0, 0, 0)]), txt(lab['anchor']))
           + ub(pmat(LADDER), txt(lab['ladder']))
           + ub(pmat([(3, 2, 1)]), txt(lab['root']))
           + ub(ub(pmat([(4, 2, 1)]), txt(lab['digit']))
                + ub(pmat(tail), r'\mathrm{%s}' % emb), txt(lab['mult'])))
    return (ub(seg, txt(lab['unit'])), full)


def render_omega(v, lang):
    """alpha = Omega_v。**BMS より 1 ブロック少ない**のがここの違い。"""
    lab = LAB[lang]
    full = mrf3.b2d([tuple(c) for c in Many('W' if v == '1' else 'W_' + v)])
    b0 = shl(BASE_B[1:])                      # 根 ＋ 桁 ＋ 末尾
    seg = (ub(pmat([(0, 0, 0)]), txt(lab['anchor']))
           + ub(pmat(LADDER), txt(lab['ladder']))
           + ub(pmat([b0[0]]), txt(lab['root']))
           + ub(ub(pmat([b0[1]]), txt(lab['digit']))
                + ub(pmat([full[5]]), r'\Omega_1'), txt(lab['mult'])))
    rest = list(full[6:])
    if v.isdigit():
        k = 1
        while rest:
            blk = shl([(c[0] + k, c[1] + k, c[2]) for c in BASE_B])
            assert [tuple(c) for c in rest[:4]] == blk, (v, rest[:4], blk)
            seg += ub(pmat(blk),
                      r'\mathrm{L}(B)' if k == 1 else r'\mathrm{L}^{%d}(B)' % k)
            rest = rest[4:]
            k += 1
    elif rest:
        seg += ub(pmat(rest), 'B')
    return ub(seg, txt(lab['unit'])), [tuple(c) for c in full]


# ---- Omega_1 <= alpha < Omega_2 ----
TAIL_LAB = {
 'W+1': r'{+}1', 'W+2': r'{+}2', 'W+w': r'{+}\omega', 'W+w^2': r'{+}\omega^2',
 'W*2': r'\cdot 2', 'W*w': r'\cdot\omega', 'W^2': r'{}^{2}',
 'W^w': r'{}^{\omega}', 'W^W': r'{}^{\Omega_1}', 'W^W^W': r'{}^{\Omega_1^{\Omega_1}}',
}


def render_between(alpha, lang):
    """`Omega_1 <= alpha < Omega_2`。頭の 6 列はどれも `Omega_1` そのもの（全数で確認）。

    残りは `alpha < eps_0` の表のユニットと同じ形をしているので、ひとまとめに括る。
    """
    full = [tuple(c) for c in mrf3.b2d([tuple(c) for c in Many(alpha)])]
    head, tail = full[:6], full[6:]
    seg = ub(pmat(head), r'\Omega_1')
    if tail:
        seg += ub(pmat(tail), TAIL_LAB[alpha])
    return seg, full


def cell(alpha, lang, emb='P'):
    if alpha in TAIL_LAB:
        tex, flat = render_between(alpha, lang)
        want = [tuple(c) for c in mrf3.b2d([tuple(c) for c in Many(alpha)])]
        assert [tuple(c) for c in flat] == want, alpha
        return MDEF + tex
    b = big_parse(alpha)
    if b and b[0] == 'psi':
        tex, flat = render_psi(b[1], lang, emb)
    elif b and b[0] == 'om':
        tex, flat = render_omega(b[1], lang)
    else:
        tex, flat = render_generic(parse(alpha), lang, emb)
    want = [tuple(c) for c in mrf3.b2d([tuple(c) for c in Many(alpha)])]
    assert [tuple(c) for c in flat] == want, (alpha, flat, want)
    return MDEF + tex


if __name__ == '__main__':
    for a in sys.argv[1:]:
        print('%s: %s' % (a, cell(a, 'ja')))
