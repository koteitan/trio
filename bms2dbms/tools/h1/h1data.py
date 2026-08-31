# -*- coding: utf-8 -*-
"""H1: `_cw2` が発火する柱の教師つきデータを 2 つの出典から作る。

出典 A: シート（1354 行の正解）。いまの conv3 はシートで満点なので、
        シート行の分岐列の綴りは**そのまま正解**。
出典 B: ImgClosedT の目標 (conv3 A)<m> vs conv3(A<m+1>)。長さが揃う対で
        柱ごとに整列し、目標の行 1 から正しい綴りを読む。
"""
import sys, os, pickle, time
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, sheet3, provh
from rows3 import (is_branch, is_w_col, closes_unit, par0, hi_block,
                   is_repeat, wchain_head, ANCHOR)
from core import expand


def unit_head(Mo, off):
    for j in range(off, -1, -1):
        c = Mo[j]
        if c[0] == 0 or (c[1] == 0 and c[2] == 0) or tuple(c) == ANCHOR:
            return j
    return 0


def anc_chain(Mo, off):
    """off の行 0 の祖先の鎖（根に近い順）の添字。"""
    out, x = [], off
    while True:
        q = par0(Mo, x)
        if q < 0:
            break
        out.append(q)
        x = q
    return list(reversed(out))


def features(Mo, off):
    """行列から直に読める素性だけ。状態は入れない。"""
    n = len(Mo)
    p = Mo[off]
    g = lambda i: tuple(Mo[i]) if 0 <= i < n else None
    nx1, nx2, nx3 = g(off + 1), g(off + 2), g(off + 3)
    pv, pv2, pv3 = g(off - 1), g(off - 2), g(off - 3)
    uh = unit_head(Mo, off)
    j = wchain_head(Mo, off)
    q = par0(Mo, off)
    qn = par0(Mo, off + 1) if off + 1 < n else -1
    ch = anc_chain(Mo, off)
    f = {
        'p': tuple(p), 'p0': p[0],
        'nx1': nx1, 'nx2': nx2, 'nx3': nx3,
        'pv': pv, 'pv2': pv2, 'pv3': pv3,
        'off': off, 'n': n, 'islast': off == n - 1,
        'nxt_is_last': off + 1 == n - 1,
        'hi': hi_block(Mo, off),
        'rep': is_repeat(Mo, off),
        'wjs': None if j is None else off - j,
        'wpar0': None if j is None else par0(Mo, j),
        'wcol': None if j is None else tuple(Mo[j]),
        'par0': q, 'parcol': g(q),
        'npar0': qn, 'nparcol': g(qn),
        'uh': off - uh, 'uhcol': tuple(Mo[uh]),
        'nbr': sum(1 for t in range(uh, off) if is_branch(Mo[t])),
        'nw': sum(1 for t in range(uh, off) if is_w_col(Mo[t])),
        'pvw': bool(pv) and is_w_col(pv),
        'pvbr': bool(pv) and is_branch(pv),
        'nanch': sum(1 for t in range(off) if tuple(Mo[t]) == ANCHOR),
        'ndepth': len(ch),
        'z1any': any(c[2] > 0 for c in Mo[:off]),
        'z1after': any(c[2] > 0 for c in Mo[off + 1:]),
    }
    return f


def dec_ok(dec):
    return dec is not None and dec.get('why') != 'tie' and dec.get('shallow') is not None


def from_sheet(zcap=1):
    T = sheet3.load(zcap)
    out = []
    nok = 0
    for row, b, d in T:
        Mo = tuple(map(tuple, b))
        img, pr = provh.b2d3p(list(b))
        if tuple(img) != tuple(map(tuple, d)):
            continue
        nok += 1
        for kind, off, why, ctx, dec in pr:
            if kind != 'body' or not dec_ok(dec):
                continue
            out.append(dict(src='sheet', tag=row, A=Mo, off=off,
                            shallow=dec['shallow'], dec=dec,
                            ctx=''.join(ctx), feat=features(Mo, off)))
    return out, nok


def from_teach(lim=6, mmax=3, zcap=1, verbose=1):
    A = sorted(rows3.gen3('BMS', lim, zcap=zcap), key=rows3.key)
    out = []
    nal = nmis = 0
    t0 = time.time()
    for k, M in enumerate(A):
        if len(M) < 2:
            continue
        fM = rows3.b2d3(list(M))
        for m in range(1, mmax + 1):
            T = tuple(expand(tuple(map(tuple, fM)), m))
            E = tuple(tuple(c) for c in expand(tuple(map(tuple, M)), m + 1))
            U, pr = provh.b2d3p(list(E))
            if len(U) != len(T):
                nmis += 1
                continue
            nal += 1
            for i, (c, want, pe) in enumerate(zip(U, T, pr)):
                kind, off, why, ctx, dec = pe
                if kind != 'body' or not dec_ok(dec):
                    continue
                bs, dp = dec['base_s'], dec['deep']
                w1 = want[1]
                if w1 == bs and w1 != dp:
                    lab = True
                elif w1 == dp and w1 != bs:
                    lab = False
                else:
                    continue
                out.append(dict(src='teach', tag=(rows3.key(M), m),
                                A=E, off=off, shallow=lab, got=dec['shallow'],
                                dec=dec, ctx=''.join(ctx),
                                feat=features(E, off)))
        if verbose and (k + 1) % 1000 == 0:
            print('  %d/%d  柱 %d  整列 %d / 不一致 %d  %.0fs'
                  % (k + 1, len(A), len(out), nal, nmis, time.time() - t0),
                  flush=True)
    if verbose:
        print('整列 %d / 不揃い %d   ラベル付き柱 %d 本  %.0fs'
              % (nal, nmis, len(out), time.time() - t0), flush=True)
    return out


if __name__ == '__main__':
    what = sys.argv[1]
    if what == 'sheet':
        rs, nok = from_sheet()
        print('シート正解 %d 行  分岐列の決定 %d 本' % (nok, len(rs)))
        pickle.dump(rs, open('/tmp/h1work/S.pkl', 'wb'))
    else:
        lim = int(sys.argv[2]) if len(sys.argv) > 2 else 6
        mm = int(sys.argv[3]) if len(sys.argv) > 3 else 3
        rs = from_teach(lim, mm)
        pickle.dump(rs, open('/tmp/h1work/T%d_%d.pkl' % (lim, mm), 'wb'))
        print('書いた /tmp/h1work/T%d.pkl' % lim)
