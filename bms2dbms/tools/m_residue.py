"""残り 23 件（シート不一致 20 + 像が非標準 3）の原因分類。

rows3.py は読むだけ。conv3 は**このファイルにコピー**して、
どの入力列がどの出力列を書いたかを記録する版 conv3T を使う。

    python3 m_residue.py sheet     不一致 20 件の分類
    python3 m_residue.py ns        像が非標準の 3 件
    python3 m_residue.py hunt      非標準の接頭辞の正しい像を総当たり
    python3 m_residue.py fix       修正案の採点
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, expand, isstd, cmpmat
import rows3
from rows3 import (split0, shift1, units_split, predlab, ok_place, fit,
                   NOTLAST, ANCHOR, closes_unit, Lat, is_branch, dmap_at,
                   copy_shift, contrPre, gen3, key)
import sheet3

TRACE = []


# ---------------------------------------------------------------- 追跡版 conv3
def conv3T(M, d=0, L=(), F=(), ps=(0, 0), pw=(0, 0), first=True, force=False,
           st=None, nx=None, tag=()):
    """rows3.conv3 の逐語コピー ＋ TRACE への記録だけ足したもの。

    TRACE の並びは出力列の並びと一致する（cols を作ってから再帰するので）。
    """
    if st is None:
        st = {'ST': (), 'prev': None, 'dmap': []}
    if not M:
        return []
    p, r = M[0], M[1:]
    v, s2 = p[1], p[2]
    A, B = split0(p, r)

    if v == 0:
        base_d = base_s = 0
        pl2, force1 = 0, False
    else:
        e = Lat(L, v - 1)
        base_d, pl2, force1, base_s = e[0] + 1, e[1], e[2], e[3] + 1
    first1 = F[v] if v < len(F) else True

    if p == (1, 1, 0):
        st['prev'] = 0
    sh = None
    if is_branch(p) and base_s != base_d:
        nxt = M[1] if len(M) > 1 else nx
        sh = (st['prev'] == 0) or closes_unit(nxt)
        base = base_s if sh else base_d
        st['prev'] = 0 if sh else 1
    else:
        base = base_d

    lad1 = first1 and s2 == pl2 + 1 and (base <= s2 or force1)
    e1 = base + 1 if lad1 else (s2 + 1 if (s2 > 0 and base <= s2) else base)
    e2 = s2
    h1 = base if lad1 else e1
    lad0 = first and v == ps[0] + 1 and (d <= h1 or force)

    ST = st['ST']
    cols = []
    if lad0:
        cols.append((d, pw[0], pw[1]))
        ST = ST[:d] + ((pw[0], pw[1]),)
        dd = d + 1
    else:
        dd = fit(ST, d, h1)
        if dd is None:
            dd = max(d, len(ST))
    if lad1:
        cols.append((dd, base, pl2))
        ST = ST[:dd] + ((base, pl2),)
        dd += 1
    if not ok_place(ST, dd, e1):
        x = fit(ST, dd, e1)
        if x is not None:
            dd = x
    cols.append((dd, e1, e2))
    ST = ST[:dd] + ((e1, e2),)
    st['ST'] = ST
    st['dmap'] = st['dmap'][:p[0]] + [dd]

    info = {'p': p, 'tag': tag, 'cols': list(cols), 'lad0': lad0, 'lad1': lad1,
            'base': base, 'base_d': base_d, 'base_s': base_s, 'shallow': sh,
            'e1': e1, 'e2': e2, 'd': d, 'dd': dd, 'nx': nx, 'contr': None,
            'ST': ST, 'L': L}
    TRACE.append(info)

    fc = (not lad1) and first1 and s2 == pl2
    f0 = (not lad0) and first and (v, s2) == ps
    if e1 == base + 1 and v >= 1:
        Lb = L[:v - 1] + ((base, pl2, False, Lat(L, v - 1)[3]),)
    else:
        Lb = L
    LA = Lb[:v] + ((e1, s2, fc, e1),)
    FA = F[:v] + (False,)

    if lad0:
        for e in (0, 1):
            qlab = (ps[0] + e, ps[1])
            U, B2 = units_split(p, B, qlab)
            if not B2:
                continue
            q, r2 = B2[0], B2[1:]
            if (q[1], q[2]) != qlab or q[0] != p[0]:
                continue
            Aq, Bq = split0(q, r2)
            for na in (q, NOTLAST):
                pre = contrPre(p, U, A, e, ps[0], st['prev'], na)
                if list(Aq[:len(pre)]) == pre:
                    break
            else:
                continue
            blk = [p] + list(A) + list(U)
            deep_end = is_branch(blk[-1]) and pre[-1][1] > blk[-1][1]
            rest2 = list(Aq[len(pre):])
            if rest2:
                if rest2[0][0] < p[0] + 1:
                    continue
                if (rest2[0][0] == p[0] + 1
                        and (rest2[0][1], rest2[0][2]) >= (v + e, s2) and e == 0):
                    continue
            elif e == 0 or not deep_end:
                continue
            Lr = L[:v] + (((base, pl2, fc, base) if e else (e1, s2, fc, e1)),)
            hd = lambda *ls: next((l[0] for l in ls if l), nx)
            rd = (d + 1 + e if (not rest2 or rest2[0][0] == p[0] + 1)
                  else dmap_at(st, rest2[0][0] - 1))
            info['contr'] = {'e': e, 'U': list(U), 'rest2': list(rest2),
                             'rd': rd, 'deep_end': deep_end, 'Aq': list(Aq),
                             'pre': list(pre), 'Bq': list(Bq)}
            cA = conv3T(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
                        U[0] if U else na, tag + ('A',))
            cU = conv3T(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na,
                        tag + ('U',))
            cR = conv3T(rest2, rd, Lr, (False,) * 12,
                        (v, s2), (e1, e2), False, False, st, hd(Bq),
                        tag + ('R',))
            cB = conv3T(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                        tag + ('B',))
            return cols + cA + cU + cR + cB

    cA = conv3T(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
                B[0] if B else nx, tag + ('a',))
    cB = conv3T(B, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                tag + ('b',))
    return cols + cA + cB


def run(M):
    """変換して (像, TRACE) を返す。TRACE の cols を並べると像になる。"""
    global TRACE
    TRACE = []
    out = tuple(conv3T(list(M)))
    tr = TRACE
    flat = [(i, c) for i, inf in enumerate(tr) for c in inf['cols']]
    assert tuple(c for _, c in flat) == out, (show(out), flat)
    return out, tr, flat


# ---------------------------------------------------------------- 分類
def diagnose(row, b, d, n):
    out, tr, flat = run(b)
    assert out == n
    k = 0
    while k < min(len(d), len(n)) and d[k] == n[k]:
        k += 1
    ti, bad = flat[k] if k < len(flat) else (None, None)
    inf = tr[ti] if ti is not None else None
    return {'row': row, 'k': k, 'good': d[k] if k < len(d) else None,
            'bad': n[k] if k < len(n) else None, 'inf': inf,
            'tr': tr, 'flat': flat}


def cause(dg, b, d, n):
    """最初の食い違いを規則の言葉に落とす。"""
    g, x, inf = dg['good'], dg['bad'], dg['inf']
    if g is None:
        return 'ours-short（像が正解より短い）'
    if x is None:
        return 'ours-long?（像が正解より長い）'
    if g[0] != x[0] and g[1:] == x[1:]:
        return 'depth: 深さが %+d（%s の柱）' % (x[0] - g[0], inf['p'] if inf else '?')
    if g[0] == x[0] and g[1] != x[1]:
        if inf and is_branch(inf['p']):
            return ('row1-branch: 分岐列 %s の浅い/深い（浅い=%s, 浅側=%d 深側=%d, 正=%d）'
                    % (inf['p'], inf['shallow'], inf['base_s'], inf['base_d'], g[1]))
        return 'row1: 行 1 の値 %d != %d（柱 %s）' % (x[1], g[1], inf['p'] if inf else '?')
    return 'other: %s vs %s（柱 %s）' % (g, x, inf['p'] if inf else '?')


def sheet_report(verbose=True):
    T = sheet3.load(1)
    bad = []
    for row, b, dd in T:
        n = rows3.b2d3(b)
        if n != dd:
            bad.append((row, b, dd, n))
    print('シート 3 行 z<=1: %d 対  不一致 %d' % (len(T), len(bad)))
    groups = {}
    for row, b, dd, n in bad:
        std = isstd(dd, 'DBMS')
        dg = diagnose(row, b, dd, n)
        c = cause(dg, b, dd, n) if std else 'SHEET-ERROR（正解欄が DBMS 標準形でない）'
        head = c.split(':')[0]
        groups.setdefault(head, []).append((row, b, dd, n, dg, c))
    for h, L in sorted(groups.items(), key=lambda t: -len(t[1])):
        print('\n=== %s : %d 件 ===' % (h, len(L)))
        for row, b, dd, n, dg, c in L:
            print(' 行%-5d %s' % (row, show(b)))
            print('   正 %s' % show(dd))
            print('   誤 %s' % show(n))
            print('   最初の食い違い 列%d: 正%s 誤%s   %s' % (dg['k'], dg['good'], dg['bad'], c))
            if verbose and dg['inf'] is not None:
                i = dg['inf']
                print('   書いた柱 p=%s tag=%s lad0=%s lad1=%s base=%d(浅%d/深%d) e1=%d d=%d dd=%d nx=%s'
                      % (i['p'], ''.join(i['tag']), i['lad0'], i['lad1'], i['base'],
                         i['base_s'], i['base_d'], i['e1'], i['d'], i['dd'], i['nx']))
                print('   ST=%s' % (i['ST'],))
                ci = [t for t in dg['tr'] if t['contr']]
                if ci:
                    for t in ci:
                        cc = t['contr']
                        print('   縮約: 頭=%s e=%d U=%s rest=%s rd=%d deep_end=%s'
                              % (t['p'], cc['e'], [show((u,)) for u in cc['U']],
                                 [show((u,)) for u in cc['rest2']], cc['rd'], cc['deep_end']))
                else:
                    print('   縮約: 発火せず')
    return groups


# ---------------------------------------------------------------- 非標準 3 件
def ns_report(lim=7):
    t0 = time.time()
    A = gen3('BMS', lim, zcap=1)
    print('<=%d 列 BMS 標準形 %d 個 (%.1fs)' % (lim, len(A), time.time() - t0))
    ns = []
    for M in A:
        N = rows3.b2d3(M)
        if not isstd(N, 'DBMS'):
            ns.append((M, N))
    print('像が非標準: %d 件 (%.1fs)' % (len(ns), time.time() - t0))
    for M, N in ns:
        out, tr, flat = run(M)
        print('\n %s' % show(M))
        print('   -> %s' % show(N))
        # どこで標準形が破れるか（接頭辞ごとに）
        for j in range(1, len(N) + 1):
            if not isstd(N[:j], 'DBMS'):
                ti, c = flat[j - 1]
                i = tr[ti]
                print('   最初に非標準になる列 %d = %s（柱 p=%s tag=%s lad0=%s lad1=%s '
                      'base=%d(浅%d/深%d) e1=%d dd=%d nx=%s）'
                      % (j - 1, c, i['p'], ''.join(i['tag']), i['lad0'], i['lad1'],
                         i['base'], i['base_s'], i['base_d'], i['e1'], i['dd'], i['nx']))
                break
        for t in tr:
            if t['contr']:
                cc = t['contr']
                print('   縮約: 頭=%s e=%d U=%s rest=%s rd=%d deep_end=%s'
                      % (t['p'], cc['e'], [show((u,)) for u in cc['U']],
                         [show((u,)) for u in cc['rest2']], cc['rd'], cc['deep_end']))
    return ns


# ---------------------------------------------------------------- 総当たり
def gen_pref(pref, lim, zcap=1, ver='DBMS'):
    """`pref` を接頭辞に持つ `ver` の標準形を、全長 `lim` 列以下で全部。"""
    cur = [tuple(pref)]
    out = [tuple(pref)] if isstd(tuple(pref), ver) else []
    if not out:
        return []
    for _ in range(lim - len(pref)):
        nxt = []
        for S in cur:
            amax = (S[-1][0] + 1) if S else 0
            for a in range(amax + 1):
                bmax = a if ver == 'BMS' else max(a - 1, 0)
                for b in range(bmax + 1):
                    cmax = b if ver == 'BMS' else max(b - 1, 0)
                    if zcap is not None:
                        cmax = min(cmax, zcap)
                    for c in range(cmax + 1):
                        T = S + ((a, b, c),)
                        if isstd(T, ver):
                            nxt.append(T)
        cur = nxt
        out.extend(nxt)
    return out


def hunt(Mstr, plen=5, lim=12, K=10, zcap=1):
    """M の像の候補 N を総当たり。

    条件: N は DBMS 標準形で、N の基本列の第 1,2,3 項がすべて
          {b2d3(M<n>) : n=1..K} に入り、かつ互いに異なる。
    候補は「いまの像の先頭 `plen` 列」を共有するものに限る。
    """
    M = parse(Mstr, 3)
    cur = rows3.b2d3(M)
    IMG = {}
    for n in range(1, K + 1):
        IMG[tuple(rows3.b2d3(expand(M, n)))] = n
    pref = cur[:plen]
    t0 = time.time()
    C = gen_pref(pref, lim, zcap)
    print('M    %s' % show(M))
    print('いまの像 %s  std=%s' % (show(cur), isstd(cur, 'DBMS')))
    print('接頭辞 %s   候補 %d 個 (%.1fs)' % (show(pref), len(C), time.time() - t0))
    hits = []
    for N in C:
        ts = [tuple(expand(N, m)) for m in (1, 2, 3)]
        if len(set(ts)) != 3:
            continue
        if all(t in IMG for t in ts):
            hits.append((N, [IMG[t] for t in ts]))
    print('条件を満たす N: %d 個' % len(hits))
    for N, ns in hits:
        print('   %-60s  基本列 -> M<%s>' % (show(N), ','.join(map(str, ns))))
    return hits


def hunt2(Mstr, K=12, zcap=2):
    """`hunt` の高速版。

    expand(N,1) は必ず「N から最終列を落としたもの」なので、
    N<1> in IMG ということは **N = IMG の元 + 1 列**に限られる。
    そこだけを総当たりする。
    """
    M = parse(Mstr, 3)
    cur = rows3.b2d3(M)
    IMG, order = {}, []
    for n in range(1, K + 1):
        t = tuple(rows3.b2d3(expand(M, n)))
        IMG[t] = n
        order.append(t)
    print('M    %s' % show(M))
    print('いまの像 %s  std=%s' % (show(cur), isstd(cur, 'DBMS')))
    hits = []
    seen = set()
    for base in order:
        amax = base[-1][0] + 1 if base else 0
        for a in range(amax + 1):
            for b in range(max(a - 1, 0) + 1):
                for c in range(min(max(b - 1, 0), zcap) + 1):
                    N = base + ((a, b, c),)
                    if N in seen:
                        continue
                    seen.add(N)
                    if not isstd(N, 'DBMS'):
                        continue
                    ts = [tuple(expand(N, m)) for m in (1, 2, 3)]
                    if len(set(ts)) != 3 or not all(t in IMG for t in ts):
                        continue
                    hits.append((N, [IMG[t] for t in ts]))
    print('条件を満たす N: %d 個' % len(hits))
    for N, ns in hits:
        print('   %-64s 基本列 -> M<%s>' % (show(N), ','.join(map(str, ns))))
    return hits


# ---------------------------------------------------------------- 修正案
def closes_unitF(nxt, FIX):
    """`FIX` つきの closes_unit。

    'anchorC'   : (1,1,1) も「ユニットを閉じる次の列」と数える。
    'tailfirm'  : 「行列の末尾の分岐列は浅い」をやめる。
    """
    if nxt is None:
        return 'tailfirm' not in FIX
    if 'anchorC' in FIX and nxt == (1, 1, 1):
        return True
    return nxt[0] <= 1 and nxt[2] == 0


def padL(L, v, FIX):
    """L を長さ v まで Lat で伸ばしてから返す（'L' のとき）。"""
    if 'L' in FIX and len(L) < v:
        return tuple(Lat(L, k) for k in range(v))
    return L[:v]


def copy_shiftF(block, e, ps0, prev0, nxt_after, FIX):
    out, prev = [], prev0
    for i, c in enumerate(block):
        nxt = block[i + 1] if i + 1 < len(block) else nxt_after
        if c == ANCHOR or ('anchorP' in FIX and c == (1, 1, 1)):
            prev = 0
        if is_branch(c):
            shallow = (prev == 0) or closes_unitF(nxt, FIX)
            prev = 0 if shallow else 1
            dl = 0 if shallow else (e if c[1] > ps0 else 0)
        else:
            dl = e if c[1] > ps0 else 0
        out.append((c[0] + 1, c[1] + dl, c[2]))
    return out


def conv3F(M, d=0, L=(), F=(), ps=(0, 0), pw=(0, 0), first=True, force=False,
           st=None, nx=None, FIX=()):
    """rows3.conv3 のコピー ＋ 修正案スイッチ。

    FIX に入れられるもの:
      'resid'    残余を「もとの深さを保った森」として読む
      'L'        段の表 L を長さ v まで Lat で埋めてから継ぎ足す（穴を作らない）
      'anchorC'  closes_unit で (1,1,1) も「ユニットを閉じる次の列」と数える
      'anchorP'  (1,1,1) を通ったら状態機械の prev を 0 に戻す
      'tailfirm' 「行列の末尾の分岐列は浅い」をやめる
    """
    if st is None:
        st = {'ST': (), 'prev': None, 'dmap': []}
    if not M:
        return []
    p, r = M[0], M[1:]
    v, s2 = p[1], p[2]
    A, B = split0(p, r)

    if v == 0:
        base_d = base_s = 0
        pl2, force1 = 0, False
    else:
        e = Lat(L, v - 1)
        base_d, pl2, force1, base_s = e[0] + 1, e[1], e[2], e[3] + 1
    first1 = F[v] if v < len(F) else True

    if p == ANCHOR or ('anchorP' in FIX and p == (1, 1, 1)):
        st['prev'] = 0
    if is_branch(p) and base_s != base_d:
        nxt = M[1] if len(M) > 1 else nx
        shallow = (st['prev'] == 0) or closes_unitF(nxt, FIX)
        base = base_s if shallow else base_d
        st['prev'] = 0 if shallow else 1
    else:
        base = base_d

    lad1 = first1 and s2 == pl2 + 1 and (base <= s2 or force1)
    e1 = base + 1 if lad1 else (s2 + 1 if (s2 > 0 and base <= s2) else base)
    e2 = s2
    h1 = base if lad1 else e1
    lad0 = first and v == ps[0] + 1 and (d <= h1 or force)

    ST = st['ST']
    cols = []
    if lad0:
        cols.append((d, pw[0], pw[1]))
        ST = ST[:d] + ((pw[0], pw[1]),)
        dd = d + 1
    else:
        dd = fit(ST, d, h1)
        if dd is None:
            dd = max(d, len(ST))
    if lad1:
        cols.append((dd, base, pl2))
        ST = ST[:dd] + ((base, pl2),)
        dd += 1
    if not ok_place(ST, dd, e1):
        x = fit(ST, dd, e1)
        if x is not None:
            dd = x
    cols.append((dd, e1, e2))
    ST = ST[:dd] + ((e1, e2),)
    st['ST'] = ST
    st['dmap'] = st['dmap'][:p[0]] + [dd]

    fc = (not lad1) and first1 and s2 == pl2
    f0 = (not lad0) and first and (v, s2) == ps
    if e1 == base + 1 and v >= 1:
        Lb = padL(L, v - 1, FIX) + ((base, pl2, False, Lat(L, v - 1)[3]),)
    else:
        Lb = L
    LA = padL(Lb, v, FIX) + ((e1, s2, fc, e1),)
    FA = F[:v] + (False,)

    if lad0:
        for e in (0, 1):
            qlab = (ps[0] + e, ps[1])
            U, B2 = units_split(p, B, qlab)
            if not B2:
                continue
            q, r2 = B2[0], B2[1:]
            if (q[1], q[2]) != qlab or q[0] != p[0]:
                continue
            Aq, Bq = split0(q, r2)
            for na in (q, NOTLAST):
                pre = copy_shiftF([p] + list(A) + list(U), e, ps[0],
                                  st['prev'], na, FIX)
                if list(Aq[:len(pre)]) == pre:
                    break
            else:
                continue
            blk = [p] + list(A) + list(U)
            deep_end = is_branch(blk[-1]) and pre[-1][1] > blk[-1][1]
            rest2 = list(Aq[len(pre):])
            if rest2:
                if rest2[0][0] < p[0] + 1:
                    continue
                if (rest2[0][0] == p[0] + 1
                        and (rest2[0][1], rest2[0][2]) >= (v + e, s2) and e == 0):
                    continue
            elif e == 0 or not deep_end:
                continue
            Lr = padL(L, v, FIX) + (((base, pl2, fc, base) if e else (e1, s2, fc, e1)),)
            hd = lambda *ls: next((l[0] for l in ls if l), nx)
            rd = (d + 1 + e if (not rest2 or rest2[0][0] == p[0] + 1)
                  else dmap_at(st, rest2[0][0] - 1))
            cA = conv3F(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
                        U[0] if U else na, FIX)
            cU = conv3F(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na, FIX)
            if 'resid' in FIX:
                cR = conv_resid(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq), FIX)
            else:
                cR = conv3F(rest2, rd, Lr, (False,) * 12,
                            (v, s2), (e1, e2), False, False, st, hd(Bq), FIX)
            cB = conv3F(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx, FIX)
            return cols + cA + cU + cR + cB

    cA = conv3F(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
                B[0] if B else nx, FIX)
    cB = conv3F(B, d, L, FA, (v, s2), (e1, e2), False, False, st, nx, FIX)
    return cols + cA + cB


def conv_resid(rest, rd, Lr, ps, pw, st, nx, FIX):
    """残余を「もとの深さを保った森」として読む（修正案 'resid'）。

    いまの conv3 は残余をまるごと深さ `rd` の 1 本の木として読むので、
    残余の中でもとの行 0 が **rest[0][0] より小さい** 柱まで深さ `rd` に
    そろえてしまう。そこを、もとの深さの差だけ浅くして読み直す。
    """
    out = []
    while rest:
        m0 = rest[0][0]
        i = 1
        while i < len(rest) and rest[i][0] >= m0:
            i += 1
        head, tail = rest[:i], rest[i:]
        nx2 = tail[0] if tail else nx
        out += conv3F(head, rd, Lr, (False,) * 12, ps, pw, False, False,
                      st, nx2, FIX)
        if not tail:
            break
        rd = max(0, rd - (m0 - tail[0][0]))
        rest = tail
    return out


def b2d3F(M, FIX=()):
    return tuple(conv3F(list(M), FIX=FIX))


def score_fix(FIX, A6=None, verbose=0):
    """シート 1358 対と 生成 <=6 列での成績。"""
    f = lambda M: b2d3F(M, FIX)
    T = sheet3.load(1)
    ok = sum(1 for row, b, dd in T if tuple(f(b)) == dd)
    res = {'FIX': FIX, 'sheet': (ok, len(T))}
    if A6 is not None:
        W = [f(M) for M in A6]
        res['ns'] = sum(1 for N in W if not isstd(N, 'DBMS'))
        res['inj'] = len(set(W)) == len(W)
        res['ord'] = sum(1 for i in range(len(A6) - 1) if cmpmat(W[i], W[i + 1]) >= 0)
    return res


# ------------------------------------------- 修正案 'ruledepth'（rule.py の深さ表）
import rule as RULE


def conv3G(M, d=0, L=(), F=(), ps=(0, 0), pw=(0, 0), first=True, force=False,
           st=None, nx=None, FIX=(), D=None, off=0):
    """conv3F ＋ 分岐列の浅い/深いを `rule.depths` の表 `D` から読む版。

    `M` はつねに**もとの行列の連続部分**なので、先頭の添字 `off` を持ち回れば
    `D[off+k]` でその列の深さが引ける。写しの側 `pre` も `Aq` の添字で引く。
    """
    if st is None:
        st = {'ST': (), 'prev': None, 'dmap': []}
    if not M:
        return []
    p, r = M[0], M[1:]
    v, s2 = p[1], p[2]
    A, B = split0(p, r)
    oA, oB = off + 1, off + 1 + len(A)

    if v == 0:
        base_d = base_s = 0
        pl2, force1 = 0, False
    else:
        e = Lat(L, v - 1)
        base_d, pl2, force1, base_s = e[0] + 1, e[1], e[2], e[3] + 1
    first1 = F[v] if v < len(F) else True

    if p == ANCHOR:
        st['prev'] = 0
    if is_branch(p) and base_s != base_d:
        if D is not None:
            shallow = (D[off] == 0)
        else:
            nxt = M[1] if len(M) > 1 else nx
            shallow = (st['prev'] == 0) or closes_unitF(nxt, FIX)
            Mo = st.get('Mo')
            if Mo is not None and ('afterw' in FIX or 'hiclose' in FIX):
                pv = Mo[off - 1] if off >= 1 else None
                pv2 = Mo[off - 2] if off >= 2 else None
                onx = Mo[off + 1] if off + 1 < len(Mo) else None
                hi = RULE.hi_block(Mo, off)
                # after_w: 直前が「×w」の列 (k,0,0) でユニットの端にいるとき、
                # W_(w^2) 系（hi）で直前の分岐列が深いなら段は残る＝深い。
                if ('afterw' in FIX and st['prev'] == 1
                        and RULE.is_w_col(pv) and closes_unitF(onx, FIX)):
                    pnt = off > 0 and st['pim'][off - 1][0] == 0
                    shallow = not (hi and not pnt)
                # closes_hi_unit: (a,2,1)(a,2,0)(a,1,0) と積んだ直後に (1,1,1)
                # が来るなら段を上げずに閉じる＝浅い。
                if 'hiclose' in FIX and RULE.closes_hi_unit(
                        p, onx, pv, pv2, hi, RULE.is_repeat(Mo, off)):
                    shallow = True
        base = base_s if shallow else base_d
        st['prev'] = 0 if shallow else 1
    else:
        base = base_d

    lad1 = first1 and s2 == pl2 + 1 and (base <= s2 or force1)
    e1 = base + 1 if lad1 else (s2 + 1 if (s2 > 0 and base <= s2) else base)
    e2 = s2
    h1 = base if lad1 else e1
    lad0 = first and v == ps[0] + 1 and (d <= h1 or force)

    ST = st['ST']
    cols = []
    if lad0:
        cols.append((d, pw[0], pw[1]))
        ST = ST[:d] + ((pw[0], pw[1]),)
        dd = d + 1
    else:
        dd = fit(ST, d, h1)
        if dd is None:
            dd = max(d, len(ST))
    if lad1:
        cols.append((dd, base, pl2))
        ST = ST[:dd] + ((base, pl2),)
        dd += 1
    if not ok_place(ST, dd, e1):
        x = fit(ST, dd, e1)
        if x is not None:
            dd = x
    cols.append((dd, e1, e2))
    ST = ST[:dd] + ((e1, e2),)
    st['ST'] = ST
    st['dmap'] = st['dmap'][:p[0]] + [dd]

    fc = (not lad1) and first1 and s2 == pl2
    f0 = (not lad0) and first and (v, s2) == ps
    if e1 == base + 1 and v >= 1:
        Lb = padL(L, v - 1, FIX) + ((base, pl2, False, Lat(L, v - 1)[3]),)
    else:
        Lb = L
    LA = padL(Lb, v, FIX) + ((e1, s2, fc, e1),)
    FA = F[:v] + (False,)

    if lad0:
        for e in (0, 1):
            qlab = (ps[0] + e, ps[1])
            U, B2 = units_split(p, B, qlab)
            if not B2:
                continue
            oU, oq = oB, oB + len(U)
            q, r2 = B2[0], B2[1:]
            if (q[1], q[2]) != qlab or q[0] != p[0]:
                continue
            Aq, Bq = split0(q, r2)
            oAq = oq + 1
            oBq = oAq + len(Aq)
            blk = [p] + list(A) + list(U)
            for na in (q, NOTLAST):
                if D is not None:
                    # 写しの側の深さは、写しが載っている Aq の添字から引く
                    pre = [(c[0] + 1,
                            c[1] + ((e if c[1] > ps[0] else 0)
                                    if (not is_branch(c)
                                        or (oAq + i < len(D) and D[oAq + i]))
                                    else 0),
                            c[2]) for i, c in enumerate(blk)]
                else:
                    pre = copy_shiftF(blk, e, ps[0], st['prev'], na, FIX)
                if list(Aq[:len(pre)]) == pre:
                    break
            else:
                continue
            deep_end = is_branch(blk[-1]) and pre[-1][1] > blk[-1][1]
            rest2 = list(Aq[len(pre):])
            oR = oAq + len(pre)
            if rest2:
                if rest2[0][0] < p[0] + 1:
                    continue
                if (rest2[0][0] == p[0] + 1
                        and (rest2[0][1], rest2[0][2]) >= (v + e, s2) and e == 0):
                    continue
            elif e == 0 or not deep_end:
                continue
            Lr = padL(L, v, FIX) + (((base, pl2, fc, base) if e else (e1, s2, fc, e1)),)
            hd = lambda *ls: next((l[0] for l in ls if l), nx)
            rd = (d + 1 + e if (not rest2 or rest2[0][0] == p[0] + 1)
                  else dmap_at(st, rest2[0][0] - 1))
            cA = conv3G(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
                        U[0] if U else na, FIX, D, oA)
            cU = conv3G(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na,
                        FIX, D, oU)
            if 'resid' in FIX:
                cR = conv_residG(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq),
                                 FIX, D, oR)
            else:
                cR = conv3G(rest2, rd, Lr, (False,) * 12,
                            (v, s2), (e1, e2), False, False, st, hd(Bq), FIX, D, oR)
            cB = conv3G(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                        FIX, D, oBq)
            return cols + cA + cU + cR + cB

    # 'sibbody': 行 1 の影を立てた柱の**兄弟**は、影の横ではなく本体の横に付く。
    db = dd if ('sibbody' in FIX and lad1) else d
    dc = dd if ('sibbody0' in FIX and lad1 and not lad0) else d
    if 'sibbody0' in FIX:
        db = dc
    cA = conv3G(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
                B[0] if B else nx, FIX, D, oA)
    cB = conv3G(B, db, L, FA, (v, s2), (e1, e2), False, False, st, nx, FIX, D, oB)
    return cols + cA + cB


def conv_residG(rest, rd, Lr, ps, pw, st, nx, FIX, D, off):
    out = []
    while rest:
        m0 = rest[0][0]
        i = 1
        while i < len(rest) and rest[i][0] >= m0:
            i += 1
        head, tail = rest[:i], rest[i:]
        nx2 = tail[0] if tail else nx
        out += conv3G(head, rd, Lr, (False,) * 12, ps, pw, False, False,
                      st, nx2, FIX, D, off)
        if not tail:
            break
        rd = max(0, rd - (m0 - tail[0][0]))
        off += i
        rest = tail
    return out


def b2d3G(M, FIX=(), ruledepth=False):
    D = RULE.depths(tuple(M)) if ruledepth else None
    from core import pim
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M),
          'pim': pim(tuple(M)) if M else []}
    return tuple(conv3G(list(M), FIX=FIX, D=D, st=st))


def score_G(FIX, ruledepth=False, A6=None):
    f = lambda M: b2d3G(M, FIX, ruledepth)
    T = sheet3.load(1)
    bad = [(row, b, dd, tuple(f(b))) for row, b, dd in T if tuple(f(b)) != dd]
    res = {'sheet': (len(T) - len(bad), len(T)), 'bad': bad}
    if A6 is not None:
        W = [f(M) for M in A6]
        res['ns'] = sum(1 for N in W if not isstd(N, 'DBMS'))
        res['inj'] = len(set(W)) == len(W)
        res['ord'] = sum(1 for i in range(len(A6) - 1) if cmpmat(W[i], W[i + 1]) >= 0)
    return res


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'sheet'
    if cmd == 'sheet':
        sheet_report()
    elif cmd == 'ns':
        ns_report(int(sys.argv[2]) if len(sys.argv) > 2 else 7)
    elif cmd == 'hunt':
        for s in ['(0,0,0)(1,1,1)(2,0,0)(3,1,1)',
                  '(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)',
                  '(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)',
                  '(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)(4,0,0)',
                  '(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)(4,1,0)',
                  '(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)(4,2,0)']:
            hunt2(s)
            print()
    elif cmd == 'fix':
        A6 = sorted(gen3('BMS', 6, zcap=1), key=key)
        B = ('resid', 'L', 'afterw', 'hiclose')
        for FIX in [(), ('resid',), ('L',), ('anchorC',), ('tailfirm',),
                    ('resid', 'L'), ('resid', 'L', 'afterw'),
                    ('resid', 'L', 'hiclose'), B,
                    B + ('sibbody',), B + ('sibbody0',)]:
            r = score_G(FIX, False, A6)
            print('%-34s シート %4d/%d  <=6列: 非標準 %d 単射 %s 順序違反 %d'
                  % (','.join(FIX) or '(なし)', r['sheet'][0], r['sheet'][1],
                     r['ns'], r['inj'], r['ord']))
        r = score_G(('ruledepth-marker',), True, A6)
        print('%-34s シート %4d/%d  <=6列: 非標準 %d 単射 %s 順序違反 %d'
              % ('rule.depths を丸ごと使う', r['sheet'][0], r['sheet'][1],
                 r['ns'], r['inj'], r['ord']))
