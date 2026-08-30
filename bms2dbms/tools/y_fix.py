"""課題 D2: 残る非標準と共終性 C1 の破れを潰すための、conv3 の候補比較台。

`rows3.conv3` (= v10, 候補1) をまるごと写して、争点になっている 1 箇所を
**候補 1 / 2 / 3** で切り替えられるようにしたもの。rows3.py は読むだけ。

争点（C3 が残したもの）: P6 = (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)
の正しい像はどれか。

  候補1 (v10)      ...(3,2,1)(4,0,0)(5,1,0)(6,2,1)(5,1,0)(6,2,1)
  候補2 (sibbody2) ...(3,2,1)(4,0,0)(5,1,0)(6,2,1)(6,1,0)(7,2,1)
  候補3 (rule)     ...(3,2,1)(4,0,0)(5,1,0)(6,2,1)(6,2,0)(7,3,1)

候補 1/2 は conv3 の**同じ 1 行**（兄弟をどの深さに付けるか）の違いなので
この中で切り替えられる。候補 3 は `rule.convert` の別機構（`rule.depths`）
なので中に埋め込めない。ここでは `rule.convert` をまるごと第 3 の変換器として
同じ土俵で採点する。

**2026-08-27（課題 D5）: 候補4 が採用されて `rows3.conv3` は v11 になった。**
だから `F(1)`（= 候補1 = v10、アンカーで段をリセットする版）は
**もう rows3.b2d3 と同じではない**。旧版と新版を比べたいときは
`F(1)` が旧 v10、`rows3.b2d3` と `F(4)` が新 v11 である。

採用の根拠（測定, 課題 D5）:

| 指標 | 候補1 = v10 | 候補4 = v11（採用） |
|---|---|---|
| 生成 <=7 列 77282 個の像 | — | **1 ビットも変わらない**（差 0） |
| 展開閉包 28158 個の像 | — | 45 個だけ変わる |
| 展開閉包 非標準 / 潰れ / 順序違反 | 103 / 1 / 4 | 103 / 1 / 4 |
| 共終性 C1 の破れ（<=6 列） | 136 | **121**（121 ⊂ 136、片側） |
| ImgClosedT 速い道の外れ A（<=6 列） | 342 | **327**（327 ⊂ 342、片側） |
| 像が変わった 45 個の d2b3 往復 | 30/45（衝突 15） | **45/45** |

使い方:
    python3 y_fix.py c1 6        共終性 C1 の破れを分類（候補1, <=6 列）
    python3 y_fix.py battery 6   候補 1/2/3 の全指標
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import parse, show, expand, isstd, cmpmat
import rows3
from rows3 import (gen3, key, split0, shift1, units_split, predlab, ok_place,
                   fit, NOTLAST, ANCHOR, closes_unit, par0, hi_block, is_repeat,
                   is_w_col, closes_hi_unit, Lat, padL, is_branch, dmap_at,
                   copy_shift, contrPre, pad, two)
from rows2 import convC as convC2
import rule


# ================================================================ 変換（候補切替）
def conv3Y(M, d=0, L=(), F=(), ps=(0, 0), pw=(0, 0), first=True, force=False,
           st=None, nx=None, off=0, cand=1):
    """rows3.conv3 の写し。差分は末尾の `db`（兄弟を付ける深さ）だけ。"""
    if st is None:
        st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0}
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

    if p == ANCHOR and cand != 4:
        # 候補4（診断用）: 型D の破れは「写しの中のアンカーで prev が 0 に戻り、
        # もとでは深く書かれた分岐列が写しでは浅く書かれる」ことで起きる、という
        # 見立てを試す版。アンカーでのリセットをやめるだけ。
        st['prev'] = 0
    if is_branch(p) and base_s != base_d:
        nxt = M[1] if len(M) > 1 else nx
        shallow = (st['prev'] == 0) or closes_unit(nxt)
        Mo = st['Mo']
        pv = Mo[off - 1] if off >= 1 else None
        pv2 = Mo[off - 2] if off >= 2 else None
        onx = Mo[off + 1] if off + 1 < len(Mo) else None
        hi = hi_block(Mo, off)
        if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):
            pnt = off > 0 and par0(Mo, off - 1) == 0
            shallow = not (hi and not pnt)
        if closes_hi_unit(p, onx, pv, pv2, hi, is_repeat(Mo, off)):
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
        Lb = padL(L, v - 1) + ((base, pl2, False, Lat(L, v - 1)[3]),)
    else:
        Lb = L
    LA = padL(Lb, v) + ((e1, s2, fc, e1),)
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
            oAq, oBq = oq + 1, oq + 1 + len(Aq)
            for na in (q, NOTLAST):
                pre = contrPre(p, U, A, e, ps[0], st['prev'], na)
                if list(Aq[:len(pre)]) == pre:
                    break
            else:
                continue
            blk = [p] + list(A) + list(U)
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
            Lr = padL(L, v) + (((base, pl2, fc, base) if e else (e1, s2, fc, e1)),)
            hd = lambda *ls: next((l[0] for l in ls if l), nx)
            cA = conv3Y(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
                        U[0] if U else na, oA, cand)
            cU = conv3Y(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na,
                        oU, cand)
            rd = (d + 1 + e if (not rest2 or rest2[0][0] == p[0] + 1)
                  else dmap_at(st, rest2[0][0] - 1))
            cR = conv_residY(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq), oR,
                             cand)
            cB = conv3Y(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                        oBq, cand)
            st['nc'] = st.get('nc', 0) + 1
            return cols + cA + cU + cR + cB

    # ---- ここが争点。兄弟 B をどの深さに付けるか。
    db = d
    if cand == 2 and lad1 and not lad0:
        # sibbody2: 行 1 の影を立てた柱で、行 0 の影は立てておらず、かつ
        # 祖先の鎖に行 2 を使った柱があるなら、兄弟は影の横ではなく本体の横。
        if any(ST[y][1] >= 1 for y in range(min(dd, len(ST)))):
            db = dd
    cA = conv3Y(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
                B[0] if B else nx, oA, cand)
    cB = conv3Y(B, db, L, FA, (v, s2), (e1, e2), False, False, st, nx, oB, cand)
    return cols + cA + cB


def conv_residY(rest, rd, Lr, ps, pw, st, nx, off, cand):
    out = []
    while rest:
        m0 = rest[0][0]
        i = 1
        while i < len(rest) and rest[i][0] >= m0:
            i += 1
        head, tail = rest[:i], rest[i:]
        nx2 = tail[0] if tail else nx
        out += conv3Y(head, rd, Lr, (False,) * 12, ps, pw, False, False,
                      st, nx2, off, cand)
        if not tail:
            break
        rd = max(0, rd - (m0 - tail[0][0]))
        off += i
        rest = tail
    return out


def b2d3y(M, cand=1):
    if cand == 3:
        return tuple(rule.convert(tuple(M)))
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0}
    return tuple(conv3Y(list(M), st=st, cand=cand))


def F(cand):
    return lambda M: b2d3y(M, cand)


CANDS = [(1, 'v10'), (2, 'sibbody2'), (3, 'rule')]
CANDS4 = CANDS + [(4, 'noanchor')]    # 候補4 = 採用された v11（= いまの rows3.conv3）


# ================================================================ 共終性
def cof_detail(f, M, mm=10, nn=24, mc=40):
    """(C1 の破れの最小 m, C2 の破れの最小 n, N, E, G)。破れなければ None。"""
    N = f(M)
    E = [tuple(expand(N, m)) for m in range(1, mc + 1)]
    G = [tuple(f(expand(M, n))) for n in range(1, nn + 1)]
    b1 = b2 = None
    for m in range(mm):
        if not any(cmpmat(E[m], g) <= 0 for g in G):
            b1 = m + 1
            break
    for n in range(nn):
        if not any(cmpmat(G[n], e) <= 0 for e in E):
            b2 = n + 1
            break
    return b1, b2, N, E, G


def cof_counts(f, A, mm=10, nn=24, mc=40, collect=False):
    c1, c2 = [], []
    for i, M in enumerate(A):
        if len(M) < 2:
            continue
        if i % 500 == 0:
            core._exp_memo.clear()
            core._isstd_memo.clear()
            core._flat_memo.clear()
        b1, b2, N, E, G = cof_detail(f, M, mm, nn, mc)
        if b1 is not None:
            c1.append((M, b1, N) if collect else M)
        if b2 is not None:
            c2.append((M, b2, N) if collect else M)
    return c1, c2


# ================================================================ C1 の分類
def c1_class(lim=6, cand=1, dump=0):
    """共終性 C1 の破れを分類する。"""
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    f = F(cand)
    t0 = time.time()
    c1, c2 = cof_counts(f, A, collect=True)
    print('候補%d  <=%d 列 %d 個   C1 の破れ %d   C2 の破れ %d   (%.1fs)'
          % (cand, lim, len(A), len(c1), len(c2), time.time() - t0))
    return A, c1, c2


def firstdiff(a, b):
    """列の並びで最初に食い違う添字（無ければ短いほうの長さ）。"""
    for i in range(min(len(a), len(b))):
        if a[i] != b[i]:
            return i
    return min(len(a), len(b))


def c1_table(lim=6, cand=1, dump=40):
    """C1 の破れを『どの m で破れるか』『何が違うか』で分類する。"""
    from collections import Counter, defaultdict
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    f = F(cand)
    c1, c2 = cof_counts(f, A, collect=True)
    print('候補%d  <=%d 列 %d 個   C1 の破れ %d   C2 の破れ %d'
          % (cand, lim, len(A), len(c1), len(c2)))
    grp = defaultdict(list)
    for M, m, N in c1:
        G = f(expand(M, 24))
        E = tuple(expand(N, m))
        j = firstdiff(E, G)
        # 破れの型: 像側 E[j] と BMS 側 G[j] の差
        typ = (E[j] if j < len(E) else None, G[j] if j < len(G) else None)
        grp[typ].append((M, m, N, j))
    print('  破れの型（像<m> と f(M<24>) が最初に食い違う列の対）')
    for t, L in sorted(grp.items(), key=lambda kv: -len(kv[1])):
        print('    %-22s vs %-22s : %d 件' % (t[0], t[1], len(L)))
    print('  最小 m の分布 :', dict(Counter(m for M, m, N in c1)))
    print('  列数の分布   :', dict(Counter(len(M) for M, m, N in c1)))
    return A, c1, c2, grp


# ================================================================ 全指標
def metrics(cand, A6, A7, closure, nn=24):
    """1 つの候補についての全指標。"""
    import sheet3
    f = F(cand)
    out = {}
    T = sheet3.load(1)
    out['sheet'] = (sum(1 for row, b, d in T if tuple(f(b)) == d), len(T))
    for tag, A in (('6', A6), ('7', A7)):
        W = [f(M) for M in A]
        out['ns' + tag] = sum(1 for N in W if not isstd(N, 'DBMS'))
        out['inj' + tag] = (len(set(W)) == len(W))
        out['ord' + tag] = sum(1 for i in range(len(A) - 1)
                               if cmpmat(W[i], W[i + 1]) >= 0)
        core._isstd_memo.clear()
        core._flat_memo.clear()
    out['z0'] = sum(1 for M in A6 if all(c[2] == 0 for c in M)
                    and f(M) != pad(convC2(two(M))))
    out['clo'] = sum(1 for M in closure if not isstd(f(M), 'DBMS'))
    core._isstd_memo.clear()
    A5 = [M for M in A6 if len(M) <= 5]
    c1a, c2a = cof_counts(f, A5, nn=nn, collect=True)
    c1b, c2b = cof_counts(f, A6, nn=nn, collect=True)
    out['c1_5'], out['c2_5'] = len(c1a), len(c2a)
    out['c1_6'], out['c2_6'] = len(c1b), len(c2b)
    out['c1set'] = set(tuple(M) for M, m, N in c1b)
    out['c2set'] = set(tuple(M) for M, m, N in c2b)
    return out


def battery(lim6=6, lim7=7, cands=(1, 2, 3)):
    t0 = time.time()
    A6 = sorted(gen3('BMS', lim6, zcap=1), key=key)
    A7 = sorted(gen3('BMS', lim7, zcap=1), key=key)
    print('gen <=%d %d 個 / <=%d %d 個  (%.0fs)'
          % (lim6, len(A6), lim7, len(A7), time.time() - t0))
    clo = set()
    for M in A6:
        for n in range(1, 5):
            clo.add(tuple(expand(M, n)))
    clo = sorted(clo, key=key)
    core._exp_memo.clear()
    print('展開閉包 {M<n>: M in gen<=%d, n<=4} = %d 個  (%.0fs)'
          % (lim6, len(clo), time.time() - t0))
    R = {}
    for c in cands:
        nm = dict(CANDS4)[c]
        R[c] = metrics(c, A6, A7, clo)
        print('  候補%d (%s) 済 %.0fs  %s' % (c, nm, time.time() - t0,
              {k: v for k, v in R[c].items() if not k.endswith('set')}))
    hdr = ['指標'] + ['候補%d %s' % (c, dict(CANDS4)[c]) for c in cands]
    rows_ = [
        ('シート (満点 1354/1358)', lambda r: '%d/%d' % r['sheet']),
        ('gen<=%d 非標準' % lim6, lambda r: r['ns6']),
        ('gen<=%d 単射' % lim6, lambda r: 'ok' if r['inj6'] else 'NG'),
        ('gen<=%d 順序違反' % lim6, lambda r: r['ord6']),
        ('gen<=%d z=0 不一致' % lim6, lambda r: r['z0']),
        ('gen<=%d 非標準' % lim7, lambda r: r['ns7']),
        ('gen<=%d 単射' % lim7, lambda r: 'ok' if r['inj7'] else 'NG'),
        ('gen<=%d 順序違反' % lim7, lambda r: r['ord7']),
        ('展開閉包 非標準', lambda r: r['clo']),
        ('C1 の破れ <=5', lambda r: r['c1_5']),
        ('C1 の破れ <=6', lambda r: r['c1_6']),
        ('C2 の破れ <=5', lambda r: r['c2_5']),
        ('C2 の破れ <=6', lambda r: r['c2_6']),
    ]
    w = max(len(h) for h in hdr)
    print()
    print('| %-26s | %s |' % (hdr[0], ' | '.join('%-14s' % h for h in hdr[1:])))
    print('|%s|%s|' % ('-' * 28, '|'.join('-' * 16 for c in cands)))
    for name, g in rows_:
        print('| %-26s | %s |' % (name, ' | '.join('%-14s' % g(R[c]) for c in cands)))
    print()
    for c in cands:
        for d in cands:
            if c < d:
                a, b = R[c]['c1set'], R[d]['c1set']
                print('C1: 候補%d だけ破れる %d / 候補%d だけ %d / 共通 %d'
                      % (c, len(a - b), d, len(b - a), len(a & b)))
    return R


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'battery'
    if cmd == 'c1':
        c1_table(int(sys.argv[2]) if len(sys.argv) > 2 else 6,
                 int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    else:
        battery()


# ================================================================ 展開閉包の検査
def closure_set(lim=6, nmax=4):
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    clo = set()
    for M in A:
        clo.add(tuple(M))
        for n in range(1, nmax + 1):
            clo.add(tuple(expand(M, n)))
    core._exp_memo.clear()
    return sorted(clo, key=key)


def clos_check(lim=6, nmax=4, cands=(1, 2, 3)):
    """展開閉包 {M} ∪ {M<n>} の上で 非標準 / 単射 / 順序 を測る。

    もとの gen<=6 だけを見ると 3 つとも「非標準 0・単射 ok・順序違反 0」で
    差がつかないが、**展開閉包では差がつく**。ImgClosedT が要求するのは
    まさに『展開したものの像も像の展開に一致する』ことなので、閉包の上での
    健全性のほうが証明に近い。
    """
    C = closure_set(lim, nmax)
    print('展開閉包 (gen<=%d, n<=%d): %d 個' % (lim, nmax, len(C)))
    out = {}
    for c in cands:
        f = F(c)
        W = [f(M) for M in C]
        ns = sum(1 for N in W if not isstd(N, 'DBMS'))
        core._isstd_memo.clear()
        col = len(C) - len(set(W))
        ordb = [i for i in range(len(C) - 1) if cmpmat(W[i], W[i + 1]) >= 0]
        out[c] = (ns, col, len(ordb))
        print('  候補%d %-9s  非標準 %5d   同じ像に潰れた対 %4d   順序違反 %5d'
              % (c, dict(CANDS4)[c], ns, col, len(ordb)))
        for i in ordb[:3]:
            print('        %-46s -> %s' % (show(C[i]), show(W[i])))
            print('        %-46s -> %s' % (show(C[i + 1]), show(W[i + 1])))
    return C, out


def imgclosed(lim=6, mm=4, cands=(1, 2, 3)):
    """ImgClosedT の直接検査: (f A)<m> が f(BMS 標準形) になっているか。

    逆像を探すのは重いので、**まず f(A<n>) の中にあるか**を見る（n<=nn）。
    見つからなければ「像の集合（閉包の像）」の中にあるかを見る。
    """
    C = closure_set(lim, 4)
    A = [M for M in C if len(M) <= lim]
    res = {}
    for c in cands:
        f = F(c)
        S = set(f(M) for M in C)
        miss = 0
        tot = 0
        ex = []
        for M in A:
            if len(M) < 2:
                continue
            N = f(M)
            for m in range(1, mm + 1):
                E = tuple(expand(N, m))
                tot += 1
                if E not in S:
                    miss += 1
                    if len(ex) < 3:
                        ex.append((M, m, N, E))
        res[c] = (miss, tot)
        print('  候補%d %-9s  (f A)<m> が閉包の像に無い : %d / %d'
              % (c, dict(CANDS4)[c], miss, tot))
        for M, m, N, E in ex:
            print('        A=%s  m=%d' % (show(M), m))
            print('          (f A)<m> = %s' % show(E))
    return res


def imgclosed2(lim=6, mm=4, cands=(1, 2, 3)):
    """ImgClosedT の直接検査（逆写像で逆像を作って前向きに確かめる）。

    E = (f A)<m> について `inv3.d2b3(E)` で BMS 側の候補 B を作り、
    B が BMS 標準形で f(B) == E なら ImgClosedT はこの (A,m) で成り立つ。
    d2b3 は候補1（v10）の像の綴りに合わせて書かれているので候補 2/3 には
    不利だが、**同じ物差し**ではある。
    """
    from inv3 import d2b3
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    for c in cands:
        f = F(c)
        ok = ns = bad = tot = 0
        ex = []
        for M in A:
            if len(M) < 2:
                continue
            N = f(M)
            for m in range(1, mm + 1):
                E = tuple(expand(N, m))
                tot += 1
                if not isstd(E, 'DBMS'):
                    ns += 1
                    continue
                try:
                    B = d2b3(E)
                except Exception:
                    B = None
                if B and isstd(B, 'BMS') and tuple(f(B)) == E:
                    ok += 1
                else:
                    bad += 1
                    if len(ex) < 2:
                        ex.append((M, m, E, B))
            core._exp_memo.clear()
            core._isstd_memo.clear()
        print('  候補%d %-9s  逆像あり %5d / %5d   像が非標準 %4d   逆像なし %5d'
              % (c, dict(CANDS4)[c], ok, tot, ns, bad))
        for M, m, E, B in ex:
            print('        A=%s  m=%d' % (show(M), m))
            print('          (f A)<m> = %s' % show(E))


# ================================================================ 測定結果
RESULTS = """課題 D2 の測定（2026-08-27, y_fix.py）

== 1. 共終性 C1 の破れ 136 件（候補1 v10, gen<=6 列 8387 個）の分類 ==

破れの定義: ある m<=10 について、どの n<=24 でも  f(M)<m> <= f(M<n>)  が成り立たない。
f(M<n>) は n について単調増加なので、これは f(M)<m> > f(M<24>) と同じ。
nn を 120 に伸ばしても破れは消えない（先頭 12 件で確認）。

  最小 m の分布   m=2 が 134 件、m=3 が 1 件、m=1 が 1 件
  列数の分布      6 列 129 件、5 列 7 件
  C2 の破れ       0 件

  f(M)<m> と f(M<24>) が最初に食い違う列の対で 2 型に割れる（型O は 0 件）:

  | 型 | 件数 | 食い違う列（像側 vs BMS 側） | 何が違うか |
  |----|------|------------------------------|------------|
  | D  |  89  | 行 0 が同じ・行 1 が像側で +1 | 写しの中の分岐列が浅く書かれる |
  | I  |  47  | 行 0 が像側で +1              | f(M<n>) が浅い柱を先に挟む |

  型D の代表  M = (0,0,0)(1,1,1)(2,1,0)(1,1,1)(1,1,0)(1,1,0)
      N        = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,2,0)(3,2,1)(2,1,0)(2,1,0)
      N<2>     = ...(2,1,0)(2,0,0)(3,1,0)(4,2,1)(5,2,0)(4,2,1)(3,1,0)
      f(M<3>)  = ...(2,1,0)(2,0,0)(3,1,0)(4,2,1)(5,1,0)(4,2,1)(3,1,0)
      もとの (2,1,0) は「深い」ので像で (4,2,0) になるのに、M<3> の中の同じ役の
      柱 (4,1,0) は直前のアンカー (1,1,0) で prev が 0 に戻るため「浅い」と判定され、
      像が (5,1,0) になる。段の状態機械が写しをまたいで一貫しない。

  型I の代表  M = (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,1)
      N        = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,0,0)(5,1,0)(6,2,1)(6,2,1)
      N<2>     = ...(6,2,1)(6,2,0)(7,3,1)
      f(M<2>)  = ...(6,2,1)(5,1,0)(6,2,1)          <- M<2> はまさに争点の P6
      f(M<3>)  = ...(6,2,1)(5,1,0)(6,2,1)(6,2,0)(7,3,1)
      f(M<n>) は N<2> の前に (5,1,0)(6,2,1) を挟むので、永久に N<2> より小さい。

== 2. 争点 P6 の決着（型I の正体） ==

M = (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,1) は 5 列の BMS 標準形で、
**3 候補とも同じ像**を出す:  N = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,0,0)(5,1,0)(6,2,1)(6,2,1)。
そして  M<2> = P6  ちょうど。だから ImgClosedT が要求するのは

    N<2> = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,0,0)(5,1,0)(6,2,1)(6,2,0)(7,3,1) = conv3 B

で、自然な B は M<2> = P6。これは**候補3 の像そのもの**（候補1 は (5,1,0)(6,2,1)、
候補2 は (6,1,0)(7,2,1) を出す）。しかも候補1・候補2 はこの M で C1 を破る。
したがって **P6 の綴りは候補3 が正しい**。

裏づけ: 候補1 が C1 を破る 136 個をそのまま候補3 で測ると

    候補1  136/136 破れ    候補2  136/136 破れ    候補3  89/136 破れ

直った 47 件のうち 46 件が型I（型I 47 件中 46 件が直る、型D 89 件中は 1 件だけ）。
**型I = 候補3 の綴りが直す欠陥、型D = どの候補も直さない別の欠陥。**

== 3. しかし変換器としての候補3（rule.convert）は採れない ==

閉包の z=0 の部分（3961 個）で、**証明済みの 2 行版 rows2.convC と 35 件食い違う**。
壊れ方は直和の潰し:

    M = (0,0,0)(1,1,0)(1,0,0)(2,1,0)(2,0,0) を 2 個つないだもの
    rule -> (0,0,0)(1,0,0)(2,1,0)(2,0,0)          （1 個ぶんに潰れる）
    正   -> (0,0,0)(1,0,0)(2,1,0)(2,0,0)(0,0,0)(1,0,0)(2,1,0)(2,0,0)

候補1・候補2 はこの範囲で食い違い 0。z=0 は答えが Lean で証明済みなので、
これは候補3 の**確定した誤り**（rule.convert の dedup / 吸収が効きすぎる）。

== 4. 全指標の表 ==

  gen<=6 = 8387、gen<=7 = 77282、シート 3 行 z<=1 = 1358 対（満点 1354）、
  展開閉包 = {M} ∪ {M<n> : M in gen<=6, n<=4} = 28158 個。

  | 指標                                   | 候補1 v10 | 候補2 sibbody2 | 候補3 rule |
  |----------------------------------------|-----------|----------------|------------|
  | シート（満点 1354/1358）               | 1354      | 1354           | 1357 (*1)  |
  | gen<=6 非標準                          | 0         | 0              | 0          |
  | gen<=6 単射 / 順序違反 / z=0 不一致    | ok/0/0    | ok/0/0         | ok/0/0     |
  | gen<=7 非標準                          | 3         | 1              | **0**      |
  | gen<=7 単射 / 順序違反                 | ok / 0    | ok / 0         | **NG / 6** |
  | 展開閉包 非標準                        | 103       | 115            | **52**     |
  | 展開閉包 同じ像に潰れた対              | 1         | 1              | **34**     |
  | 展開閉包 順序違反                      | 4         | 4              | **51**     |
  | 閉包の z=0 部分 3961 で convC と不一致 | **0**     | **0**          | **35**     |
  | 共終性 C1 の破れ <=5 列 / <=6 列       | 7 / 136   | 8 / 149        | (*2)       |
  | 共終性 C2 の破れ <=5 列 / <=6 列       | 0 / 0     | 0 / 4          | (*2)       |
  | C1 を破る 136 個での再測定             | 136       | 136            | **89**     |
  | ImgClosedT: (f A)<m> の逆像を d2b3 が  | 27597     | 27546          | 27314      |
  |   出せた数（/33544, m<=4, gen<=6）     |           |                |            |

  (*1) シート 1357 は良いのではなく悪い。増えた 3 行は 891/897/898 で、
       NOTES §「シート行 891/897/898 も誤り」の通り**採用すると単射が壊れる**。
       実際 gen<=7 で単射 NG・順序違反 6 が出るのはこれと同根。
  (*2) rule.convert は expand(M,24) のような長い行列で探索が走って重く、
       gen<=6 の全数（8387 x 64 回の変換）は現実的な時間で終わらなかった。
       代わりに「候補1 が破る 136 個」で測った（表の下から 2 行目）。

  候補1 と候補2 の C1 破れの包含関係: 共通 136 / 候補1 だけ 0 / 候補2 だけ 13。
  **候補2 は候補1 の破れを 1 つも直さず、13 件足すだけ**（完全に片側）。

== 5. 結論 ==

* 候補2（sibbody2）は**落ちる**。非標準を 3->1 に減らすが、C1 を 136->149、
  C2 を 0->4、閉包の非標準を 103->115 に増やす。良くなる指標が非標準だけ。
* 候補3（rule.convert）は**変換器としては落ちる**（z=0 で証明済みの答えと 35 件食い違い、
  閉包で 34 組が潰れる）。しかし **P6 の綴りとしては正しい**。
* 候補1（v10）は変換器としては最良のまま。**ただし P6 の像は間違っている。**

  したがって「勝った候補」は 1 つに決まらない。決まったのは
  **P6 の像は候補3 の綴り ...(6,2,1)(6,2,0)(7,3,1) である**ことと、
  **共終性 C1 の破れは 2 つの独立な欠陥（型D 89 / 型I 47）に割れる**ことの 2 つ。

== 6. おまけ: 型D の見立ての検査（候補4 = noanchor） ==

型D の見立て「写しの中のアンカー (1,1,0) で prev が 0 に戻るせいで、もとでは
深く書かれた分岐列が写しでは浅く書かれる」を試すため、`p == ANCHOR` での
`st['prev'] = 0` を**やめただけ**の版を測った（`cand=4`）。

  | 指標                     | 候補1 v10 | 候補4 noanchor |
  |--------------------------|-----------|----------------|
  | シート                   | 1354/1358 | 1354/1358      |
  | gen<=6 非標準/単射/順序/z=0 | 0/ok/0/0 | 0/ok/0/0       |
  | gen<=7 非標準/単射/順序  | 3/ok/0    | 3/ok/0         |
  | C1 の破れ <=6 列         | 136       | **121**        |
  | C2 の破れ <=6 列         | 0         | 0              |
  | 型D 89 個での破れ        | 89        | **74**         |
  | 型I 47 個での破れ        | 47        | 47             |

**測った範囲では 1 つも悪くならずに C1 の破れが 136 -> 121 に減る**（型D を 15 件
直し、型I は 1 件も直さない）。見立ての方向は合っているが、prev のリセットを
やめるだけでは足りない（残り 74 件）。ここが型D の次の一手。
"""
