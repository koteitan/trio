"""G2 段 2: 破れた対 (A,m,T) について「T のどの柱から先が像で有り得ないか」を出す。

  maxpre(A,m,T) = max{ lcp(conv3 P, T) : P は BMS 3 行 z<2 標準形の接頭辞, P <= A }

`search2` と同じ木を歩くが、**一致を探すのではなく lcp の最大**を取る。
上限 `P <= A`（`hi_state`）だけを使う（下限 `A<m-1>` は sandwich の破れが
既知なので使わない）。`k = maxpre` が「先頭から数えて最初に像で有り得なくなる
柱の位置」であり、`T[k]` がその柱。

`T = expand(conv3 A, m)` なので、`T[k]` は `conv3 A` の第 `src` 柱の写しである。
`provc` が `conv3 A` の柱ごとに出どころを記録しているので、`src` から
「どの分岐が出した柱か」が引ける。
"""
import sys, os, time, collections, pickle
import multiprocessing as mp
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import core, rows3, provc
from core import expand, isstd, show, pim
from m_imgclosed import flat, lcp, hi_state, lo_state


def maxpre(A, T, SL=4, nodecap=40000, Lcap=None):
    """T の接頭辞のうち、像として実現できる最長のもの（の長さ）と証人 P。"""
    fhi = flat(tuple(A))
    LT = len(T)
    if Lcap is None:
        Lcap = (3 * LT + 1) // 2
    best = [0, None]
    cnt = [0]
    cap = [False]

    def rec(S, fs, hst):
        if len(S) >= Lcap:
            return
        amax = (S[-1][0] + 1) if S else 0
        for a in range(amax + 1):
            for b in range(a + 1):
                for c in range(min(b, 1) + 1):
                    P = S + ((a, b, c),)
                    fp = fs + [a, b, c]
                    h2 = hi_state(fp, fhi)
                    if h2 < 0:
                        continue
                    try:
                        Q = tuple(rows3.b2d3(list(P)))
                    except Exception:
                        Q = None
                    if Q is not None:
                        l = lcp(Q, T)
                        if l > best[0] and isstd(P, 'BMS'):
                            best[0], best[1] = l, P
                        if len(Q) > LT + SL:
                            continue
                        if l < len(Q) - SL:
                            continue
                    if not isstd(P, 'BMS'):
                        continue
                    cnt[0] += 1
                    if cnt[0] >= nodecap:
                        cap[0] = True
                        return
                    rec(P, fp, h2)
                    if cap[0]:
                        return

    rec((), [], hi_state([], fhi))
    return best[0], best[1], cnt[0], cap[0]


def expmap(N, m):
    """T = expand(N, m) の第 i 柱が N の第 src 柱の第 cp 写しであることの表。
    返り値 (src の並び, cp の並び, r, bp)。頭 N[:r] は cp = -1。"""
    X = len(N); x = X - 1; Y = len(N[0])
    t = max(y for y in range(Y) if N[x][y] > 0)
    P = pim(N)
    r = P[x][t]
    bp = x - r
    src, cp = [], []
    for i in range(r):
        src.append(i); cp.append(-1)
    for a in range(m):
        for xx in range(bp):
            src.append(r + xx); cp.append(a)
    return src, cp, r, bp


def probe(A, m, T=None, nodecap=40000):
    """1 対の逆算。返り値は dict。"""
    A = tuple(A)
    N, PR = provc.b2d3p(list(A))
    if T is None:
        T = tuple(expand(N, m))
    k, P, cnt, cap = maxpre(A, T, nodecap=nodecap)
    src, cp, r, bp = expmap(N, m)
    d = dict(A=A, m=m, T=T, N=N, k=k, P=P, nodes=cnt, capped=cap,
             r=r, bp=bp, LT=len(T), LN=len(N))
    if k < len(T):
        d['col'] = T[k]
        d['src'] = src[k]
        d['cp'] = cp[k]
        d['prov'] = PR[src[k]]
        d['ocol'] = A[PR[src[k]][1]]
        d['ncol'] = N[src[k]]
    return d


_TASK = None


def _w(t):
    A, m, T = t
    t0 = time.time()
    d = probe(A, m, T)
    d['sec'] = time.time() - t0
    return d


def run(pkl='/home/koteitan/proofs/dbms/tools/dbms/g2/bad6.pkl', jobs=28,
        out='/home/koteitan/proofs/dbms/tools/dbms/g2/probe6.pkl'):
    bad = pickle.load(open(pkl, 'rb'))
    tasks = [(tuple(A), m, tuple(map(tuple, T))) for A, m, T in bad]
    t0 = time.time()
    ctx = mp.get_context('fork')
    with ctx.Pool(min(jobs, len(tasks))) as pool:
        res = list(pool.imap_unordered(_w, tasks, chunksize=1))
    pickle.dump(res, open(out, 'wb'))
    print('%d 対 %.0fs  打ち切り %d' % (len(res), time.time() - t0,
                                        sum(1 for d in res if d['capped'])))
    return res


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'run':
        run(jobs=int(sys.argv[2]) if len(sys.argv) > 2 else 28)
    else:
        from core import parse
        for s, ms in [("(0,0,0)(1,1,1)(2,0,0)(3,1,1)(1,1,1)", (2, 3)),
                      ("(0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,1,0)", (3,)),
                      ("(0,0,0)(1,1,1)(2,1,0)(2,1,0)(1,1,0)", (2, 3)),
                      ("(0,0,0)(1,1,1)(2,1,0)(3,1,0)(1,1,0)", (2, 3))]:
            A = tuple(parse(s, 3))
            for m in ms:
                t0 = time.time()
                d = probe(A, m)
                print('A=%s m=%d' % (show(A), m))
                print('  N   = %s' % show(d['N']))
                print('  T   = %s (%d 柱, r=%d bp=%d)'
                      % (show(d['T']), d['LT'], d['r'], d['bp']))
                print('  最長の像の接頭辞 k=%d  証人 P=%s  節点 %d %s %.1fs'
                      % (d['k'], show(d['P']) if d['P'] else '-', d['nodes'],
                         '打ち切り' if d['capped'] else '', time.time() - t0))
                if 'col' in d:
                    print('  詰まる柱 T[%d]=%s  写し %d 本目  N[%d]=%s  '
                          'もとの柱 A[%d]=%s  出どころ %s'
                          % (d['k'], d['col'], d['cp'], d['src'],
                             d['ncol'], d['prov'][1], d['ocol'], d['prov']))
