"""G2 段 7: 「最初に像で有り得なくなる柱」の位置を締め直す。

段 2 の `maxpre` は像の枝刈り（SL=4）を通すので**取りこぼす**（実測: F1 の
代表で DFS は 7 で止まるが、`d2b3(T)` の接頭辞をたどると 10 まで届く）。
安い側（候補 B = d2b3(T) の接頭辞ぜんぶ）と合わせて最大を取る。
結果の k は**下からの評価**（真の値はこれ以上）である。
"""
import sys, collections, pickle
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import rows3, provc, inv3
from core import show, isstd, parse, pim
from rows3 import key
from m_imgclosed import lcp
from g2a import ctype, tail2
from g2e import pstr

SC = '/home/koteitan/proofs/dbms/tools/dbms/g2/'
R = pickle.load(open(SC + 'probe6.pkl', 'rb'))
byA = collections.defaultdict(list)
for d in R:
    byA[d['A']].append(d)
for v in byA.values():
    v.sort(key=lambda d: d['m'])


def candk(T):
    """候補 B = d2b3(T) の接頭辞から届く最長の lcp と、その証人。"""
    try:
        B = tuple(map(tuple, inv3.d2b3(list(T))))
    except Exception:
        return 0, None
    if not B:
        return 0, None
    best, bp = 0, None
    for k in range(1, len(B) + 1):
        P = B[:k]
        if not isstd(P, 'BMS'):
            continue
        try:
            Q = tuple(rows3.b2d3(list(P)))
        except Exception:
            continue
        l = lcp(Q, T)
        if l > best:
            best, bp = l, P
    return best, bp


def expsrc(N, m, i):
    X = len(N); x = X - 1; Y = len(N[0])
    t = max(y for y in range(Y) if N[x][y] > 0)
    r = pim(N)[x][t]
    bp = x - r
    if i < r:
        return r, bp, i, -1
    j = i - r
    return r, bp, r + j % bp, j // bp


out = {}
for A in sorted(byA, key=key):
    d = byA[A][0]
    T = d['T']
    ck, cp_ = candk(T)
    k = max(d['k'], ck)
    N, PR = provc.b2d3p(list(A))
    o = dict(A=A, m=d['m'], T=T, k=k, kdfs=d['k'], kcand=ck, LT=len(T))
    if k < len(T):
        r, bp, src, cpi = expsrc(N, d['m'], k)
        o.update(col=T[k], src=src, cp=cpi, r=r, bp=bp, prov=PR[src],
                 ocol=A[PR[src][1]])
    out[A] = o
pickle.dump(out, open(SC + 'kstar6.pkl', 'wb'))

print('DFS だけの k と締め直した k の差:',
      collections.Counter(out[A]['k'] - out[A]['kdfs'] for A in out).most_common())
print('T 全部が像の接頭辞（k = |T|）:', sum(1 for A in out if out[A]['k'] == len(out[A]['T'])), '/', len(out))
print()
M = collections.Counter()
for A, o in out.items():
    if o['k'] == len(o['T']):
        M[('III 末尾切れ', '-', '-')] += 1
    else:
        M[('I 写しの頭' if o['src'] == o['r'] else 'II 写しの途中',
           pstr(o['prov']), ctype(o['col']))] += 1
print('仕掛け x 詰まる柱を出した分岐 x 柱の型')
for k, v in M.most_common():
    print('%3d  %-14s %-20s %s' % (v, k[0], k[1], k[2]))
print()
print('何番目の写しで詰まるか:',
      sorted(collections.Counter(out[A].get('cp') for A in out).items(), key=str))
print('写しの中の何本目か    :',
      sorted(collections.Counter(
          (out[A]['src'] - out[A]['r']) if 'src' in out[A] else None
          for A in out).items(), key=str))
