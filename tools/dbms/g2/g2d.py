"""G2 段 4: 代表 1 個を G1 と同じ深さで逆算して刷る。"""
import sys, pickle, collections
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import rows3, provc, inv3
from core import parse, show, expand, isstd
import g2b

SC = '/home/koteitan/proofs/dbms/tools/dbms/g2/'


_CACHE = None


def cached(A, m):
    global _CACHE
    if _CACHE is None:
        try:
            _CACHE = {(d['A'], d['m']): d
                      for d in pickle.load(open(SC + 'probe6.pkl', 'rb'))}
        except Exception:
            _CACHE = {}
    return _CACHE.get((tuple(A), m))


def deep(A, ms):
    A = tuple(A)
    N, PR = provc.b2d3p(list(A))
    print('A       = %s   (%d 列)' % (show(A), len(A)))
    print('conv3 A = %s   (%d 柱)' % (show(N), len(N)))
    print('  柱ごとの出どころ:')
    for i, (c, p) in enumerate(zip(N, PR)):
        print('    N[%d]=%-9s <- A[%d]=%-9s %s%s%s'
              % (i, str(c), p[1], str(A[p[1]]), p[0],
                 '' if p[2] is None else ':' + p[2],
                 '' if not p[3] else '@' + '/'.join(p[3])))
    for m in ms:
        T = tuple(expand(N, m))
        lo = tuple(expand(A, max(m - 1, 1)))
        d = cached(A, m) or g2b.probe(A, m, T)
        print('  --- m=%d ---' % m)
        print('  T = conv3(A)<%d> = %s   (%d 柱)' % (m, show(T), len(T)))
        print('  窓の下 A<%d> = %s' % (max(m - 1, 1), show(lo)))
        print('  T の柱 -> conv3 A の柱: r=%d bp=%d（頭 %d 柱 ＋ 写し %d 本 x %d 柱）'
              % (d['r'], d['bp'], d['r'], m, d['bp']))
        print('  像で作れる最長の接頭辞 %d / %d 柱  証人 P = %s%s'
              % (d['k'], d['LT'], show(d['P']) if d['P'] else '-',
                 '  （節点 %d, 打ち切り %s）' % (d['nodes'], d['capped'])))
        if d['P']:
            print('    conv3 P = %s' % show(rows3.b2d3(list(d['P']))))
        if 'col' in d:
            k, src, cp = d['k'], d['src'], d['cp']
            p = PR[src]
            print('  詰まる柱 T[%d] = %s' % (k, str(d['col'])))
            print('    もと N[%d] = %s（写し %d 本目、写しの %d 本目の柱）'
                  % (src, str(d['ncol']), cp, src - d['r']))
            print('    それを出した分岐: %s%s%s   もとの BMS 柱 A[%d] = %s'
                  % (p[0], '' if p[2] is None else ':' + p[2],
                     '' if not p[3] else '@' + '/'.join(p[3]), p[1],
                     str(A[p[1]])))
            print('    上昇ぶん T[%d] - N[%d] = %s'
                  % (k, src, tuple(x - y for x, y in zip(d['col'], d['ncol']))))
        try:
            D = inv3.d2b3(list(T))
        except Exception:
            D = None
        if D:
            fD = tuple(rows3.b2d3(list(D)))
            print('  d2b3(T) = %s  (BMS 標準形 %s)  conv3 それ = %s  一致 %s'
                  % (show(D), isstd(tuple(D), 'BMS'), show(fD), fD == T))
        else:
            print('  d2b3(T) = なし')


if __name__ == '__main__':
    A = tuple(parse(sys.argv[1], 3))
    ms = [int(x) for x in sys.argv[2].split(',')]
    deep(A, ms)
